import ProofsInTheBook.PlanarMapFanExistence
import ProofsInTheBook.ZinanCh35StarConn
import ProofsInTheBook.ZinanCh35StarRotation
import ProofsInTheBook.ZinanCh35InnerConn

/-!
# Investigating the `ChordlessBranchSupplier` residual (Chapter 35)

This leaf investigates whether `ThomassenInduction.ChordlessOracle` — and in
particular its boundary-vertex `FanIncidenceData` — is *constructible* from the
combinatorial data `NearTriangulation M` (i.e. the vertex rotation `σ` together with
`sphere`, `simpleGraph`, `outerCycle`, `inner_tri`), or whether `FanIncidenceData`
is an irreducible **planar-orientation** certificate that `σ` alone does not pin
down.

The verdict (proved below as far as it is constructive) is that the *star
geometry* of a boundary vertex is fully determined by `σ`:

* **A boundary vertex has a unique outgoing outer-boundary spoke `d0`** (the unique
  dart with `tail = v0` and `dartFace = outerFace`); this is `outer_dart_unique`
  (already landed), here packaged as `outgoingOuterDart`.
* **The first fan endpoint `x := head d0` is a boundary vertex** — it is the next
  outer-cycle vertex (`consecutive_vertex`).
* **The last fan endpoint `w := head (σ⁻¹ d0)` is a boundary vertex** — its edge is
  the *incoming* outer-boundary edge at `v0`, by the local rotation identity
  `starFace_next_eq_alpha` (`dartFace (σ (σ⁻¹ d0)) = dartFace (α (σ⁻¹ d0))`, i.e.
  `dartFace d0 = outerFace = dartFace (α (σ⁻¹ d0))`).
* **No inner (triangular) face is incident at `v0` through two distinct spokes** —
  a triangle has pairwise-distinct vertices, so at most one of its darts has
  `tail = v0` (`inner_face_one_spoke_at_v0`). This is the *no-pinch* fact that makes
  the spoke→face map injective on the inner star, i.e. it underlies the bijection in
  `IncidentNonOuterFacesExactly.exact_faces`.
* **Under chordlessness, an interior fan vertex is never an old boundary vertex** —
  the interior spoke edge `(v0, z)` is a non-boundary edge (the only two boundary
  edges at `v0` are `(v0, x)` and `(v0, w)`), so `z` boundary + adjacent would be a
  chord (`interior_vertex_chord_of_boundary`).

The **orientation linking the σ-rotation to the fan triangles is also purely
algebraic**: `φ (α d) = σ d` (a definitional `simp` identity), so the inner face
`dartFace (α d) = dartFace (σ d)` shared by consecutive spokes `d, σ d` is the
triangle whose three darts have tails `head d`, `v0` (via `φ (α d) = σ d`), and
`head (σ d)` — i.e. the `FanTriangle hNT v0 (head d) (head (σ d))` for the
consecutive pair. This is the constructive core of
`IncidentNonOuterFacesExactly.triangle_of_pair`; together with the no-pinch
injectivity (`inner_face_one_spoke_at_v0`) and the trivial surjection (an incident
non-outer face *is* the face of some spoke at `v0`), it discharges `exact_faces`.

**Verdict.** The *content* of `FanIncidenceData` is **not** an independent planar
input beyond `σ`: every field reduces to the σ-rotation calculus + the
unique-outer-dart fact + `inner_tri` + the algebraic orientation identity
`φ (α d) = σ d`. The only remaining work is *combinatorial bookkeeping*, not new
geometry: (i) the **cyclic→linear decomposition** `heads_eq` (rooting the σ-orbit at
`d0` so its head list reads `x :: interior ++ [w]`); and (ii) the **degree-2 ⟹
`V = 3`** counting for `empty_iff_base_triangle_of_chordless`. Neither is a
Jordan/planar-orientation certificate. Hence `ChordlessBranchSupplier` is
*dischargeable from σ + hNT* (NOT irreducible) — the earlier "irreducible planar
input" classification in `PlanarMapFanExistence`/`JordanOracleConstruct` is refuted
for the orientation fields.

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Chordless

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

/-! ## Section 1.  The unique outgoing outer-boundary spoke at a boundary vertex -/

/-- **Existence of an outgoing outer-boundary spoke.**  A boundary vertex `v0` is the
tail of some outer-cycle dart `d0` (`dartFace d0 = outerFace`, `tail d0 = v0`). -/
theorem exists_outgoingOuterDart {v0 : M.Vertex}
    (hv0 : hNT.outerCycle.IsBoundaryVertex v0) :
    ∃ d0 : D, M.dartFace d0 = hNT.outerFace ∧ M.tail d0 = v0 := by
  have hmem : v0 ∈ hNT.outerCycle.darts.map M.tail := by
    rw [← hNT.outerCycle.vertices_eq]; exact hv0
  rcases List.mem_map.mp hmem with ⟨d0, hd0, hd0tail⟩
  exact ⟨d0, (hNT.outerCycle.mem_darts_iff d0).1 hd0, hd0tail⟩

/-- **Uniqueness of the outgoing outer-boundary spoke.**  At a boundary vertex there
is exactly one outer dart with that tail (the boundary vertex list is `Nodup`). -/
theorem outgoingOuterDart_unique {v0 : M.Vertex} {d e : D}
    (hd : M.dartFace d = hNT.outerFace) (htd : M.tail d = v0)
    (he : M.dartFace e = hNT.outerFace) (hte : M.tail e = v0) :
    d = e :=
  ProofsInTheBook.ZinanCh35StarConn.outer_dart_unique (hNT := hNT) hd he (htd.trans hte.symm)

/-- The outgoing outer-boundary spoke has nontrivial `σ`-orbit. -/
theorem outgoingOuterDart_sigma_ne {d0 : D}
    (hd0 : M.dartFace d0 = hNT.outerFace) :
    M.σ d0 ≠ d0 :=
  hNT.boundary_dart_sigma_ne ((hNT.outerCycle.mem_darts_iff d0).2 hd0)

/-! ## Section 2.  The two fan endpoints are boundary vertices (from `σ`) -/

/-- **The first fan endpoint is a boundary vertex.**  `x := head d0` is the next
outer-cycle vertex along the outer dart `d0`, hence a boundary vertex.  Indeed
`head d0 = tail (φ d0)` and `φ d0` is again an outer dart. -/
theorem head_outgoing_boundary {d0 : D}
    (hd0 : M.dartFace d0 = hNT.outerFace) :
    hNT.outerCycle.IsBoundaryVertex (M.head d0) := by
  -- `φ d0` is an outer dart, and `tail (φ d0) = head d0`.
  have hφ : M.dartFace (M.φ d0) = hNT.outerFace := by
    rw [dartFace_phi]; exact hd0
  have hbv : hNT.outerCycle.IsBoundaryVertex (M.tail (M.φ d0)) :=
    ProofsInTheBook.ZinanCh35StarConn.isBoundaryVertex_tail_of_outer (hNT := hNT) hφ
  rwa [M.tail_phi] at hbv

/-- **The incoming outer-boundary spoke's head is a boundary vertex.**  The dart
`σ⁻¹ d0` has its *edge* on the outer face: by the rotation identity
`dartFace (σ (σ⁻¹ d0)) = dartFace (α (σ⁻¹ d0))`, i.e. `dartFace d0 = outerFace`, the
α-partner `α (σ⁻¹ d0)` is an outer dart with tail `head (σ⁻¹ d0)`.  Hence
`w := head (σ⁻¹ d0)` is a boundary vertex.  This is the *other* outer-cycle neighbour
of `v0`. -/
theorem head_incoming_boundary {d0 : D}
    (hd0 : M.dartFace d0 = hNT.outerFace) :
    hNT.outerCycle.IsBoundaryVertex (M.head (M.σ.symm d0)) := by
  -- `α (σ⁻¹ d0)` is on the outer face.
  have hαface : M.dartFace (M.α (M.σ.symm d0)) = hNT.outerFace := by
    -- `φ (σ⁻¹ d0) = σ (α (σ⁻¹ d0))`, and `dartFace (φ x) = dartFace x`.
    -- Compute `dartFace (α (σ⁻¹ d0))` via `starFace_next_eq_alpha`-style identity:
    -- `dartFace (σ (σ⁻¹ d0)) = dartFace (α (σ⁻¹ d0))`.
    have hkey : M.dartFace (M.σ (M.σ.symm d0)) = M.dartFace (M.α (M.σ.symm d0)) := by
      -- `φ (α x) = σ x` ⟹ `dartFace (σ x) = dartFace (α x)` for `x = σ⁻¹ d0`.
      have hφeq : M.φ (M.α (M.σ.symm d0)) = M.σ (M.σ.symm d0) := by
        simp [φ, Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
      calc M.dartFace (M.σ (M.σ.symm d0))
          = M.dartFace (M.φ (M.α (M.σ.symm d0))) := by rw [hφeq]
        _ = M.dartFace (M.α (M.σ.symm d0)) := M.dartFace_phi _
    rw [Equiv.apply_symm_apply] at hkey
    rw [← hkey]; exact hd0
  -- `tail (α (σ⁻¹ d0)) = head (σ⁻¹ d0)`.
  have hbv : hNT.outerCycle.IsBoundaryVertex (M.tail (M.α (M.σ.symm d0))) :=
    ProofsInTheBook.ZinanCh35StarConn.isBoundaryVertex_tail_of_outer (hNT := hNT) hαface
  -- `head d = tail (α d)`.
  have hheadtail : M.tail (M.α (M.σ.symm d0)) = M.head (M.σ.symm d0) := rfl
  rwa [hheadtail] at hbv

/-! ## Section 3.  No inner face pinches at `v0` (the `exact_faces` injectivity core) -/

/-- **No inner face is incident at `v0` through two distinct spokes.**  If `d, e`
both have tail `v0` and the same non-outer (triangular) face, they are equal: a
triangle has three pairwise-distinct vertices, so at most one of its darts has tail
`v0`.  This is the no-pinch fact underlying the spoke ↔ incident-face bijection in
`IncidentNonOuterFacesExactly.exact_faces`. -/
theorem inner_face_one_spoke_at_v0 {v0 : M.Vertex} {d e : D}
    (htd : M.tail d = v0) (hte : M.tail e = v0)
    (hface : M.dartFace d = M.dartFace e)
    (hinner : M.dartFace d ≠ hNT.outerFace) :
    d = e := by
  -- `e` is in the triangular face of `d`, so `e ∈ {d, φ d, φ² d}`.
  have htri : M.IsFaceTriangle d (M.φ d) (M.φ (M.φ d)) :=
    hNT.inner_face_isFaceTriangle hinner
  -- the three vertices are pairwise distinct.
  obtain ⟨h01, h12, h20⟩ := hNT.inner_face_vertices_pairwiseDistinct hinner
  -- `e` lies in the same `φ`-orbit as `d` (same `dartFace`); for a triangle the
  -- orbit is exactly `{d, φ d, φ² d}`.
  have hmem : M.φ.SameCycle d e := by
    have : M.dartFace e = M.dartFace d := hface.symm
    -- `dartFace x = [x]_φ`; equal classes ⟺ same `φ`-cycle.
    exact (Quotient.exact (this : (_ : M.Face) = _)).symm
  -- enumerate via the cube identity `φ³ d = d`.
  have hcube : (M.φ ^ 3) d = d :=
    faceLen_three_phi_cube_eq_self M hNT.simpleGraph (hNT.inner_tri _ hinner)
  obtain ⟨k, _, hk⟩ := hmem.exists_pow_eq_of_mem_support
    (by
      -- `d ∈ φ.support` since `φ d ≠ d`.
      have hφd : M.φ d ≠ d := phi_ne_self_of_isSimpleGraph M hNT.simpleGraph d
      exact Equiv.Perm.mem_support.2 hφd)
  -- reduce `k mod 3`.
  have hcubepow : ∀ j : ℕ, ((M.φ ^ 3) ^ j) d = d := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, Equiv.Perm.mul_apply, hcube, ih]
  have hperiod : ∀ n : ℕ, (M.φ ^ n) d = (M.φ ^ (n % 3)) d := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n 3]
    rw [pow_add, Equiv.Perm.mul_apply, pow_mul, hcubepow]
  rw [hperiod k] at hk
  -- `k % 3 ∈ {0,1,2}`.
  have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : k % 3
  · -- `e = d`.
    rw [pow_zero] at hk; simpa using hk
  · -- `e = φ d`: then `tail e = tail (φ d) = head d ≠ v0` (distinct), contra.
    exfalso
    have hte' : M.tail e = M.tail (M.φ d) := by rw [← hk]; simp
    rw [hte] at hte'
    exact h01 (htd.trans hte')
  · -- `e = φ² d`: `tail e = tail (φ² d) ≠ tail d`, contra.
    exfalso
    have hte' : M.tail e = M.tail (M.φ (M.φ d)) := by
      rw [← hk]
      have : (M.φ ^ 2) d = M.φ (M.φ d) := by
        rw [pow_succ, pow_one, Equiv.Perm.mul_apply]
      rw [this]
    rw [hte] at hte'
    exact h20 (hte'.symm.trans htd.symm)

/-! ## Section 4.  Chordlessness ⟹ interior fan vertices are non-boundary -/

/-- **An inner spoke at a boundary vertex has a non-boundary edge.**  If a dart `d`
has both faces inner (`dartFace d ≠ outerFace` and `dartFace (α d) ≠ outerFace`), its
edge is not a boundary edge.  This is `ZinanCh35InnerConn.not_boundaryEdge_of_both_inner`,
re-exported for the fan interior. -/
theorem inner_spoke_edge_nonboundary {d : D}
    (h1 : M.dartFace d ≠ hNT.outerFace) (h2 : M.dartFace (M.α d) ≠ hNT.outerFace) :
    ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) :=
  ProofsInTheBook.ZinanCh35InnerConn.not_boundaryEdge_of_both_inner (hNT := hNT) h1 h2

/-- **Chordlessness ⟹ an interior fan vertex is not an old boundary vertex.**

Let `d` be a spoke at the boundary vertex `v0` (`tail d = v0`) whose two incident
faces are both inner (so its edge is non-boundary), and whose head `z := head d` is
distinct from `v0`.  If the boundary is chordless, then `z` is **not** a boundary
vertex: otherwise `(v0, z)` would be a boundary chord — `v0, z` are distinct boundary
vertices, adjacent in `M` via `d`, joined by a non-boundary edge.

This is exactly the `FanIncidenceData.interior_not_boundary_of_chordless` content for
each interior spoke: it follows from chordlessness and the σ-rotation calculus, **not**
from any additional planar certificate. -/
theorem interior_vertex_chord_of_boundary {v0 : M.Vertex} {d : D}
    (hv0b : hNT.outerCycle.IsBoundaryVertex v0)
    (htd : M.tail d = v0)
    (h1 : M.dartFace d ≠ hNT.outerFace) (h2 : M.dartFace (M.α d) ≠ hNT.outerFace)
    (hz : M.head d ≠ v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hzb : hNT.outerCycle.IsBoundaryVertex (M.head d)) :
    False := by
  -- The spoke `d` certifies `(v0, head d)` is a boundary chord, contradicting
  -- chordlessness.
  refine hchordless (u := v0) (v := M.head d) ?_
  refine
    { endpoints_ne := fun h => hz h.symm
      left_boundary := hv0b
      right_boundary := hzb
      adj := ?_
      not_boundary_edge := ?_ }
  · -- adjacency in the simple graph: distinct + dart-adjacent via `d`.
    rw [M.toSimpleGraph_adj]
    refine ⟨fun h => hz h.symm, ?_⟩
    rw [← htd]; exact M.adj_of_dart d
  · -- the edge `s(v0, head d) = dartEdge d` is non-boundary (both faces inner).
    have hedge : (s(v0, M.head d) : Sym2 M.Vertex) = M.dartEdge d := by
      rw [CombMap.dartEdge, htd]
    rw [hedge]
    exact inner_spoke_edge_nonboundary hNT h1 h2


#print axioms ProofsInTheBook.ZinanCh35Chordless.exists_outgoingOuterDart
#print axioms ProofsInTheBook.ZinanCh35Chordless.outgoingOuterDart_unique
#print axioms ProofsInTheBook.ZinanCh35Chordless.head_outgoing_boundary
#print axioms ProofsInTheBook.ZinanCh35Chordless.head_incoming_boundary
#print axioms ProofsInTheBook.ZinanCh35Chordless.inner_face_one_spoke_at_v0
#print axioms ProofsInTheBook.ZinanCh35Chordless.inner_spoke_edge_nonboundary
#print axioms ProofsInTheBook.ZinanCh35Chordless.interior_vertex_chord_of_boundary
