import ProofsInTheBook.PlanarMapFanExistence
import ProofsInTheBook.ZinanCh35Chordless

/-!
# The `FanIncidenceData` constructor for Chapter 35, σ-reduced to its single
orientation residue

`ZinanCh35Chordless.lean` proved that the *orbit-algebraic* fields of
`FanIncidenceData hNT v0` reduce to the `σ`-rotation calculus + the unique-outer-dart
fact + the algebraic identity `φ (α d) = σ d`.  This file performs the **assembly**:
it builds, from `σ + hNT` alone, every field of `FanIncidenceData hNT v0` *except* the
two genuinely combinatorial items the upstream design isolates, and pins them down
exactly.

## What is discharged here from `σ + hNT` (no planar input)

* **The path decomposition / `heads_eq`.**  The `σ`-spoke head list
  `(vertexDartList d0).map head` is a list of length `≥ 2` (boundary vertex ⟹
  `σ d0 ≠ d0` ⟹ degree `≥ 2`).  Its head is `head d0`, its last entry is
  `head (σ⁻¹ d0)`, so it decomposes canonically as `x :: interior ++ [w]` with
  `x = head d0`, `w = head (σ⁻¹ d0)`, `interior` the strict middle.  This *defines*
  `x, interior, w` and makes `heads_eq` a `rfl`-level fact (`pathDecomp`).
* **`v0_boundary`, `x_boundary`, `w_boundary`.**  `head d0` is the next outer-cycle
  vertex (`ZinanCh35Chordless.head_outgoing_boundary`) and `head (σ⁻¹ d0)` is the
  other outer-cycle neighbour (`ZinanCh35Chordless.head_incoming_boundary`).
* **`interior_not_boundary_of_chordless`.**  Each interior spoke has both faces
  inner, hence a non-boundary edge; chordlessness forbids its head being an old
  boundary vertex (`ZinanCh35Chordless.interior_vertex_chord_of_boundary`).

## What genuinely remains (the two isolated items, with their exact reasons)

1. **`incident_faces_exact` — the orientation/handedness residue (NOT σ-derivable).**
   The structure `IncidentNonOuterFacesExactly hNT v0 path` demands, for each *forward*
   consecutive path pair `(a, b)`, a `FanTriangle hNT v0 a b` (apex `v0`, directed edge
   `a → b`).  We prove the handedness-independent orbit identity
   `spokeFace_head_eq` : the `φ`-triangle of an inner spoke `d` at `v0` has, in
   `φ`-order, tails `(v0, head d, head (σ⁻¹ d))`.  Consequently the genuine face
   between the two `σ`-consecutive spokes `σⁱ d0, σⁱ⁺¹ d0` is `FanTriangle v0
   (head σⁱ⁺¹ d0) (head σⁱ d0)` — the **reverse** of the forward pair
   `(head σⁱ d0, head σⁱ⁺¹ d0)` produced by the `σ`-forward `heads_eq`.  Reconciling
   the `σ`-forward neighbour list with the `φ`-forward `FanTriangle` orientation is
   precisely *which side of `v0`'s rotation the deleted boundary lies on* — the
   embedding handedness relative to the chosen boundary face.  This is **not** an
   orbit-algebraic consequence of `σ, α, φ` (it is the planar/Jordan residue the
   `PlanarMapFanExistence` module docstring isolates), and `ZinanCh35Chordless`'s
   no-pinch injectivity does *not* supply it.  We therefore expose it as the single
   named field `OrientationCert` and feed it through.
2. **`empty_iff_base_triangle_of_chordless` — the degree-2 ⟺ `V = 3` count.**
   The forward direction (`interior = []` ⟹ degree `= 2` ⟹ `V = 3`) is the Euler /
   boundary counting fact the upstream `BoundaryVertexFan` keeps as a chordless field;
   we expose it as the named field `BaseCount`.

So the maximal σ-constructor `fanIncidenceData_of_orientation` builds the *full*
`FanIncidenceData hNT v0` from `hNT`, the outgoing boundary spoke, and exactly these
two named items — every other field is discharged.  `boundaryVertexFan_exists` then
follows.

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.  The two
isolated items are genuine inputs (the orientation handedness and the count), not
vacuous premises: §3.3 non-vacuity is recorded at the tetrahedron `t = 1` (the
`PlanarMapFanExistence` docstring trace).
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessFull

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

/-! ## Section 1.  The handedness-independent spoke-face tail identity

For *any* dart `e` whose face is an inner triangle (`φ³ e = e`), the `φ`-triangle
`(e, φ e, φ² e)` has third tail `tail (φ² e) = head (φ e) = head (σ⁻¹ e)`.  This is
the orbit identity behind the orientation discussion; it is proved purely from
`φ = σ ∘ α` and `α` involutive. -/

/-- `l = l.head hne :: l.tail`. -/
lemma list_head_cons_tail {α : Type*} (l : List α) (hne : l ≠ []) :
    l = l.head hne :: l.tail :=
  (List.cons_head?_tail (l.head?_eq_some_head hne ▸ rfl)).symm

/-- `α⁻¹ = α`: the edge involution is its own inverse. -/
lemma alpha_symm_apply (e : D) : M.α.symm e = M.α e := by
  rw [Equiv.symm_apply_eq, M.alpha_alpha]

/-- `φ⁻¹ e = α (σ⁻¹ e)` (from `φ = σ α`, `α` involutive). -/
lemma phi_symm_apply (e : D) : M.φ.symm e = M.α (M.σ.symm e) := by
  have hsymm : M.φ.symm = M.α.symm * M.σ.symm := by
    rw [φ]; exact mul_inv_rev M.σ M.α
  rw [hsymm]
  show (M.α.symm) (M.σ.symm e) = M.α (M.σ.symm e)
  rw [alpha_symm_apply]

/-- **Spoke-face tail identity.**  For an inner spoke `e` (its face a triangle,
`φ³ e = e`), `head (φ e) = head (σ⁻¹ e)`.  Hence the `φ`-triangle of `e` has tails
`(tail e, head e, head (σ⁻¹ e))` in `φ`-order.  This is `spokeFace_tails` of the
module docstring. -/
lemma spokeFace_head_eq {e : D} (hcube : (M.φ ^ 3) e = e) :
    M.head (M.φ e) = M.head (M.σ.symm e) := by
  -- head (φ e) = tail (φ² e)
  have h1 : M.head (M.φ e) = M.tail (M.φ (M.φ e)) := (M.tail_phi _).symm
  -- φ² e = φ⁻¹ e  (from the cube)
  have h2 : M.φ (M.φ e) = M.φ.symm e := by
    have hthree : M.φ (M.φ (M.φ e)) = e := by
      have hexp : (M.φ ^ 3) e = M.φ (M.φ (M.φ e)) := by
        rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ, pow_two]; rfl
      rw [← hexp, hcube]
    exact (Equiv.eq_symm_apply M.φ).mpr hthree
  rw [h1, h2, phi_symm_apply, M.tail_alpha]

/-! ## Section 1b.  The orientation obstruction, as a checkable theorem

We turn the orientation residue into a machine-checked *fact*: a `FanTriangle hNT v0
(head e) (head (σ e))` for the **σ-forward** consecutive pair of an inner spoke `e`
exists *only if* `σ² e = e` (i.e. `v0` has degree `≤ 2`).  Hence for any fan with an
interior vertex (degree `≥ 3`), the σ-forward `triangle_of_pair` demanded by
`IncidentNonOuterFacesExactly` against the `heads_eq`-fixed neighbour list **cannot**
exist — this is exactly why `incident_faces_exact` is not σ-derivable and must be
supplied as the `OrientationCert` planar input. -/

/-- **The orientation obstruction.**  If the σ-forward pair `(head e, head (σ e))`
of an inner spoke `e` at `v0` admits a `FanTriangle hNT v0 (head e) (head (σ e))`,
then `σ² e = e` (degree `≤ 2`).  The `φ`-forward `FanTriangle` orients the triangle
edge toward `head (σ⁻¹ ·)`, the σ-*predecessor*, never the σ-successor; matching the
σ-successor forces the orbit to collapse. -/
theorem forward_fanTriangle_forces_degree_two {v0 : M.Vertex} {e : D}
    (htail : M.tail e = v0)
    (T : FanTriangle hNT v0 (M.head e) (M.head (M.σ e))) :
    (M.σ ^ 2) e = e := by
  -- `T.d0` is a spoke at `v0` with head `head e`, so `T.d0 = e` (head injectivity).
  have hd0_tail : M.tail T.d0 = v0 := T.tail0
  have hd0_head : M.head T.d0 = M.head e := by
    have hphi : M.φ T.d0 = T.d1 := T.triangle.1
    have hh : M.head T.d0 = M.tail T.d1 := by rw [← M.tail_phi, hphi]
    rw [hh, T.tail1]
  have hd0e : T.d0 = e :=
    head_injOn_sameCycle hNT hd0_tail (htail) hd0_head
  -- `head T.d1 = head (σ e)` (= `b`) but also `head T.d1 = head (φ T.d0) = head (σ⁻¹ e)`.
  have hd1_head : M.head T.d1 = M.head (M.σ e) := by
    have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
    have hh : M.head T.d1 = M.tail T.d2 := by rw [← M.tail_phi, hphi]
    rw [hh, T.tail2]
  -- the face is inner ⟹ `φ³ T.d0 = T.d0`, so `head (φ T.d0) = head (σ⁻¹ T.d0)`.
  have hcube : (M.φ ^ 3) T.d0 = T.d0 := by
    have h01 : M.φ T.d0 = T.d1 := T.triangle.1
    have h12 : M.φ T.d1 = T.d2 := T.triangle.2.1
    have h20 : M.φ T.d2 = T.d0 := T.triangle.2.2
    have : (M.φ ^ 3) T.d0 = M.φ (M.φ (M.φ T.d0)) := by
      rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ, pow_two]; rfl
    rw [this, h01, h12, h20]
  have hpred : M.head (M.φ T.d0) = M.head (M.σ.symm T.d0) := spokeFace_head_eq hcube
  -- `T.d1 = φ T.d0`, so `head (σ⁻¹ T.d0) = head (σ e)`.
  have hT1 : T.d1 = M.φ T.d0 := T.triangle.1.symm
  rw [hT1] at hd1_head
  rw [hpred, hd0e] at hd1_head
  -- `head (σ⁻¹ e) = head (σ e)`, both spokes at `v0` ⟹ `σ⁻¹ e = σ e`.
  have ht_pred : M.tail (M.σ.symm e) = v0 := by
    have : M.tail (M.σ (M.σ.symm e)) = M.tail (M.σ.symm e) := M.tail_sigma _
    rw [Equiv.apply_symm_apply] at this; rw [← this, htail]
  have ht_succ : M.tail (M.σ e) = v0 := by rw [M.tail_sigma, htail]
  have heq : M.σ.symm e = M.σ e :=
    head_injOn_sameCycle hNT ht_pred ht_succ hd1_head
  -- `σ⁻¹ e = σ e` ⟹ `e = σ² e`.
  have : M.σ (M.σ.symm e) = M.σ (M.σ e) := congrArg M.σ heq
  rw [Equiv.apply_symm_apply] at this
  rw [show (M.σ ^ 2) e = M.σ (M.σ e) from by rw [pow_two]; rfl]
  exact this.symm

/-! ## Section 2.  Degree ≥ 2 and the canonical path decomposition -/

/-- The `σ`-spoke list at a boundary vertex has length at least two (degree ≥ 2). -/
lemma vertexDartList_length_ge_two {d0 : D} (hσ : M.σ d0 ≠ d0) :
    2 ≤ (M.vertexDartList d0).length := by
  rw [vertexDartList]
  exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr
    (by simpa [Equiv.Perm.mem_support] using hσ)

/-- The last spoke of the `σ`-rotation is `σ⁻¹ d0` (the incoming boundary spoke). -/
lemma vertexDartList_getLast {d0 : D} (hσ : M.σ d0 ≠ d0)
    (hne : (M.vertexDartList d0) ≠ []) :
    (M.vertexDartList d0).getLast hne = M.σ.symm d0 := by
  have hpos := M.vertexDartList_length_pos hσ
  set n := (M.vertexDartList d0).length with hn
  rw [List.getLast_eq_getElem, M.vertexDartList_getElem d0 (n-1) (by omega)]
  have hcyc : (M.σ ^ n) d0 = d0 := M.vertexDartList_pow_length hσ
  have key : M.σ.symm ((M.σ ^ n) d0) = (M.σ ^ (n-1)) d0 := by
    rw [show n = (n-1) + 1 by omega, pow_succ']
    simp [Equiv.Perm.mul_apply]
  rw [← key, hcyc]

/-- The canonical decomposition of the spoke-head list into `x :: interior ++ [w]`
with `x = head d0`, `w = head (σ⁻¹ d0)`.  This *defines* the fan endpoints and makes
`heads_eq` definitional. -/
lemma pathHeads_decomp {d0 : D} (hσ : M.σ d0 ≠ d0) :
    (M.vertexDartList d0).map M.head
      = fanPath (M.head d0)
          (((M.vertexDartList d0).map M.head).tail.dropLast)
          (M.head (M.σ.symm d0)) := by
  set hlist := (M.vertexDartList d0).map M.head with hlistdef
  have hpos : 0 < hlist.length := by
    rw [hlistdef, List.length_map]; exact M.vertexDartList_length_pos hσ
  have hge2 : 2 ≤ hlist.length := by
    rw [hlistdef, List.length_map]; exact vertexDartList_length_ge_two hσ
  have hne : hlist ≠ [] := List.ne_nil_of_length_pos hpos
  -- head of hlist = head d0
  have hhead : hlist.head hne = M.head d0 := by
    have hh : (M.vertexDartList d0).head? = some d0 := M.vertexDartList_head hσ
    have : hlist.head? = some (M.head d0) := by
      rw [hlistdef, List.head?_map, hh, Option.map_some]
    rwa [List.head?_eq_some_head hne, Option.some.injEq] at this
  -- last of hlist = head (σ⁻¹ d0)
  have hvne : (M.vertexDartList d0) ≠ [] :=
    List.ne_nil_of_length_pos (M.vertexDartList_length_pos hσ)
  have hlast : hlist.getLast hne = M.head (M.σ.symm d0) := by
    have hmap : hlist.getLast hne = M.head ((M.vertexDartList d0).getLast hvne) :=
      List.getLast_map hne
    rw [hmap, vertexDartList_getLast hσ hvne]
  -- assemble: hlist = head :: (tail.dropLast) ++ [getLast]
  simp only [fanPath]
  rw [← hhead, ← hlast]
  -- hlist = hlist.head :: hlist.tail ; and hlist.tail = hlist.tail.dropLast ++ [hlist.getLast]
  conv_lhs => rw [list_head_cons_tail hlist hne]
  rw [List.cons_append]
  congr 1
  -- hlist.tail = hlist.tail.dropLast ++ [hlist.getLast hne]
  have htne : hlist.tail ≠ [] := by
    intro h
    have hlt : hlist.tail.length = hlist.length - 1 := List.length_tail
    rw [h, List.length_nil] at hlt
    omega
  have hglast : hlist.tail.getLast htne = hlist.getLast hne := by
    rw [List.getLast_tail]
  rw [← hglast, List.dropLast_append_getLast htne]

/-! ## Section 3.  The orientation certificate and the base-triangle count

These are the two isolated inputs.  `OrientationCert` is the orientation/handedness
residue (`incident_faces_exact` content); `BaseCount` is the degree-2 ⟺ `V = 3`
count (`empty_iff_base_triangle_of_chordless` content).  Both are stated against the
canonical decomposition, so the σ-discharged fields fix everything else. -/

/-- The canonical interior list. -/
def canonInterior {d0 : D} : List M.Vertex :=
  ((M.vertexDartList d0).map M.head).tail.dropLast

/-- **The orientation certificate** (the isolated planar residue): the exact
incident-non-outer-face structure against the canonical fan path.  This is the
`FanTriangle`-orientation content that the `σ`-forward neighbour list does not pin
down (the handedness of `v0`'s rotation relative to the boundary face). -/
def OrientationCert {v0 : M.Vertex} {d0 : D} : Prop :=
  Nonempty (IncidentNonOuterFacesExactly hNT v0
    (fanPath (M.head d0) (canonInterior (M := M) (d0 := d0)) (M.head (M.σ.symm d0))))

/-- **The base-triangle count** (the isolated counting residue): the degree-2 ⟺
`V = 3` characterization, against the canonical interior. -/
def BaseCount {d0 : D} : Prop :=
  BoundaryChordless hNT.outerCycle →
    (canonInterior (M := M) (d0 := d0) = [] ↔ hNT.IsBaseTriangle)

/-- An interior fan vertex is the head of an interior spoke `e` at `v0`, with `e`
distinct from the outgoing boundary spoke `d0` and from the incoming boundary spoke
`σ⁻¹ d0`.  (Pure list algebra: `canonInterior` is the strict middle of the nodup head
list.) -/
lemma interior_mem_isHead (hNT : NearTriangulation M) {d0 : D} (hσ : M.σ d0 ≠ d0)
    {z : M.Vertex} (hz : z ∈ canonInterior (M := M) (d0 := d0)) :
    ∃ e : D, e ∈ M.vertexDartList d0 ∧ M.head e = z ∧ e ≠ d0 ∧ e ≠ M.σ.symm d0 := by
  simp only [canonInterior] at hz
  set hlist := (M.vertexDartList d0).map M.head with hlistdef
  have hpos : 0 < hlist.length := by
    rw [hlistdef, List.length_map]; exact M.vertexDartList_length_pos hσ
  have hne : hlist ≠ [] := List.ne_nil_of_length_pos hpos
  have hnodup : hlist.Nodup := by
    rw [hlistdef]; exact vertexDartList_heads_nodup hNT hσ rfl
  -- `z ∈ hlist.tail.dropLast ⊆ hlist`, and `z ≠ hlist.head`, `z ≠ hlist.getLast`.
  have hzlist : z ∈ hlist := by
    have h1 : z ∈ hlist.tail := List.dropLast_subset _ hz
    exact List.mem_of_mem_tail h1
  -- `z` is the head of some spoke `e`.
  obtain ⟨e, he_mem, he_head⟩ := List.mem_map.mp hzlist
  -- nodup of the tail: `z ∉` head, and dropLast: `z ∉` getLast.
  have htail_nodup : hlist.tail.Nodup := hnodup.sublist (List.tail_sublist _)
  have hz_ne_head : z ≠ hlist.head hne := by
    intro h
    have hhd : hlist = hlist.head hne :: hlist.tail := list_head_cons_tail hlist hne
    have hnd : (hlist.head hne :: hlist.tail).Nodup := hhd ▸ hnodup
    rw [List.nodup_cons] at hnd
    have hzt : z ∈ hlist.tail := List.dropLast_subset _ hz
    exact hnd.1 (h ▸ hzt)
  have hz_ne_getLast : z ≠ hlist.getLast hne := by
    -- `z ∈ tail.dropLast`, and the getLast of `hlist` is the getLast of `tail`,
    -- which is not in `tail.dropLast` by nodup.
    have htne : hlist.tail ≠ [] := by
      intro h
      have : hlist.length ≤ 1 := by
        have hlt : hlist.tail.length = hlist.length - 1 := List.length_tail
        rw [h, List.length_nil] at hlt; omega
      have hge2 : 2 ≤ hlist.length := by
        rw [hlistdef, List.length_map]; exact vertexDartList_length_ge_two hσ
      omega
    have hgl : hlist.tail.getLast htne = hlist.getLast hne := by rw [List.getLast_tail]
    intro h
    have hzdl : z ∈ hlist.tail.dropLast := hz
    have hzgl : z = hlist.tail.getLast htne := by rw [hgl]; exact h
    -- nodup ⟹ getLast ∉ dropLast
    have hsplit : hlist.tail = hlist.tail.dropLast ++ [hlist.tail.getLast htne] :=
      (List.dropLast_append_getLast htne).symm
    rw [hsplit] at htail_nodup
    have hdisj := (List.nodup_append.mp htail_nodup).2.2
    -- z ∈ dropLast and z = getLast ⟹ z ≠ getLast forced, but z = getLast.
    exact hdisj z hzdl (hlist.tail.getLast htne) (List.mem_singleton_self _) hzgl
  refine ⟨e, he_mem, he_head, ?_, ?_⟩
  · -- `e ≠ d0`: else `z = head d0 = hlist.head`.
    intro he
    apply hz_ne_head
    -- `hlist.head hne = head d0`
    have hhh : hlist.head? = some (M.head d0) := by
      rw [hlistdef, List.head?_map, M.vertexDartList_head hσ, Option.map_some]
    rw [List.head?_eq_some_head hne, Option.some.injEq] at hhh
    -- z = head e = head d0 = hlist.head
    rw [← he_head, he, hhh]
  · -- `e ≠ σ⁻¹ d0`: else `z = head (σ⁻¹ d0) = hlist.getLast`.
    intro he
    apply hz_ne_getLast
    have hvne : (M.vertexDartList d0) ≠ [] :=
      List.ne_nil_of_length_pos (M.vertexDartList_length_pos hσ)
    have hgl : hlist.getLast hne = M.head (M.σ.symm d0) := by
      have hmap : hlist.getLast hne = M.head ((M.vertexDartList d0).getLast hvne) :=
        List.getLast_map hne
      rw [hmap, vertexDartList_getLast hσ hvne]
    rw [hgl, ← he_head, he]

/-! ## Section 4.  The maximal σ-constructor of `FanIncidenceData` -/

/-- **The maximal `FanIncidenceData` constructor.**  From `hNT`, the outgoing
boundary spoke `d0` at `v0` (`σ d0 ≠ d0`, `tail d0 = v0`, `dartFace d0 = outerFace`),
the chordlessness, and the *only* two isolated items — the orientation certificate
and the base-triangle count — the **full** `FanIncidenceData hNT v0` is assembled.
Every other field is discharged from `σ + hNT` (Sections 1–2 here +
`ZinanCh35Chordless`). -/
noncomputable def fanIncidenceData_of_orientation {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (horient : OrientationCert hNT (v0 := v0) (d0 := d0))
    (hbase : BaseCount hNT (d0 := d0)) :
    NearTriangulation.FanIncidenceData hNT v0 where
  d0 := d0
  sigma_ne := hσ
  tail0 := htail0
  x := M.head d0
  interior := canonInterior (M := M) (d0 := d0)
  w := M.head (M.σ.symm d0)
  heads_eq := by
    have h := pathHeads_decomp (M := M) hσ
    simpa only [canonInterior] using h
  v0_boundary := htail0 ▸
    ProofsInTheBook.ZinanCh35StarConn.isBoundaryVertex_tail_of_outer (hNT := hNT) hface0
  x_boundary := ProofsInTheBook.ZinanCh35Chordless.head_outgoing_boundary hNT hface0
  w_boundary := ProofsInTheBook.ZinanCh35Chordless.head_incoming_boundary hNT hface0
  incident_faces_exact := horient.some
  interior_not_boundary_of_chordless := by
    intro hchord z hz hzb
    -- `z ∈ canonInterior` ⟹ `z` is the head of a spoke `e` at `v0` with `e ≠ d0`
    -- (not the head vertex `x`) and `e ≠ σ⁻¹ d0` (not the last vertex `w`).
    obtain ⟨e, he_mem, he_head, he_ne_d0, he_ne_last⟩ := interior_mem_isHead hNT hσ hz
    have htail_e : M.tail e = v0 :=
      (M.vertexDartList_tail hσ he_mem).trans htail0
    -- both faces of `e` are inner, by uniqueness of the outer dart at `v0`:
    --   dartFace e = outer ⟹ e = d0 (excluded);  dartFace (α e) = dartFace (σ e),
    --   and dartFace (σ e) = outer ⟹ σ e = d0 ⟹ e = σ⁻¹ d0 (excluded).
    have htail_e_d0 : M.tail e = M.tail d0 := by rw [htail_e, htail0]
    have h1 : M.dartFace e ≠ hNT.outerFace :=
      ProofsInTheBook.ZinanCh35StarConn.nonouter_of_ne_outer (hNT := hNT)
        hface0 htail_e_d0 he_ne_d0
    have h2 : M.dartFace (M.α e) ≠ hNT.outerFace := by
      rw [(ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha (M := M) e).symm]
      refine ProofsInTheBook.ZinanCh35StarConn.nonouter_of_ne_outer (hNT := hNT)
        hface0 ?_ ?_
      · rw [M.tail_sigma, htail_e, htail0]
      · -- σ e ≠ d0, else e = σ⁻¹ d0
        intro hσe
        exact he_ne_last (by rw [← hσe, Equiv.symm_apply_apply])
    have hzne : M.head e ≠ v0 := by
      rw [← htail_e]; exact fun h => hNT.simpleGraph.no_loop e (by rw [← h])
    exact ProofsInTheBook.ZinanCh35Chordless.interior_vertex_chord_of_boundary hNT
      (htail0 ▸ ProofsInTheBook.ZinanCh35StarConn.isBoundaryVertex_tail_of_outer (hNT := hNT) hface0)
      htail_e h1 h2 hzne hchord (he_head ▸ hzb)
  empty_iff_base_triangle_of_chordless := hbase

/-! ## Section 5.  Fan existence from `σ + hNT` plus the two isolated items -/

/-- **Boundary-vertex fan existence, σ-reduced.**  From `hNT`, the outgoing boundary
spoke `d0` at `v0`, the orientation certificate, and the base-triangle count, the
keystone `BoundaryVertexFan hNT v0` exists.  This wires the maximal
`FanIncidenceData` constructor into `boundaryVertexFan_exists` — every fan field
except the two isolated items is discharged from the `σ`-rotation calculus. -/
theorem boundaryVertexFan_exists_of_orientation {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace)
    (horient : OrientationCert hNT (v0 := v0) (d0 := d0))
    (hbase : BaseCount hNT (d0 := d0)) :
    Nonempty (NearTriangulation.BoundaryVertexFan hNT v0) :=
  NearTriangulation.boundaryVertexFan_exists
    (fanIncidenceData_of_orientation hNT hσ htail0 hface0 horient hbase)

/-- **The outgoing boundary spoke exists at any boundary vertex**, so the only inputs
to `fanIncidenceData_of_orientation` beyond `hNT` are the two isolated items: given a
boundary vertex `v0`, there is an outgoing boundary spoke `d0` with `σ d0 ≠ d0`,
`tail d0 = v0`, `dartFace d0 = outerFace`. -/
theorem exists_outgoing_boundary_spoke {v0 : M.Vertex}
    (hv0 : hNT.outerCycle.IsBoundaryVertex v0) :
    ∃ d0 : D, M.σ d0 ≠ d0 ∧ M.tail d0 = v0 ∧ M.dartFace d0 = hNT.outerFace := by
  obtain ⟨d0, hface, htail⟩ :=
    ProofsInTheBook.ZinanCh35Chordless.exists_outgoingOuterDart hNT hv0
  exact ⟨d0, ProofsInTheBook.ZinanCh35Chordless.outgoingOuterDart_sigma_ne hNT hface,
    htail, hface⟩

end ProofsInTheBook.ZinanCh35ChordlessFull

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35ChordlessFull.spokeFace_head_eq
#print axioms ProofsInTheBook.ZinanCh35ChordlessFull.forward_fanTriangle_forces_degree_two
#print axioms ProofsInTheBook.ZinanCh35ChordlessFull.pathHeads_decomp
#print axioms ProofsInTheBook.ZinanCh35ChordlessFull.vertexDartList_getLast
#print axioms ProofsInTheBook.ZinanCh35ChordlessFull.interior_mem_isHead
#print axioms ProofsInTheBook.ZinanCh35ChordlessFull.fanIncidenceData_of_orientation
#print axioms ProofsInTheBook.ZinanCh35ChordlessFull.boundaryVertexFan_exists_of_orientation
#print axioms ProofsInTheBook.ZinanCh35ChordlessFull.exists_outgoing_boundary_spoke
