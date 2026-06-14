import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns

/-!
# Ch13 marked sphere: the discrete Cauchy sign-change lemma (combinatorial core)

This is the faithful combinatorial heart of Cauchy's rigidity theorem, on a
triangulated sphere combinatorial map `M : CombMap D`.  The arm lemma (the
geometric "≥ 4 flips at an active vertex" engine) is a black box elsewhere; here
we prove the *counting* lemma that turns "every active vertex has ≥ 4 flips" into
a contradiction with Euler's formula.

## The corner double-count (the key exact equality)

A *signing* on the strict (no-zero) layer is a function `s : D → StrictEdgeSign`
that is **edge-invariant**: `s (α d) = s d` (a sign on the α-orbit = edge).

A **corner** is a dart `d`.  We say the corner at `d` is a *change* when the two
consecutive edges it sits between differ in sign.  Reading the corner from the
vertex side, the consecutive edges are `edge(d)` and `edge(σ d)`, so the
vertex-change predicate is `s d ≠ s (σ d)`.  Reading from the face side, the
consecutive edges along the face boundary are `edge(d)` and `edge(φ d)`, so the
face-change predicate is `s d ≠ s (φ d)`.

The **corner double-count** is the exact identity

  `#{d : s d ≠ s (σ d)} = #{d : s d ≠ s (φ d)}`

proved by the change of variables `d ↦ α d`: since `α` is a fixed-point-free
involution and `φ = σ α`, we have `φ (α d) = σ d` and `s (α d) = s d`, so the
bijection `α` carries the vertex-change set onto the face-change set.

Summing the left side over `σ`-orbits gives `∑_v vertexFlip v`; summing the right
side over `φ`-orbits gives `∑_f faceFlip f`.  Both equal the same dart count, hence

  `∑_v vertexFlip v = ∑_f faceFlip f`.

## The strict-core contradiction

For a triangulated sphere (`FaceRegular 3`), each face has 3 darts and the cyclic
flip count of three strict signs is `≤ 2`, so `faceFlip f ≤ 2`, hence
`∑_f faceFlip ≤ 2 F`.  If every vertex were *active with ≥ 4 flips* we would get
`4 V ≤ ∑_v vertexFlip = ∑_f faceFlip ≤ 2 F`.  Euler `V - E + F = 2` together with
`3 F = 2 E` gives `F + 4 = 2 V`, i.e. `2 F = 4 V - 8 < 4 V` — contradiction.

`strict_signed_triangulated_sphere_not_all_ge_four` packages exactly this.

## Non-vacuity

`tetraMap` is the tetrahedron combinatorial map (12 darts), proven to be a sphere
(`tetraMap_isSphereMap`) with triangular faces (`tetraMap_faceRegular_three`); it
carries a strict signing with a genuine flip, witnessing that the hypotheses of the
strict core are satisfiable.
-/

namespace ProofsInTheBook.Ch13MarkedSphere

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Edge-invariant strict signings and corner changes -/

/-- A strict (no-zero) signing on darts that is invariant under the edge involution
`α`, i.e. a sign attached to each edge (`α`-orbit) of `M`. -/
def EdgeInvariant (M : CombMap D) (s : D → StrictEdgeSign) : Prop :=
  ∀ d, s (M.α d) = s d

/-- The set of darts whose corner is a sign **change** read from the vertex side:
the edge of `d` and the edge of `σ d` differ. -/
def vertexChangeSet (M : CombMap D) (s : D → StrictEdgeSign) : Finset D :=
  Finset.univ.filter (fun d => s d ≠ s (M.σ d))

/-- The set of darts whose corner is a sign **change** read from the face side:
the edge of `d` and the edge of `φ d` differ. -/
def faceChangeSet (M : CombMap D) (s : D → StrictEdgeSign) : Finset D :=
  Finset.univ.filter (fun d => s d ≠ s (M.φ d))

/-- **Corner double-count (exact).**  For an edge-invariant strict signing, the
number of vertex-side corner changes equals the number of face-side corner changes.
Proof: the edge involution `α` is a bijection carrying one set onto the other, using
`φ (α d) = σ d` and `s (α d) = s d`. -/
theorem corner_double_count (M : CombMap D) (s : D → StrictEdgeSign)
    (hs : EdgeInvariant M s) :
    (vertexChangeSet M s).card = (faceChangeSet M s).card := by
  -- `φ (α d) = σ d`, since `φ = σ α` and `α` is an involution.
  have hφα : ∀ d, M.φ (M.α d) = M.σ d := by
    intro d
    show (M.σ * M.α) (M.α d) = M.σ d
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    have : M.α (M.α d) = d := by
      have := congrArg (fun p => p d) M.α_invol
      simpa using this
    rw [this]
  refine Finset.card_bij (fun d _ => M.α d) ?_ ?_ ?_
  · -- maps vertexChangeSet into faceChangeSet
    intro d hd
    simp only [vertexChangeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    simp only [faceChangeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hs d, hφα d]
    exact hd
  · -- injective on the set
    intro a _ b _ hab
    exact M.α.injective hab
  · -- surjective onto faceChangeSet
    intro b hb
    simp only [faceChangeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨M.α b, ?_, ?_⟩
    · simp only [vertexChangeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      -- want: s (α b) ≠ s (σ (α b)); use hs and hφα: σ(αb) = φ(α(αb))? compute directly
      have hαα : M.α (M.α b) = b := by
        have := congrArg (fun p => p b) M.α_invol
        simpa using this
      -- s (α b) = s b ; s (σ (α b)) = ?  σ (α b) = φ (α (α b)) = φ b
      have hσαb : M.σ (M.α b) = M.φ b := by
        have := hφα (M.α b)
        rw [hαα] at this
        exact this.symm
      rw [hs b, hσαb]
      exact hb
    · have hαα : M.α (M.α b) = b := by
        have := congrArg (fun p => p b) M.α_invol
        simpa using this
      exact hαα

/-! ## Per-orbit flip counts and their sums -/

/-- The vertex flip count at a `σ`-orbit (vertex) `Q`: the number of darts at that
vertex whose corner is a sign change. -/
def vertexFlip (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.σ)) : ℕ :=
  ((vertexChangeSet M s).filter (fun d => Quotient.mk (cycleSetoid M.σ) d = Q)).card

/-- The face flip count at a `φ`-orbit (face) `Q`. -/
def faceFlip (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.φ)) : ℕ :=
  ((faceChangeSet M s).filter (fun d => Quotient.mk (cycleSetoid M.φ) d = Q)).card

/-- Summing the vertex flip counts over all vertices recovers the total number of
vertex-side corner changes. -/
theorem sum_vertexFlip (M : CombMap D) (s : D → StrictEdgeSign) :
    (∑ Q : Quotient (cycleSetoid M.σ), vertexFlip M s Q) = (vertexChangeSet M s).card := by
  rw [eq_comm]
  apply Finset.card_eq_sum_card_fiberwise
  intro d _
  exact Finset.mem_univ _

/-- Summing the face flip counts over all faces recovers the total number of
face-side corner changes. -/
theorem sum_faceFlip (M : CombMap D) (s : D → StrictEdgeSign) :
    (∑ Q : Quotient (cycleSetoid M.φ), faceFlip M s Q) = (faceChangeSet M s).card := by
  rw [eq_comm]
  apply Finset.card_eq_sum_card_fiberwise
  intro d _
  exact Finset.mem_univ _

/-- **The double-count, as a sum equality**: total vertex flips = total face flips. -/
theorem sum_vertexFlip_eq_sum_faceFlip (M : CombMap D) (s : D → StrictEdgeSign)
    (hs : EdgeInvariant M s) :
    (∑ Q : Quotient (cycleSetoid M.σ), vertexFlip M s Q)
      = ∑ Q : Quotient (cycleSetoid M.φ), faceFlip M s Q := by
  rw [sum_vertexFlip, sum_faceFlip, corner_double_count M s hs]

/-! ## Per-orbit parity (general): change counts around any orbit are even -/

/-- The fiber of a `p`-orbit is closed under `p`. -/
theorem mem_fiber_apply_gen (p : Equiv.Perm D) (Q : Quotient (cycleSetoid p)) {x : D}
    (hx : Quotient.mk (cycleSetoid p) x = Q) :
    Quotient.mk (cycleSetoid p) (p x) = Q := by
  rw [← hx]
  apply Quotient.sound
  show p.SameCycle (p x) x
  exact (Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl _ _))

/-- **Per-orbit parity (general).**  For any permutation `p` and any strict signing
`s`, the number of darts in a single `p`-orbit `Q` whose corner is a change
(`s x ≠ s (p x)`) is even.  Proof: in `ZMod 2` the indicator sum telescopes to
`2 ∑ valZ (s x) = 0` because `p` is a bijection of the orbit. -/
theorem orbitFlip_even (p : Equiv.Perm D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid p)) :
    Even ((Finset.univ.filter
      (fun x => Quotient.mk (cycleSetoid p) x = Q ∧ s x ≠ s (p x))).card) := by
  classical
  set B := Finset.univ.filter (fun x => Quotient.mk (cycleSetoid p) x = Q) with hB
  have hcount : (Finset.univ.filter
      (fun x => Quotient.mk (cycleSetoid p) x = Q ∧ s x ≠ s (p x))).card
      = (B.filter (fun x => s x ≠ s (p x))).card := by
    congr 1
    ext x
    simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hcount, ← ZMod.natCast_eq_zero_iff_even]
  have hcard_sum : ((B.filter (fun x => s x ≠ s (p x))).card : ZMod 2)
      = ∑ x ∈ B, ((if s x ≠ s (p x) then 1 else 0 : ℕ) : ZMod 2) := by
    rw [Finset.card_filter]; push_cast; rfl
  rw [hcard_sum]
  have hind : ∀ x, ((if s x ≠ s (p x) then 1 else 0 : ℕ) : ZMod 2)
      = StrictEdgeSign.valZ (s x) + StrictEdgeSign.valZ (s (p x)) :=
    fun x => indicator_eq_valZ_add (s x) (s (p x))
  simp only [hind]
  rw [Finset.sum_add_distrib]
  have hbij : (∑ x ∈ B, StrictEdgeSign.valZ (s (p x)))
      = ∑ x ∈ B, StrictEdgeSign.valZ (s x) := by
    apply Finset.sum_bij (fun x _ => p x)
    · intro x hx
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact mem_fiber_apply_gen p Q hx
    · intro a _ b _ hab; exact p.injective hab
    · intro b hb
      refine ⟨p.symm b, ?_, ?_⟩
      · simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        have : Quotient.mk (cycleSetoid p) (p (p.symm b)) = Q := by
          rw [Equiv.apply_symm_apply]; exact hb
        rw [← this]
        apply Quotient.sound
        show p.SameCycle (p.symm b) (p (p.symm b))
        exact (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))
      · rw [Equiv.apply_symm_apply]
    · intro x _; rfl
  rw [hbij, ← two_mul]
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [h2, zero_mul]

/-! ## Per-face bound: a triangle has at most two strict corner changes -/

/-- The fiber of a `φ`-orbit is closed under `φ`: if `x` is in the orbit `Q` then so
is `φ x`. -/
theorem mem_fiber_apply (M : CombMap D) (Q : Quotient (cycleSetoid M.φ)) {x : D}
    (hx : Quotient.mk (cycleSetoid M.φ) x = Q) :
    Quotient.mk (cycleSetoid M.φ) (M.φ x) = Q :=
  mem_fiber_apply_gen M.φ Q hx

/-- `vertexFlip` is even (per-orbit parity for `σ`). -/
theorem vertexFlip_even (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.σ)) :
    Even (vertexFlip M s Q) := by
  have h := orbitFlip_even M.σ s Q
  convert h using 2
  rw [vertexFlip, vertexChangeSet]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- **Per-face parity.**  The face flip count at any face is even, because the
change-indicator summed over a `φ`-orbit telescopes to `0` in `ZMod 2`: `φ` is a
bijection of the orbit, so `∑ valZ (s (φ x)) = ∑ valZ (s x)`, and the sum of
indicators is `2 ∑ valZ (s x) = 0`. -/
theorem faceFlip_even (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.φ)) :
    Even (faceFlip M s Q) := by
  have h := orbitFlip_even M.φ s Q
  convert h using 2
  rw [faceFlip, faceChangeSet]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

/-- On a triangular face (a `φ`-orbit of exactly three darts), the face flip count is
at most `2`: it is even (`faceFlip_even`) and bounded by the face size `3`. -/
theorem faceFlip_le_two (M : CombMap D) (s : D → StrictEdgeSign)
    (hTri : M.FaceRegular 3) (Q : Quotient (cycleSetoid M.φ)) :
    faceFlip M s Q ≤ 2 := by
  have hcard3 : (Finset.univ.filter
      (fun x => Quotient.mk (cycleSetoid M.φ) x = Q)).card = 3 := hTri Q
  have hsub : (faceChangeSet M s).filter (fun x => Quotient.mk (cycleSetoid M.φ) x = Q)
      ⊆ Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.φ) x = Q) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.2
  have hle3 : faceFlip M s Q ≤ 3 := by
    rw [faceFlip, ← hcard3]
    exact Finset.card_le_card hsub
  rcases faceFlip_even M s Q with ⟨k, hk⟩
  omega

/-! ## The strict-core contradiction -/

/-- A vertex `Q` is **active** for the signing `s` if some dart at `Q` already has a
corner change there (equivalently the vertex sees two different edge signs around it). -/
def ActiveVertexStrict (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.σ)) : Prop :=
  0 < vertexFlip M s Q

/-- **The strict-signing core of Cauchy's discrete sign-change lemma.**

On a triangulated sphere combinatorial map `M`, no edge-invariant strict signing can
have `≥ 4` corner changes at *every* vertex.  (Equivalently: some vertex has `≤ 2`
flips — the low-active vertex Cauchy's arm lemma needs.)

Proof: the corner double-count gives `∑_v vertexFlip = ∑_f faceFlip`; each triangular
face contributes `≤ 2`, so `∑_f faceFlip ≤ 2 F`; Euler `V - E + F = 2` with `3 F = 2 E`
gives `F + 4 = 2 V`; hence `4 V ≤ 2 F = 4 V - 8`, impossible. -/
theorem strict_signed_triangulated_sphere_not_all_ge_four
    (M : CombMap D) (hSphere : M.IsSphereMap) (hTri : M.FaceRegular 3)
    (s : D → StrictEdgeSign) (hs : EdgeInvariant M s) :
    ¬ (∀ Q : Quotient (cycleSetoid M.σ), 4 ≤ vertexFlip M s Q) := by
  intro hall
  -- ∑_v vertexFlip ≥ 4 V
  have hV : 4 * M.V ≤ ∑ Q : Quotient (cycleSetoid M.σ), vertexFlip M s Q := by
    have : (∑ _Q : Quotient (cycleSetoid M.σ), (4 : ℕ)) ≤
        ∑ Q : Quotient (cycleSetoid M.σ), vertexFlip M s Q :=
      Finset.sum_le_sum (fun Q _ => hall Q)
    simpa [Finset.sum_const, Finset.card_univ, V, Nat.mul_comm] using this
  -- ∑_f faceFlip ≤ 2 F
  have hF : (∑ Q : Quotient (cycleSetoid M.φ), faceFlip M s Q) ≤ 2 * M.F := by
    have : (∑ Q : Quotient (cycleSetoid M.φ), faceFlip M s Q) ≤
        ∑ _Q : Quotient (cycleSetoid M.φ), (2 : ℕ) :=
      Finset.sum_le_sum (fun Q _ => faceFlip_le_two M s hTri Q)
    simpa [Finset.sum_const, Finset.card_univ, F, Nat.mul_comm] using this
  -- double-count links the two
  have heq := sum_vertexFlip_eq_sum_faceFlip M s hs
  -- Euler + 3F = 2E ⟹ F + 4 = 2 V
  have heuler : (M.V : ℤ) - (M.E : ℤ) + (M.F : ℤ) = 2 := hSphere.2
  have htri : 3 * M.F = 2 * M.E := faceRegular_pF M hTri
  have hFV : M.F + 4 = 2 * M.V :=
    euler_triangular_faces_eq_two_mul_vertices_sub_four heuler htri
  -- combine: 4V ≤ ∑_v = ∑_f ≤ 2F, and F + 4 = 2V
  omega

/-- **Strict marked-sphere low-flip vertex (existential form).**

On a triangulated sphere, any edge-invariant strict signing has *some* vertex with
at most two sign changes around it.  This is the low sign-change vertex that feeds
Cauchy's arm lemma.  It is the contrapositive of
`strict_signed_triangulated_sphere_not_all_ge_four` plus the parity fact that a
vertex flip count is even, so "`< 4`" sharpens to "`≤ 2`". -/
theorem cauchy_marked_sphere_low_vertex_strict
    (M : CombMap D) (hSphere : M.IsSphereMap) (hTri : M.FaceRegular 3)
    (s : D → StrictEdgeSign) (hs : EdgeInvariant M s) :
    ∃ Q : Quotient (cycleSetoid M.σ), vertexFlip M s Q ≤ 2 := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  -- ¬∃ low ⟹ ∀ Q, 3 ≤ vertexFlip; with evenness, 4 ≤ vertexFlip.
  apply strict_signed_triangulated_sphere_not_all_ge_four M hSphere hTri s hs
  intro Q
  have h3 : 3 ≤ vertexFlip M s Q := hcon Q
  -- vertexFlip is even (same telescoping argument as faceFlip, now over σ-orbits)
  have hev : Even (vertexFlip M s Q) := vertexFlip_even M s Q
  rcases hev with ⟨k, hk⟩
  omega

/-! ## Faithful spec-shaped definitions (with zeros)

The book's count is the cyclic sign-flip count of the edge signs around a vertex,
read in `σ`-order, with the **zeros skipped** (edges whose dihedral angle does not
change).  We record the faithful definitions matching the statement spec.  The
`σ`-ordered list of signs around the vertex represented by a dart `d` is obtained
from `Equiv.Perm.toList`, and the count is the `cyclicFlipCountSkipZeros` of the
cyclic-sign layer (`Ch13CyclicSigns`).  A vertex is *active* if some dart at it
carries a nonzero edge sign. -/

/-- The `σ`-ordered list of edge signs around the vertex represented by dart `d`. -/
def vertexSignList (M : CombMap D) (es : D → EdgeSign) (d : D) : List EdgeSign :=
  (M.σ.toList d).map es

/-- The book's per-vertex count: the cyclic sign-flip count of the edge signs around
the vertex of `d`, in `σ`-order, with zeros skipped. -/
def vertexFlipCountSkipZeros (M : CombMap D) (es : D → EdgeSign) (d : D) : ℕ :=
  cyclicFlipCountSkipZeros (vertexSignList M es d)

/-- A vertex (represented by dart `d`) is **active** if some dart in its `σ`-orbit
carries a nonzero edge sign. -/
def ActiveVertex (M : CombMap D) (es : D → EdgeSign) (d : D) : Prop :=
  ∃ x, M.σ.SameCycle d x ∧ es x ≠ EdgeSign.zero

/-- The per-vertex skip-zero flip count is always even (cyclic parity). -/
theorem vertexFlipCountSkipZeros_even (M : CombMap D) (es : D → EdgeSign) (d : D) :
    Even (vertexFlipCountSkipZeros M es d) :=
  cyclicFlipCountSkipZeros_even _

/-! ## Non-vacuity: the tetrahedron carries the hypotheses

We exhibit the tetrahedron combinatorial map `tetraMap` (12 darts, 4 vertices, 6
edges, 4 triangular faces) — a genuine triangulated sphere — together with a strict
edge-invariant signing that has a real sign flip, so the hypotheses of the strict
core are satisfiable (and the strict core is therefore not vacuously true). -/

/-- Edge involution of the tetrahedron map: the six transpositions pairing each dart
with its reverse. -/
def tetraAlpha : Equiv.Perm (Fin 12) :=
  (List.formPerm [0, 3]) * (List.formPerm [1, 6]) * (List.formPerm [2, 9]) *
    (List.formPerm [4, 7]) * (List.formPerm [5, 10]) * (List.formPerm [8, 11])

/-- Vertex rotation of the tetrahedron map: the four `3`-cycles rotating the darts
around each of the four vertices. -/
def tetraSigma : Equiv.Perm (Fin 12) :=
  (List.formPerm [0, 1, 2]) * (List.formPerm [3, 5, 4]) *
    (List.formPerm [6, 7, 8]) * (List.formPerm [9, 11, 10])

/-- The tetrahedron as a combinatorial map on `Fin 12`. -/
def tetraMap : CombMap (Fin 12) where
  α := tetraAlpha
  σ := tetraSigma
  α_invol := by decide
  α_no_fixed := by decide

theorem tetraMap_V : tetraMap.V = 4 := by decide
theorem tetraMap_E : tetraMap.E = 6 := by decide
theorem tetraMap_F : tetraMap.F = 4 := by decide
theorem tetraMap_eulerChar : tetraMap.eulerChar = 2 := by decide
noncomputable instance : DecidableEq (Quotient (cycleSetoid tetraMap.φ)) :=
  Quotient.decidableEq

set_option maxRecDepth 10000 in
theorem tetraMap_faceRegular_three : tetraMap.FaceRegular 3 := by
  rw [CombMap.FaceRegular]; decide

/-- One `dartStep` of the tetrahedron map, the connectivity obligations closed by
`decide`. -/
private theorem tetraEdge (a b : Fin 12)
    (h : tetraMap.σ.SameCycle a b ∨ b = tetraMap.α a) : tetraMap.dartStep a b := h

/-- `dartStep` is symmetric on the tetrahedron map. -/
private theorem tetra_dartStep_symm {a b : Fin 12} (h : tetraMap.dartStep a b) :
    tetraMap.dartStep b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · refine Or.inr ?_
    rw [h]
    have : tetraMap.α (tetraMap.α a) = a := by
      have := congrArg (fun p => p a) tetraMap.α_invol; simpa using this
    rw [this]

private theorem tetra_rtg_symm {a b : Fin 12}
    (h : Relation.ReflTransGen tetraMap.dartStep a b) :
    Relation.ReflTransGen tetraMap.dartStep b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (tetra_dartStep_symm hbc)).trans ih

/-- Every dart of the tetrahedron reaches dart `0` by a chain of `dartStep`s. -/
private theorem tetra_reach_zero (d : Fin 12) :
    Relation.ReflTransGen tetraMap.dartStep d 0 := by
  have e10 : tetraMap.dartStep 1 0 := tetraEdge 1 0 (by decide)
  have e20 : tetraMap.dartStep 2 0 := tetraEdge 2 0 (by decide)
  have e30 : tetraMap.dartStep 3 0 := tetraEdge 3 0 (by decide)
  have e61 : tetraMap.dartStep 6 1 := tetraEdge 6 1 (by decide)
  have e92 : tetraMap.dartStep 9 2 := tetraEdge 9 2 (by decide)
  fin_cases d
  · exact .refl
  · exact .single e10
  · exact .single e20
  · exact .single e30
  · exact .head (tetraEdge 4 3 (by decide)) (.single e30)
  · exact .head (tetraEdge 5 3 (by decide)) (.single e30)
  · exact .head e61 (.single e10)
  · exact .head (tetraEdge 7 6 (by decide)) (.head e61 (.single e10))
  · exact .head (tetraEdge 8 6 (by decide)) (.head e61 (.single e10))
  · exact .head e92 (.single e20)
  · exact .head (tetraEdge 10 9 (by decide)) (.head e92 (.single e20))
  · exact .head (tetraEdge 11 9 (by decide)) (.head e92 (.single e20))

theorem tetraMap_connected : tetraMap.Connected :=
  fun a b => (tetra_reach_zero a).trans (tetra_rtg_symm (tetra_reach_zero b))

/-- The tetrahedron is a genuine sphere map. -/
theorem tetraMap_isSphereMap : tetraMap.IsSphereMap :=
  ⟨tetraMap_connected, tetraMap_eulerChar⟩

/-- A strict edge-invariant signing on the tetrahedron with a genuine sign flip:
the edge `{0,3}` (darts `0` and `3`) is `minus`, every other edge `plus`. -/
def tetraSign : Fin 12 → StrictEdgeSign := fun d =>
  if d = 0 ∨ d = 3 then StrictEdgeSign.minus else StrictEdgeSign.plus

theorem tetraSign_edgeInvariant : EdgeInvariant tetraMap tetraSign := by
  rw [EdgeInvariant]; decide

/-- The signing `tetraSign` genuinely flips: there is a dart whose corner is a change,
so the vertex-change set is non-empty (the signing is nontrivial). -/
theorem tetraSign_nontrivial : (vertexChangeSet tetraMap tetraSign).Nonempty := by
  rw [vertexChangeSet]; decide

/-- **Non-vacuity.**  The hypotheses of the strict core
(`strict_signed_triangulated_sphere_not_all_ge_four`,
`cauchy_marked_sphere_low_vertex_strict`) are satisfiable: the tetrahedron is a
triangulated sphere carrying a nontrivial strict edge-invariant signing.  In
particular the low-flip vertex it provides is genuine, not vacuous. -/
theorem strict_core_nonvacuous :
    ∃ (M : CombMap (Fin 12)) (s : Fin 12 → StrictEdgeSign),
      M.IsSphereMap ∧ M.FaceRegular 3 ∧ EdgeInvariant M s ∧
        (vertexChangeSet M s).Nonempty :=
  ⟨tetraMap, tetraSign, tetraMap_isSphereMap, tetraMap_faceRegular_three,
    tetraSign_edgeInvariant, tetraSign_nontrivial⟩

end ProofsInTheBook.Ch13MarkedSphere
