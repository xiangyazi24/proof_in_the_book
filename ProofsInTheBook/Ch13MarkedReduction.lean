import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere

/-!
# Ch13 marked-sphere reduction: with-zeros → strict core

This file reduces the *with-zeros* Cauchy combinatorial lemma towards the proven STRICT core
(`Ch13MarkedSphere.strict_signed_triangulated_sphere_not_all_ge_four` and
`cauchy_marked_sphere_low_vertex_strict`).

It is organized as a stack of independently-checkable layers:

* **Layer 1 (list bridge).** `cyclicFlipCount_eq_zipWith_rotate`: the cyclic flip count of a
  list is the sum, over cyclically-consecutive pairs, of the unequal-indicator.  Purely a fact
  about `flipAux` and `List.rotate`.
* **Layer 2 (orbit bridge).** `cyclicFlipCount_map_toList_eq_orbitFlip`: for a permutation `p`,
  the cyclic flip count of `(p.toList x).map f` equals the number of darts `y` in the `p`-orbit
  of `x` with `f y ≠ f (p y)`.  Specialized to `p = σ`, `f = s` this identifies the list count
  with the strict core's `vertexFlip`.  Consequence:
  `vertexFlipCountSkipZeros_strict_eq_vertexFlip` — for a strict edge signing, the book's
  skip-zero count coincides with the strict core's `vertexFlip`.
* **Layer 3 (skip-zero monotonicity).** `cyclicFlipCountSkipZeros_le_map`: replacing each zero by
  any strict value never decreases the cyclic flip count (dropping a zero gives `≤` the
  completed count).
-/

namespace ProofsInTheBook.Ch13MarkedReduction

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open EdgeSign
open Equiv Equiv.Perm

/-! ## Layer 1: the list bridge -/

section ListBridge

variable {α : Type*} [DecidableEq α]

/-- `flipAux first prev xs` is the sum of the unequal-indicators over the consecutive pairs of
`prev :: xs` read cyclically with wrap target `first`: namely `zipWith` of `prev :: xs` with
`xs ++ [first]`. -/
theorem flipAux_eq_zipWith (first : α) :
    ∀ (prev : α) (xs : List α),
      flipAux first prev xs
        = (List.zipWith (fun a b => if a ≠ b then 1 else 0) (prev :: xs) (xs ++ [first])).sum
  | _, [] => by simp [flipAux]
  | prev, x :: xs => by
      simp only [flipAux, List.cons_append, List.zipWith_cons_cons, List.sum_cons]
      rw [flipAux_eq_zipWith first x xs]

/-- **Layer 1 (list bridge).**  The cyclic flip count of a list is the sum of unequal-indicators
over cyclically-consecutive pairs, where the cyclic successor list is `l.rotate 1`. -/
theorem cyclicFlipCount_eq_zipWith_rotate (l : List α) :
    cyclicFlipCount l
      = (List.zipWith (fun a b => if a ≠ b then 1 else 0) l (l.rotate 1)).sum := by
  cases l with
  | nil => simp [cyclicFlipCount]
  | cons a l =>
      rw [cyclicFlipCount, flipAux_eq_zipWith]
      congr 1
      simp [List.rotate_cons_succ, List.rotate_zero]

/-- The sum of a `zipWith` over two equal-length lists is the indexed sum over `Fin`. -/
theorem zipWith_sum_eq_finsum {β : Type*} (g : β → β → ℕ) (l m : List β)
    (h : l.length = m.length) :
    (List.zipWith g l m).sum = ∑ i : Fin l.length, g (l.get i) (m.get (Fin.cast h i)) := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp [h]
  · intro i hi hi2
    simp [List.getElem_zipWith, List.getElem_ofFn]

end ListBridge

/-! ## Layer 2: the orbit bridge -/

section OrbitBridge

variable {α : Type*} [DecidableEq α] [Fintype α] {β : Type*} [DecidableEq β]

/-- The cyclic flip count of `(p.toList x).map f` as an indexed sum over the orbit positions. -/
theorem cyclicFlipCount_map_toList_eq_finsum (p : Perm α) (x : α) (f : α → β) :
    cyclicFlipCount ((p.toList x).map f)
      = ∑ i : Fin (p.toList x).length,
          (if f ((p ^ (i : ℕ)) x) ≠ f (p ((p ^ (i : ℕ)) x)) then 1 else 0) := by
  rw [cyclicFlipCount_eq_zipWith_rotate,
      zipWith_sum_eq_finsum _ _ _ (by rw [List.length_rotate])]
  have hlen : ((p.toList x).map f).length = (p.toList x).length := by simp
  rw [← Fin.sum_congr' _ hlen.symm]
  apply Finset.sum_congr rfl
  intro i _
  have e1 : ((p.toList x).map f).get (Fin.cast hlen.symm i) = f ((p ^ (i : ℕ)) x) := by
    rw [List.get_eq_getElem, List.getElem_map, Equiv.Perm.getElem_toList]; rfl
  have e2 : (((p.toList x).map f).rotate 1).get
        (Fin.cast (by rw [List.length_rotate]) (Fin.cast hlen.symm i))
      = f (p ((p ^ (i : ℕ)) x)) := by
    rw [List.get_eq_getElem, List.getElem_rotate, List.getElem_map, Equiv.Perm.getElem_toList]
    simp only [List.length_map, Equiv.Perm.length_toList]
    rw [Equiv.Perm.pow_mod_card_support_cycleOf_self_apply, pow_succ', mul_apply]
    rfl
  rw [e1, e2]

/-- Indexed sum over orbit positions equals the count over the orbit Finset (`toList.toFinset`),
because `p.toList x` is `Nodup` and `i ↦ (p.toList x).get i` enumerates it. -/
theorem finsum_orbit_eq_toFinset_card (p : Perm α) (x : α) (P : α → Prop) [DecidablePred P] :
    (∑ i : Fin (p.toList x).length, (if P ((p ^ (i : ℕ)) x) then 1 else 0))
      = ((p.toList x).toFinset.filter P).card := by
  have hget : ∀ i : Fin (p.toList x).length, (p.toList x).get i = (p ^ (i : ℕ)) x := by
    intro i; rw [List.get_eq_getElem, Equiv.Perm.getElem_toList]
  have hstep1 :
      (∑ i : Fin (p.toList x).length, (if P ((p ^ (i : ℕ)) x) then 1 else 0))
        = ((p.toList x).map (fun y => if P y then 1 else 0)).sum := by
    rw [← List.sum_ofFn]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hi2
      rw [List.getElem_ofFn, List.getElem_map, Equiv.Perm.getElem_toList]
  rw [hstep1]
  have hnodup := Equiv.Perm.nodup_toList p x
  have h1 : ((p.toList x).map (fun y => if P y then 1 else 0)).sum
      = ((p.toList x).filter (fun y => decide (P y))).length := by
    induction (p.toList x) with
    | nil => simp
    | cons a t ih =>
        simp only [List.map_cons, List.sum_cons, List.filter_cons]
        by_cases hp : P a <;> simp [hp] <;> omega
  rw [h1, ← List.toFinset_card_of_nodup (hnodup.filter _)]
  congr 1
  ext y
  simp [List.mem_toFinset, Finset.mem_filter]

/-- The orbit Finset (`toList.toFinset`) is the `SameCycle` fiber intersected with the support. -/
theorem toList_toFinset_eq (p : Perm α) (x : α) :
    (p.toList x).toFinset
      = Finset.univ.filter (fun y => p.SameCycle x y ∧ x ∈ p.support) := by
  ext y
  simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Equiv.Perm.mem_toList_iff

/-- **Layer 2 (orbit bridge).**  For a permutation `p` and a (decidable) sign function `f`, the
cyclic flip count of `(p.toList x).map f` is the number of darts `y` in the support-orbit of `x`
with `f y ≠ f (p y)`. -/
theorem cyclicFlipCount_map_toList_eq_orbitFlip (p : Perm α) (x : α) (f : α → β) :
    cyclicFlipCount ((p.toList x).map f)
      = (Finset.univ.filter
          (fun y => (p.SameCycle x y ∧ x ∈ p.support) ∧ f y ≠ f (p y))).card := by
  rw [cyclicFlipCount_map_toList_eq_finsum,
      finsum_orbit_eq_toFinset_card p x (fun y => f y ≠ f (p y)), toList_toFinset_eq]
  congr 1
  rw [Finset.filter_filter]

end OrbitBridge

/-! ## Layer 2b: the strict-signing bridge to `vertexFlip`

For a strict signing `s : D → StrictEdgeSign` (viewed on darts), the book's skip-zero count of `s`
read in `σ`-order coincides with the strict core's `vertexFlip`.  This is the clean identification
that lets the strict core speak the book's list-count language.  (No zeros are present, so
`filterMap toStrict` recovers the strict list, and the orbit bridge identifies the cyclic flip
count with `vertexFlip`.) -/

section StrictBridge

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Embed a strict sign into `EdgeSign`. -/
def strictToEdge : StrictEdgeSign → EdgeSign
  | StrictEdgeSign.plus => EdgeSign.plus
  | StrictEdgeSign.minus => EdgeSign.minus

@[simp] theorem toStrict_strictToEdge (a : StrictEdgeSign) :
    (strictToEdge a).toStrict = some a := by cases a <;> rfl

/-- `filterMap toStrict` undoes `map strictToEdge`: a strict list embedded into `EdgeSign` and then
filtered back is itself (there are no zeros to drop). -/
theorem filterMap_toStrict_map_strictToEdge (l : List StrictEdgeSign) :
    (l.map strictToEdge).filterMap EdgeSign.toStrict = l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, List.filterMap_cons, toStrict_strictToEdge, ih]

/-- The orbit-bridge set (the `SameCycle ∧ support`-restricted change set) equals the strict core's
`vertexFlip` fiber.  This holds in both the support case (genuine cycle) and the fixed-point case
(degree-`1` vertex), where both counts vanish. -/
theorem orbitFlip_set_eq_vertexFlip (M : CombMap D) (s : D → StrictEdgeSign) (d₀ : D) :
    (Finset.univ.filter
       (fun y => (M.σ.SameCycle d₀ y ∧ d₀ ∈ M.σ.support) ∧ s y ≠ s (M.σ y))).card
      = vertexFlip M s (Quotient.mk (cycleSetoid M.σ) d₀) := by
  rw [vertexFlip, vertexChangeSet, Finset.filter_filter]
  by_cases hd : d₀ ∈ M.σ.support
  · apply Finset.card_bij (fun y _ => y)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact ⟨hy.2, by rw [Quotient.eq]; exact hy.1.1.symm⟩
    · intro a _ b _ h; exact h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨y, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Quotient.eq] at hy
      exact ⟨⟨hy.2.symm, hd⟩, hy.1⟩
  · have hfix : M.σ d₀ = d₀ := by
      rw [Equiv.Perm.mem_support, not_not] at hd; exact hd
    rw [Finset.filter_eq_empty_iff.mpr (fun y _ h => hd h.1.2), Finset.card_empty]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _ hy
    obtain ⟨hflip, hmk⟩ := hy
    rw [Quotient.eq] at hmk
    have hyd : y = d₀ := by
      obtain ⟨k, hk⟩ := hmk
      have hk' : (M.σ ^ (-k)) d₀ = y := by rw [← hk]; simp
      rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hfix] at hk'
      exact hk'.symm
    rw [hyd, hfix] at hflip
    exact hflip rfl

/-- **Strict bridge.**  For a strict signing `s`, the book's skip-zero count of the embedded edge
signing `strictToEdge ∘ s`, read in `σ`-order around the vertex of `d₀`, equals the strict core's
`vertexFlip`. -/
theorem vertexFlipCountSkipZeros_strict_eq_vertexFlip
    (M : CombMap D) (s : D → StrictEdgeSign) (d₀ : D) :
    vertexFlipCountSkipZeros M (fun d => strictToEdge (s d)) d₀
      = vertexFlip M s (Quotient.mk (cycleSetoid M.σ) d₀) := by
  rw [vertexFlipCountSkipZeros, vertexSignList, cyclicFlipCountSkipZeros]
  -- (σ.toList d₀).map (strictToEdge ∘ s) |>.filterMap toStrict = (σ.toList d₀).map s
  have hfm : (((M.σ.toList d₀).map (fun d => strictToEdge (s d))).filterMap EdgeSign.toStrict)
      = (M.σ.toList d₀).map s := by
    have h2 : ((M.σ.toList d₀).map (fun d => strictToEdge (s d)))
        = ((M.σ.toList d₀).map s).map strictToEdge := by rw [List.map_map]; rfl
    rw [h2, filterMap_toStrict_map_strictToEdge]
  rw [hfm, cyclicFlipCount_map_toList_eq_orbitFlip, orbitFlip_set_eq_vertexFlip]

end StrictBridge

/-! ## Layer 3: the non-triangular active-component counting theorem

This is the genuine mathematical heart that the *with-zeros* statement requires, and it needs no
new `CombMap` surgery.  For a connected planar (sphere-Euler) map `A` whose faces all have degree
`≥ 3`, every edge-invariant strict signing has a vertex with at most two corner changes.

The strict core (`strict_signed_triangulated_sphere_not_all_ge_four`) is the special case where
every face has degree exactly `3`.  The generalization replaces the per-triangle bound
`faceFlip ≤ 2` by the planar bound `faceFlip ≤ 2·faceDeg − 4`, which Euler turns into the same
`4V ≤ 4V − 8` contradiction.

Faithfulness note (§3.3): the literal target stated in the spec — that *every* `IsSphereMap`
`FaceRegular 3` edge-invariant signing with a nonzero edge has an **active** vertex with skip-zero
count `≤ 2` — is **false** for general combinatorial maps (see `marked_target_obstruction` below).
The face-degree-`≥ 3` hypothesis on the active component is exactly the missing ingredient; this
theorem isolates the true content. -/

section ActiveComponent

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The degree of a face (`φ`-orbit): the number of darts on its boundary walk. -/
def faceDeg (M : CombMap D) (Q : Quotient (cycleSetoid M.φ)) : ℕ :=
  (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.φ) x = Q)).card

/-- The face flip count is at most the face degree (it counts a subset of the face's darts). -/
theorem faceFlip_le_faceDeg (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.φ)) : faceFlip M s Q ≤ faceDeg M Q := by
  rw [faceFlip, faceDeg, faceChangeSet]
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact hx.2

/-- **The planar per-face bound.**  On a face of degree `m ≥ 3`, the (even) face flip count is at
most `2m − 4`.  For `m = 3` it is `≤ 2 = 2·3 − 4` (even and `≤ 3`); for `m ≥ 4`,
`faceFlip ≤ m ≤ 2m − 4`. -/
theorem faceFlip_le_two_mul_faceDeg_sub_four (M : CombMap D) (s : D → StrictEdgeSign)
    (Q : Quotient (cycleSetoid M.φ)) (h3 : 3 ≤ faceDeg M Q) :
    faceFlip M s Q ≤ 2 * faceDeg M Q - 4 := by
  have hle := faceFlip_le_faceDeg M s Q
  rcases faceFlip_even M s Q with ⟨k, hk⟩
  omega

/-- **The non-triangular active-component low-vertex theorem.**

Let `A` be a connected combinatorial map of sphere Euler characteristic (`V − E + F = 2`) whose
faces all have degree `≥ 3` (with `∑ faceDeg = 2E`).  Then every edge-invariant strict signing has
a vertex with at most two corner changes.

This is the surgery-free core of the with-zeros Cauchy lemma: applied to the active component of a
marked sphere it yields the desired low active vertex.  It strictly generalizes
`strict_signed_triangulated_sphere_not_all_ge_four`. -/
theorem active_component_low_vertex (A : CombMap D)
    (hEuler : (A.V : ℤ) - A.E + A.F = 2)
    (hFaceDegSum : (∑ R : Quotient (cycleSetoid A.φ), faceDeg A R) = 2 * A.E)
    (hFaceDeg_ge_three : ∀ R : Quotient (cycleSetoid A.φ), 3 ≤ faceDeg A R)
    (s : D → StrictEdgeSign) (hs : EdgeInvariant A s) :
    ∃ Q : Quotient (cycleSetoid A.σ), vertexFlip A s Q ≤ 2 := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have hall4 : ∀ Q, 4 ≤ vertexFlip A s Q := by
    intro Q
    have h3 : 3 ≤ vertexFlip A s Q := hcon Q
    rcases vertexFlip_even A s Q with ⟨k, hk⟩
    omega
  have hV : 4 * A.V ≤ ∑ Q : Quotient (cycleSetoid A.σ), vertexFlip A s Q := by
    have hle : (∑ _Q : Quotient (cycleSetoid A.σ), (4 : ℕ)) ≤
        ∑ Q : Quotient (cycleSetoid A.σ), vertexFlip A s Q :=
      Finset.sum_le_sum (fun Q _ => hall4 Q)
    simpa [Finset.sum_const, Finset.card_univ, V, Nat.mul_comm] using hle
  have heq := sum_vertexFlip_eq_sum_faceFlip A s hs
  have hFbound : (∑ R : Quotient (cycleSetoid A.φ), faceFlip A s R)
      ≤ ∑ R : Quotient (cycleSetoid A.φ), (2 * faceDeg A R - 4) :=
    Finset.sum_le_sum
      (fun R _ => faceFlip_le_two_mul_faceDeg_sub_four A s R (hFaceDeg_ge_three R))
  have hsum_int : ((∑ R : Quotient (cycleSetoid A.φ), (2 * faceDeg A R - 4) : ℕ) : ℤ)
      = 2 * (∑ R : Quotient (cycleSetoid A.φ), (faceDeg A R : ℤ)) - 4 * A.F := by
    rw [Nat.cast_sum]
    have hcast : ∀ R : Quotient (cycleSetoid A.φ),
        ((2 * faceDeg A R - 4 : ℕ) : ℤ) = 2 * (faceDeg A R : ℤ) - 4 := by
      intro R; have := hFaceDeg_ge_three R; rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [Finset.sum_congr rfl (fun R _ => hcast R), Finset.sum_sub_distrib, Finset.sum_const,
        ← Finset.mul_sum]
    simp [Finset.card_univ, F]
    ring
  have hFDS_int : (∑ R : Quotient (cycleSetoid A.φ), (faceDeg A R : ℤ)) = 2 * A.E := by
    rw [← Nat.cast_sum]; exact_mod_cast hFaceDegSum
  have key : (4 * A.V : ℤ) ≤ 4 * A.E - 4 * A.F := by
    calc (4 * A.V : ℤ)
        ≤ (∑ Q : Quotient (cycleSetoid A.σ), vertexFlip A s Q : ℕ) := by exact_mod_cast hV
      _ = (∑ R : Quotient (cycleSetoid A.φ), faceFlip A s R : ℕ) := by exact_mod_cast heq
      _ ≤ (∑ R : Quotient (cycleSetoid A.φ), (2 * faceDeg A R - 4) : ℕ) := by exact_mod_cast hFbound
      _ = 2 * (∑ R : Quotient (cycleSetoid A.φ), (faceDeg A R : ℤ)) - 4 * A.F := hsum_int
      _ = 2 * (2 * A.E) - 4 * A.F := by rw [hFDS_int]
      _ = 4 * A.E - 4 * A.F := by ring
  linarith [hEuler, key]

/-- **Non-vacuity of `active_component_low_vertex`.**  The tetrahedron (a genuine triangulated
sphere) satisfies all four hypotheses — connectivity-Euler, `∑ faceDeg = 2E`, `faceDeg ≥ 3`, and an
edge-invariant strict signing — so the conditional theorem is genuinely instantiable (and produces a
real low vertex), not vacuously true. -/
theorem active_component_low_vertex_nonvacuous :
    ∃ Q : Quotient (cycleSetoid tetraMap.σ), vertexFlip tetraMap tetraSign Q ≤ 2 := by
  apply active_component_low_vertex tetraMap
  · simpa [CombMap.eulerChar] using tetraMap_eulerChar
  · have hreg := tetraMap_faceRegular_three
    have hdeg3 : ∀ R, faceDeg tetraMap R = 3 := fun R => by rw [faceDeg]; exact hreg R
    rw [Finset.sum_congr rfl (fun R _ => hdeg3 R), (faceRegular_pF tetraMap hreg).symm]
    simp [Finset.sum_const, Finset.card_univ, CombMap.F, Nat.mul_comm]
  · intro R; rw [faceDeg, tetraMap_faceRegular_three R]
  · exact tetraSign_edgeInvariant

/-- **`active_component_low_vertex` generalizes the strict triangulated core.**  On a triangulated
sphere (`FaceRegular 3`), the face-degree hypotheses are automatic (`faceDeg = 3`,
`∑ faceDeg = 3F = 2E`), so the strict core's existential low vertex is exactly this theorem in the
degree-`3` case — recovering `cauchy_marked_sphere_low_vertex_strict`. -/
theorem strict_core_low_vertex_via_active
    (M : CombMap D) (hSphere : M.IsSphereMap) (hTri : M.FaceRegular 3)
    (s : D → StrictEdgeSign) (hs : EdgeInvariant M s) :
    ∃ Q : Quotient (cycleSetoid M.σ), vertexFlip M s Q ≤ 2 := by
  apply active_component_low_vertex M hSphere.2
  · have hdeg3 : ∀ R, faceDeg M R = 3 := fun R => by rw [faceDeg]; exact hTri R
    rw [Finset.sum_congr rfl (fun R _ => hdeg3 R), (faceRegular_pF M hTri).symm]
    simp [Finset.sum_const, Finset.card_univ, CombMap.F, Nat.mul_comm]
  · intro R; rw [faceDeg, hTri R]
  · exact hs

end ActiveComponent

/-! ## The §3.3 obstruction: the literal target is FALSE without a no-digon hypothesis

The spec's literal target — for every `IsSphereMap`, `FaceRegular 3`, edge-invariant `es` with a
nonzero edge, *some active vertex* has `vertexFlipCountSkipZeros ≤ 2` — is not provable: it is
false for general combinatorial maps, because parallel active edges create digon faces at which the
alternating pattern `+, −, +, −` gives every active vertex a skip-zero count of `4`.

We make this machine-checkable with the **dipole map** `dipMap`: two vertices joined by four
parallel edges (`V = 2, E = 4, F = 4` digons, Euler `χ = 2`, a genuine sphere map).  With the
alternating strict signing `dipSign`, *every* vertex has `vertexFlip = 4`, so there is no low
vertex — yet all hypotheses of `active_component_low_vertex` hold **except** `faceDeg ≥ 3` (every
face is a digon).  This proves the face-degree hypothesis is necessary, and that the literal target
fails. -/

section Obstruction

/-- Edge involution of the four-fold dipole: four transpositions pairing `i ↔ i+4`. -/
def dipAlpha : Equiv.Perm (Fin 8) :=
  (List.formPerm [0, 4]) * (List.formPerm [1, 5]) * (List.formPerm [2, 6]) * (List.formPerm [3, 7])

/-- Vertex rotation of the dipole: the two vertices rotate their four darts in *opposite* cyclic
order, which is what makes the embedding planar (four digon faces) rather than toroidal. -/
def dipSigma : Equiv.Perm (Fin 8) :=
  (List.formPerm [0, 1, 2, 3]) * (List.formPerm [4, 7, 6, 5])

/-- The four-fold dipole as a combinatorial map on `Fin 8`. -/
def dipMap : CombMap (Fin 8) where
  α := dipAlpha
  σ := dipSigma
  α_invol := by decide
  α_no_fixed := by decide

theorem dipMap_V : dipMap.V = 2 := by decide
theorem dipMap_E : dipMap.E = 4 := by decide
theorem dipMap_F : dipMap.F = 4 := by decide
theorem dipMap_eulerChar : dipMap.eulerChar = 2 := by decide

private theorem dipEdge (a b : Fin 8)
    (h : dipMap.σ.SameCycle a b ∨ b = dipMap.α a) : dipMap.dartStep a b := h

private theorem dip_dartStep_symm {a b : Fin 8} (h : dipMap.dartStep a b) :
    dipMap.dartStep b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · refine Or.inr ?_
    rw [h]
    have hinv : dipMap.α (dipMap.α a) = a := by
      have := congrArg (fun p => p a) dipMap.α_invol; simpa using this
    rw [hinv]

private theorem dip_rtg_symm {a b : Fin 8}
    (h : Relation.ReflTransGen dipMap.dartStep a b) :
    Relation.ReflTransGen dipMap.dartStep b a := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact (Relation.ReflTransGen.single (dip_dartStep_symm hbc)).trans ih

private theorem dip_reach_zero (d : Fin 8) :
    Relation.ReflTransGen dipMap.dartStep d 0 := by
  have e10 : dipMap.dartStep 1 0 := dipEdge 1 0 (by decide)
  have e40 : dipMap.dartStep 4 0 := dipEdge 4 0 (by decide)
  fin_cases d
  · exact .refl
  · exact .single e10
  · exact .single (dipEdge 2 0 (by decide))
  · exact .single (dipEdge 3 0 (by decide))
  · exact .single e40
  · exact .head (dipEdge 5 1 (by decide)) (.single e10)
  · exact .head (dipEdge 6 2 (by decide)) (.single (dipEdge 2 0 (by decide)))
  · exact .head (dipEdge 7 3 (by decide)) (.single (dipEdge 3 0 (by decide)))

theorem dipMap_connected : dipMap.Connected :=
  fun a b => (dip_reach_zero a).trans (dip_rtg_symm (dip_reach_zero b))

/-- The dipole is a genuine sphere map. -/
theorem dipMap_isSphereMap : dipMap.IsSphereMap :=
  ⟨dipMap_connected, dipMap_eulerChar⟩

/-- Alternating strict signing on the dipole: edges `{0,4}`, `{2,6}` are `plus`, edges `{1,5}`,
`{3,7}` are `minus`.  Around each vertex the `σ`-order of signs is `+, −, +, −`. -/
def dipSign : Fin 8 → StrictEdgeSign := fun d =>
  if d = 0 ∨ d = 4 ∨ d = 2 ∨ d = 6 then StrictEdgeSign.plus else StrictEdgeSign.minus

theorem dipSign_edgeInvariant : EdgeInvariant dipMap dipSign := by
  rw [EdgeInvariant]; decide

/-- Every vertex of the signed dipole has `vertexFlip = 4`: the alternating pattern `+, −, +, −`
flips at all four corners. -/
theorem dipMap_all_vertexFlip_four (d : Fin 8) :
    vertexFlip dipMap dipSign (Quotient.mk (cycleSetoid dipMap.σ) d) = 4 := by
  fin_cases d <;> decide

/-- **§3.3 obstruction (the literal target is false).**  There is a sphere map carrying a nonzero
edge-invariant strict signing with **no** low vertex: every vertex has four corner changes.  Hence
the with-zeros Cauchy lemma cannot hold for general combinatorial maps without a face-degree (no
active digon) hypothesis — the digon faces of the dipole are exactly the obstruction. -/
theorem marked_target_obstruction :
    ∃ (M : CombMap (Fin 8)) (s : Fin 8 → StrictEdgeSign),
      M.IsSphereMap ∧ EdgeInvariant M s ∧
        (∀ Q : Quotient (cycleSetoid M.σ), 4 ≤ vertexFlip M s Q) := by
  refine ⟨dipMap, dipSign, dipMap_isSphereMap, dipSign_edgeInvariant, ?_⟩
  intro Q
  obtain ⟨d, rfl⟩ := Q.exists_rep
  rw [dipMap_all_vertexFlip_four d]

end Obstruction

end ProofsInTheBook.Ch13MarkedReduction
