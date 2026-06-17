import ProofsInTheBook.ZinanFFCT22

/-!
# `ZinanFFCT23` — the Chapter 13 `no_repeat` supplier: `a > 0` at the far-fold consumption site

`ZinanFFCT21` proved the far-fold boundary classification `i = 0` half, but only *conditional on*
the leading span coefficient being strictly positive (`hapos : 0 < (a : ℝ)` in
`far_fold_i_eq_zero`).  The comment there names the missing input:

> The leading coefficient `a > 0` remains a hypothesis: the `no_repeat` master brick that supplies it
> (a nonadjacent repeated vertex forcing an interior flat joint) is out of scope.

This module supplies that brick.  The exact consumption site is the `hapos` argument of
`ProofsInTheBook.ZinanFFCT21.far_fold_i_eq_zero` (and the `0 < (a : ℝ)` slot of the `hnd` datum of
`far_fold_boundary_classification_of_nondeg`).

## The mathematics

The fold datum is `(a : ℝ) • A(i+1) + (b : ℝ) • A j = A i` with `a, b : ℝ≥0` and `i + 2 < j < n+1`.

* **The reduction (unconditional).**  If `a = 0` then `A i = b • A j` with `b ≥ 0`; both endpoints lie
  on the sphere, so `nnreal_smul_unit_eq_unit` (FFCT21 Brick 2) forces `b = 1` **and** `A i = A j`.
  Since `i + 2 < j`, this is a *nonadjacent repeated vertex*.

* **The obstruction (the master gap = the named input).**  A nonadjacent repeat
  `A i = A j` (`i + 2 < j ≤ n`) is incompatible with the geometry: on a weakly convex
  `PositiveJoints` arm the chain cannot return to a previously visited vertex without flattening an
  interior joint (the polygon would have to double back, but every interior joint is strictly in
  `(0, π)`).  Locally the determinant-collapse of FFCT21 Brick 4 does **not** fire here — the two
  weak supports of the predecessor edge of `j` are *equal* multiples (same sign) of one determinant,
  not opposite multiples — so this is exactly the same out-of-plane/global obstruction the audit
  scoped out for the tail half (`HANDOFF/design-rounds/ch13-B5-B1-audit.md`, line 3).  We therefore
  package it, in the honest CONDITIONAL form of FFCT22, as the explicit *satisfiable* hypothesis
  `NoNonadjacentRepeat A` — "the arm visits each vertex at most once at nonadjacent positions".

## Deliverables

* `NoNonadjacentRepeat` — the named, satisfiable no-repeat predicate.
* `repeat_of_a_eq_zero` — **unconditional**: `a = 0` forces the nonadjacent repeat `A i = A j`.
* `no_repeat_of_positiveJoints` — the deliverable: `0 < (a : ℝ)` from the fold datum plus
  `NoNonadjacentRepeat A` (the conditional input).
* `far_fold_nondeg_datum_of_no_repeat` — assembles the full `∃ a b, 0 < a ∧ 0 < b ∧ …` datum that
  `far_fold_boundary_classification_of_nondeg` consumes, eliminating *both* `hapos` and the manual
  `b`-extraction; this is the drop-in replacement at the consumption site.
* `far_fold_i_eq_zero_of_no_repeat` — the FFCT21 wrapper with `hapos` discharged from
  `NoNonadjacentRepeat`.

Non-vacuity guards witness `NoNonadjacentRepeat` is a real (satisfiable, non-trivial) hypothesis.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT3 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10
open ProofsInTheBook.ZinanFFCT12 ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT21

namespace ProofsInTheBook.ZinanFFCT23

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## The named no-repeat predicate. -/

/-- **`NoNonadjacentRepeat A`** — the arm `A` never revisits a vertex at two *nonadjacent* positions:
for indices `r + 2 ≤ s` (both in range, `s < n + 1`), the vertices `A r` and `A s` are distinct.

This is the global geometric fact that, on a weakly convex `PositiveJoints` arm, the chain cannot
return to a previously visited vertex without flattening an interior joint.  Supplying it from
`PositiveJoints` alone is the audited out-of-plane master gap (the same obstruction as the tail-half
cone propagation, `HANDOFF/design-rounds/ch13-B5-B1-audit.md` line 3); here it is the honest
explicit, satisfiable hypothesis (see the non-vacuity guards below). -/
def NoNonadjacentRepeat {n : ℕ} (A : Fin (n + 1) → S2) : Prop :=
  ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1), r + 2 ≤ s →
    A ⟨r, hr⟩ ≠ A ⟨s, hs⟩

/-! ## The unconditional reduction: `a = 0` forces a nonadjacent repeat. -/

/-- **The reduction (unconditional).**  From the fold datum `(a : ℝ)•A(i+1) + (b : ℝ)•A j = A i`
with `a, b : ℝ≥0`, if `a = 0` then `A i = A j` (and `b = 1`).

Proof: with `a = 0` the datum reads `A i = b • A j`; both are unit vectors and `b ≥ 0`, so
`nnreal_smul_unit_eq_unit` (FFCT21 Brick 2) gives `b = 1` and `A i = A j`. -/
theorem repeat_of_a_eq_zero {n : ℕ} {A : Fin (n + 1) → S2} {i j : ℕ}
    (hi2 : i + 1 < n + 1) (hj : j < n + 1) (hii : i < n + 1)
    {a b : ℝ≥0}
    (hcoeff : (a : ℝ) • (A ⟨i + 1, hi2⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3) = (A ⟨i, hii⟩ : E3))
    (ha0 : (a : ℝ) = 0) :
    A ⟨i, hii⟩ = A ⟨j, hj⟩ := by
  -- with `a = 0` the datum is `A i = b • A j`.
  have hpav : (A ⟨i, hii⟩ : E3) = (b : ℝ) • (A ⟨j, hj⟩ : E3) := by
    rw [← hcoeff, ha0, zero_smul, zero_add]
  -- Brick 2: a nonnegative multiple of a unit equal to a unit forces equality.
  exact (nnreal_smul_unit_eq_unit (a := (b : ℝ)) b.2 hpav).2

/-! ## The deliverable: `a > 0` from the no-repeat hypothesis. -/

/-- **(`no_repeat_of_positiveJoints`) The leading coefficient is strictly positive.**  Given the fold
datum `(a : ℝ)•A(i+1) + (b : ℝ)•A j = A i` with `a, b : ℝ≥0`, the nonadjacency `i + 2 < j < n+1`, and
the no-repeat hypothesis `NoNonadjacentRepeat A`, the leading coefficient is strictly positive:
`0 < (a : ℝ)`.

This is the exact input the FFCT21 consumption site (`far_fold_i_eq_zero` / the `hnd` datum of
`far_fold_boundary_classification_of_nondeg`) names "out of scope".  Proof: `a ≥ 0` always; if
`a = 0`, the reduction `repeat_of_a_eq_zero` produces the nonadjacent repeat `A i = A j`, contradicted
by `NoNonadjacentRepeat A` at the positions `i, j` (`i + 2 ≤ j`). -/
theorem no_repeat_of_positiveJoints {n : ℕ} {A : Fin (n + 1) → S2}
    (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    {a b : ℝ≥0}
    (hcoeff : (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3)
      = (A ⟨i, by omega⟩ : E3)) :
    0 < (a : ℝ) := by
  rcases lt_or_eq_of_le a.2 with hpos | hzero
  · exact hpos
  · exfalso
    have ha0 : (a : ℝ) = 0 := hzero.symm
    have hii : i < n + 1 := by omega
    have hi2 : i + 1 < n + 1 := by omega
    -- the nonadjacent repeat `A i = A j`.
    have hrep : A ⟨i, hii⟩ = A ⟨j, hj⟩ :=
      repeat_of_a_eq_zero hi2 hj hii hcoeff ha0
    -- contradict `NoNonadjacentRepeat` at `(i, j)` with `i + 2 ≤ j`.
    exact hnr i j hii hj (by omega) hrep

/-! ## Drop-in assembly for the FFCT21 consumption site. -/

/-- **Assemble the full nondegenerate fold datum.**  From the NNReal span membership
`A i ∈ span≥0 {A(i+1), A j}` (the raw far-fold input), weak convexity, and `NoNonadjacentRepeat A`,
produce the full datum `∃ a b : ℝ≥0, 0 < a ∧ 0 < b ∧ (a:ℝ)•A(i+1) + (b:ℝ)•A j = A i` that
`far_fold_boundary_classification_of_nondeg` consumes.

`b > 0` is FFCT21 Brick 3 (`coeff_b_pos_of_edge_short`) from the short fold edge `(A i, A(i+1))`;
`a > 0` is `no_repeat_of_positiveJoints`.  This eliminates the `hapos` hypothesis entirely. -/
theorem far_fold_nondeg_datum_of_no_repeat {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3)) :
    ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
      (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3)
        = (A ⟨i, by omega⟩ : E3) := by
  have hii : i < n + 1 := by omega
  have hi2 : i + 1 < n + 1 := by omega
  -- Brick 1: extract the nonnegative coefficients.
  obtain ⟨a, b, hcoeff⟩ := span_pair_coeffs_S2 hcol
  -- the short fold edge `(A i, A(i+1))` from weak convexity.
  have hedge : ShortArc (A ⟨i, hii⟩) (A ⟨i + 1, hi2⟩) := by
    have hn2 : 2 ≤ n := hA.two_le
    have h := hA.closed_convex.edge_short ⟨i, hii⟩
    have hsucc2 : ((⟨i, hii⟩ : Fin (n + 1)) + 1) = (⟨i + 1, hi2⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone,
        Nat.mod_eq_of_lt (show i + 1 < n + 1 by omega)]
    rwa [hsucc2] at h
  -- `b > 0` (FFCT21 Brick 3) and `a > 0` (this module).
  have hbpos : 0 < (b : ℝ) := coeff_b_pos_of_edge_short hcoeff hedge
  have hapos : 0 < (a : ℝ) := no_repeat_of_positiveJoints hnr hij hj hcoeff
  exact ⟨a, b, hapos, hbpos, hcoeff⟩

/-- **The FFCT21 wrapper with `hapos` discharged.**  `far_fold_i_eq_zero` required the caller to
supply `0 < (a : ℝ)`; here it is discharged from `NoNonadjacentRepeat A`, giving the unconditional
`i = 0` conclusion on the no-repeat class. -/
theorem far_fold_i_eq_zero_of_no_repeat {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A) (hnr : NoNonadjacentRepeat A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    {a b : ℝ≥0}
    (hab : (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3)
      = (A ⟨i, by omega⟩ : E3)) :
    i = 0 := by
  have hapos : 0 < (a : ℝ) := no_repeat_of_positiveJoints hnr hij hj hab
  exact far_fold_i_eq_zero hA hposA hB hangle hij hj hab hapos

/-- **The full boundary classification with `a > 0` discharged from no-repeat.**  Combining the
assembled datum (`far_fold_nondeg_datum_of_no_repeat`) with FFCT21's `i = 0` half: from the raw span
membership `A i ∈ span≥0 {A(i+1), A j}`, weak convexity, `PositiveJoints`, and `NoNonadjacentRepeat`,
the far fold can only occur at `i = 0`. -/
theorem far_fold_boundary_i_eq_zero_of_span {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A) (hnr : NoNonadjacentRepeat A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3)) :
    i = 0 :=
  far_fold_boundary_classification_of_nondeg hA hposA hB hangle hij hj
    (far_fold_nondeg_datum_of_no_repeat hA hnr hij hj hcol)

/-! ## Non-vacuity / anti-impostor guards (playbook §3.3).

`NoNonadjacentRepeat` is a *genuine* (satisfiable, non-trivial) hypothesis: it is not vacuously true
(it constrains the arm) and it is satisfiable (any arm with injective vertices satisfies it). -/

/-- `NoNonadjacentRepeat` is satisfied by every arm with injective vertices — so the hypothesis is
**satisfiable**, not vacuous.  (A strictly convex arm has injective vertices; this is the class on
which the whole comparison lives.) -/
theorem noNonadjacentRepeat_of_injective {n : ℕ} {A : Fin (n + 1) → S2}
    (hinj : Function.Injective A) : NoNonadjacentRepeat A := by
  intro r s hr hs hrs hne
  -- `A ⟨r,_⟩ = A ⟨s,_⟩` with injectivity forces `r = s`, contradicting `r + 2 ≤ s`.
  have : (⟨r, hr⟩ : Fin (n + 1)) = ⟨s, hs⟩ := hinj hne
  have : r = s := by exact congrArg Fin.val this
  omega

/-- `NoNonadjacentRepeat` is **not vacuously true**: it has genuine content — it can *fail*.  Witness:
a constant arm (every vertex equal) on `n = 2` violates it at the nonadjacent pair `(0, 2)`.  (This
is a non-convex arm; the witness only certifies that the predicate is a real constraint, ruling out
the impostor reading where the conclusion `0 < a` is asserted under a vacuously-false premise.) -/
theorem noNonadjacentRepeat_can_fail :
    ∃ (A : Fin (2 + 1) → S2), ¬ NoNonadjacentRepeat A := by
  classical
  -- the constant arm at the north pole `e₀ = (1,0,0)`.
  refine ⟨fun _ => ⟨!₂[(1:ℝ), 0, 0], ?_⟩, ?_⟩
  · -- `‖e₀‖ = 1`.
    rw [EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_three]
  · intro hnr
    -- the constant arm repeats `A 0 = A 2`, nonadjacent (`0 + 2 ≤ 2`).
    exact hnr 0 2 (by omega) (by omega) (by omega) rfl

/-- Non-vacuity of the reduction's conclusion: the repeat `A i = A j` is the genuine target — the
reduction `repeat_of_a_eq_zero` is *not* vacuous, since `a = 0` is realisable (e.g. `A i = A j`,
`a = 0`, `b = 1`, with `A(i+1)` arbitrary witnesses the fold datum). -/
theorem repeat_reduction_nonvacuous (v w : S2) :
    (0 : ℝ) • (w : E3) + (1 : ℝ) • (v : E3) = (v : E3) := by
  rw [zero_smul, one_smul, zero_add]

#print axioms repeat_of_a_eq_zero
#print axioms no_repeat_of_positiveJoints
#print axioms far_fold_nondeg_datum_of_no_repeat
#print axioms far_fold_i_eq_zero_of_no_repeat
#print axioms far_fold_boundary_i_eq_zero_of_span
#print axioms noNonadjacentRepeat_of_injective
#print axioms noNonadjacentRepeat_can_fail

end ProofsInTheBook.ZinanFFCT23
