import Agafonov.Kamae1973.RandomFillCoordinates
import Agafonov.Kamae1973.FillExpectation
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Expectations of finite random-fill windows

Finite word indicators for the random fill are measurable cylinder functions.
Their expectations are the deterministic fill products, so centering gives
bounded mean-zero variables whose finite sums recover sliding word counts.
This is the expectation step in Kamae (1973), statement (4.9), pp. 142–147.
-/

namespace Agafonov.Kamae1973

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The indicator that the random fill realizes one prescribed finite word at
one starting position.  This is the window indicator in Kamae (1973),
statement (4.9), pp. 142–147. -/
noncomputable def randomFillHit {b q : ℕ}
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b) (z : ℕ → Fin b) : ℝ :=
  if ∀ r : Fin q, randomFill τ y z (i + r.val) = w r then 1 else 0

/-- The centered finite-window indicator.  This is the mean-zero summand in
Kamae (1973), statement (4.9), pp. 142–147. -/
noncomputable def centeredFillHit {b q : ℕ}
    (P : LetterDistribution b) (τ : ℕ → ℕ) (y : ℕ → Fin b)
    (i : ℕ) (w : Fin q → Fin b) (z : ℕ → Fin b) : ℝ :=
  randomFillHit τ y i w z - fillWindowExpectation P τ y i w

/-- The finite sum of centered random-fill word indicators.  This is the
partial centered count in Kamae (1973), statement (4.9), pp. 142–147. -/
noncomputable def centeredFillSum {b q : ℕ}
    (P : LetterDistribution b) (τ : ℕ → ℕ) (y : ℕ → Fin b)
    (N : ℕ) (w : Fin q → Fin b) (z : ℕ → Fin b) : ℝ :=
  ∑ i ∈ Finset.range N, centeredFillHit P τ y i w z

private instance randomFillRangeMembershipDecidable
    (τ : ℕ → ℕ) (k : ℕ) : Decidable (k ∈ Set.range τ) :=
  Classical.propDecidable _

private noncomputable def fillHitEvent {b q : ℕ}
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b) : Set (ℕ → Fin b) :=
  {z | ∀ r : Fin q, randomFill τ y z (i + r.val) = w r}

private noncomputable def selectedCoordinatesMatch {b q : ℕ}
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b) : Prop :=
  ∀ r : Fin q, ∀ h : i + r.val ∈ Set.range τ,
    y (Classical.choose h) = w r

private noncomputable def unselectedOffsets
    (τ : ℕ → ℕ) (i q : ℕ) : Finset (Fin q) :=
  Finset.univ.filter fun r => i + r.val ∉ Set.range τ

private def shiftedOffsetEmbedding {q : ℕ} (i : ℕ) : Fin q ↪ ℕ where
  toFun r := i + r.val
  inj' := by
    intro r s hrs
    apply Fin.ext
    exact Nat.add_left_cancel hrs

private noncomputable def unselectedCoordinates
    (τ : ℕ → ℕ) (i q : ℕ) : Finset ℕ :=
  (unselectedOffsets τ i q).map (shiftedOffsetEmbedding i)

private noncomputable def fillCylinderTarget {b q : ℕ}
    (y : ℕ → Fin b) (i : ℕ) (w : Fin q → Fin b) (k : ℕ) : Fin b :=
  if h : i ≤ k ∧ k < i + q then
    w ⟨k - i, by omega⟩
  else y 0

private noncomputable def freeFillCylinder {b q : ℕ}
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b) : Set (ℕ → Fin b) :=
  {z | ∀ k ∈ unselectedCoordinates τ i q,
    z k = fillCylinderTarget y i w k}

private theorem fillCylinderTarget_shiftedOffset {b q : ℕ}
    (y : ℕ → Fin b) (i : ℕ) (w : Fin q → Fin b) (r : Fin q) :
    fillCylinderTarget y i w (i + r.val) = w r := by
  classical
  have hbounds : i ≤ i + r.val ∧ i + r.val < i + q := by
    omega
  unfold fillCylinderTarget
  rw [dif_pos hbounds]
  apply congrArg w
  apply Fin.ext
  simp

private theorem measurable_randomFillCoordinate {b : ℕ}
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (k : ℕ) :
    Measurable (fun z : ℕ → Fin b => randomFill τ y z k) := by
  classical
  by_cases hk : k ∈ Set.range τ
  · have heq :
        (fun z : ℕ → Fin b => randomFill τ y z k) =
          fun _ => y (Classical.choose hk) := by
      funext z
      simp only [randomFill, dif_pos hk]
    rw [heq]
    exact measurable_const
  · have heq :
        (fun z : ℕ → Fin b => randomFill τ y z k) =
          fun z => z k := by
      funext z
      simp only [randomFill, dif_neg hk]
    rw [heq]
    exact measurable_pi_apply k

private theorem measurableSet_fillHitEvent {b q : ℕ}
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b) :
    MeasurableSet (fillHitEvent τ y i w) := by
  classical
  rw [show fillHitEvent τ y i w =
      ⋂ r : Fin q,
        {z : ℕ → Fin b | randomFill τ y z (i + r.val) = w r} by
    ext z
    simp [fillHitEvent]]
  apply MeasurableSet.iInter
  intro r
  exact measurableSet_eq_fun
    (measurable_randomFillCoordinate τ y (i + r.val)) measurable_const

private theorem randomFillHit_eq_indicator {b q : ℕ}
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b) :
    randomFillHit τ y i w = (fillHitEvent τ y i w).indicator 1 := by
  classical
  funext z
  by_cases hz : ∀ r : Fin q, randomFill τ y z (i + r.val) = w r
  · simp [randomFillHit, fillHitEvent, Set.indicator_apply, hz]
  · simp [randomFillHit, fillHitEvent, Set.indicator_apply, hz]

private theorem fillHitEvent_eq_freeFillCylinder {b q : ℕ}
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b)
    (hmatch : selectedCoordinatesMatch τ y i w) :
    fillHitEvent τ y i w = freeFillCylinder τ y i w := by
  classical
  ext z
  change
    (∀ r : Fin q, randomFill τ y z (i + r.val) = w r) ↔
      ∀ k ∈ unselectedCoordinates τ i q,
        z k = fillCylinderTarget y i w k
  constructor
  · intro hz k hk
    rcases Finset.mem_map.mp hk with ⟨r, hr, rfl⟩
    have hrnot : i + r.val ∉ Set.range τ :=
      (Finset.mem_filter.mp hr).2
    calc
      z (i + r.val) = randomFill τ y z (i + r.val) :=
        (randomFill_at_unselected τ y z hrnot).symm
      _ = w r := hz r
      _ = fillCylinderTarget y i w (i + r.val) :=
        (fillCylinderTarget_shiftedOffset y i w r).symm
  · intro hz r
    by_cases hrsel : i + r.val ∈ Set.range τ
    · unfold randomFill
      rw [dif_pos hrsel]
      exact hmatch r hrsel
    · rw [randomFill_at_unselected τ y z hrsel]
      have hrfree : r ∈ unselectedOffsets τ i q := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrsel⟩
      have hk : i + r.val ∈ unselectedCoordinates τ i q := by
        exact Finset.mem_map.mpr ⟨r, hrfree, rfl⟩
      calc
        z (i + r.val) = fillCylinderTarget y i w (i + r.val) :=
          hz (i + r.val) hk
        _ = w r := fillCylinderTarget_shiftedOffset y i w r

private theorem freeFillCylinder_real {b q : ℕ}
    (P : LetterDistribution b) (τ : ℕ → ℕ)
    (y : ℕ → Fin b) (i : ℕ) (w : Fin q → Fin b) :
    (randomFillMeasure P).real (freeFillCylinder τ y i w) =
      ∏ r ∈ unselectedOffsets τ i q, P.prob (w r) := by
  classical
  unfold freeFillCylinder
  rw [measureReal_def,
    randomFillMeasure_cylinder P (unselectedCoordinates τ i q)
      (fillCylinderTarget y i w)]
  unfold unselectedCoordinates
  rw [Finset.prod_map, ENNReal.toReal_prod]
  simp only [ENNReal.toReal_ofReal (P.nonneg _)]
  apply Finset.prod_congr rfl
  intro r _
  rw [fillCylinderTarget_shiftedOffset]

private theorem fillWindowExpectation_eq_unselectedProduct {b q : ℕ}
    (P : LetterDistribution b) (τ : ℕ → ℕ)
    (y : ℕ → Fin b) (i : ℕ) (w : Fin q → Fin b)
    (hmatch : selectedCoordinatesMatch τ y i w) :
    fillWindowExpectation P τ y i w =
      ∏ r ∈ unselectedOffsets τ i q, P.prob (w r) := by
  classical
  unfold fillWindowExpectation
  calc
    (∏ r : Fin q,
      if h : i + r.val ∈ Set.range τ then
        if y (Classical.choose h) = w r then 1 else 0
      else P.prob (w r)) =
        ∏ r : Fin q,
          if r ∈ unselectedOffsets τ i q then P.prob (w r) else 1 := by
      apply Finset.prod_congr rfl
      intro r _
      by_cases hrsel : i + r.val ∈ Set.range τ
      · have hrnot : r ∉ unselectedOffsets τ i q := by
          intro hr
          exact (Finset.mem_filter.mp hr).2 hrsel
        rw [dif_pos hrsel, if_pos (hmatch r hrsel), if_neg hrnot]
      · have hrmem : r ∈ unselectedOffsets τ i q :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrsel⟩
        rw [dif_neg hrsel, if_pos hrmem]
    _ = ∏ r ∈ unselectedOffsets τ i q, P.prob (w r) := by
      exact Finset.prod_ite_mem_eq
        (unselectedOffsets τ i q) (fun r => P.prob (w r))

private theorem randomFillHit_eq_zero_of_selectedMismatch {b q : ℕ}
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b)
    (hmismatch : ¬ selectedCoordinatesMatch τ y i w) :
    randomFillHit τ y i w = fun _ => 0 := by
  classical
  unfold selectedCoordinatesMatch at hmismatch
  obtain ⟨r, hr⟩ := not_forall.mp hmismatch
  obtain ⟨hsel, hletter⟩ := not_forall.mp hr
  funext z
  unfold randomFillHit
  have hnot :
      ¬ ∀ s : Fin q, randomFill τ y z (i + s.val) = w s := by
    intro hall
    have hfill :
        randomFill τ y z (i + r.val) = y (Classical.choose hsel) := by
      unfold randomFill
      rw [dif_pos hsel]
    exact hletter (hfill.symm.trans (hall r))
  rw [if_neg hnot]

private theorem fillWindowExpectation_eq_zero_of_selectedMismatch {b q : ℕ}
    (P : LetterDistribution b) (τ : ℕ → ℕ)
    (y : ℕ → Fin b) (i : ℕ) (w : Fin q → Fin b)
    (hmismatch : ¬ selectedCoordinatesMatch τ y i w) :
    fillWindowExpectation P τ y i w = 0 := by
  classical
  unfold selectedCoordinatesMatch at hmismatch
  obtain ⟨r, hr⟩ := not_forall.mp hmismatch
  obtain ⟨hsel, hletter⟩ := not_forall.mp hr
  unfold fillWindowExpectation
  apply Finset.prod_eq_zero (Finset.mem_univ r)
  rw [dif_pos hsel, if_neg hletter]

private theorem finsetProduct_mem_Icc
    {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, f i ∈ Set.Icc (0 : ℝ) 1) :
    (∏ i ∈ s, f i) ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp
  | @insert i s hi ih =>
      intro hf
      rw [Finset.prod_insert hi]
      have hiI : f i ∈ Set.Icc (0 : ℝ) 1 :=
        hf i (Finset.mem_insert_self i s)
      have hsI : (∏ j ∈ s, f j) ∈ Set.Icc (0 : ℝ) 1 :=
        ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
      constructor
      · exact mul_nonneg hiI.1 hsI.1
      · calc
          f i * ∏ j ∈ s, f j ≤ (1 : ℝ) * 1 :=
            mul_le_mul hiI.2 hsI.2 hsI.1 zero_le_one
          _ = 1 := one_mul 1

private theorem randomFillHit_mem_Icc {b q : ℕ}
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b) (z : ℕ → Fin b) :
    randomFillHit τ y i w z ∈ Set.Icc (0 : ℝ) 1 := by
  unfold randomFillHit
  split_ifs <;> simp

private theorem fillWindowExpectation_mem_Icc {b q : ℕ}
    (P : LetterDistribution b) (τ : ℕ → ℕ)
    (y : ℕ → Fin b) (i : ℕ) (w : Fin q → Fin b) :
    fillWindowExpectation P τ y i w ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  unfold fillWindowExpectation
  apply finsetProduct_mem_Icc
  intro r _
  by_cases hsel : i + r.val ∈ Set.range τ
  · by_cases hletter : y (Classical.choose hsel) = w r
    · simp [hsel, hletter]
    · simp [hsel, hletter]
  · simp [hsel, P.nonneg (w r), P.prob_le_one (w r)]

private theorem integrable_randomFillHit {b q : ℕ}
    (P : LetterDistribution b) (τ : ℕ → ℕ)
    (y : ℕ → Fin b) (i : ℕ) (w : Fin q → Fin b) :
    Integrable (randomFillHit τ y i w) (randomFillMeasure P) := by
  rw [randomFillHit_eq_indicator]
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_fillHitEvent τ y i w)

private def profileWindow {C : Type*}
    (x : ℕ → C) (i q : ℕ) : Fin q → C :=
  fun r => x (i + r.val)

private def profileHitNat {C : Type*} [DecidableEq C]
    (x : ℕ → C) {q : ℕ} (w : Fin q → C) (i : ℕ) : ℕ :=
  if w = profileWindow x i q then 1 else 0

private theorem wordCount_ofFn_succ {C : Type*} [DecidableEq C]
    (x : ℕ → C) {q : ℕ} (w : Fin q → C) (N : ℕ) :
    wordCount x (List.ofFn w) (N + 1) =
      wordCount x (List.ofFn w) N + profileHitNat x w N := by
  simp [wordCount, List.range_succ, profileHitNat, profileWindow,
    prefixList, eq_comm] <;> rfl

private theorem cast_profileHitNat_eq_randomFillHit
    {b q : ℕ} (τ : ℕ → ℕ) (y z : ℕ → Fin b)
    (i : ℕ) (w : Fin q → Fin b) :
    (profileHitNat (randomFill τ y z) w i : ℝ) =
      randomFillHit τ y i w z := by
  classical
  unfold profileHitNat profileWindow randomFillHit
  by_cases hword : w = fun r : Fin q => randomFill τ y z (i + r.val)
  · rw [if_pos hword]
    have hall :
        ∀ r : Fin q, randomFill τ y z (i + r.val) = w r := by
      intro r
      exact (congrFun hword r).symm
    rw [if_pos hall]
    simp
  · rw [if_neg hword]
    have hnot :
        ¬ ∀ r : Fin q, randomFill τ y z (i + r.val) = w r := by
      intro hall
      apply hword
      funext r
      exact (hall r).symm
    rw [if_neg hnot]
    simp

private theorem cast_wordCount_ofFn_eq_sum_hit
    {b q : ℕ} (τ : ℕ → ℕ) (y z : ℕ → Fin b)
    (N : ℕ) (w : Fin q → Fin b) :
    (wordCount (randomFill τ y z) (List.ofFn w) N : ℝ) =
      ∑ i ∈ Finset.range N, randomFillHit τ y i w z := by
  induction N with
  | zero =>
      simp [wordCount]
  | succ N ih =>
      rw [wordCount_ofFn_succ, Nat.cast_add, Finset.sum_range_succ, ih]
      rw [cast_profileHitNat_eq_randomFillHit]

/-- A finite-window random-fill indicator is measurable.  This is the cylinder
measurability assertion used in Kamae (1973), statement (4.9), pp. 142–147. -/
theorem measurable_randomFillHit
    {b q : ℕ} (τ : ℕ → ℕ) (y : ℕ → Fin b)
    (i : ℕ) (w : Fin q → Fin b) :
    Measurable (randomFillHit τ y i w) := by
  unfold randomFillHit
  exact Measurable.ite (measurableSet_fillHitEvent τ y i w)
    measurable_const measurable_const

/-- The expectation of one random-fill word indicator is the deterministic
conditional fill product.  This is the one-window expectation calculation in
Kamae (1973), statement (4.9), pp. 142–147. -/
theorem randomFillHit_integral
    {b q : ℕ} (P : LetterDistribution b)
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b) :
    ∫ z, randomFillHit τ y i w z ∂(randomFillMeasure P) =
      fillWindowExpectation P τ y i w := by
  classical
  by_cases hmatch : selectedCoordinatesMatch τ y i w
  · rw [randomFillHit_eq_indicator]
    rw [integral_indicator_one (measurableSet_fillHitEvent τ y i w)]
    rw [fillHitEvent_eq_freeFillCylinder τ y i w hmatch]
    rw [freeFillCylinder_real P τ y i w]
    exact (fillWindowExpectation_eq_unselectedProduct
      P τ y i w hmatch).symm
  · rw [randomFillHit_eq_zero_of_selectedMismatch τ y i w hmatch]
    rw [integral_zero]
    exact (fillWindowExpectation_eq_zero_of_selectedMismatch
      P τ y i w hmatch).symm

/-- The centered one-window indicator has integral zero.  This is the centering
identity in Kamae (1973), statement (4.9), pp. 142–147. -/
theorem centeredFillHit_integral
    {b q : ℕ} (P : LetterDistribution b)
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b) :
    ∫ z, centeredFillHit P τ y i w z ∂(randomFillMeasure P) = 0 := by
  unfold centeredFillHit
  rw [integral_sub
    (integrable_randomFillHit P τ y i w)
    (integrable_const (fillWindowExpectation P τ y i w))]
  rw [randomFillHit_integral]
  simp

/-- Every centered finite-window indicator has absolute value at most one.  This
is the pointwise bound in Kamae (1973), statement (4.9), pp. 142–147. -/
theorem abs_centeredFillHit_le_one
    {b q : ℕ} (P : LetterDistribution b)
    (τ : ℕ → ℕ) (y : ℕ → Fin b) (i : ℕ)
    (w : Fin q → Fin b) (z : ℕ → Fin b) :
    |centeredFillHit P τ y i w z| ≤ 1 := by
  have hhit := randomFillHit_mem_Icc τ y i w z
  have hexpect := fillWindowExpectation_mem_Icc P τ y i w
  unfold centeredFillHit
  rw [abs_le]
  constructor
  · simpa using sub_le_sub hhit.1 hexpect.2
  · simpa using sub_le_sub hhit.2 hexpect.1

/-- Sliding word count for the random fill is the sum of its finite-window hit
indicators.  This is the finite count decomposition in Kamae (1973),
statement (4.9), pp. 142–147. -/
theorem wordCount_randomFill_eq_sum_hit
    {b q : ℕ} (τ : ℕ → ℕ) (y z : ℕ → Fin b)
    (N : ℕ) (w : Fin q → Fin b) :
    (wordCount (randomFill τ y z) (List.ofFn w) N : ℝ) =
      ∑ i ∈ Finset.range N, randomFillHit τ y i w z := by
  exact cast_wordCount_ofFn_eq_sum_hit τ y z N w

end

end Agafonov.Kamae1973

#print axioms Agafonov.Kamae1973.measurable_randomFillHit
#print axioms Agafonov.Kamae1973.randomFillHit_integral
#print axioms Agafonov.Kamae1973.centeredFillHit_integral
#print axioms Agafonov.Kamae1973.abs_centeredFillHit_le_one
#print axioms Agafonov.Kamae1973.wordCount_randomFill_eq_sum_hit
