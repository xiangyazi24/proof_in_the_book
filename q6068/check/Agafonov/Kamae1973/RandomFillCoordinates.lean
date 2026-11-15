import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

namespace Agafonov

open MeasureTheory
open scoped BigOperators ENNReal

structure LetterDistribution (b : ℕ) where
  prob : Fin b → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_eq_one : ∑ a, prob a = 1

namespace LetterDistribution

variable {b : ℕ}

theorem prob_le_one (P : LetterDistribution b) (a : Fin b) : P.prob a ≤ 1 := by
  rw [← P.sum_eq_one]
  exact Finset.single_le_sum (fun c _ => P.nonneg c) (Finset.mem_univ a)

end LetterDistribution

def prefixList {C : Type*} (x : ℕ → C) (n : ℕ) : List C :=
  List.ofFn (fun i : Fin n => x i)

def wordCount {C : Type*} [DecidableEq C]
    (x : ℕ → C) (w : List C) (N : ℕ) : ℕ :=
  (List.range N).countP (fun i =>
    decide (prefixList (fun j => x (i + j)) w.length = w))

namespace Kamae1973

noncomputable section

noncomputable def letterMeasure {b : ℕ}
    (P : LetterDistribution b) : Measure (Fin b) :=
  ∑ a : Fin b, ENNReal.ofReal (P.prob a) • Measure.dirac a

@[simp] theorem letterMeasure_singleton {b : ℕ}
    (P : LetterDistribution b) (a : Fin b) :
    letterMeasure P {a} = ENNReal.ofReal (P.prob a) := by
  classical
  simp [letterMeasure, Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq']

@[simp] theorem letterMeasure_univ {b : ℕ}
    (P : LetterDistribution b) :
    letterMeasure P Set.univ = 1 := by
  classical
  have hsum :
      (∑ a : Fin b, ENNReal.ofReal (P.prob a)) = 1 := by
    calc
      (∑ a : Fin b, ENNReal.ofReal (P.prob a)) =
          ENNReal.ofReal (∑ a : Fin b, P.prob a) := by
        symm
        exact ENNReal.ofReal_sum_of_nonneg (fun a _ => P.nonneg a)
      _ = 1 := by
        rw [P.sum_eq_one]
        simp
  simpa [letterMeasure] using hsum

noncomputable instance letterMeasure_isProbabilityMeasure
    {b : ℕ} (P : LetterDistribution b) :
    IsProbabilityMeasure (letterMeasure P) :=
  ⟨letterMeasure_univ P⟩

noncomputable abbrev randomFillMeasure {b : ℕ}
    (P : LetterDistribution b) : Measure (ℕ → Fin b) :=
  Measure.infinitePi fun _ : ℕ => letterMeasure P

noncomputable def randomFill {b : ℕ}
    (τ : ℕ → ℕ) (y z : ℕ → Fin b) (k : ℕ) : Fin b :=
  @dite _ (k ∈ Set.range τ) (Classical.propDecidable _)
    (fun hk => y (Classical.choose hk)) (fun _ => z k)

 theorem randomFillMeasure_cylinder {b : ℕ}
    (P : LetterDistribution b) (s : Finset ℕ)
    (a : ℕ → Fin b) :
    randomFillMeasure P {z | ∀ k ∈ s, z k = a k} =
      ∏ k ∈ s, ENNReal.ofReal (P.prob (a k)) := by
  classical
  have hcylinder :
      {z : ℕ → Fin b | ∀ k ∈ s, z k = a k} =
        Set.pi (s : Set ℕ) (fun k => {a k}) := by
    ext z
    simp
  calc
    randomFillMeasure P {z | ∀ k ∈ s, z k = a k} =
        Measure.infinitePi (fun _ : ℕ => letterMeasure P)
          (Set.pi (s : Set ℕ) (fun k => {a k})) := by
      rw [hcylinder]
    _ = ∏ k ∈ s, letterMeasure P {a k} := by
      exact Measure.infinitePi_pi
        (fun _ : ℕ => letterMeasure P)
        (by
          intro k _
          exact measurableSet_singleton (a k))
    _ = ∏ k ∈ s, ENNReal.ofReal (P.prob (a k)) := by
      simp only [letterMeasure_singleton]

theorem randomFill_at_unselected
    {b : ℕ} (τ : ℕ → ℕ) (y z : ℕ → Fin b) {k : ℕ}
    (hk : k ∉ Set.range τ) :
    randomFill τ y z k = z k := by
  classical
  unfold randomFill
  rw [dif_neg hk]

end

end Kamae1973
end Agafonov
