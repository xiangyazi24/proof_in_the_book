import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Agafonov

open scoped BigOperators

/-- The first `n` values of a stream. -/
def prefixList {A : Type*} (x : ℕ → A) (n : ℕ) : List A :=
  List.ofFn (fun i : Fin n => x i)

/-- A probability vector on a finite alphabet. -/
structure LetterDistribution (b : ℕ) where
  prob : Fin b → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_eq_one : ∑ a, prob a = 1

namespace LetterDistribution

/-- Product probability of a finite word. -/
def wordMass {b : ℕ} (P : LetterDistribution b) (w : List (Fin b)) : ℝ :=
  (w.map P.prob).prod

/-- Word masses are nonnegative. -/
theorem wordMass_nonneg {b : ℕ} (P : LetterDistribution b)
    (w : List (Fin b)) : 0 ≤ P.wordMass w := by
  induction w with
  | nil => simp [wordMass]
  | cons a w ih =>
      simp only [wordMass, List.map_cons, List.prod_cons]
      exact mul_nonneg (P.nonneg a) ih

/-- Every coordinate of a probability vector is at most one. -/
theorem prob_le_one {b : ℕ} (P : LetterDistribution b) (a : Fin b) :
    P.prob a ≤ 1 := by
  rw [← P.sum_eq_one]
  exact Finset.single_le_sum (fun c _ => P.nonneg c) (Finset.mem_univ a)

/-- Every finite word mass is at most one. -/
theorem wordMass_le_one {b : ℕ} (P : LetterDistribution b)
    (w : List (Fin b)) : P.wordMass w ≤ 1 := by
  induction w with
  | nil => simp [wordMass]
  | cons a w ih =>
      simp only [wordMass, List.map_cons, List.prod_cons]
      exact le_trans (mul_le_mul_of_nonneg_left ih (P.nonneg a))
        (by simpa using P.prob_le_one a)

end LetterDistribution

/-- Sliding occurrences with starts below `N`. -/
def wordCount {C : Type*} [DecidableEq C]
    (x : ℕ → C) (w : List C) (N : ℕ) : ℕ :=
  (List.range N).countP (fun i =>
    decide (prefixList (fun j => x (i + j)) w.length = w))

namespace Kamae1973

/-- A finite-block law family; only the law field is used by this packet. -/
structure BlockFamily (C : Type*) [Fintype C] where
  law : (n : ℕ) → (Fin n → C) → ℝ

/-- Occurrences with starts in one interval. -/
def intervalWordCount {C : Type*} [DecidableEq C]
    (x : ℕ → C) (a T : ℕ) (w : List C) : ℕ :=
  wordCount (fun i => x (a + i)) w T

/-- Finite `L¹` distance between arrays. -/
noncomputable def finiteLOne {D : Type*} [Fintype D]
    (p q : D → ℝ) : ℝ :=
  ∑ d, |p d - q d|

/-- Parameters controlling one painted stage. -/
structure PaintingParameters {b : ℕ}
    (P : LetterDistribution b) (R : ℕ) (β : ℝ) where
  blockLength : ℕ
  blocksPerMacro : ℕ
  macroLength : ℕ
  minMacroblocks : ℕ
  one_le_blockLength : 1 ≤ blockLength
  resolution_le : R ≤ blockLength
  two_le_blocksPerMacro : 2 ≤ blocksPerMacro
  macro_eq : macroLength = blocksPerMacro * blockLength
  reciprocal_blocks_le : 1 / (blocksPerMacro : ℝ) ≤ β
  edge_le : ((R - 1 : ℕ) : ℝ) / (blockLength : ℝ) ≤ β

/-- Index of a selected block. -/
abbrev SelectedBlock (H Q : ℕ) := Fin H × Fin (Q - 1)

/-- The selected-pair law; its body is irrelevant to this packet. -/
noncomputable def selectedPairLaw {b : ℕ}
    (t : ℕ → Bool) (a L Q H : ℕ)
    (offsets : Fin H → Fin L)
    (labels : SelectedBlock H Q → Fin L → Fin b) :
    (Fin L → Fin b × Bool) → ℝ :=
  fun _ => 0

end Kamae1973
end Agafonov
