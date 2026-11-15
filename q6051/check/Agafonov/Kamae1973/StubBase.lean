import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

namespace Agafonov

open Filter Topology
open scoped BigOperators

structure LetterDistribution (b : ℕ) where
  prob : Fin b → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_eq_one : ∑ a, prob a = 1

namespace LetterDistribution

noncomputable def wordMass {b : ℕ} (P : LetterDistribution b)
    (_w : List (Fin b)) : ℝ := 0

axiom positiveLetter {b : ℕ} (P : LetterDistribution b) : Fin b

end LetterDistribution

structure BlockFamily (C : Type*) [Fintype C] where
  law : (n : ℕ) → (Fin n → C) → ℝ

noncomputable def BlockFamily.entropyRate {C : Type*} [Fintype C]
    (_μ : BlockFamily C) : ℝ := 0

noncomputable def BlockFamily.fst {A B : Type*}
    [Fintype A] [Fintype B] (ν : BlockFamily (A × B)) :
    (n : ℕ) → (Fin n → A) → ℝ :=
  fun n u => ∑ v : Fin n → B, ν.law n (fun i => (u i, v i))

noncomputable def BlockFamily.snd {A B : Type*}
    [Fintype A] [Fintype B] (ν : BlockFamily (A × B)) :
    (n : ℕ) → (Fin n → B) → ℝ :=
  fun n v => ∑ u : Fin n → A, ν.law n (fun i => (u i, v i))

noncomputable def empiricalLaw {C : Type*} [DecidableEq C]
    (_x : ℕ → C) (_N n : ℕ) (_w : Fin n → C) : ℝ := 0

def IsLimitProfile {C : Type*} [Fintype C] [DecidableEq C]
    (_x : ℕ → C) (_S : Set ℕ) (_μ : BlockFamily C) : Prop := True

def IsWeightedNormal {b : ℕ}
    (_P : LetterDistribution b) (_x : ℕ → Fin b) : Prop := True

namespace Kamae1973

noncomputable def finiteLOne {D : Type*} [Fintype D]
    (_p _q : D → ℝ) : ℝ := 0

noncomputable def intervalEmpiricalLaw {C : Type*} [DecidableEq C]
    (_x : ℕ → C) (_a T n : ℕ) (_w : Fin n → C) : ℝ := 0

def intervalWordCount {C : Type*} [DecidableEq C]
    (_x : ℕ → C) (_a T : ℕ) (_w : List C) : ℕ := 0

structure PaintingParameters {b : ℕ}
    (_P : LetterDistribution b) (_R : ℕ) (_β : ℝ) where
  blockLength : ℕ
  macroLength : ℕ
  minMacroblocks : ℕ


def ExtendsInterval {A : Type*} (_a : ℕ) {T : ℕ}
    (_u : Fin T → A) (_x : ℕ → A) : Prop := True

end Kamae1973
end Agafonov
