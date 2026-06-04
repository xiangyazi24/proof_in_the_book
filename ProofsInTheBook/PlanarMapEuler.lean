import ProofsInTheBook.PlanarMap

/-!
# Euler consequences for plane maps (toward the Five Color Theorem)

On top of `PlanarMap` (combinatorial maps + `IsSphereMap`), the standard consequences of
Euler's formula for simple plane maps: `3F ≤ 2E` when every face has length `≥ 3`, the edge
bound `E ≤ 3V - 6`, and the existence of a vertex of degree `≤ 5` (the seed of the 5-color
induction).
-/

namespace ProofsInTheBook.PlanarMap.CombMap

open ProofsInTheBook.PlanarMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- Degree of a vertex = number of darts in its `σ`-orbit. -/
def vertexDegree (M : CombMap D) (Q : Quotient (cycleSetoid M.σ)) : ℕ :=
  (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.σ) x = Q)).card

/-- Length of a face = number of darts in its `φ`-orbit. -/
def faceLen (M : CombMap D) (Q : Quotient (cycleSetoid M.φ)) : ℕ :=
  (Finset.univ.filter (fun x => Quotient.mk (cycleSetoid M.φ) x = Q)).card

/-- Every face has length at least `k` (a simple plane map satisfies this with `k = 3`). -/
def FaceLengthGe (M : CombMap D) (k : ℕ) : Prop :=
  ∀ Q : Quotient (cycleSetoid M.φ), k ≤ M.faceLen Q

/-- The vertex degrees sum to `2E`. -/
lemma sum_vertexDegree (M : CombMap D) :
    ∑ Q : Quotient (cycleSetoid M.σ), M.vertexDegree Q = 2 * M.E := by
  rw [two_mul_E_eq_card]; exact sum_class_card M.σ

/-- The face lengths sum to `2E`. -/
lemma sum_faceLen (M : CombMap D) :
    ∑ Q : Quotient (cycleSetoid M.φ), M.faceLen Q = 2 * M.E := by
  rw [two_mul_E_eq_card]; exact sum_class_card M.φ

/-- If every face has length `≥ 3`, then `3F ≤ 2E`. -/
lemma three_F_le_two_E (M : CombMap D) (h : M.FaceLengthGe 3) :
    3 * M.F ≤ 2 * M.E := by
  have hge : 3 * M.F ≤ ∑ Q : Quotient (cycleSetoid M.φ), M.faceLen Q := by
    have : (∑ _Q : Quotient (cycleSetoid M.φ), 3) ≤
        ∑ Q : Quotient (cycleSetoid M.φ), M.faceLen Q :=
      Finset.sum_le_sum (fun Q _ => h Q)
    simpa [Finset.sum_const, Finset.card_univ, F, Nat.mul_comm] using this
  rw [sum_faceLen] at hge
  exact hge

/-- **Edge bound** `E ≤ 3V - 6` for a simple sphere map with `V ≥ 3`. -/
lemma edge_bound (M : CombMap D) (hsphere : M.IsSphereMap) (h3 : M.FaceLengthGe 3)
    (hV : 3 ≤ M.V) : M.E ≤ 3 * M.V - 6 := by
  have heuler : (M.V : ℤ) - (M.E : ℤ) + (M.F : ℤ) = 2 := hsphere.2
  have hF : 3 * (M.F : ℤ) ≤ 2 * (M.E : ℤ) := by exact_mod_cast three_F_le_two_E M h3
  have hVz : (3 : ℤ) ≤ (M.V : ℤ) := by exact_mod_cast hV
  have : (M.E : ℤ) ≤ 3 * (M.V : ℤ) - 6 := by linarith
  omega

/-- **A vertex of degree ≤ 5 exists** in a simple sphere map with `V ≥ 3`. The seed of the
inductive five-coloring argument. -/
lemma exists_vertexDegree_le_five (M : CombMap D) (hsphere : M.IsSphereMap)
    (h3 : M.FaceLengthGe 3) (hV : 3 ≤ M.V) :
    ∃ Q : Quotient (cycleSetoid M.σ), M.vertexDegree Q ≤ 5 := by
  by_contra hcon
  push_neg at hcon
  -- every vertex degree ≥ 6, so ∑ deg ≥ 6V; but ∑ deg = 2E ≤ 6V - 12
  have hge : 6 * M.V ≤ ∑ Q : Quotient (cycleSetoid M.σ), M.vertexDegree Q := by
    have : (∑ _Q : Quotient (cycleSetoid M.σ), 6) ≤
        ∑ Q : Quotient (cycleSetoid M.σ), M.vertexDegree Q :=
      Finset.sum_le_sum (fun Q _ => hcon Q)
    simpa [Finset.sum_const, Finset.card_univ, V, Nat.mul_comm] using this
  rw [sum_vertexDegree] at hge
  have hEb : M.E ≤ 3 * M.V - 6 := edge_bound M hsphere h3 hV
  omega

end ProofsInTheBook.PlanarMap.CombMap
