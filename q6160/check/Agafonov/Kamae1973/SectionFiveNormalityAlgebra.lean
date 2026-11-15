import Agafonov.Kamae1973.Statements

/-!
# Normality algebra under selector composition

These lemmas isolate the set-theoretic lifting half of Condition 3 and the
composition and cancellation rules for preservation of weighted normality.
They are the normality-algebra steps used in Kamae (1973), Theorem 5.
-/

namespace Agafonov.Kamae1973

/-- Condition 3 supplies a normal preimage for every normal sequence.
This is the lifting direction of Kamae (1973), condition (4.9). -/
theorem ConditionThree.exists_normal_preimage
    {b : ℕ} {P : LetterDistribution b} {σ : ℕ → ℕ}
    (hσ : ConditionThree P σ) {y : ℕ → Fin b}
    (hy : IsWeightedNormal P y) :
    ∃ x : ℕ → Fin b,
      IsWeightedNormal P x ∧ y = fun n => x (σ n) := by
  unfold ConditionThree at hσ
  change y ∈ {z : ℕ → Fin b |
    ∃ x : ℕ → Fin b,
      IsWeightedNormal P x ∧ z = fun n => x (σ n)}
  rw [hσ]
  exact hy

/-- Preservation of weighted normality is closed under selector composition.
This is the composition step in the proof of Kamae (1973), Theorem 5. -/
theorem conditionTwo_comp
    {b : ℕ} {P : LetterDistribution b} {σ τ : ℕ → ℕ}
    (hσ : ConditionTwo P σ) (hτ : ConditionTwo P τ) :
    ConditionTwo P (σ ∘ τ) := by
  unfold ConditionTwo at hσ hτ ⊢
  intro x hx
  change IsWeightedNormal P (fun n => x (σ (τ n)))
  exact hτ (fun n => x (σ n)) (hσ x hx)

/-- A Condition 3 lift through the outer selector cancels that selector from
composite preservation. This is the reverse-direction algebra in Kamae
(1973), Theorem 5. -/
theorem conditionTwo_cancel_left
    {b : ℕ} {P : LetterDistribution b} {σ τ : ℕ → ℕ}
    (hσ : ConditionThree P σ)
    (hcomp : ConditionTwo P (σ ∘ τ)) :
    ConditionTwo P τ := by
  unfold ConditionTwo at hcomp ⊢
  intro y hy
  rcases ConditionThree.exists_normal_preimage hσ hy with
    ⟨x, hx, hxy⟩
  rw [hxy]
  change IsWeightedNormal P (fun n => x (σ (τ n)))
  exact hcomp x hx

end Agafonov.Kamae1973

#print axioms Agafonov.Kamae1973.ConditionThree.exists_normal_preimage
#print axioms Agafonov.Kamae1973.conditionTwo_comp
#print axioms Agafonov.Kamae1973.conditionTwo_cancel_left
