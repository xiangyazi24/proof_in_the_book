import Agafonov.Kamae1973.SelectorCounts

namespace Agafonov

open scoped BigOperators

structure LetterDistribution (b : ℕ) where
  prob : Fin b → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_eq_one : ∑ a, prob a = 1

namespace LetterDistribution

variable {b : ℕ}

def wordMass (P : LetterDistribution b) (w : List (Fin b)) : ℝ :=
  (w.map P.prob).prod

@[simp] theorem wordMass_ofFn (P : LetterDistribution b)
    {q : ℕ} (w : Fin q → Fin b) :
    P.wordMass (List.ofFn w) = ∏ r, P.prob (w r) := by
  simp [wordMass, List.map_ofFn, List.prod_ofFn]

end LetterDistribution

namespace Kamae1973

/-- The gap between successive selected positions. -/
def selectorGap (τ : ℕ → ℕ) (j : ℕ) : ℕ :=
  τ (j + 1) - τ j

/-- The span of a finite run of selector gaps. -/
def selectorSpan (τ : ℕ → ℕ) (j m : ℕ) : ℕ :=
  τ (j + m) - τ j

/-- A selector gap capped at `L`. -/
def cappedGap (τ : ℕ → ℕ) (L j : ℕ) : Fin (L + 1) :=
  ⟨min (selectorGap τ j) L, Nat.lt_succ_of_le (min_le_right _ _)⟩

@[simp] theorem cappedGap_val (τ : ℕ → ℕ) (L j : ℕ) :
    (cappedGap τ L j).val = min (selectorGap τ j) L := rfl

axiom selectorSpan_eq_sum_gap (τ : ℕ → ℕ) (hτ : StrictMono τ)
    (j m : ℕ) :
    selectorSpan τ j m = ∑ r ∈ Finset.range m, selectorGap τ (j + r)

/-- Cumulative local selected offset. -/
def localSelectedOffset {q : ℕ}
    (a : Fin q) (γ : Fin q → Fin (q + 1)) (r : Fin q) : ℕ :=
  a.val + ∑ s : Fin r.val, (γ ⟨s.val + 1, by omega⟩).val

/-- Predicate that an offset is one of the cumulative selected offsets. -/
def isLocalSelectedOffset {q : ℕ}
    (a : Fin q) (γ : Fin q → Fin (q + 1)) (ell : Fin q) : Prop :=
  ∃ r : Fin q, localSelectedOffset a γ r = ell.val

axiom localSelectedOffset_strictMono
    {q : ℕ} (a : Fin q) (γ : Fin q → Fin (q + 1))
    (hγ : ∀ r, 0 < (γ r).val) :
    StrictMono (localSelectedOffset a γ)

axiom cappedGap_mem_Icc (τ : ℕ → ℕ) (hτ : StrictMono τ)
    {L : ℕ} (hL : 0 < L) (j : ℕ) :
    (cappedGap τ L j).val ∈ Set.Icc 1 L

axiom cappedGaps_determine_selected_offsets
    (τ : ℕ → ℕ) (hτ : StrictMono τ)
    {q : ℕ} (hq : 0 < q)
    {k : ℕ} (hk : 0 < k) (a ell : Fin q)
    (hstart : a.val ≤ τ k)
    (hfirst : a.val < selectorGap τ (k - 1)) :
    rangeIndicator τ (τ k - a.val + ell.val) = true ↔
      isLocalSelectedOffset a
        (fun r => cappedGap τ q (k - 1 + r.val)) ell

private instance localSelectedOffsetDecidable {q : ℕ}
    (a : Fin q) (γ : Fin q → Fin (q + 1)) (ell : Fin q) :
    Decidable (isLocalSelectedOffset a γ ell) := by
  unfold isLocalSelectedOffset
  infer_instance

noncomputable def localFillWeight {b q : ℕ}
    (P : LetterDistribution b) (w : Fin q → Fin b)
    (a : Fin q) (z : Fin q → Fin b × Fin (q + 1)) : ℝ :=
  let γ : Fin q → Fin (q + 1) := fun r => (z r).2
  (∏ r : Fin q,
      if h : localSelectedOffset a γ r < q then
        if (z r).1 = w ⟨localSelectedOffset a γ r, h⟩ then 1 else 0
      else 1) *
    ∏ ell : Fin q,
      if isLocalSelectedOffset a γ ell then 1 else P.prob (w ell)

noncomputable def localCorrection {b q : ℕ}
    (P : LetterDistribution b) (hq : 0 < q)
    (w : Fin q → Fin b) (a : Fin q)
    (z : Fin q → Fin b × Fin (q + 1)) : ℝ :=
  if a.val < ((z ⟨0, hq⟩).2).val then
    localFillWeight P w a z - P.wordMass (List.ofFn w)
  else 0

end Kamae1973
end Agafonov
