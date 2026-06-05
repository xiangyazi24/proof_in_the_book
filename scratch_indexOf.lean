import Mathlib

open List

lemma findIdx_append_of_mem {α} [BEq α] (l₁ l₂ : List α) (x : α) (h : x ∈ l₁) :
    (l₁ ++ l₂).findIdx (· == x) = l₁.findIdx (· == x) := by
  induction l₁ with
  | nil => contradiction
  | cons a as ih =>
    simp only [findIdx_cons, append_eq]
    cases h_eq : (a == x)
    · simp only [h_eq, cond_false, add_left_cancel_iff]
      apply ih
      simp only [mem_cons] at h
      cases h
      · exfalso; revert h_eq; -- needs LawfulBEq to contradict a = x and a != x
        sorry
      · assumption
    · simp only [h_eq, cond_true]
