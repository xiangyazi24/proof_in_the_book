import Mathlib

open Polynomial Chebyshev

def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | (q + 2) => 2 * a (q + 1) - 9 * a q

lemma a_zmod_3 (q : ℕ) : (a q : ZMod 3) = 1 ∨ (a q : ZMod 3) = 2 := by
  induction' q using Nat.strong_induction_on with q ih
  rcases q with _ | q
  · left; rfl
  rcases q with _ | q
  · left; rfl
  · have h1 := ih (q + 1) (by omega)
    have eq : (a (q + 2) : ZMod 3) = 2 * (a (q + 1) : ZMod 3) := by
      have h_a : a (q + 2) = 2 * a (q + 1) - 9 * a q := rfl
      rw [h_a]
      push_cast
      have : (9 : ZMod 3) = 0 := rfl
      rw [this, zero_mul, sub_zero]
    rcases h1 with h | h
    · right; rw [eq, h]; rfl
    · left; rw [eq, h]; rfl

lemma a_eq_T (q : ℕ) :
    (a q : ℝ) = (3 : ℝ)^q * (T ℝ (q : ℤ)).eval (1/3) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    match q with
    | 0 =>
      simp [a, T_zero, eval_one]
    | 1 =>
      simp [a, T_one, eval_X]
    | q + 2 =>
      have ih_q  : (a q : ℝ) = (3 : ℝ)^q * (T ℝ (q : ℤ)).eval (1/3) := ih q (by omega)
      have ih_q1 : (a (q+1) : ℝ) = (3 : ℝ)^(q+1) * (T ℝ ((q+1 : ℕ) : ℤ)).eval (1/3) :=
        ih (q+1) (by omega)
      have hcast : ((q + 2 : ℕ) : ℤ) = (q : ℤ) + 2 := by push_cast; rfl
      have hT :
          (T ℝ ((q + 2 : ℕ) : ℤ)).eval (1/3 : ℝ) =
            2 * (1/3) * (T ℝ ((q : ℤ) + 1)).eval (1/3) -
              (T ℝ ((q : ℕ) : ℤ)).eval (1/3) := by
        rw [hcast, T_add_two]
        simp [eval_sub, eval_mul, eval_X]
      have ha_rec : (a (q + 2) : ℝ) = 2 * (a (q + 1) : ℝ) - 9 * (a q : ℝ) := by
        have : a (q + 2) = 2 * a (q + 1) - 9 * a q := rfl
        rw [this]
        push_cast
        rfl
      have hcast_norm : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; rfl
      rw [hcast_norm] at ih_q1
      rw [ha_rec, hT, ih_q, ih_q1]
      have h3 : (3 : ℝ)^(q+2) = (3 : ℝ)^q * 9 := by rw [pow_add]; norm_num
      have h31 : (3 : ℝ)^(q+1) = (3 : ℝ)^q * 3 := by rw [pow_add]; norm_num
      rw [h3, h31]
      ring

theorem arccos_one_third_irrational_over_pi (q : ℚ) :
    Real.arccos (1/3) ≠ q * Real.pi := by
  intro h
  rcases eq_or_ne q 0 with hq | hq
  · rw [hq] at h
    simp at h
    revert h
    norm_num
  have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have h_int : (q.den : ℝ) * Real.arccos (1/3) = (q.num : ℝ) * Real.pi := by
    have hq_eq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by rw [Rat.cast_def]
    rw [h, hq_eq]
    field_simp <;> ring
  have h_cos_lhs :
      Real.cos ((q.den : ℝ) * Real.arccos (1/3)) =
        (T ℝ (q.den : ℤ)).eval (1/3) := by
    have hcos_arccos : Real.cos (Real.arccos (1/3)) = 1/3 := by
      rw [Real.cos_arccos] <;> norm_num
    have h_symm := (T_real_cos (Real.arccos (1/3)) (q.den : ℤ)).symm
    have h_cast : ((q.den : ℤ) : ℝ) = (q.den : ℝ) := by push_cast; rfl
    rw [h_cast] at h_symm
    rw [hcos_arccos] at h_symm
    exact h_symm
  
  have h_cos_eq : Real.cos ((q.den : ℝ) * Real.arccos (1/3)) =
                  Real.cos ((q.num : ℝ) * Real.pi) := by rw [h_int]
  
  have h_sin : Real.sin ((q.num : ℝ) * Real.pi) = 0 := by
    have : (q.num : ℝ) * Real.pi = (q.num : ℤ) * Real.pi := by push_cast; rfl
    rw [this, Real.sin_int_mul_pi]
  have h_cos_sq : Real.cos ((q.num : ℝ) * Real.pi) ^ 2 = 1 := by
    have := Real.cos_sq_add_sin_sq ((q.num : ℝ) * Real.pi)
    rw [h_sin] at this
    linarith
  have h4 : Real.cos ((q.num : ℝ) * Real.pi) = 1 ∨ Real.cos ((q.num : ℝ) * Real.pi) = -1 := sq_eq_one_iff.mp h_cos_sq

  have h_T_eval : (T ℝ (q.den : ℤ)).eval (1/3) = 1 ∨ (T ℝ (q.den : ℤ)).eval (1/3) = -1 := by
    rcases h4 with h4 | h4
    · left; rw [← h_cos_lhs, h_cos_eq, h4]
    · right; rw [← h_cos_lhs, h_cos_eq, h4]

  have h_a_eq : (a q.den : ℝ) = (3 : ℝ)^q.den ∨ (a q.den : ℝ) = -(3 : ℝ)^q.den := by
    have eq := a_eq_T q.den
    rcases h_T_eval with ht | ht
    · left; rw [eq, ht, mul_one]
    · right; rw [eq, ht]; ring
  
  have h_a_eq_int : (a q.den : ℤ) = (3 : ℤ)^q.den ∨ (a q.den : ℤ) = -(3 : ℤ)^q.den := by
    rcases h_a_eq with ha | ha
    · left; exact_mod_cast ha
    · right; exact_mod_cast ha

  have h_den_pos : 1 ≤ q.den := q.pos
  have h_a_zmod : (a q.den : ZMod 3) = 0 := by
    have h_pow : (3 : ZMod 3)^q.den = 0 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt h_den_pos)
      rw [hk]
      have h3 : (3 : ZMod 3) = 0 := rfl
      rw [h3]
      exact zero_pow (by omega)
    rcases h_a_eq_int with ha | ha
    · have : ((a q.den : ℤ) : ZMod 3) = (3 : ZMod 3)^q.den := by
        rw [ha]
        exact Int.cast_pow 3 q.den
      rw [this, h_pow]
    · have : ((a q.den : ℤ) : ZMod 3) = -(3 : ZMod 3)^q.den := by
        rw [ha]
        have h_pow_cast : (((3 : ℤ)^q.den : ℤ) : ZMod 3) = (3 : ZMod 3)^q.den := Int.cast_pow 3 q.den
        rw [Int.cast_neg, h_pow_cast]
      rw [this, h_pow, neg_zero]
      
  rcases a_zmod_3 q.den with h1 | h2
  · rw [h_a_zmod] at h1; revert h1; decide
  · rw [h_a_zmod] at h2; revert h2; decide
