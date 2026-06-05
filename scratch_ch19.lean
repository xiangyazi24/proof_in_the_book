import Mathlib.Topology.Algebra.Polynomial
import Mathlib

open Polynomial Bornology

noncomputable section

lemma poly_norm_tendsto_top (p : ℂ[X]) (hdeg : 1 ≤ p.natDegree) :
    Filter.Tendsto (fun z => ‖p.eval z‖) (cobounded ℂ) Filter.atTop := by
  have hp0 : 0 < p.degree := by
    rwa [natDegree_pos_iff_degree_pos.symm]
  exact p.tendsto_norm_atTop hp0 tendsto_norm_cobounded_atTop

lemma exists_min_norm (p : ℂ[X]) :
    ∃ z₀ : ℂ, ∀ z : ℂ, ‖p.eval z₀‖ ≤ ‖p.eval z‖ :=
  Polynomial.exists_forall_norm_le p

theorem exists_complex_nth_root (z : ℂ) (m : ℕ) (hm : 0 < m) :
    ∃ ζ : ℂ, ζ ^ m = z :=
  ⟨z ^ ((m : ℂ)⁻¹), by simpa using Complex.cpow_nat_inv_pow z hm.ne'⟩

lemma poly_decompose (r : ℂ[X]) (a c : ℂ) (m : ℕ) (hm0 : 0 < m)
    (hconst : r.coeff 0 = a)
    (hbelow : ∀ k, 0 < k → k < m → r.coeff k = 0)
    (hm : r.coeff m = c) :
    ∃ q : ℂ[X], r = C a + C c * X^m + X^(m+1) * q := by
  have hdvd : X^(m+1) ∣ (r - (C a + C c * X^m)) := by
    rw [X_pow_dvd_iff]
    intro i hi
    have hi_le : i ≤ m := by omega
    rcases lt_trichotomy i m with h | h | h
    · rcases eq_or_ne i 0 with hi0 | hi0
      · rw [hi0]
        simp only [coeff_sub, coeff_add]
        have h1 : (C a).coeff 0 = a := by simp
        have h2 : (C c * X^m).coeff 0 = 0 := by
          rw [coeff_C_mul, coeff_X_pow]
          have : 0 ≠ m := by omega
          simp [this]
        rw [h1, h2, hconst]
        ring
      · simp only [coeff_sub, coeff_add]
        have h1 : (C a).coeff i = 0 := by
          rw [coeff_C]; split_ifs with h_eq
          · exfalso; exact hi0 h_eq
          · rfl
        have h2 : (C c * X^m).coeff i = 0 := by
          rw [coeff_C_mul, coeff_X_pow]
          have : i ≠ m := by omega
          simp [this]
        have hr : r.coeff i = 0 := hbelow i (by omega) h
        rw [hr, h1, h2]
        ring
    · rw [h]
      simp only [coeff_sub, coeff_add]
      have h1 : (C a).coeff m = 0 := by
        rw [coeff_C]; split_ifs with h_eq
        · exfalso; exact ne_of_gt hm0 h_eq
        · rfl
      have h2 : (C c * X^m).coeff m = c := by
        rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
      rw [h1, h2, hm]
      ring
    · omega
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q, ?_⟩
  calc r = (r - (C a + C c * X^m)) + (C a + C c * X^m) := by ring
       _ = X^(m+1) * q + (C a + C c * X^m) := by rw [hq]
       _ = C a + C c * X^m + X^(m+1) * q := by ring

theorem complex_poly_local_norm_decrease
    (r : ℂ[X]) (a c : ℂ) (m : ℕ)
    (hm0 : 0 < m)
    (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hconst : r.coeff 0 = a)
    (hbelow : ∀ k, 0 < k → k < m → r.coeff k = 0)
    (hm : r.coeff m = c) :
    ∃ w : ℂ, ‖r.eval w‖ < ‖a‖ := by
  obtain ⟨ζ, hζ⟩ := exists_complex_nth_root (-a / c) m hm0
  have hcζ : c * ζ ^ m = -a := by
    rw [hζ]; field_simp
  
  obtain ⟨q, hq⟩ := poly_decompose r a c m hm0 hconst hbelow hm
  
  have h_cont : Continuous (fun (t : ℝ) => ‖(ζ^(m+1)) * q.eval ((t:ℂ) * ζ)‖) := by
    fun_prop
  
  have h_compact : IsCompact (Set.Icc (0:ℝ) 1) := isCompact_Icc
  have h_nonempty : (Set.Icc (0:ℝ) 1).Nonempty := Set.nonempty_Icc.mpr zero_le_one
  obtain ⟨t_max, _, h_max⟩ := IsCompact.exists_isMaxOn h_compact h_nonempty h_cont.continuousOn
  
  set M : ℝ := ‖(ζ^(m+1)) * q.eval ((t_max:ℂ) * ζ)‖ with hM_def
  have hM_nonneg : 0 ≤ M := norm_nonneg _
  
  set t : ℝ := min (1/2) (‖a‖ / (2 * (M + 1))) with ht_def
  have ht_pos : 0 < t := by
    apply lt_min; · norm_num
    · apply div_pos (norm_pos_iff.mpr ha)
      positivity
  have ht_le_half : t ≤ 1/2 := min_le_left _ _
  have ht_le_one : t ≤ 1 := le_trans ht_le_half (by norm_num)
  have ht_le_bound : t ≤ ‖a‖ / (2 * (M + 1)) := min_le_right _ _

  refine ⟨(t : ℂ) * ζ, ?_⟩
  
  have h_eval : r.eval ((t : ℂ) * ζ) = a * (1 - (t : ℂ)^m) + (t : ℂ)^(m+1) * ((ζ^(m+1)) * q.eval ((t : ℂ) * ζ)) := by
    rw [hq]
    simp only [eval_add, eval_C, eval_mul, eval_X_pow]
    rw [mul_pow, mul_pow]
    have h_c_zeta : c * ((t : ℂ)^m * ζ^m) = (t : ℂ)^m * (c * ζ^m) := by ring
    rw [h_c_zeta, hcζ]
    ring
  
  rw [h_eval]
  
  have ht_m_real : (t : ℂ)^m = ((t^m : ℝ) : ℂ) := by push_cast; rfl
  have ht_m1_real : (t : ℂ)^(m+1) = ((t^(m+1) : ℝ) : ℂ) := by push_cast; rfl
  
  have h_triangle := norm_add_le (a * (1 - (t : ℂ)^m)) ((t : ℂ)^(m+1) * ((ζ^(m+1)) * q.eval ((t : ℂ) * ζ)))
  
  have h_term1 : ‖a * (1 - (t : ℂ)^m)‖ = ‖a‖ * (1 - t^m) := by
    rw [norm_mul]
    have : 1 - (t : ℂ)^m = ((1 - t^m : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    have ht_m_le_one : t^m ≤ 1 := pow_le_one₀ ht_pos.le ht_le_one
    rw [abs_of_nonneg (by linarith)]
  
  have h_term2 : ‖(t : ℂ)^(m+1) * ((ζ^(m+1)) * q.eval ((t : ℂ) * ζ))‖ = t^(m+1) * ‖(ζ^(m+1)) * q.eval ((t : ℂ) * ζ)‖ := by
    rw [norm_mul, ht_m1_real, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    
  have h_M_bound : ‖(ζ^(m+1)) * q.eval ((t : ℂ) * ζ)‖ ≤ M := by
    have ht_Icc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht_pos.le, ht_le_one⟩
    exact h_max ht_Icc
    
  have h_term2_le : t^(m+1) * ‖(ζ^(m+1)) * q.eval ((t : ℂ) * ζ)‖ ≤ t^(m+1) * M := by
    gcongr
    
  calc ‖a * (1 - (t : ℂ)^m) + (t : ℂ)^(m+1) * ((ζ^(m+1)) * q.eval ((t : ℂ) * ζ))‖
    _ ≤ ‖a * (1 - (t : ℂ)^m)‖ + ‖(t : ℂ)^(m+1) * ((ζ^(m+1)) * q.eval ((t : ℂ) * ζ))‖ := h_triangle
    _ = ‖a‖ * (1 - t^m) + t^(m+1) * ‖(ζ^(m+1)) * q.eval ((t : ℂ) * ζ)‖ := by rw [h_term1, h_term2]
    _ ≤ ‖a‖ * (1 - t^m) + t^(m+1) * M := by linarith [h_term2_le]
    _ = ‖a‖ - t^m * (‖a‖ - M * t) := by ring
    _ < ‖a‖ := by
        have ht_m_pos : 0 < t^m := pow_pos ht_pos m
        have h_M_t : M * t ≤ ‖a‖ / 2 := by
          have h2 : (M * ‖a‖) / (2 * (M + 1)) ≤ ‖a‖ / 2 := by
            have hm1 : 0 < 2 * (M + 1) := by positivity
            have h2pos : (0 : ℝ) < 2 := by positivity
            rw [div_le_div_iff₀ hm1 h2pos]
            calc (M * ‖a‖) * 2
              _ ≤ (M * ‖a‖) * 2 + ‖a‖ * 2 := by
                  have ha_pos : 0 ≤ ‖a‖ * 2 := by positivity
                  exact le_add_of_nonneg_right ha_pos
              _ = ‖a‖ * (2 * (M + 1)) := by ring
          calc M * t
              ≤ M * (‖a‖ / (2 * (M + 1))) := mul_le_mul_of_nonneg_left ht_le_bound hM_nonneg
            _ = (M * ‖a‖) / (2 * (M + 1)) := mul_div_assoc' M ‖a‖ _
            _ ≤ ‖a‖ / 2 := h2
        have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
        have h_diff : 0 < ‖a‖ - M * t := by linarith
        have h_prod : 0 < t^m * (‖a‖ - M * t) := mul_pos ht_m_pos h_diff
        exact sub_lt_self ‖a‖ h_prod

