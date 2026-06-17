import ProofsInTheBook.ZinanFFCT10

/-!
# `ZinanFFCT12` — bridge lemmas toward `PlanarWeakNoflatStrictEdgeCore`

Stage 1 of the assembly (see `HANDOFF/ffct12-assembly-spec.md`): the abstract `E3` bridges that
the forward/backward instantiations of `ZinanFFCT9.forward_strict_support` consume.

* row-permutation identities for `det3` (cyclic / swap / repeated-argument / negated normal);
* the **antiparallel decomposition**: `theta b ρ = π` (equivalently `ncos = -1`) forces
  `ρ = -(t • b)` with `t > 0` — the algebraic form of the antipodal care-point;
* **collinearity from a vanishing area form**: `det3 h b u = 0` with `b, u ⊥ h` forces `u ∈ span b`
  (via the Pythagorean identity `det3h_sq` = equality in Cauchy–Schwarz).

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT8 ProofsInTheBook.ZinanFFCT9 ProofsInTheBook.ZinanFFCT10

namespace ProofsInTheBook.ZinanFFCT12

set_option maxHeartbeats 1600000

/-! ## §1. `det3` row algebra. -/

theorem det3_cyclic (a b c : E3) : det3 a b c = det3 b c a := by
  simp only [det3]; ring

theorem det3_swap12 (a b c : E3) : det3 a b c = -det3 b a c := by
  simp only [det3]; ring

theorem det3_right_eq_first (p q : E3) : det3 p q p = 0 := by
  simp only [det3]; ring

theorem det3_neg_left (h u v : E3) : det3 (-h) u v = -det3 h u v := by
  simp only [det3, PiLp.neg_apply]; ring

/-- Linearity of `det3` in the third argument over an explicit affine combination:
if the third argument is `(1 + s) • p - s • q` then the value is `-s` times the value at `q`. -/
theorem det3_affine_comb (p r q : E3) (s : ℝ) :
    det3 p r ((1 + s) • p - s • q) = -s * det3 p r q := by
  have h1 : (1 + s) • p - s • q = (1 + s) • p + (-s) • q := by module
  rw [h1, det3_add_right, det3_smul_right, det3_smul_right, det3_right_eq_first]
  ring

/-! ## §2. The antiparallel decomposition and collinearity from a vanishing area form. -/

/-- `ncos b ρ = -1` forces antiparallelism: `ρ = -(t • b)` with `t = ‖ρ‖/‖b‖ > 0`. -/
theorem antiparallel_of_ncos_neg_one {b ρ : E3} (hb : b ≠ 0) (hρ : ρ ≠ 0)
    (hc : ncos b ρ = -1) : ∃ t : ℝ, 0 < t ∧ ρ = -(t • b) := by
  have hbn : (0:ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hρn : (0:ℝ) < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hd : (0:ℝ) < ‖b‖ * ‖ρ‖ := by positivity
  have hinner : (⟪b, ρ⟫ : ℝ) = -(‖b‖ * ‖ρ‖) := by
    rw [ncos, div_eq_iff (ne_of_gt hd)] at hc
    linarith [hc]
  have hneg : (⟪b, -ρ⟫ : ℝ) = ‖b‖ * ‖-ρ‖ := by
    rw [inner_neg_right, hinner, norm_neg]; ring
  have hpar := inner_eq_norm_mul_iff_real.mp hneg
  -- hpar : ‖-ρ‖ • b = ‖b‖ • -ρ
  rw [norm_neg] at hpar
  have h2 : ‖ρ‖ • b = -(‖b‖ • ρ) := by rw [hpar, smul_neg]
  have hb0' : (‖b‖ : ℝ) ≠ 0 := ne_of_gt hbn
  refine ⟨‖ρ‖ / ‖b‖, by positivity, ?_⟩
  have h3 := congrArg (fun v : E3 => (‖b‖)⁻¹ • v) h2
  simp only [smul_smul, smul_neg] at h3
  rw [inv_mul_cancel₀ hb0', one_smul] at h3
  -- h3 : (‖b‖⁻¹ * ‖ρ‖) • b = -ρ
  rw [div_eq_inv_mul, h3, neg_neg]

/-- `theta b ρ = π` forces antiparallelism. -/
theorem antiparallel_of_theta_pi {b ρ : E3} (hb : b ≠ 0) (hρ : ρ ≠ 0)
    (hθ : theta b ρ = Real.pi) : ∃ t : ℝ, 0 < t ∧ ρ = -(t • b) := by
  apply antiparallel_of_ncos_neg_one hb hρ
  have hmem := ncos_mem hb hρ
  have hle : ncos b ρ ≤ -1 := by
    by_contra hgt
    push_neg at hgt
    have harc := Real.arccos_lt_pi.mpr hgt
    rw [theta] at hθ
    rw [hθ] at harc
    exact lt_irrefl _ harc
  linarith [hmem.1]

/-- **Collinearity from a vanishing oriented area.**  For `b, u ⊥ h`, `h ≠ 0`, `b ≠ 0`:
`det3 h b u = 0` forces `u = c • b` for some `c : ℝ`. -/
theorem collinear_of_det3_zero {h b u : E3} (hb0 : (⟪h,b⟫:ℝ) = 0) (hu0 : (⟪h,u⟫:ℝ) = 0)
    (hh : h ≠ 0) (hb : b ≠ 0) (hzero : det3 h b u = 0) : ∃ c : ℝ, u = c • b := by
  rcases eq_or_ne u 0 with hu | hu
  · exact ⟨0, by rw [hu, zero_smul]⟩
  have hbn : (0:ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hun : (0:ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hsq := det3h_sq (h := h) (u := b) (v := u) hb0 hu0
  rw [hzero] at hsq
  -- 0 = ‖h‖²(‖b‖²‖u‖² − ⟪b,u⟫²)
  have hsq' : ‖h‖^2 * (‖b‖^2 * ‖u‖^2 - (⟪b,u⟫:ℝ)^2) = 0 := by
    have h0 := hsq.symm
    simpa using h0
  have hD : ‖b‖^2 * ‖u‖^2 - (⟪b,u⟫:ℝ)^2 = 0 := by
    rcases mul_eq_zero.mp hsq' with h1 | h1
    · exact absurd h1 (by positivity)
    · exact h1
  have h2 : ((⟪b,u⟫:ℝ) - ‖b‖ * ‖u‖) * ((⟪b,u⟫:ℝ) + ‖b‖ * ‖u‖) = 0 := by
    linear_combination -hD
  rcases mul_eq_zero.mp h2 with h3 | h3
  · -- parallel: ⟪b,u⟫ = ‖b‖‖u‖
    have hpos : (⟪b, u⟫ : ℝ) = ‖b‖ * ‖u‖ := by linarith
    have hpar := inner_eq_norm_mul_iff_real.mp hpos
    -- hpar : ‖u‖ • b = ‖b‖ • u
    have h4 := congrArg (fun v : E3 => (‖b‖)⁻¹ • v) hpar
    simp only [smul_smul] at h4
    rw [inv_mul_cancel₀ (ne_of_gt hbn), one_smul] at h4
    exact ⟨‖b‖⁻¹ * ‖u‖, h4.symm⟩
  · -- antiparallel: ncos = -1 route
    have hneg : (⟪b, u⟫ : ℝ) = -(‖b‖ * ‖u‖) := by linarith
    have hd : (‖b‖ * ‖u‖ : ℝ) ≠ 0 := by positivity
    have hc : ncos b u = -1 := by
      rw [ncos, hneg, neg_div, div_self hd]
    obtain ⟨t, _, hu'⟩ := antiparallel_of_ncos_neg_one hb hu hc
    exact ⟨-t, by rw [hu', neg_smul]⟩

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanFFCT12.antiparallel_of_theta_pi
#print axioms ProofsInTheBook.ZinanFFCT12.collinear_of_det3_zero
#print axioms ProofsInTheBook.ZinanFFCT12.det3_affine_comb

end ProofsInTheBook.ZinanFFCT12
