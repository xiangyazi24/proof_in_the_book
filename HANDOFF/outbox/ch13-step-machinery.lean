import Mathlib
open Complex Real
set_option maxHeartbeats 1600000
noncomputable def edge (θ ρ : ℕ → ℝ) (i : ℕ) : ℂ := (ρ i : ℂ) * Complex.exp ((θ i : ℂ) * I)
noncomputable def chord (θ ρ : ℕ → ℝ) (n j : ℕ) : ℂ := ∑ i ∈ Finset.Ico j n, edge θ ρ i
noncomputable def wrot (θ ρ : ℕ → ℝ) (n j : ℕ) : ℂ := Complex.exp (-(θ j : ℂ) * I) * chord θ ρ n j
noncomputable def aang (θ ρ : ℕ → ℝ) (n j : ℕ) : ℝ := Complex.arg (wrot θ ρ n j)
-- (stub-import the proved lemmas)
axiom cone_arg (ρ r φ : ℝ) (h0 : 0 < φ) (hπ : φ ≤ π) (hρ : 0 ≤ ρ) (hr : 0 ≤ r) :
    0 ≤ Complex.arg (↑ρ + ↑r * Complex.exp (↑φ * I)) ∧
    Complex.arg (↑ρ + ↑r * Complex.exp (↑φ * I)) ≤ φ
axiom im_rot_chord (θ ρ : ℕ → ℝ) (n j a : ℕ) :
    (Complex.exp (-(θ a : ℂ) * I) * chord θ ρ n j).im = ∑ i ∈ Finset.Ico j n, ρ i * Real.sin (θ i - θ a)
axiom im_end_chord (θ ρ : ℕ → ℝ) (n j : ℕ) :
    (Complex.exp (-(θ (n-1) : ℂ) * I) * chord θ ρ n j).im
      = - (‖chord θ ρ n j‖ * Real.sin ((θ (n-1) - θ j) - aang θ ρ n j))
axiom wrot_succ (θ ρ : ℕ → ℝ) (n j : ℕ) (h : j < n) :
    wrot θ ρ n j = (ρ j : ℂ) + (‖chord θ ρ n (j+1)‖ : ℂ) *
          Complex.exp (((θ (j+1) - θ j + aang θ ρ n (j+1) : ℝ) : ℂ) * I)

theorem sin_helper (x : ℝ) (h0 : 0 ≤ x) (h2 : x ≤ 2*π) (hs : 0 ≤ Real.sin x) : x ≤ π ∨ x = 2*π := by
  by_contra hcon; push_neg at hcon
  obtain ⟨h1, h2'⟩ := hcon
  have hlt : x < 2*π := lt_of_le_of_ne h2 h2'
  have : Real.sin x < 0 := by
    have hp1 : 0 < x - π := by linarith
    have hp2 : x - π < π := by linarith
    have := Real.sin_pos_of_pos_of_lt_pi hp1 hp2
    rw [show x = (x-π)+π by ring, Real.sin_add_pi]; linarith
  linarith

theorem step (θ ρ : ℕ → ℝ) (n j : ℕ) (hjn : j+1 < n)
    (hmono : θ j < θ (j+1)) (hgap : θ (j+1) - θ j < π)
    (hpos : ∀ i, 0 < ρ i)
    (hfwd : 0 ≤ ∑ i ∈ Finset.Ico j n, ρ i * Real.sin (θ i - θ j))
    (hbwd : (∑ i ∈ Finset.Ico j n, ρ i * Real.sin (θ i - θ (n-1))) ≤ 0)
    (hnzj : chord θ ρ n j ≠ 0) (hnzj1 : chord θ ρ n (j+1) ≠ 0)
    (ha1 : aang θ ρ n (j+1) ∈ Set.Icc (0:ℝ) π)
    (hle1 : aang θ ρ n (j+1) ≤ θ (n-1) - θ (j+1))
    (hb1 : θ (n-1) - θ (j+1) - aang θ ρ n (j+1) ≤ π) :
    aang θ ρ n j ∈ Set.Icc (0:ℝ) π ∧ aang θ ρ n j ≤ θ (n-1) - θ j ∧
    θ (n-1) - θ j - aang θ ρ n j ≤ π := by
  have hr : 0 < ‖chord θ ρ n (j+1)‖ := norm_pos_iff.mpr hnzj1
  set δ := θ (j+1) - θ j with hδ
  set a1 := aang θ ρ n (j+1) with ha1def
  set r := ‖chord θ ρ n (j+1)‖ with hrdef
  set a0 := aang θ ρ n j with ha0def
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hφpos : 0 < δ + a1 := by have := ha1.1; linarith
  -- wrot(j) form & its Im
  have hwform := wrot_succ θ ρ n j (by omega)
  rw [← hrdef, show θ (j+1) - θ j + aang θ ρ n (j+1) = δ + a1 from by rw [hδ, ha1def]] at hwform
  have himw : (wrot θ ρ n j).im = r * Real.sin (δ + a1) := by
    rw [hwform, Complex.add_im, Complex.mul_im, Complex.exp_ofReal_mul_I_im,
      Complex.exp_ofReal_mul_I_re]
    simp
  have himw2 : (wrot θ ρ n j).im = ∑ i ∈ Finset.Ico j n, ρ i * Real.sin (θ i - θ j) := by
    rw [wrot]; exact im_rot_chord θ ρ n j j
  have hsinφ : 0 ≤ Real.sin (δ + a1) := by
    have h := himw.symm.trans himw2
    -- r sin = sum ≥0
    nlinarith [h, hr, hfwd]
  have hφπ : δ + a1 ≤ π := by
    by_contra hcon; push_neg at hcon
    have h1 : 0 < δ + a1 - π := by linarith
    have h2 : δ + a1 - π < π := by have := ha1.2; linarith
    have hpos' := Real.sin_pos_of_pos_of_lt_pi h1 h2
    rw [show δ + a1 = (δ+a1-π)+π by ring, Real.sin_add_pi] at hsinφ; linarith
  -- cone
  have hcone := cone_arg (ρ j) r (δ + a1) hφpos hφπ (hpos j).le hr.le
  have harg : Complex.arg ((ρ j:ℂ) + (r:ℂ)*Complex.exp (((δ+a1:ℝ):ℂ)*I)) = a0 := by
    rw [ha0def, aang]; rw [hwform]
  rw [harg] at hcone
  obtain ⟨ha0low, ha0φ⟩ := hcone
  -- a0 ∈ [0,π]
  have ha0π : a0 ≤ π := le_trans ha0φ hφπ
  -- a0 ≤ Δj
  have ha0Δ : a0 ≤ θ (n-1) - θ j := by
    have : δ + a1 ≤ θ (n-1) - θ j := by rw [hδ]; linarith [hle1]
    linarith [ha0φ]
  refine ⟨⟨ha0low, ha0π⟩, ha0Δ, ?_⟩
  -- B: Δj - a0 ≤ π
  set b0 := θ (n-1) - θ j - a0 with hb0def
  have hb0low : 0 ≤ b0 := by rw [hb0def]; linarith [ha0Δ]
  have hb0up : b0 ≤ 2*π := by
    rw [hb0def]
    have : θ (n-1) - θ j = δ + (θ (n-1) - θ (j+1)) := by rw [hδ]; ring
    rw [this]
    have hΔ1 : θ (n-1) - θ (j+1) ≤ π + a1 := by linarith [hb1]
    linarith [ha0low, hφπ]
  have hsinb : 0 ≤ Real.sin b0 := by
    have hend := im_end_chord θ ρ n j
    rw [im_rot_chord θ ρ n j (n-1)] at hend
    -- hend : sum = -(‖chord j‖ * sin(Δj - a0))  ; note Δj-a0 = b0
    have hbwd' : - (‖chord θ ρ n j‖ * Real.sin b0) ≤ 0 := by
      rw [← hend]; exact hbwd
    have hcn : 0 < ‖chord θ ρ n j‖ := norm_pos_iff.mpr hnzj
    nlinarith [hbwd', hcn]
  rcases sin_helper b0 hb0low hb0up hsinb with h | h
  · exact h
  · -- b0 = 2π corner
    exfalso
    sorry
