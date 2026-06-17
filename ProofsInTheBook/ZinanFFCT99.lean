import ProofsInTheBook.ZinanFFCT97

/-!
# `ZinanFFCT99` -- machine-checked refutation of `PlanarOneWindNoRepeat`

`ProofsInTheBook.ZinanFFCT97.PlanarOneWindNoRepeat` claims: for every planar
lifted-turn certificate (`PlanarLiftedTurnSpan`) with the single-wind bound
`θ N − θ 0 < 2π`, the chain has no nonadjacent repeated vertices.

This is **false**.  The single equilateral triangle traversed once, as a
`4`-vertex chain `Q₀, Q₁, Q₂, Q₃ = Q₀`, carries a genuine lifted certificate:

* edge directions `θ : 0, 2π/3, 4π/3` (each consecutive turn `2π/3 < π`),
* total span `θ 4 − θ 0 = 5π/3 < 2π` (single-wind holds),
* unit edge lengths,

yet `Q₀ = Q₃` is a nonadjacent repeat (`r = 0, s = 3`, `0 + 2 ≤ 3`).  The
"convex partial-sum polygon cannot return to its origin" intuition is simply
false in the span band `[π, 2π)`: a convex polygon *does* close on its own
vertex.  This file builds the certificate explicitly and derives the
contradiction, proving `¬ PlanarOneWindNoRepeat`.

This is exactly the obstruction flagged in `ZinanFFCT94`'s header comment
(the single equilateral triangle, `span 4π/3 < 2π`, nonadjacent repeat at
`r=0, s=3`), now turned into a full machine-checked refutation.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.ZinanFFCT94
open ProofsInTheBook.ZinanFFCT97

namespace ProofsInTheBook.ZinanFFCT99

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## The counterexample chain: an equilateral triangle that closes. -/

/-- The orthonormal planar frame: `h = e₂`, `u = e₀`, `v = e₁`. -/
def triH : E3 := !₂[(0 : ℝ), 0, 1]
def triU : E3 := !₂[(1 : ℝ), 0, 0]
def triV : E3 := !₂[(0 : ℝ), 1, 0]

/-- The equilateral triangle as a closed `4`-vertex chain in the plane `z = 1`.
`Q 3 = Q 0 = (0,0,1)`. -/
def triChain : Fin 4 → E3 :=
  ![ !₂[(0 : ℝ), 0, 1],
     !₂[(1 : ℝ), 0, 1],
     !₂[(1 / 2 : ℝ), Real.sqrt 3 / 2, 1],
     !₂[(0 : ℝ), 0, 1] ]

/-- The lifted turn function: `θ m = m·(2π/3)` for `m ≤ 2`, and from `m ≥ 2`
it continues by `π/6` per step, so `θ 3 = 3π/2`, `θ 4 = 5π/3 < 2π`.  Every
consecutive gap lies in `(0, π)` (gaps are `2π/3` for `m = 0,1` and `π/6` for
`m ≥ 2`), and `θ 4 − θ 0 = 5π/3 < 2π`. -/
def triθ : ℕ → ℝ :=
  fun m => if m ≤ 2 then (m : ℝ) * (2 * Real.pi / 3)
           else 4 * Real.pi / 3 + ((m : ℝ) - 2) * (Real.pi / 6)

/-! ## Helper cos/sin values at the three edge directions. -/

/-- `cos (2π/3) = -1/2`. -/
theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  have h : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]

/-- `sin (2π/3) = √3/2`. -/
theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have h : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]

/-- `cos (4π/3) = -1/2`. -/
theorem cos_four_pi_div_three : Real.cos (4 * Real.pi / 3) = -(1 / 2) := by
  have h : (4 : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
  rw [h, Real.cos_add_pi, Real.cos_pi_div_three]

/-- `sin (4π/3) = -√3/2`. -/
theorem sin_four_pi_div_three : Real.sin (4 * Real.pi / 3) = -(Real.sqrt 3 / 2) := by
  have h : (4 : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
  rw [h, Real.sin_add_pi, Real.sin_pi_div_three]

/-- Every consecutive gap of `triθ` is either `2π/3` (for `m = 0, 1`) or
`π/6` (for `m ≥ 2`).  Both lie strictly in `(0, π)`. -/
theorem triθ_gap (m : ℕ) :
    triθ (m + 1) - triθ m = 2 * Real.pi / 3 ∨ triθ (m + 1) - triθ m = Real.pi / 6 := by
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · -- m = 0 or 1: gap is 2π/3
    left
    interval_cases m
    · -- θ 1 - θ 0
      simp only [triθ, show (0 + 1 : ℕ) ≤ 2 from by norm_num,
        show (0 : ℕ) ≤ 2 from by norm_num, if_true]
      push_cast; ring
    · -- θ 2 - θ 1
      simp only [triθ, show (1 + 1 : ℕ) ≤ 2 from by norm_num,
        show (1 : ℕ) ≤ 2 from by norm_num, if_true]
      push_cast; ring
  · -- m ≥ 2: gap is π/6
    right
    rcases eq_or_lt_of_le hge with heq | hgt
    · -- m = 2: θ 3 uses else-branch, θ 2 uses the ≤2 branch (both give 4π/3)
      rw [← heq]
      simp only [triθ, show ¬ ((2 + 1 : ℕ) ≤ 2) from by norm_num,
        show (2 : ℕ) ≤ 2 from by norm_num, if_true, if_false]
      push_cast; ring
    · -- m ≥ 3: both θ(m+1), θ m use the else-branch
      have hm1 : ¬ (m + 1 ≤ 2) := by omega
      have hm0 : ¬ (m ≤ 2) := by omega
      simp only [triθ, hm1, hm0, if_false]
      have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      ring

/-! ## The certificate. -/

/-- The equilateral-triangle chain carries a `PlanarLiftedTurnSpan` with
single-wind `θ 4 − θ 0 = 5π/3 < 2π`. -/
theorem triChain_certificate :
    Nonempty (PlanarLiftedTurnSpan triChain triH triU triV) := by
  refine ⟨{
    θ := triθ
    ρ := fun _ => 1
    ρ_pos := fun _ => one_pos
    in_plane := ?_
    u_perp_h := ?_
    v_perp_h := ?_
    u_unit := ?_
    v_unit := ?_
    uv_perp := ?_
    edge_eq := ?_
    turn_pos := ?_
    turn_lt_pi := ?_
    one_wind := ?_ }⟩
  · -- in_plane
    intro i
    fin_cases i
    · show (⟪triH, !₂[(0 : ℝ), 0, 1]⟫ : ℝ) = 1
      rw [triH, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
    · show (⟪triH, !₂[(1 : ℝ), 0, 1]⟫ : ℝ) = 1
      rw [triH, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
    · show (⟪triH, !₂[(1 / 2 : ℝ), Real.sqrt 3 / 2, 1]⟫ : ℝ) = 1
      rw [triH, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
    · show (⟪triH, !₂[(0 : ℝ), 0, 1]⟫ : ℝ) = 1
      rw [triH, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · rw [triH, triU, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · rw [triH, triV, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · rw [triU, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · rw [triV, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · rw [triU, triV, ProofsInTheBook.ZinanFFCT10.innerE3]; norm_num
  · -- edge_eq for m = 0, 1, 2
    intro m hm
    have hm3 : m < 3 := by omega
    interval_cases m
    · -- edge 0: θ 0 = 0, direction (1,0,0)
      have hθ0 : triθ 0 = 0 := by simp [triθ]
      show triChain ⟨1, _⟩ - triChain ⟨0, _⟩
          = (1 : ℝ) • (Real.cos (triθ 0) • triU + Real.sin (triθ 0) • triV)
      rw [hθ0, Real.cos_zero, Real.sin_zero]
      simp only [one_smul, zero_smul, add_zero]
      ext k
      fin_cases k <;>
        simp [triChain, triU, PiLp.sub_apply]
    · -- edge 1: θ 1 = 2π/3, direction (-1/2, √3/2, 0)
      have hθ1 : triθ 1 = 2 * Real.pi / 3 := by
        simp only [triθ, show (1 : ℕ) ≤ 2 from by norm_num, if_true]
        push_cast; ring
      show triChain ⟨2, _⟩ - triChain ⟨1, _⟩
          = (1 : ℝ) • (Real.cos (triθ 1) • triU + Real.sin (triθ 1) • triV)
      rw [hθ1, cos_two_pi_div_three, sin_two_pi_div_three]
      simp only [one_smul]
      ext k
      fin_cases k <;>
        (simp [triChain, triU, triV,
          PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply] <;> try ring)
    · -- edge 2: θ 2 = 4π/3, direction (-1/2, -√3/2, 0)
      have hθ2 : triθ 2 = 4 * Real.pi / 3 := by
        simp only [triθ, show (2 : ℕ) ≤ 2 from by norm_num, if_true]
        push_cast; ring
      show triChain ⟨3, _⟩ - triChain ⟨2, _⟩
          = (1 : ℝ) • (Real.cos (triθ 2) • triU + Real.sin (triθ 2) • triV)
      rw [hθ2, cos_four_pi_div_three, sin_four_pi_div_three]
      simp only [one_smul]
      ext k
      fin_cases k <;>
        simp [triChain, triU, triV,
          PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply]
  · -- turn_pos: every consecutive gap > 0
    intro m
    have hgap := triθ_gap m
    have hpi := Real.pi_pos
    rcases hgap with h | h <;> rw [h] <;> positivity
  · -- turn_lt_pi: every consecutive gap < π
    intro m
    have hgap := triθ_gap m
    have hpi := Real.pi_pos
    rcases hgap with h | h <;> rw [h] <;> nlinarith [Real.pi_pos]
  · -- one_wind: θ 4 - θ 0 = 5π/3 < 2π
    have hpi := Real.pi_pos
    have hθ4 : triθ 4 = 5 * Real.pi / 3 := by
      simp only [triθ, show ¬ ((4 : ℕ) ≤ 2) from by norm_num, if_false]
      norm_num; ring
    have hθ0 : triθ 0 = 0 := by
      simp only [triθ, show (0 : ℕ) ≤ 2 from by norm_num, if_true]
      norm_num
    rw [hθ4, hθ0]
    nlinarith [Real.pi_pos]

/-! ## The refutation. -/

/-- `PlanarOneWindNoRepeat` is **false**: the single equilateral triangle,
traversed once as a `4`-vertex closed chain, carries a lifted single-wind
certificate yet has `Q₀ = Q₃`, a nonadjacent repeat. -/
theorem not_planarOneWindNoRepeat :
    ¬ ProofsInTheBook.ZinanFFCT97.PlanarOneWindNoRepeat := by
  intro H
  obtain ⟨cert⟩ := triChain_certificate
  have hnr : PlanarNoNonadjacentRepeat triChain := H cert
  -- instantiate at r = 0, s = 3
  have hne : triChain ⟨0, by norm_num⟩ ≠ triChain ⟨3, by norm_num⟩ :=
    hnr 0 3 (by norm_num) (by norm_num) (by norm_num)
  apply hne
  -- but Q 0 = Q 3 = (0,0,1)
  rfl

#print axioms not_planarOneWindNoRepeat

end ProofsInTheBook.ZinanFFCT99
