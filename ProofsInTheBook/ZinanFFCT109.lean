import ProofsInTheBook.ZinanFFCT108

/-!
# `ZinanFFCT109` — recovering the discrete-Fenchel layer from two strong planar facts

The over-generalized statements `DiscreteFenchelCore` / `OpenedArmTurningLtTwoPi` were **false**
(a flat-closing rectangle satisfies the weak premises but turns exactly `2π`).  The hard analytic
core `core_of_nondeg` in `ZinanFFCT108` is **sound**: it proves `θ(n-1) − θ0 < 2π` under the
discrete-Fenchel premises *plus* the non-degeneracy residue

  for `1 ≤ k ≤ n-1`,  `chord θ ρ n k ≠ 0`  and  `(θ_{n-1} − θ k) − arg(wₖ) ≠ π`.

This file supplies that residue from two stronger geometric facts that a strict convex arc
actually has:
* `hsuffix_ne`  : every proper suffix chord is nonzero (no proper sub-arc closes up);
* `hfinal_strict` : strict final-edge backward support for every interior earlier vertex.

The bridge is purely planar (ChatGPT 5.5 Pro's Option-B design, §§6–9).  No
`sorry`/`axiom`/`admit`/`native_decide`.
-/

noncomputable section

open Complex Real

namespace ProofsInTheBook.ZinanFFCT109

open ProofsInTheBook.ZinanFFCT108

/-- **§6.** Strict first-edge closing makes the *total* chord nonzero.  (Useful, but not enough on
its own — it does not control proper suffix chords; see the `n=6` counterexample in the design.) -/
lemma chord_zero_ne_of_strict_first {n : ℕ} (θ ρ : ℕ → ℝ)
    (hstrict0 : 0 < ∑ i ∈ Finset.Ico 0 n, ρ i * Real.sin (θ i - θ 0)) :
    chord θ ρ n 0 ≠ 0 := by
  intro hzero
  have him := im_rot_chord θ ρ n 0 0
  rw [hzero, mul_zero, Complex.zero_im] at him
  linarith

/-- **§7.2.** The two strong geometric hypotheses imply the per-instance non-degeneracy residue
consumed by `core_of_nondeg`. -/
lemma hnd_of_suffix_ne_and_final_strict {n : ℕ} (θ ρ : ℕ → ℝ)
    (hpos : ∀ i, 0 < ρ i)
    (hsuffix_ne : ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 → chord θ ρ n k ≠ 0)
    (hfinal_strict : ∀ k : ℕ, 1 ≤ k → k ≤ n - 2 →
      0 < - ∑ i ∈ Finset.Ico k (n - 1), ρ i * Real.sin (θ i - θ (n - 1))) :
    ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →
      chord θ ρ n k ≠ 0 ∧ (θ (n - 1) - θ k) - aang θ ρ n k ≠ Real.pi := by
  intro k hk1 hkn
  refine ⟨hsuffix_ne k hk1 hkn, ?_⟩
  intro hbpi
  by_cases hk_last : k = n - 1
  · subst hk_last
    have ha : aang θ ρ n (n - 1) = 0 :=
      aang_last θ ρ n (by omega) (hpos (n - 1))
    rw [ha] at hbpi
    nlinarith [Real.pi_pos]
  · have hk_n2 : k ≤ n - 2 := by omega
    have hstrict := hfinal_strict k hk1 hk_n2
    have him := im_end_chord θ ρ n k
    rw [im_rot_chord θ ρ n k (n - 1)] at him
    have hsum_zero :
        ∑ i ∈ Finset.Ico k n, ρ i * Real.sin (θ i - θ (n - 1)) = 0 := by
      rw [hbpi, Real.sin_pi, mul_zero, neg_zero] at him
      exact him
    have hsplit :
        ∑ i ∈ Finset.Ico k n, ρ i * Real.sin (θ i - θ (n - 1))
          = ∑ i ∈ Finset.Ico k (n - 1), ρ i * Real.sin (θ i - θ (n - 1)) := by
      rw [show n = (n - 1) + 1 by omega]
      rw [Finset.sum_Ico_succ_top (by omega : k ≤ n - 1)]
      rw [show (n - 1 + 1 - 1) = n - 1 by omega, sub_self, Real.sin_zero, mul_zero, add_zero]
    rw [hsplit] at hsum_zero
    linarith

/-- **§7 final.** The recovered discrete-Fenchel core: under the discrete-Fenchel premises plus the
two strong geometric facts (`hsuffix_ne`, `hfinal_strict`), the total turning is `< 2π`. -/
theorem discreteFenchelCore_of_strict_final_support {n : ℕ} (θ ρ : ℕ → ℝ) (hn : 2 ≤ n)
    (hmono : ∀ m : ℕ, m + 1 ≤ n - 1 → θ m < θ (m + 1))
    (hgap : ∀ m : ℕ, m + 2 ≤ n → θ (m + 1) - θ m < Real.pi)
    (hpos : ∀ i : ℕ, 0 < ρ i)
    (hfwd : ∀ a j : ℕ, a + 1 ≤ n → a ≤ j → j ≤ n →
      0 ≤ ∑ i ∈ Finset.Ico a j, ρ i * Real.sin (θ i - θ a))
    (hbwd : ∀ a j : ℕ, a + 1 ≤ n → j ≤ a →
      0 ≤ - ∑ i ∈ Finset.Ico j a, ρ i * Real.sin (θ i - θ a))
    (hsuffix_ne : ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 → chord θ ρ n k ≠ 0)
    (hfinal_strict : ∀ k : ℕ, 1 ≤ k → k ≤ n - 2 →
      0 < - ∑ i ∈ Finset.Ico k (n - 1), ρ i * Real.sin (θ i - θ (n - 1))) :
    θ (n - 1) - θ 0 < 2 * Real.pi :=
  core_of_nondeg n θ ρ hn hmono hgap hpos hfwd hbwd
    (hnd_of_suffix_ne_and_final_strict θ ρ hpos hsuffix_ne hfinal_strict)

/-! ## Guards. -/
#check @chord_zero_ne_of_strict_first
#check @hnd_of_suffix_ne_and_final_strict
#check @discreteFenchelCore_of_strict_final_support
#print axioms discreteFenchelCore_of_strict_final_support

end ProofsInTheBook.ZinanFFCT109
