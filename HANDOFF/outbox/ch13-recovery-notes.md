# Ch13 discrete-Fenchel recovery — FFCT109 notes

## Result
`ProofsInTheBook/ZinanFFCT109.lean` builds 0-sorry, axioms `{propext, Classical.choice, Quot.sound}`.

Recovers the discrete-Fenchel layer from two STRONG planar facts (the weak
`DiscreteFenchelCore`/`OpenedArmTurningLtTwoPi` were FALSE — flat-closing rectangle turns exactly 2π).

## Theorems proved
1. `chord_zero_ne_of_strict_first` — strict first-edge closing ⇒ total chord ≠ 0. (§6; useful but
   not sufficient on its own — `n=6` counterexample has `s_2=0`.)
2. `hnd_of_suffix_ne_and_final_strict` — the two strong hypotheses
   - `hsuffix_ne` : every proper suffix chord `chord θ ρ n k ≠ 0` (1≤k≤n-1)
   - `hfinal_strict` : strict final-edge backward support (1≤k≤n-2)
   imply the per-instance non-degeneracy residue `chord k ≠ 0 ∧ b_k ≠ π` that `core_of_nondeg`
   consumes. (§7.2.)
3. `discreteFenchelCore_of_strict_final_support` — one-line composition of `core_of_nondeg` (all the
   hard analytic suffix-lift induction, already in FFCT108) with theorem 2. (§7 final.)

## Lean-detail fixes vs ChatGPT skeleton
- Thm 1: skeleton's `simp at him; linarith` failed (simp renormalized the `Finset.Ico` sum away
  from `hstrict0`'s form). Replaced with explicit `rw [hzero, mul_zero, Complex.zero_im]`.
- Thm 2: skeleton's `exact him.symm` for `hsum_zero` had wrong orientation — after
  `rw [im_rot_chord …] at him` then `rw [hbpi, Real.sin_pi, mul_zero, neg_zero]`, `him` is already
  `∑ … = 0`, so `exact him` (not `.symm`).
- Thm 2 `hsplit`: needed an extra `rw [show (n-1+1-1) = n-1 by omega]` after
  `Finset.sum_Ico_succ_top` because the top index appears as `n-1+1-1`.

## Key signature confirmed
`core_of_nondeg`'s last argument is the PER-INSTANCE form
`∀ k, 1≤k → k≤n-1 → chord θ ρ n k ≠ 0 ∧ (θ(n-1)-θk)-aang θ ρ n k ≠ π`,
NOT the bundled `DiscreteFenchelNondeg` def. So `hnd_of_…` produces the per-instance form directly.
Argument order: `n θ ρ hn hmono hgap hpos hfwd hbwd hnd`.
