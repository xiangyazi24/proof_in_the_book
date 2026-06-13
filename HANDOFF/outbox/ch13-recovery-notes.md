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

---

# Ch13 recovery — FFCT110 planar SINGLE-STUCK bridge (0-sorry, clean-3)

`ProofsInTheBook/ZinanFFCT110.lean` — the ChatGPT-designed `ch13-recovery-DIRECTION.md`
recovery, proved unconditionally. WEAKER and more faithful than FFCT109's two strong
facts: weak cyclic support + **at most one** nonincident support zero (the single
`openedWBS` stuck tangency), instead of global strict suffix-ne + strict final support.

## Self-contained planar setup (pure ℂ; depends only on FFCT108, no E3/det3/spherical)
- `cross u v := u.re*v.im - u.im*v.re` (= `Im(conj u · v)`).
- `vert θ ρ n j := -chord θ ρ n j` (vertices anchored `Vₙ=0`; `vert n - vert j = chord j`).
- `nxtV n i := if i=n then 0 else i+1` (cyclic; closing edge `n ↦ 0`).
- `EV n i := vert(nxtV i) - vert i` (arm edge = `edge i`; closing edge = `-chord 0`).
- `supp n i j := cross (EV i) (vert j - vert i)`; `NonInc n i j := j≠i ∧ j≠nxtV i`.
- `AtMostOneZero θ ρ n` : any two nonincident zero supports are equal.

## Theorems
1. `chord_ne_of_atMostOne` : collision `chord k=0` ⇒ `supp(k,n)=0` (cross_zero_right) +
   `supp(n-1,k)=0` (cross_self) — two distinct nonincident zeros ⇒ contra.
2. `final_ray_of_b_eq_pi` : `bₖ=π` ⇒ `chord k = -λ·edge(n-1)`, λ>0. Via `end_rot_chord`
   (= `im_end_chord`'s `key`) + `exp(-πI)=-1`.
3. `b_ne_pi_of_atMostOne` : `bₖ=π` ⇒ final-edge zero `supp(n-1,k)=0` + CLOSING-edge zero
   `supp(n,n-1)=0` (opposite weak supports `λ·cross(g,f)≥0`, `-cross(g,f)≥0` ⇒ `=0`).
4. `suffix_nondeg_of_atMostOneZero` : assembles 1+3 → per-instance residue.
5. `discreteFenchelCore_of_atMostOneZero` : `= core_of_nondeg ∘ 4` → `θ(n-1)-θ0 < 2π`.

## Non-vacuity / orientation (checked)
Regular increasing-θ (CCW) arc has ALL nonincident `supp > 0` (n=3: `supp(0,3)=sinα+sin2α
>0`), so `hweak` + `AtMostOneZero` are satisfiable (zero nonincident zeros) and the
conclusion holds there — non-circular, non-vacuous. Orientation convention `supp ≥ 0`
matches increasing-θ.

## Lean gotchas
- `rw [hchordval]` rewrites `chord k` inside `‖chord k‖` (norm contains the term) → mess.
  Fix: `set s := ‖chord k‖` first. (`field_simp; ring` also failed on the `exp` factor.)
- `div_mul_cancel₀ _ hρne` after `Complex.ofReal_div`; `exp(↑(-π)·I)=-1` via `exp_neg`+
  `exp_pi_mul_I`.

## REMAINING (separate file): spherical `AtMostOneZero`
Prove `openedWBS`'s gproj image satisfies `ZinanFFCT110.AtMostOneZero` (single stuck
tangency = unique nonincident det3 zero). Then Ch13's discrete-Fenchel layer closes.
