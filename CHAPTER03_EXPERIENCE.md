# Chapter 03 Sylvester-Schur: Proof Notes and Lessons

Date: 2026-05-18

This note records the practical lessons from closing the Chapter 03 Sylvester-Schur proof in Lean.

## Final outcome

Chapter 03 now proves the full binomial-coefficient form needed for Sylvester-Schur:

```lean
theorem sylvester_general (n k : ℕ) (hn : 2 * k ≤ n) (hk : 0 < k) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k
```

The old smoothness premise on `n.descFactorial k` was removed. The final proof is by splitting on `k` and on whether `k^2 ≤ n`.

## Main split that worked

The successful global split is:

1. `k < 9`: finite certificate.
2. `9 ≤ k` and `k^2 ≤ n`: prime-counting gap, using `2 * Nat.primeCounting k < k`.
3. `9 ≤ k` and `n < k^2`: below-square case.

The below-square case is the hard part. It is now split as:

1. `sqrt n < 33`: finite interval-prime certificate, with a few explicit exceptional cases.
2. `sqrt n ≥ 33`, `k < 120`: finite interval-prime certificate.
3. `sqrt n ≥ 33`, `k ≥ 120`, close branch: `min k (n / 3) - sqrt n ≤ sqrt n`.
4. `sqrt n ≥ 33`, `k ≥ 120`, far branch: `2 * sqrt n < min k (n / 3)`.

This was more robust than trying to force one analytic inequality over all small `k`.

## Key mathematical lesson

The original Erdos-style argument is short on paper because several product estimates and finite prime-table checks are compressed into phrases like "it follows". In Lean those compressed parts are not free. The proof became manageable only after separating:

1. analytic estimates for genuinely large ranges;
2. finite certificates for small or irregular ranges;
3. interval-prime arguments whenever they are enough;
4. entropy/Stirling lower bounds as reusable inequalities.

The decisive move was not to use the old `4^M` bound uniformly for all `k`. It fails or becomes too weak in the small range. The clean cutoff was `k = 120`.

## Far branch strategy

For the far branch, set:

```lean
x := (n : ℝ) / (k : ℝ)
M := min k (n / 3)
```

The hard real inequality is packaged as:

```lean
theorem below_square_B_core {K x : ℝ}
    (hK120 : 120 ≤ K) (hx2 : 2 ≤ x) (hxhi : x ≤ K / 4 + 1) :
    Real.sqrt (x / K) / 3 * Real.log (K * x)
        + min 1 (x / 3) * Real.log 4 + (1 : ℝ) / 32
      ≤ x * Real.log x - (x - 1) * Real.log (x - 1)
```

It is split into:

1. compact range `2 ≤ x ≤ 31`, proved by interval-style rational/log certificates;
2. large range `31 ≤ x`, proved analytically with crude but Lean-friendly constants.

The large range was easier than expected once we used:

1. monotonicity of `sqrt (x/K) * log(K*x)` in `K` after the `exp 2` threshold;
2. the replacement `K0 = 4*x - 4` from `x ≤ K/4 + 1`;
3. the crude lower bound for entropy ratio:

```lean
x * log x - (x - 1) * log (x - 1) ≥ log x + 1 - 1/x
```

## Lean engineering lessons

### Use finite certificates only for the right statement

A direct finite certificate involving `Nat.choose n k` is often too expensive. For `k < 120`, the useful certificate was instead:

```lean
let p := nextPrimeWithin 120 (n.val - k.val)
k.val < p ∧ n.val - k.val < p ∧ p ≤ n.val ∧ Nat.Prime p
```

This gives divisibility of `n.choose k` by the existing interval-prime lemma, without computing huge binomial coefficients.

### Avoid existential search over large `Fin`

This shape was bad:

```lean
∃ p : Fin 14400, ...
```

Lean failed to synthesize or expand the decidable search efficiently. The better pattern was deterministic witness extraction:

```lean
def nextPrimeWithin : ℕ → ℕ → ℕ
  | 0, m => m
  | fuel + 1, m => if Nat.Prime (m + 1) then m + 1 else nextPrimeWithin fuel (m + 1)
```

Then `native_decide` checks the concrete witness, rather than searching an existential space.

### Keep hard real inequalities standalone

The real-analysis parts should be isolated from number theory. This made each failure local:

1. first prove compact real intervals;
2. then prove large real intervals;
3. then bridge Nat inequalities to the real lemma;
4. only at the end call the prime-factor existence theorem.

This avoided huge mixed goals containing logs, casts, `Nat.sqrt`, `min`, and divisibility all at once.

### Prefer monotonicity plus crude constants

Precise inequalities are harder to formalize. The successful proof uses deliberately crude constants:

1. `log 4 < 7/5`;
2. `log 16 > 69/25`;
3. `log k / 2 + 6/5 < k/32` for `120 ≤ k`;
4. interval-specific log upper bounds for compact certificates.

The constants are not elegant, but they leave room for `nlinarith`.

### Bridge lemmas matter

The final Nat-to-real bridge needed reusable lemmas such as:

```lean
nat_sqrt_div_le_sqrt_ratio
stirling_correction_ge_neg_log_k_sub_six_fifths
entropyTerm_eq_mul_entropyRatio
sqrt_div_mul_log_mul_le_of_base_le
```

These are not cosmetic. They are the infrastructure that keeps the final proof small.

## Remote build SOP

Do not run local Lean validation on the Mac mini for this repo.

Use remote single-file validation:

```bash
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book --file ProofsInTheBook/Chapter03.lean
```

Use remote full build:

```bash
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book
```

The full successful build after closing Ch03 was:

```text
Build completed successfully (8461 jobs).
=== BUILD OK (190s) ===
```

## What to reuse later

For future hard Lean proofs in this repo:

1. identify the genuinely asymptotic range;
2. choose a cutoff where the analytic inequality has comfortable slack;
3. close the residue by exact integer certificates, but avoid expensive objects like binomial coefficients if an interval-prime witness suffices;
4. isolate real inequalities as standalone lemmas;
5. bridge Nat-to-real only after the real lemma is stable;
6. remote-validate single file frequently, then full remote build before final claim.

The core lesson: for book proofs, Lean usually needs the hidden finite tables and hidden analytic slack made explicit. The fastest route is not to mimic the prose line-by-line, but to preserve the mathematical invariant while changing the proof architecture into certificate plus analytic core.
