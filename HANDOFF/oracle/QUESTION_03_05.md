# QUESTION 03 05: padicValNat/factorization API for prod a_j | k!

## (i) Theorem to prove

```lean
lemma prod_lPowerFreeParts_dvd_factorial_l2 {n k m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n)
    (h_eq : n.choose k = m ^ 2) :
    (∏ j ∈ Finset.range k, lPowerFreePart 2 (n - j)) ∣ k ! := by
```

## (ii) Mathematical proof (complete, correct)

Let `a_j = lPowerFreePart 2 (n-j)`, `P = ∏ a_j`, `B = ∏ b_j` where `b_j = lPowerRoot 2 (n-j)`.

From `C(n,k) = m^2` and `n.descFactorial k = k! * C(n,k)`:
`n.descFactorial k = ∏ (n-j) = P * B^2 = k! * m^2`

For each prime p: `v_p(P) + 2*v_p(B) = v_p(k!) + 2*v_p(m)`.
Hence `v_p(P) ≡ v_p(k!) (mod 2)`.

**For p > k**: `v_p(k!) = 0`. If `v_p(P) > 0`, then `v_p(P) = 1` (squarefree).
But `v_p(P) = 2*(v_p(m) - v_p(B))` must be even. Contradiction. So `v_p(P) = 0 ∀ p > k`.

**For p ≤ k**: Each a_j is squarefree → `v_p(a_j) ∈ {0,1}`.
Among k consecutive integers n,...,n-k+1, at most ⌊k/p⌋+1 are divisible by p.
So `v_p(P) ≤ ⌊k/p⌋ + 1`.
`v_p(k!) = Σ_{i≥1} ⌊k/p^i⌋ ≥ ⌊k/p⌋`.

- If `⌊k/p²⌋ ≥ 1`: `v_p(k!) ≥ ⌊k/p⌋ + 1 ≥ v_p(P)`.
- If `⌊k/p²⌋ = 0`: `v_p(k!) = ⌊k/p⌋`, and `v_p(P) ≤ ⌊k/p⌋ + 1`.
  The difference is 0 or 1. Since `v_p(P) ≡ v_p(k!)` (mod 2), difference ≠ 1.
  So `v_p(P) ≤ v_p(k!)`.

Thus `v_p(P) ≤ v_p(k!)` for all primes p. Hence `P ∣ k!`.

## (iii) What's blocking implementation

1. **padicValNat for products**: No `padicValNat.prod` lemma found. The standard approach uses `factorization_prod_apply` (which exists), then converts factorization to padicValNat. This conversion lemma (`factorization p = padicValNat p n` for `p.Prime`) — what's it called?

2. **padicValNat_factorial**: Exists but requires `Fact p.Prime` instance. Signature: `padicValNat_factorial {n b} [Fact p.Prime] (hnb : log p n < b) : ...`. What's the standard way to access `v_p(k!) = Σ ⌊k/p^i⌋`?

3. **factorization_le_iff_dvd**: Found in `Defs.lean:164`: `factorization_le_iff_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) : d.factorization ≤ n.factorization ↔ d ∣ n`. This is the global lemma — but it works with `Finsupp.le`, not pointwise comparison. How to prove pointwise `∀ p, ... ≤ ...` → `Finsupp.le`?

4. **The ℤ parity argument**: From the factorization equation in ℕ, how to lift to ℤ to get the parity constraint? Use `zify` like in Q04? Or `exact_mod_cast`?

5. **Interval bound**: `#{j < k | p ∣ n-j} ≤ k/p + 1`. This needs the "spacing ≥ p" argument. Is there a quick Mathlib lemma for this, or must I write Finset.card + min'/max' reasoning (~30 LOC)?

## (iv) Request

Give me the EXACT Mathlib lemma names for (1)-(4), and a concise proof snippet for (5). I'll then implement the full ~80 LOC proof using these building blocks.

File: HANDOFF/oracle/QUESTION_03_05.md
