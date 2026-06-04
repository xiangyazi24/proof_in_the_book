# ANSWER_03_03 — Step 3 + l=2 specific guidance

## (Q1) Inequality strategy: geometric sum, not induction

Use `Nat.geom_sum_eq`-style factorization:

```
a^l - b^l = (a - b) · ∑_{i=0}^{l-1} a^i · b^{l-1-i}
```

For `a = m+1, b = m, a - b = 1`:

```
(m+1)^l - m^l = ∑_{i=0}^{l-1} (m+1)^i · m^{l-1-i}
             ≥ ∑_{i=0}^{l-1} m^i · m^{l-1-i}    -- (m+1)^i ≥ m^i
             = ∑_{i=0}^{l-1} m^{l-1}
             = l · m^{l-1}
```

Mathlib has `Commute.sub_pow` and `Nat.sub_pow_le_sub_pow` variants — grep for
exact name. There's likely `Nat.add_one_pow_sub_pow` or you can chain via
`Finset.sum_le_sum` after `Nat.geom_sum_eq`.

If Mathlib doesn't expose the right packaging, prove the specific 
`(m+1)^l - m^l ≥ l * m^(l-1)` directly:

```lean
lemma pow_succ_sub_pow_ge (m l : ℕ) (hl : 1 ≤ l) :
    (m + 1)^l - m^l ≥ l * m^(l - 1) := by
  -- Use Nat.geom_sum_eq or factorize directly.
  -- Induction on l with base l = 1: LHS = 1 = 1 * m^0 = 1. ✓ (for any m)
  -- Step: assume for l, show for l+1.
  --   (m+1)^(l+1) - m^(l+1) = (m+1)·(m+1)^l - m·m^l
  --                         = (m+1)·m^l + (m+1)·((m+1)^l - m^l) - m·m^l  
  --                         = m^l + (m+1)·((m+1)^l - m^l)
  --                         ≥ m^l + (m+1)·l·m^(l-1)        (by IH)
  --                         = m^l + l·m^l + l·m^(l-1)
  --                         = (l+1)·m^l + l·m^(l-1)
  --                         ≥ (l+1)·m^l                    (since l·m^(l-1) ≥ 0)
  sorry  -- straightforward induction, ~15 LOC
```

The induction proof is cleaner than the geometric-sum approach in Lean
because we don't have to deal with Finset.sum manipulation.

## (Q2) Product-divisibility (∏ a_j ∣ k!): heavy, expect 80+ LOC

This is the genuinely hard step in Erdős's proof. The argument:
- For prime `p > k`: p ∤ a_j for all j (because p^l ∣ n-j₀ for the Sylvester
  index j₀, and p > k means p divides at most one factor in `n-j` for j < k).
- For prime `p ≤ k`: bound `v_p(∏ a_j) ≤ v_p(k!)` by Legendre.

Mathlib API:
- `Nat.factorial`, `padicValNat`, `Nat.factorization`.
- `Nat.padicValNat_factorial p n = ∑_{i≥1} n / p^i` (Legendre's formula).
  Search exact name: try `Nat.padicValNat_factorial` or
  `Nat.factorization_factorial`.
- `Nat.factorization_prod : (∏ x ∈ s, f x).factorization = ∑ x ∈ s, (f x).factorization`
  (for f x ≠ 0).

The proof structure:
```lean
-- For each prime p, bound v_p(∏ a_j) ≤ v_p(k!).
lemma prod_lPowerFreePart_dvd_factorial : (∏ j : Fin k, a_j) ∣ (k - 1)! := by
  rw [Nat.dvd_iff_div_mul_eq]  -- or use Nat.dvd_factorial-style helper
  -- Use factorization equality:
  rw [Nat.factorization_prod ...]
  -- For each prime, bound sums.
  sorry
```

If you don't find a clean Mathlib helper for this, EXPECT 80-100 LOC of
careful factorization bookkeeping.

**Pragmatic alternative**: skip the "{a_j} ⊆ {1,...,k}" route, use a WEAKER
counting argument. The bound `a_j ≤ k` for each j follows from `b_j ≥ 1` and
`a_j · b_j^l = n - j ≤ n` PLUS a tightening that uses the Sylvester
contribution. If you can avoid the full product-divisibility argument,
~30 LOC less.

**OR even more pragmatic**: state `chapter03_erdos` for l = 2 SPECIFICALLY,
making "a_j squarefree" + "distinctness" + "bounded by k" the only inputs,
then add the final 4 = 2² contradiction. Don't try the general l version.

## (Q3) Focus l=2 first: STRONGLY recommend

The l=2 case is the book's headline result (Theorem 1 in Erdős 1934/1951).
The l≥3 case is a follow-up extension. Ship `chapter03_erdos_l_eq_2` first,
verify it builds clean, then either:
- Add `chapter03_erdos` as the general statement with `l ≥ 3` case as 
  named premise / future TODO, OR
- Leave `chapter03_erdos` for l = 2 only with a docstring noting l ≥ 3
  is future Tier 2.

Both are acceptable Tier 1 deliveries.

## (Q4) Don't dispatch elsewhere

You've built up the right context for Ch03 over 50+ minutes. Switching
agents loses that context. Stay on Ch03 through Step 3 + l=2 contradiction.

The hardest single sub-step is `prod_lPowerFreePart_dvd_factorial` (Q2's
~80 LOC). If you hit > 100 LOC on JUST that lemma, file Q04 with the
specific stuck point. Otherwise grind it.

## Recommended order

1. Prove `pow_succ_sub_pow_ge` (~15 LOC induction).
2. Use it for `a_j_distinct` (the distinctness from Step 3 algebra).
3. Define `a_j` concretely as `lPowerFreePart (n - j)`.
4. Prove `a_j ≠ 0` and bounded reasonably.
5. The product-divisibility step (the hardest, ~80 LOC).
6. {a_j} ⊆ {1,...,k} from product-divisibility + distinctness.
7. {a_j} = {1,...,k} as Finset (pigeon).
8. For k ≥ 4: 4 ∈ {a_j}, but a_j squarefree, contradiction.

Each step ~20-30 LOC except step 5 (~80). Total ~250 LOC.

Go.
