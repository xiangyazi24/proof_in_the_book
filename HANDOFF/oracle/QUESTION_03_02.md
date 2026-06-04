# QUESTION 03 02: Concentration lemma + Steps 2-4 status

## (i) What's been done

1. Replaced `chapter03 : Infinite {p // Prime}` (Ch01 placeholder) with the correct Erdős theorem:
   `chapter03 {n k l m} (hk : 4 ≤ k) (hn : 2*k ≤ n) (hl : 2 ≤ l) : n.choose k ≠ m ^ l`
2. Build: 0 errors, 1 `sorry` in `chapter03_erdos` body.
3. Removed the failed `v_p ≤ 1` comments and unused `binomial_not_perfect_power_of_large_prime` lemma.
4. Retained `chapter03_binomials_coefficients_never_powers` (p|C→p|m) as a useful helper.

## (ii) Remaining work

### (a) Concentration lemma (Step 1 gap) — ~60 lines

The lemma `pow_l_dvd_one_factor_of_descFactorial`:
```
Given p prime > k, p^l | n.descFactorial k, prove ∃ i < k, p^l | n-i.
```

I have a clean proof plan (induction on k with coprime reasoning) but hit a Lean scoping issue:
when using `set P := ...` with `Finset.prod_erase_mul`, the binder `k` becomes an "unknown identifier"
inside the `calc`/`rw` block. This happened across multiple rewrite attempts.

The intended proof (avoiding Finset.range/prod_erase_mul complexity):
1. Lemma `at_most_one_factor` (proved, 0 sorry): at most one n-i has p|n-i when p>k.
2. Lemma `descFactorial_succ_mul`: n.descFactorial (k+1) = (n-k) * n.descFactorial k.
3. Main induction on k:
   - Base k=0: trivial (p^l | 1 impossible).
   - Step k→k+1: Use recurrence to split product.
     * If p | n-k: by uniqueness, all other factors have p ∤ them. So p ∤ n.descFactorial k.
       Then coprime(p, n.descFactorial k), and by Coprime lemma p^l | n-k.
     * If p ∤ n-k: then coprime(p, n-k), so p^l | n.descFactorial k.
       Apply IH to get p^l | n-i for some i < k < k+1.

The induction approach avoids `Finset.prod_erase_mul` entirely — it uses only
the recurrence `descFactorial_succ_mul` and the Finset.dvd_prod lemma
`nat_prime_dvd_finset_prod` (proved, 0 sorry).

### (b) Steps 2-4 of the a_j decomposition — ~200 lines

Step 2: Decompose each n-j = a_j * b_j^l with a_j l-th-power-free.
  Needs: `IsLPowerFree` definition + existence of decomposition.
  Challenge: constructing a_j and b_j explicitly (factorization-based or well-founded recursion).

Step 3: The product a_0*...*a_{k-1} divides k!. Hence {a_j} ⊆ {1,...,k}.
  Since the a_j's are k distinct values (Step 2) in a set of size k, they are exactly {1,...,k}.
  Challenge: Legendre formula for p-adic valuation + the bound on prime exponents in a_j product.

Step 4: Contradiction for l=2 and l≥3.
  l=2: 4 ∈ {a_j} = {1,...,k}, but a_j's are squarefree → 4 = 2² ∤ a_j, contradiction.
  l≥3: Use 1,2,4 ∈ {a_j} with algebraic inequality involving n-i₁=m₁^l, n-i₂=2*m₂^l, n-i₃=4*m₃^l.

## (iii) What I need

1. **The scoping issue**: have you seen `k` becoming "unknown identifier" inside blocks that use
   `Finset.prod_erase_mul` or `set` with Finset expressions? Is this a known Lean 4 issue?

2. **Strategy confirmation**: The induction-based approach (avoiding Finset product decomposition)
   for the concentration lemma is cleaner and avoids the scoping issue. Do you approve?

3. **Steps 2-4 approach**: Should I:
   (a) Continue with the factorization-based l-th-power-free decomposition?
   (b) Use a different construction (e.g., well-founded recursion removing l-th powers)?
   (c) Send this to an agent/external tool for the heavy combinatorics?

4. **Should I also run `scripts/goal check all` or `bash scripts/remote-build.sh proof_in_the_book`**
   (full build) to check that my changes don't break anything else?

File: /Users/huangx/repos/proof_in_the_book/HANDOFF/oracle/QUESTION_03_02.md
