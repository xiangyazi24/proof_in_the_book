# QUESTION 03 03: Steps 3-4 — distinctness + classification strategy

## (i) What's done

Steps 1-2 are complete (committed, 0 sorry):
- `pow_l_dvd_one_factor_of_descFactorial` (concentration lemma, induction-on-k)
- `erdos_step1_n_gt_k_sq` (n > k²)
- `lPowerFreePart` / `lPowerRoot` definitions
- `self_eq_lPowerFreePart_mul_lPowerRoot_pow` (decomposition: m = a * b^l)

Build: 0 errors, 1 sorry in `chapter03_erdos`.

## (ii) Remaining: Steps 3-4

### Step 3 — a_j distinctness

Book's argument:
- For each j < k, decompose n-j = a_j * b_j^l (using Step 2 machinery).
- Suppose a_i = a_j = a for i < j. Then:
  (n-i)-(n-j) = j-i = a*(b_i^l - b_j^l)
- Since n-i > n-j, b_i > b_j, so b_i ≥ b_j + 1.
- Key inequality: (m+1)^l - m^l ≥ l*m^{l-1} for m ≥ 1.
  This holds by binomial theorem but formalizing in ℕ requires
  `Nat.add_one_pow_sub_pow` or explicit geometric sum.
- Then: j-i = a*(b_i^l - b_j^l) ≥ a*l*b_j^{l-1} = l*(a*b_j^l)/b_j = l*(n-j)/b_j
- Since n > k² (Step 1) and n-j > k²-k+1, we get a contradiction.

### Step 4a — l=2 case

- From Step 3: a_j's are k distinct l-th-power-free positive integers.
- The product a_0*...*a_{k-1} divides k! (Legendre counting in the book).
  This gives {a_j} ⊆ {1,...,k}.
- Since there are k distinct values in a set of size k, {a_j} = {1,...,k}.
- For k ≥ 4, 4 ∈ {a_j}, but 4 = 2² isn't squarefree → contradiction.

### Step 4b — l≥3 case

- More complex: uses {1,2,4} and algebraic identity.

In total: Steps 3+4 estimated 130-200 LOC. The algebraic inequality
`(m+1)^l - m^l ≥ l*m^{l-1}` is the heart of Step 3.

## (iii) Questions

1. **The inequality**: Should I use `Nat.geom_sum_eq` (which exists for
   a^n - b^n = (a-b)*Σ a^i b^{n-1-i}) or prove `(m+1)^l - m^l ≥ l*m^{l-1}`
   by induction on l? Which is more Lean-friendly?

2. **The product-divisibility argument** (a_0*...*a_{k-1} | k!):
   This uses Legendre's formula bounding prime exponents. Is there a
   Mathlib lemma like `padicValNat_factorial` that I can lean on, or
   do I need to build this from scratch?

3. **Should I focus on l=2 only** (simpler: a_j squarefree, 4=2² contradiction)
   and leave l≥3 as a documented gap, or attempt the general case?

4. **Scope**: Given that Step 3 alone is 50-80 LOC of careful algebra,
   should I dispatch Steps 3+4a to an agent/subprocess while I work on
   other chapters?

File: /Users/huangx/repos/proof_in_the_book/HANDOFF/oracle/QUESTION_03_03.md
