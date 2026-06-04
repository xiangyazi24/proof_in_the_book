# QUESTION 03 04: How to prove `k*k < 4*(k*k - k + 2)` for k ≥ 4 in ℕ

## (i) What's been tried

Both `nlinarith` and `omega` fail on this inequality because it involves
multiplication of variables (`k*k`). Hand-rolled proofs using:

- Factorization: `4*(k²-k+2) = k² + (3k²-4k+8)` and `3k²-4k+8 ≥ 8 > 0`
- Squared comparison: `(2k)² < 4*(2*(k²-k+2))` etc.
- Case analysis on k=4 base + monotonicity

All hit the same wall: ℕ subtraction (`k² - k`, `3k² - 4k`) truncation
makes the algebraic identity `4*(k²-k+2) = k² + (3k²-4k+8)` provable
only with exactness hypotheses (`3k² ≥ 4k`), and `omega` can't close
the ring identities after those hypotheses are added.

The inequality `3*k*k ≥ 4*k` for k ≥ 2 is easy, and the subtraction
exactness condition is satisfiable. But chaining everything together
in a `calc` block with `omega` on polynomial terms fails.

## (ii) Specific ask

What is the Lean 4 idiom for proving `k*k < 4*(k*k - k + 2)` for
`k ≥ 4` in ℕ? I need either:
- The right combination of `arith` tactics
- A known Mathlib lemma that handles this
- A clean proof strategy that avoids the subtraction pitfalls

## (iii) Context

This inequality is the last piece of `lPowerFreePart_injective_l2`
(the a_j distinctness lemma for l=2). The proof structure is sound —
it needs this inequality to bound `n-j ≥ k²-k+2` → `4*(n-j) > k²`.

File: /Users/huangx/repos/proof_in_the_book/HANDOFF/oracle/QUESTION_03_04.md
