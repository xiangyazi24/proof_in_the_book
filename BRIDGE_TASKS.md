# ChatGPT Bridge Task Queue

This file records heavy proof tasks to outsource through chatgpt-bridge.
Local Codex should keep these tasks compact, self-contained, and avoid doing
the hard proof search locally.

Bridge channel for the current proof-in-the-book workflow: `ssem`.

## 2026-05-14 Batch A

### Task A1: Chapter03 Sylvester Smoothness Gap

- File: `ProofsInTheBook/Chapter03.lean`
- Current local reductions:
  - `HasPrimeFactorAbove k m := ∃ p, k < p ∧ p.Prime ∧ p ∣ m`
  - `exists_large_prime_dvd_choose_of_descFactorial`
  - `not_mem_smoothNumbers_succ_iff_hasPrimeFactorAbove`
  - `exists_large_prime_dvd_choose_of_descFactorial_not_smooth`
- Heavy goal:
  - Find a Lean-feasible route to prove the missing non-smoothness statement
    behind general Sylvester:
    `n.descFactorial k ∉ (k + 1).smoothNumbers` under hypotheses comparable to
    `0 < k` and `2 * k ≤ n`, or propose the exact intermediate theorem(s)
    needed to match the book proof.
- Desired answer:
  - Do not return prose only.
  - Return concrete theorem statements and proof sketches tied to existing
    Mathlib APIs (`Nat.smoothNumbers`, `Nat.descFactorial`, `Nat.factorization`,
    `primeFactorsList`, etc.).
  - If full proof is too hard, return the smallest next lemma that should
    compile and materially advances the reduction.

### Task A2: Chapter19 Minimum-Modulus Proof Layer

- File: `ProofsInTheBook/Chapter19.lean`
- Current local reductions:
  - `shiftedPolynomial p z₀ := p.comp (X + C z₀)`
  - evaluation, constant coefficient, and root-transfer lemmas for shifted
    polynomials.
- Heavy goal:
  - Identify a Lean-feasible next lemma for the minimum-modulus proof of FTA:
    either the local norm-decrease lemma after the first nonzero coefficient,
    or a precise theorem statement for obtaining the first nonzero term in
    `shiftedPolynomial p z₀ - C (p.eval z₀)`.
- Desired answer:
  - Return concrete Lean theorem statements first.
  - Prefer a small lemma that can be inserted into Chapter19 and built before
    attempting the full fundamental theorem of algebra.
