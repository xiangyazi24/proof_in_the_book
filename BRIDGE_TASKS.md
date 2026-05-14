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

Status:
- Submitted as `52a512cc` / seq 1.
- Completed.
- Useful returned next lemmas:
  - `not_mem_smoothNumbers_succ_of_large_prime_dvd`
  - `descFactorial_mem_smooth_of_no_large_prime`
  - `chapter03_not_smooth_of_hasPrimeFactorAbove`
- Heavy core remains:
  - `sylvester_descFactorial_not_smooth_book_core`

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

Status:
- Submitted as `700ae88d` / seq 2.
- Completed, but response was a duplicated Chapter03/Sylvester answer, not a
  Chapter19 answer.
- Requeued as `68d377af` / seq 3 with an explicit "Chapter19 only" prompt.
- `68d377af` completed with `[BRIDGE_ERROR] response timeout`; split the task
  into smaller Chapter19-only follow-ups.
- Requeued first-coefficient extraction subtask as `dac1dd49` / seq 4.
- Bridge restart erased `dac1dd49` from server memory, but Xiang pasted the
  delivered response manually.  Implemented the robust lemma
  `exists_first_nonzero_coeff_of_sub_C_eval_zero_ne_zero` and the shifted
  specialization in Chapter19.

### Task A3: Chapter20 Monsky/Sperner Layer

- File: `ProofsInTheBook/Chapter20.lean`
- Current local state:
  - `MonskyColor` has three colors.
  - `TrichromaticTriangle` is pairwise color inequality.
  - Only basic trichromatic/nontrichromatic lemmas are present.
- Heavy goal:
  - Propose one Lean-feasible finite combinatorial layer toward Monsky's
    theorem, preferably a Sperner-style boundary/counting lemma that does not
    require formal 2-adics yet.
- Desired answer:
  - Return concrete Lean theorem statements.
  - Keep the target local to finite triangles/coloring; do not attempt full
    geometric triangulation of the square.

Status:
- Submitted as `8b1aed53` / seq 5.
- Active delivery expected; no blocking poll.
- Bridge restart erased this task from server memory before local receipt;
  requeue required.
- Requeued after bridge restart as `6adccf76` / seq 1.
- `6adccf76` completed but returned a Chapter24/Herglotz answer, not Chapter20.
- Requeued with a shorter Chapter20-only prompt as `bfd68df6` / seq 3.
- `bfd68df6` completed with useful Chapter20 lemmas; implemented
  `RedGreenEdge`, `odd_redGreenEdges_iff_trichromatic`, and
  `redGreenEdges_zmod_two_eq_trichromatic`.

### Task A4: Chapter24 Herglotz Functional Equation Layer

- File: `ProofsInTheBook/Chapter24.lean`
- Current local state:
  - `cot_add_pi`, `cot_neg`, `cot_pi_add_one`, `cot_pi_one_sub`.
  - `reciprocal_add_one_sub` for the two singular rational terms.
- Heavy goal:
  - Propose the next small Lean lemma for the Herglotz trick, either a finite
    partial-sum rational functional equation or an abstraction of functions
    satisfying the required periodic/symmetry equations.
- Desired answer:
  - Return concrete theorem statements and Mathlib API hints.
  - Avoid infinite series unless the required summability API is named exactly.

Status:
- Submitted as `bb9ac388` / seq 6.
- Active delivery expected; no blocking poll.
- Bridge restart erased this task from server memory before local receipt;
  requeue required.
- Requeued after bridge restart as `2c682fe1` / seq 2.
- `2c682fe1` completed with useful Chapter24 lemmas; implemented
  `herglotz_cancel_of_periodic_odd`, `herglotz_add_cancel_of_periodic_odd`,
  and `cot_pi_herglotz_add_cancel`.

## 2026-05-14 Batch B

### Task B1: Chapter25 Buffon Linearity-To-Probability Layer

- File: `ProofsInTheBook/Chapter25.lean`
- Current local state:
  - `segmentExpectedCrossings d length = 2 * length / (π * d)`.
  - `curveExpectedCrossings` sums segment contributions.
  - `curveExpectedCrossings_eq_total_length` proves finite linearity.
- Heavy goal:
  - Propose one small Lean-feasible lemma connecting this finite linearity
    layer toward Buffon's needle probability, preferably assumptions for
    `0 < d`, `0 ≤ length`, `length ≤ d`, or a normalized probability value
    `2 * length / (π * d)`.
- Desired answer:
  - Chapter25 only.
  - Return concrete theorem statements and proof sketches.
  - Avoid measure theory unless the exact Mathlib APIs are named.

Status:
- Submitted as `68fb6e62` / seq 4.
- Active delivery expected; no blocking poll.
- Completed, but response was a duplicated Chapter20/Monsky answer, not
  Chapter25.
- Requeued as `f220a654` / seq 7 with a shorter Chapter25-only prompt and an
  explicit `WRONG_CHANNEL` guard.
- `f220a654` also returned the duplicated Chapter20/Monsky answer. Diagnosed
  stale-answer capture in `chatgpt-bridge` and pushed fix
  `extension: prevent stale answer capture`; the browser extension must be
  reloaded before more bridge proof tasks are trustworthy.
- Local fallback implemented `segmentExpectedCrossings_nonneg` and
  `segmentExpectedCrossings_le_one`.

### Task B2: Chapter29 GSR Riffle Label Distribution Layer

- File: `ProofsInTheBook/Chapter29.lean`
- Current local state:
  - `RiffleLabels a n := Fin n → Fin a`.
  - `pileOfLabel` and `pile_card_sum_eq_deck_size`.
  - `riffleLabels_card`.
- Heavy goal:
  - Propose one Lean-feasible finite combinatorial lemma connecting label
    assignments to an induced stable riffle order or pile-size vector.
- Desired answer:
  - Chapter29 only.
  - Return concrete theorem statements and proof sketches.
  - Keep it finite/combinatorial; avoid probability until the finite map is
    formalized.

Status:
- Submitted as `799bf07d` / seq 5.
- Active delivery expected; no blocking poll.
- Completed, but response was a duplicated Chapter20/Monsky answer, not
  Chapter29. Requeue separately after Chapter25 returns.
- Local fallback implemented the pile partition facts and
  `pileSizeVector_sum_eq_deck_size`.

### Task B3: Chapter30 LGV Cancellation Layer

- File: `ProofsInTheBook/Chapter30.lean`
- Current local state:
  - Determinant signed-permutation expansion.
  - Diagonal/off-diagonal-zero determinant case.
- Heavy goal:
  - Propose one small Lean-feasible finite lemma toward the LGV cancellation
    proof, preferably an abstract sign-reversing involution cancellation lemma
    for a finite sum over permutations/path families.
- Desired answer:
  - Chapter30 only.
  - Return concrete theorem statements and proof sketches.
  - Keep it algebraic/finite; do not attempt full lattice-path geometry.

Status:
- Submitted as `146026e6` / seq 6.
- Active delivery expected; no blocking poll.
- Completed, but response was a duplicated Chapter20/Monsky answer, not
  Chapter30. Requeue separately after Chapter25 returns.
