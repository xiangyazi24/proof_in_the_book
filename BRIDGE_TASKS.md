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
- Requeued a smaller sign-reversing-cancellation prompt as `da9681b0` / seq 1
  after the bridge stale-answer fix. It returned the correct Chapter30 content.
- Local implementation added `sum_eq_neg_self_of_sign_reversing_equiv` and
  `two_nsmul_sum_eq_zero_of_sign_reversing_equiv`; the final proof needed
  `nth_rewrite 1 [h]` instead of rewriting both summands.
- Follow-up no-two-torsion prompt `5de41f03` / seq 2 was picked up by `ssem`
  but later disappeared from `/api/result`, consistent with a bridge restart
  or in-memory queue clear.
- Requeued no-two-torsion prompt as `f469676a` / seq 1. It completed quickly
  after the restart, but repeated the previous answer. Local API search found
  the usable specialization: `[IsAddTorsionFree R]` plus
  `nsmul_eq_zero_iff`.
- Follow-up abstract-bad-family split prompt `9102ae04` / seq 2 also completed
  quickly but repeated the same cancellation lemma, so the `ssem` transport is
  healthy while the current ChatGPT conversation context is stale/repetitive.
- After refreshing the `ssem` tab, nonce task `722201e8` returned the exact
  requested marker, confirming stale-answer capture was fixed.
- Fresh split prompt `2e2a18ea` / seq 4 returned a useful good/bad split lemma
  tagged `FRESH_SPLIT_20260514`; local proof required replacing an invalid
  `rfl` after `Finset.sum_subtype` with `simp [badSet]`.
- Certificate packaging prompt `a5671c20` / seq 5 returned a useful
  `BadInvolutionCertificate` wrapper tagged `FRESH_CERT_20260514`; it compiled
  locally without changes.

## 2026-05-14 Batch C

### Task C1: Chapter03 Sylvester Smoothness Next Lemma

- File: `ProofsInTheBook/Chapter03.lean`
- Current local state:
  - `HasPrimeFactorAbove k m`.
  - `not_mem_smoothNumbers_succ_iff_hasPrimeFactorAbove`.
  - `exists_large_prime_dvd_choose_of_descFactorial_not_smooth`.
- Heavy gap:
  - Prove or reduce `n.descFactorial k ∉ (k + 1).smoothNumbers` under
    Sylvester-style hypotheses such as `0 < k` and `2 * k ≤ n`.
- Desired answer:
  - Chapter03 only.
  - Return the next smallest Lean-feasible lemma using `Nat.factorization`,
    `Nat.smoothNumbers`, or `Nat.descFactorial`; do not attempt a large
    opaque proof.

Status:
- Submitted as `9eabd2c5` / seq 6, tagged `CH03_FRESH_20260514`.
- Completed with `[BRIDGE_ERROR] response timeout`.
- Local fallback implemented:
  - `sub_dvd_descFactorial_of_lt`.
  - `sub_mem_smoothNumbers_of_descFactorial_mem`.

### Task C2: Chapter03 Smooth Factor Follow-Up

- File: `ProofsInTheBook/Chapter03.lean`
- Current local state:
  - Smoothness of `n.descFactorial k` passes to each factor `n - i`, `i < k`.
- Desired answer:
  - Chapter03 only.
  - Return a smaller bound/factorization lemma about `(k+1)`-smooth factors
    that can compile independently and move toward the Sylvester
    non-smoothness contradiction.

Status:
- Submitted as `8471a107` / seq 7, tagged `CH03_FACTOR_20260514`.
- Completed with `[BRIDGE_ERROR] response timeout`.
- Local fallback implemented:
  - `not_hasPrimeFactorAbove_sub_of_descFactorial_mem_smooth`.
  - `prime_factor_le_of_dvd_sub_of_descFactorial_mem_smooth`.
  - `descFactorial_not_smooth_of_sub_hasPrimeFactorAbove`.
  - `descFactorial_not_smooth_of_large_prime_dvd_sub`.

### Task C3: Chapter03 Statement-Only Next Step

- File: `ProofsInTheBook/Chapter03.lean`
- Purpose:
  - Since proof-producing Chapter03 bridge tasks timed out, ask for exactly
    one next theorem statement only.
- Desired answer:
  - Chapter03 only.
  - One small independently useful theorem statement toward the Sylvester
    smoothness contradiction.

Status:
- Submitted as `49c190b1` / seq 8, tagged `CH03_STATEMENT_ONLY_20260514`.
- Still processing after repeated polls; `/api/active?channel=ssem` shows this
  task occupying the channel. No local artifact applied yet.
- Completed with `[BRIDGE_ERROR] response timeout`.

## 2026-05-14 Batch D

### Task D1: Chapter04 Zagier Involution Skeleton

- File: `ProofsInTheBook/Chapter04.lean`
- Current local state:
  - Necessity modulo four is proved.
  - Brahmagupta identity is available via `Nat.sq_add_sq_mul`.
  - Sufficiency currently uses `Nat.Prime.sq_add_sq`; the book-style Zagier
    finite involution argument remains only in comments.
- Desired answer:
  - Chapter04 only.
  - Return the next smallest finite/involution lemma or data structure toward
    Zagier's proof; do not attempt the full theorem.

Status:
- Submitted as `fab126a1` / seq 9, tagged `CH04_ZAGIER_20260514`.
- Completed with `[BRIDGE_ERROR] response timeout`.
- Local fallback added `ZagierTriple`, `ZagierTriple.swapYZ`, and
  `ZagierTriple.swapYZ_fixed_iff`.

### Task D2: Chapter04 Fixed Swap Gives Representation

- File: `ProofsInTheBook/Chapter04.lean`
- Current local state:
  - `ZagierTriple.swapYZ_fixed_iff` characterizes fixed points by `y = z`.
- Desired answer:
  - Chapter04 only.
  - Prove that a fixed point of `swapYZ` yields a representation of `p` as a
    sum of two squares, taking `a = x` and `b = 2*y`.

Status:
- Submitted as `8927827d` / seq 10, tagged `CH04_FIXED_REPR_20260514`.
- Completed with `[BRIDGE_ERROR] response timeout`.
- Local fallback implemented `ZagierTriple.exists_sq_add_sq_of_swapYZ_fixed`.

## 2026-05-14 Batch E

### Task E1: Chapter04 Fintype Infrastructure for Zagier Triples

- File: `ProofsInTheBook/Chapter04.lean`
- Current local state:
  - `ZagierTriple p` is a structure over `Fin (p + 1)` coordinates with
    positivity/equation proof fields.
  - The simple swap involution is defined, fixed points are characterized by
    `y = z`, and fixed points yield sum-of-two-squares representations.
- Desired answer:
  - Chapter04 only.
  - Give Lean code likely to compile for `Fintype (ZagierTriple p)`, preferably
    by equivalence with a subtype of `(Fin (p + 1) × Fin (p + 1) × Fin (p + 1))`
    satisfying the positivity/equation constraints.
  - Mention whether `DecidableEq` derivation is feasible with proof fields.

Status:
- Submitted as `d97e0b1d` / seq 11, tagged `CH04_FINTYPE_20260514`.
- Completed with `[BRIDGE_ERROR] response timeout`.
- Local fallback implemented `ZagierTriple.instFintype`.

### Task E2: Chapter04 First Zagier Involution Branch

- File: `ProofsInTheBook/Chapter04.lean`
- Current local state:
  - `ZagierTriple p` is finite.
  - The generic odd-cardinality involution fixed-point lemma is proved and
    applied to `swapYZ`.
  - The canonical triple `(1, 1, k)` is constructed for `4k + 1`.
- Desired answer:
  - Chapter04 only.
  - Under `h : t.x.val < t.y.val - t.z.val`, construct the first branch of
    Zagier's piecewise involution with coordinates `(x + 2z, z, y - x - z)`.
  - Return Lean code likely to compile for this branch only, including the
    positivity, Fin bounds, and equation proof.

Status:
- Submitted as `94f69aae` / seq 12, tagged `CH04_ZAGIER_BRANCH1_20260514`.
- Completed with `[BRIDGE_ERROR] response timeout`.
- Local fallback implemented `ZagierTriple.branchOne`.

### Task E3: Chapter04 Total Zagier Map Assembly

- File: `ProofsInTheBook/Chapter04.lean`
- Current local state:
  - `ZagierTriple.branchOne`, `branchTwo`, and `branchThree` construct the
    three local branches of Zagier's piecewise map.
- Desired answer:
  - Chapter04 only.
  - Define a total `zagierMap : ZagierTriple p → ZagierTriple p` by decidable
    case split using the three local branch constructors.
  - Do not prove involutivity yet.
  - If the exact split needs equality-boundary handling, identify the minimal
    extra branch or lemma required.

Status:
- Submitted as `c761d828` / seq 13, tagged `CH04_ZAGIER_TOTAL_MAP_20260514`.
- Still processing after local fallback work.
- Local fallback implemented `ZagierTriple.zagierMapOfPrimeNeTwo`, with
  boundary exclusions `ne_y_sub_z_of_prime` and
  `ne_two_mul_y_of_prime_ne_two`.
