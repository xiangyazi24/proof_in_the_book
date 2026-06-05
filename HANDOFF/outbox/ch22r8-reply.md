Ch22 ROUND 8 reply

Implemented in `ProofsInTheBook/Chapter22Gurvits.lean`:

- STEP 1 positive case:
  - Added the positive all-degree coefficient invariant.
  - Proved it for row-linear products with strictly positive matrix entries.
  - Propagated it through `firstReduction`.
  - Used it to exclude degenerate sections in the stable/real-rooted specialization.
  - Proved `stable_allDegree_capacity_bound`.
  - Proved:
    ```lean
    theorem chapter22_positive (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
        (hpos : ∀ i j, 0 < A i j)
        (hA : A ∈ doublyStochastic ℝ (Fin n)) :
        (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent
    ```

- STEP 2 unconditional limit:
  - Added finite-sum/product permanent continuity:
    ```lean
    lemma permanent_tendsto_of_entrywise
    ```
  - Approximated an arbitrary doubly stochastic `A` by
    `Aθ N = (1 - θ N) • A + θ N • flatDoublyStochasticMatrix n`,
    with `θ N = (((N + 1 : ℕ) : ℝ)⁻¹)`.
  - Proved each `Aθ N` is doubly stochastic by convexity and strictly positive for `n ≥ 1`.
  - Applied `chapter22_positive` to each `Aθ N`.
  - Passed to the limit using entrywise convergence and `ge_of_tendsto`.
  - Proved:
    ```lean
    theorem chapter22_unconditional (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
        (hA : A ∈ doublyStochastic ℝ (Fin n)) :
        (n.factorial : ℝ) / (n : ℝ) ^ n ≤ A.permanent
    ```

Verified:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter22Gurvits.lean
grep -nE '\b(sorry|admit|axiom)\b' ProofsInTheBook/Chapter22Stable.lean ProofsInTheBook/Chapter22Gurvits.lean
```

The Lean check succeeds. The placeholder scan has no output.
