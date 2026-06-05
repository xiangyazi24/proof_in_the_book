## 2026-06-04

Code changes are limited to `ProofsInTheBook/Chapter33.lean`; this report is appended here.

What is now formally closed:

- Added `EvansNormalizedCellCase`, a named Prop wrapper for the existing normalized-cell exact-cardinality subgoal.
- Added `evansExactCardinalityCase_of_normalizedCellCase`, a direct wrapper around the existing relabeling/normalization theorem.
- Added `evansExactCardinalityCase_all_of_normalized_ge_four`: all orders reduce to the normalized last-cell case in orders `n >= 4`; orders `n <= 3` are discharged by the existing `evansExactCardinalityCase_le_three`.
- Added `chapter33_unconditional_of_normalized_ge_four`: the same normalized `n >= 4` subgoal implies the full Chapter 33 completion theorem for all orders, using the existing exact-to-`<=` padding reduction.

The requested unqualified

```lean
theorem evansExactCardinalityCase_all : ∀ n, EvansExactCardinalityCase n
theorem chapter33_unconditional : ∀ n, LatinSquareCompletionTheorem n
```

are not added yet, because the remaining missing theorem is exactly:

```lean
∀ n (hnpos : 0 < n), 4 ≤ n →
  EvansNormalizedCellCase n
    (lastIndex n hnpos) (lastIndex n hnpos) (lastIndex n hnpos)
```

That normalized case still requires the genuine Smetaniuk switching/diagonal construction:

- place the last symbol on a legal partial transversal through empty cells;
- delete/reduce to the order-`n - 1` partial square with at most `n - 2` prescribed cells;
- lift the order-`n - 1` completion back to order `n`;
- verify the inserted symbol, rows, columns, and prescribed normalized cell.

The direct Hall row-fill route still blocks for the same formal reason recorded in the file: `extend_partialLatin_empty_row_with_card` adds exactly `n` cells, so from an exact state with `n - 1` filled cells the next state has `2*n - 1` filled cells. The sparse Hall lemmas (`chapter33_hall_condition`, `latin_square_completion_step_from_partial`) require the original `<= n - 1` bound, so they cannot be iterated after one complete row is filled. The missing ingredient is not another Hall invocation; it is the Smetaniuk switching lemma that keeps the reduction inside the smaller order.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter33.lean
grep -nE '\b(sorry|admit|axiom|native_decide)\b' ProofsInTheBook/Chapter33.lean
```

The Lean command exits `0`. The grep has no matches. I did not run `lake build`.
