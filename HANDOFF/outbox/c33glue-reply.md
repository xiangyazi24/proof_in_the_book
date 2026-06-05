## 2026-06-05

Worked only in `ProofsInTheBook/Chapter33Smetaniuk.lean` plus this outbox note.

Implemented the book-route glue:

- B: `exists_symbol_occursExactlyOnce_of_many_used`, via an injection
  `usedSymbols P × Fin 2 ↪ filledCells P` under the negation of singleton
  occurrence.
- C: `exists_perm_singleton_diagonal_strictly_above` and
  `exists_relabel_singleton_smetaniukTriangularNormalized`, using the peeling
  normalization with row/column/symbol relabeling.
- D: generalized the Smetaniuk normalized step to arbitrary diagonal singleton:
  `smetMainPartial_diagonal`,
  `filledCells_smetMainKeepLastShrink_card_le_erase_newSymbol`,
  `smetMainKeepLastShrink_step_of_mainDiagonalNewSymbol`, and
  `smetaniuk_normalized_of_IH`.
- Added the Ryser interface:
  `ryser_few_elements_completes`.
- Added the endpoint:
  `chapter33_unconditional_of_ryser
    (hR : ∀ n, ryser_few_elements_completes n) :
    ∀ n, LatinSquareCompletionTheorem n`.

Verification:

```bash
PATH=/home/xhuan5/.elan/toolchains/leanprover--lean4---v4.30.0-rc2/bin:$PATH \
  lake env lean ProofsInTheBook/Chapter33Smetaniuk.lean

grep -nE '\b(sorry|admit|axiom)\b' ProofsInTheBook/Chapter33Smetaniuk.lean
```

Lean exits 0. The grep has no matches.
