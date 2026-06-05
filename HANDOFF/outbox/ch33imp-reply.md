## 2026-06-05

Worked in `ProofsInTheBook/Chapter33Smetaniuk.lean`.

Closed without `sorry`/`axiom`:

- Added the signed-cell layer for improper Latin squares:
  `SignedCell`, `SignedCell.coeff`, positive occurrence, `ImproperLatinSquare`,
  `ImproperlyExtends`, `ImproperCompletionTheorem`, and the proper-square
  embedding.
- Proved the 2x2 improper restore.  Main endpoints:

```lean
theorem improperLatinSquare_restoredSignedSquare
theorem improperlyExtends_restoredSignedSquare
theorem improperCompletion_restore_one
theorem evans_to_improperCompletion
```

This proves the formal `E_N => I_N` step.

- Added the strict-to-weak shrink for strictly-above-diagonal squares:
  `strictShrink`, `isPartialLatin_strictShrink`,
  `filledCells_strictShrink_card_le_erase_corner`, and
  `strictShrink_weakUpper_of_strictUpper`.
- Added the step-6 skeleton all the way through row/column/symbol
  normalization and induction:

```lean
theorem strictUpper_completion_of_improperExtension
theorem latinSquareCompletion_step_of_improperExtension
theorem chapter33_unconditional_of_improperExtensionStatements
```

So the remaining frontier is isolated as:

```lean
def ImproperSmetaniukExtensionStatement (N : Nat) : Prop :=
  forall Q : Fin N -> Fin N -> Option (Fin N),
    IsPartialLatin Q ->
      WeakUpperTriangle Q ->
        forall Lstar : Fin N -> Fin N -> SignedCell (Fin N),
          ImproperLatinSquare Lstar ->
            ImproperlyExtends Q Lstar ->
              exists L : Fin (N + 1) -> Fin (N + 1) -> Fin (N + 1),
                ShiftedCompletes Q L
```

Not closed:

- I did not prove the actual improper Smetaniuk extension generalizing
  `SmetBackDiagonalCompletableCore`.  The current proper switching proof is
  still specialized to a proper seed `L0 : Fin N -> Fin N -> Fin N` with
  `IsLatinSquare L0`; the signed one-defect invariant needed to absorb
  `[x+y-z]` through the column-switching process is not formalized.
- Consequently there is still no unconditional theorem named
  `chapter33_unconditional : forall n, LatinSquareCompletionTheorem n`.
  What is now proved is the exact conditional closure from the isolated
  improper-extension statement.

Verification:

```bash
PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter33Smetaniuk.lean
grep -nE '\b(sorry|admit|axiom)\b' \
  ProofsInTheBook/Chapter33Smetaniuk.lean ProofsInTheBook/Chapter33.lean
```

The Lean command exits `0`; the grep has no matches.  I did not run full
`lake build`.
