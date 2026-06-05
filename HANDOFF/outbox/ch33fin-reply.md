## 2026-06-05

Worked in `ProofsInTheBook/Chapter33Smetaniuk.lean`.

Verified:

```bash
PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter33Smetaniuk.lean
grep -nE '\b(sorry|admit|axiom)\b' \
  ProofsInTheBook/Chapter33Smetaniuk.lean ProofsInTheBook/Chapter33.lean
```

The Lean command exits `0`; the grep has no matches.

Closed:

- Added `SignedCell.principal` and proved that an improper Latin square with
  no improper cells yields a genuine proper Latin square:
  `isLatinSquare_signedPrincipalSquare_of_no_improper`.
- Proved preservation of prescribed cells for that principal square:
  `completes_signedPrincipalSquare_of_no_improper`.
- Added the proper shifted Smetaniuk bridge:
  `reverseSeedColumns`, `isLatinSquare_reverseSeedColumns`,
  `smetMainPartial_reverseSeedColumns_shifted`, and
  `shiftedCompletes_of_smetMainPartial_reverseSeedColumns`.
- Wired the proved proper core to the no-defect branch:
  `shiftedCompletable_of_properSeed` and
  `shiftedCompletable_of_no_improperSeed`.

Not closed:

- I did not prove `ImproperSmetaniukExtensionStatement N` for the one-defect
  case.
- Exact remaining mathematical/Lean goal: for `N ≥ 3`, `Q` weak upper,
  `Lstar : Fin N → Fin N → SignedCell (Fin N)`, `ImproperLatinSquare Lstar`,
  `ImproperlyExtends Q Lstar`, and
  `signedImproperCells Lstar = {(r,c)}` with
  `Lstar r c = SignedCell.improper x y z`, construct
  `L : Fin (N+1) → Fin (N+1) → Fin (N+1)` satisfying
  `ShiftedCompletes Q L`.
- The attempted reduction through the principal square only closes the
  `signedImproperCells Lstar = ∅` branch. In the one-defect branch, the
  principal square has one row and one column with a missing positive symbol and
  a duplicated negative symbol, so `SmetBackDiagonalCompletableCore` cannot be
  applied without the promised defect-tracking switch or an additional
  preprocessing/properization lemma that preserves the weak-upper prescribed
  cells.

No `sorry`, `admit`, or `axiom` was introduced.
