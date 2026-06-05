## 2026-06-04

Worked in `ProofsInTheBook/Chapter33Smetaniuk.lean`.

Closed:

- Replaced the old `SmetBackDiagonalCompletableCore : Prop` frontier with a
  proved theorem:

```lean
theorem SmetBackDiagonalCompletableCore {N : ℕ} (hN : 3 ≤ N)
    (L₀ : Fin N → Fin N → Fin N) (hL₀ : IsLatinSquare L₀) :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
      Completes (smetBackPartial L₀) L
```

- Formalized the switching construction used in the proof:
  `switchReach`, `smetSwitchColumn`, the row/column injection preservation
  lemmas, `smetRectInitial`, `smetRectStep`, `smetRectStage`, and
  `SmetRectStageInvariant`.
- The construction fills columns `1..N-1` by swapping reachable rows with the
  holding column `N`, proves the first `N` rows form a Latin rectangle, then
  applies the existing `latin_rectangle_extend_one` to add the last row.
- Updated `smetMainPartial_completable_of_core` so it uses the theorem directly,
  with no core hypothesis.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter33Smetaniuk.lean
grep -nE '\b(sorry|admit|axiom|native_decide)\b' ProofsInTheBook/Chapter33Smetaniuk.lean
```

The Lean command exits `0`; the grep has no matches.  I did not run `lake build`.

Not closed:

- `evansExactCardinalityCase_all` and `chapter33_unconditional` are still not
  present as unconditional theorems.
- The remaining obstacle is upstream of the proved core: the current scaffold
  still only records `SmetaniukExactNormalizedStatement` as a `Prop`, and the
  requested reduction from an arbitrary exact partial Latin square to the
  strengthened triangular normalized invariant is not in the file.
- There is also a specification issue in the handoff text: from
  `|filled P| = n - 1 < n` one gets an unused symbol, but not necessarily a
  uniquely occurring symbol.  For example, the symbol-count multiset
  `{2, 2, 0, 0, 0}` at order `5` has no singleton symbol.  The stated
  `MainDiagonalNewSymbol` invariant requires exact singleton occurrence, so
  that normalization cannot be derived from the quoted pigeonhole claim alone.

