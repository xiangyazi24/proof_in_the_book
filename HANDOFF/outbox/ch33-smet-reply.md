## 2026-06-04

Created `ProofsInTheBook/Chapter33Smetaniuk.lean`; did not modify
`ProofsInTheBook/Chapter33.lean`.

Input issue: `HANDOFF/TASK_Ch33_Smetaniuk.md` exists and was read, but
`HANDOFF/CH33_SMETANIUK_SWITCHING.md` is not present in this checkout.  I
confirmed with `find` over the repo; there is no Smetaniuk/switching blueprint
file to transcribe.

What is formally closed in the new file:

- Triangular normalization predicates:
  `SymbolOccursExactlyOnce`, `StrictUpperTriangle`, `MainDiagonalNewSymbol`,
  `SmetaniukTriangularNormalized`.
- Basic uniqueness consequences of the main-diagonal new symbol.
- Column reversal from main-diagonal to back-diagonal coordinates:
  `reverseColumnsPartial`, preservation of `IsPartialLatin`, filled-cell
  cardinality, and the strict-upper-triangle-to-back-lower-triangle inequality.
- Strengthened triangular side facts: column `0` is empty and the last row has
  no non-special entries.
- Step 1 reduction in back-diagonal coordinates:
  `smetShrink`, `isPartialLatin_smetShrink`,
  `filledCells_smetShrink_card_le_erase_backCorner`, `smetShrink_step1`, and
  `smetMainShrink_completes_from_IH`.
- Canonical Smetaniuk partial squares:
  `smetBackPartial`, `smetMainPartial`, `isPartialLatin_smetBackPartial`,
  `isPartialLatin_smetMainPartial`, `smetMainPartial_last_last`.
- Completion transfer under column reversal:
  `reverseColumnsPartial_completion_iff`,
  `smetMainPartial_completable_of_smetBackPartial_completable`.
- The remaining hard lemma is recorded only as a `Prop`, not as an unproved
  theorem:

```lean
def SmetBackDiagonalCompletableCore : Prop :=
  ∀ {N : ℕ}, 3 ≤ N →
    ∀ L₀ : Fin N → Fin N → Fin N,
      IsLatinSquare L₀ →
        ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1),
          Completes (smetBackPartial L₀) L
```

Exact blocker:

The missing proof is the Smetaniuk switching core above: the row-sequence /
value-sequence construction that completes `smetBackPartial L₀` by filling
columns `0..N-1` with the required switches, then using the Latin-rectangle
extension for the last column.

There is a second, more local place where this core is necessary.  From the IH
we can prove:

```lean
∃ L₀ : Fin N → Fin N → Fin N,
  Completes (smetShrink (reverseColumnsPartial P)) L₀
```

but this does not by itself prove:

```lean
ExtendsPartial P (smetMainPartial L₀)
```

In the branch `P i (Fin.last N) = some a`, `a ≠ Fin.last N`, the main square is
checked in back coordinates at column `0`.  The shrink deletes back column `0`,
so `Completes (smetShrink ...) L₀` gives no constraint on the needed value
`L₀ ⟨i.val, _⟩ 0`.  The exact remaining goal after unfolding is a value in the
deleted column of `L₀`; this is precisely what the switching construction must
force.

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter33Smetaniuk.lean
grep -nE '\b(sorry|admit|axiom|native_decide)\b' ProofsInTheBook/Chapter33Smetaniuk.lean
```

The Lean command exits `0`; the grep has no matches.  I did not run
`lake build`.
