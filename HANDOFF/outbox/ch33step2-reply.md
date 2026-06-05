## 2026-06-04

Read:

- `HANDOFF/TASK_Ch33step2.md`
- `HANDOFF/CH33_NORMALIZATION_RESOLVED.md`

Worked in `ProofsInTheBook/Chapter33Smetaniuk.lean`; I did not change the Lean
source.  The file currently checks with:

```bash
PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter33Smetaniuk.lean
```

It exits `0` with only existing linter warnings.

Blocker:

The resolved normalization blueprint's counting step is false for the existing
`smetBackPartial` interface.  After applying `exists_perm_strictly_above`,
reversing columns, and choosing an unused symbol as `Fin.last N`, every original
filled cell lies in the copied region `i.val + j.val < N`.  But restricting that
copied region to order `N` keeps all original `N = n - 1` cells; it does not
give `≤ N - 1 = n - 2` cells for the IH.

I checked the failure with a concrete Lean `#eval` example: order `5`, four
entries in row `0` at columns `1,2,3,4`, symbols `0,1,2,3`, with symbol `4`
unused.  The original filled-cell count is `4`; after column reversal and
restriction to `Fin 4 × Fin 4` via the copied-region map, the filled-cell count
is still `4`, not `≤ 3`.

The check was:

```lean
import ProofsInTheBook.Chapter33Smetaniuk
open ProofsInTheBook.Chapter33

def P5 : Fin 5 → Fin 5 → Option (Fin 5) :=
  fun i j =>
    if i = (0 : Fin 5) then
      if j = (1 : Fin 5) then some (0 : Fin 5)
      else if j = (2 : Fin 5) then some (1 : Fin 5)
      else if j = (3 : Fin 5) then some (2 : Fin 5)
      else if j = (4 : Fin 5) then some (3 : Fin 5)
      else none
    else none

#eval (filledCells P5).card
#eval (filledCells (fun i : Fin 4 => fun j : Fin 4 =>
  ((reverseColumnsPartial P5 (Fin.castSucc i) (Fin.castSucc j)).bind dropLastSymbol))).card
```

Output:

```text
4
4
```

So the requested wiring cannot be completed from the stated ingredients
`exists_perm_strictly_above + unused symbol + smetBackDiagonal_completable`:
the IH available from `EvansExactCardinalityCase`/`LatinSquareCompletionTheorem`
at order `N` applies to at most `N - 1` cells, while the normalized shrink can
still have exactly `N` cells.

What would be needed instead is an additional lemma stronger than the current
interface, for example one of:

- a normalization that designates at least one existing filled cell as part of
  the back diagonal, so the shrink actually deletes a filled cell; this is the
  old singleton-symbol route and is blocked by multi-occurrence symbols, or
- a stronger completion theorem for the order-`N` restricted triangular partial
  square with `N` cells, or
- a strengthened Smetaniuk core that completes `smetBackPartial L0` while also
  enforcing the extra row/column constraints obtained after deleting a
  guaranteed nonempty row or column.

No `sorry`, `axiom`, or `admit` was introduced.
