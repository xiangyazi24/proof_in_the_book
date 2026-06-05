## 2026-06-04

Worked in `ProofsInTheBook/Chapter33Smetaniuk.lean`.

Input issue: `HANDOFF/TASK_Ch33form.md` exists and was read, but
`HANDOFF/CH33_NORMALIZATION_RESOLVED.md` is not present in this checkout.  I
confirmed with `find HANDOFF -maxdepth 4 -type f` and a repo grep for the file
name.  So the resolved normalization blueprint itself was unavailable.

Closed:

- Proved the requested pure combinatorial crux:

```lean
theorem exists_perm_strictly_above {n : ℕ}
    (S : Finset (Fin n × Fin n)) (hS : S.card < n) :
    ∃ σ τ : Equiv.Perm (Fin n), ∀ p ∈ S, σ p.1 < τ p.2
```

The proof is the requested strong induction on `n`: choose an empty column,
choose a nonempty row, send both to rank `0`, recurse on the deleted
`(n-1) × (n-1)` grid, and lift recursive ranks by `Fin.succ`.

- Added the shrink that is compatible with `smetMainPartial` and preserves
  constraints in the original last column:

```lean
def smetMainKeepLastShrink
lemma isPartialLatin_smetMainKeepLastShrink
lemma filledCells_smetMainKeepLastShrink_card_le_erase_diag
theorem smetMainKeepLastShrink_step
lemma smetMainPartial_extends_of_keepLastShrink_completion
```

- Wired the proved switching core to the triangular normalized induction step:

```lean
theorem smetaniuk_exact_normalized_of_IH {N : ℕ} (hN : 3 ≤ N)
    (hIH : LatinSquareCompletionTheorem N)
    ... :
    ∃ L : Fin (N + 1) → Fin (N + 1) → Fin (N + 1), Completes P L
```

Verification:

```bash
/data/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter33Smetaniuk.lean
grep -nE '\b(sorry|admit|axiom|native_decide)\b' \
  ProofsInTheBook/Chapter33Smetaniuk.lean ProofsInTheBook/Chapter33.lean
```

The Lean command exits `0`; the grep has no matches.  I did not run full
`lake build`.

Not closed:

- `evansExactCardinalityCase_all` and `chapter33_unconditional` are still not
  present as unconditional theorems.
- The remaining missing piece is exactly the absent resolved normalization:
  converting a bare exact partial Latin square to the Smetaniuk induction
  invariant without assuming a singleton symbol.  The older
  `MainDiagonalNewSymbol` invariant still requires a genuine special cell
  using the new symbol; the current checkout does not contain the promised
  `unused symbol + positional permutation` blueprint explaining the replacement
  invariant and final wiring.
