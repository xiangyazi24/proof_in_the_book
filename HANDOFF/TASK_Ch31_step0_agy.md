# TASK Ch31 sublemma: round-trip at step 0

Both your previous lemmas built clean. Next: prove that pruferEncode applied
to pruferDecode reproduces position 0 of the code.

## Background (now available)

```lean
theorem pruferDecode_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) (v : Fin n) :
    ((pruferDecode hn s).1).degree v = countOccurrences s (n - 2) v + 1

theorem pruferDecode_isLeaf_iff (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) (v : Fin n) :
    v ∈ treeLeaves (pruferDecode hn s) ↔ isLeafInPrufer s v

theorem smallestTreeLeaf_pruferDecode ...
```

## Your task

Append two more theorems to `scratch_ch31_inverse.lean`:

### Theorem A: nextLeaf_0 identification

Show that the smallest tree-leaf of `pruferDecode hn s` is in fact the
specific `nextLeaf` chosen at step 0 of `pruferDecodeAux`. Per the existing
`pruferDecodeAux_succ_val_2` (line ~32) lemma's structure:

```lean
private theorem smallestTreeLeaf_eq_nextLeaf0 (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (hge : n ≥ 3) :  -- non-trivial code length
    -- After step 0, the chosen nextLeaf (extracted via the construction) equals
    -- smallestTreeLeaf of the decoded tree.
    sorry
```

Actually, prove a more useful form: nextLeaf_0 has the explicit definition
`(state.1.filter (...)).min'` from `pruferDecodeAux_succ_val_2 hn s 0 _`.
Show that this equals `smallestTreeLeaf n hn (pruferDecode hn s)`.

The cleanest packaging is probably:

```lean
private theorem smallestTreeLeaf_eq_min_filter (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    smallestTreeLeaf n hn (pruferDecode hn s) ∈
    (Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)) ∧
    ∀ v ∈ (Finset.univ.filter (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)),
      smallestTreeLeaf n hn (pruferDecode hn s) ≤ v
```

This is a direct consequence of `smallestTreeLeaf_pruferDecode` and `Finset.min'_mem`
+ `Finset.min'_le`.

### Theorem B: degree-1 vertex has unique neighbor s_0

Show that in `pruferDecode hn s`, the smallest tree-leaf's unique neighbor is
`s ⟨0, _⟩`.

```lean
theorem smallestTreeLeafNeighbor_pruferDecode (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (hge : 3 ≤ n) :  -- ensures n - 2 ≥ 1 so s ⟨0, _⟩ is well-typed
    smallestTreeLeafNeighbor n hn (pruferDecode hn s) = s ⟨0, by omega⟩ := by
  sorry
```

**Proof strategy**: The smallest tree-leaf is the `nextLeaf_0` from
`pruferDecodeAux`. In the partial graph at step 1, the only edge involving
nextLeaf_0 is `s(nextLeaf_0, s_0)` (from `pruferDecodeAux_succ_val_2`). Adding
later edges doesn't add neighbors of nextLeaf_0 (because nextLeaf_0 is removed
from state.1 after step 1, so it never appears as a `si` or new `nextLeaf` again).
Therefore in the full `pruferDecode` tree, nextLeaf_0 has unique neighbor s_0.

Use `smallestTreeLeaf_adj_neighbor` (line 95) and
`smallestTreeLeaf_neighbor_unique` (line 99) for the "unique" structure.

For "nextLeaf_0 is never a `si` or future `nextLeaf`": this follows from
`pruferDecodeAux_succ_val_2`'s `hFresh` property (after step 1, nextLeaf_0 is
erased from state.1; later steps only add edges from state.1 vertices).

This is the hard part of step 0 of the round-trip.

## Constraints

- 0 sorry, 0 axiom in final answer.
- Build remote: `bash ~/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book --file scratch_ch31_inverse.lean`
- File oracle questions to `HANDOFF/oracle/QUESTION_31_STEP0_NN_agy.md` if blocked.

## Scope

Theorem A: ~15 LOC (immediate from existing).
Theorem B: ~50-100 LOC (needs induction on m showing nextLeaf_0 has no new
edges added after step 1).

If you get past Theorem A and Theorem B is genuinely too heavy, file an oracle
question with the specific blocker.

Go.
