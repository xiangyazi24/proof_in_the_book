# TASK Ch31 sublemma: tree-leaf characterization

Ch30 Tier 2 (lattice-path tailSwap involution) is genuinely deep — let it stay
at Tier 1 for now. Switch to helping me complete Ch31 Tier 2.

## Background

I just proved in `scratch_ch31_inverse.lean` (committed as f7845a4):

```lean
theorem pruferDecode_degree (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) :
    ((pruferDecode hn s).1).degree v = countOccurrences s (n - 2) v + 1
```

where `countOccurrences s m v := (Finset.univ.filter (fun j : Fin (n-2) => j.val < m ∧ s j = v)).card`.

This is the famous Prüfer formula. From it, the next building block follows
directly.

## Your task

Prove these two lemmas in `scratch_ch31_inverse.lean` (just append to the bottom,
inside the namespace `ProofsInTheBook.Chapter31`):

```lean
/-- A vertex is a tree-leaf in the decoded tree iff it doesn't appear in the code. -/
theorem pruferDecode_isLeaf_iff (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n)
    (v : Fin n) :
    v ∈ treeLeaves (pruferDecode hn s) ↔ isLeafInPrufer s v := by
  sorry

/-- The smallest tree-leaf of `pruferDecode s` equals the smallest vertex not
appearing in `s`, which is `nextLeaf_0` from the decode process. -/
theorem smallestTreeLeaf_pruferDecode (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    smallestTreeLeaf n hn (pruferDecode hn s) =
    (Finset.univ.filter
      (fun (v : Fin n) => ∀ j : Fin (n - 2), s j ≠ v)).min'
      (by
        have h0_le : 0 ≤ n - 2 := Nat.zero_le _
        have := nextLeaf_nonempty hn s 0 h0_le Finset.univ (by simp [Nat.sub_zero])
        convert this using 2
        ext v; simp) := by
  sorry
```

## Definitions you'll need

- `treeLeaves T = {v | T.1.degree v = 1}` (from Ch31, line 61).
- `isLeafInPrufer s v := ∀ i : Fin (n - 2), s i ≠ v` (line 1005).
- `smallestTreeLeaf n hn T := (treeLeaves T).min' (treeLeaves_nonempty n hn T)`.
- `nextLeaf_nonempty` (line 1183).

## Proof sketch for `pruferDecode_isLeaf_iff`

```
v ∈ treeLeaves (pruferDecode hn s)
⟺ degree v = 1                                          [def of treeLeaves]
⟺ countOccurrences s (n-2) v + 1 = 1                     [pruferDecode_degree]
⟺ countOccurrences s (n-2) v = 0                          [arith]
⟺ {j | s j = v} ⊆ ∅                                       [card_eq_zero]
⟺ ∀ j, s j ≠ v                                            [unfold]
⟺ isLeafInPrufer s v
```

## Proof sketch for `smallestTreeLeaf_pruferDecode`

Both sides are `Finset.min'` of "vertices not appearing in s". Show the two
underlying Finsets are equal (via `Finset.ext` and the `pruferDecode_isLeaf_iff`
lemma), then apply `Finset.min'_eq_of_eq`.

## Constraints

- 0 sorry, 0 axiom in final answer.
- Build via `bash ~/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book --file scratch_ch31_inverse.lean`
- File oracle questions to `HANDOFF/oracle/QUESTION_31_LEAF_NN_agy.md` if blocked.

## Scope

~30-50 LOC total. Should be straightforward given the degree formula. If you hit
> 80 LOC, file an oracle Q.

Go. First read the current `scratch_ch31_inverse.lean` to see what's available,
then append the two theorems.
