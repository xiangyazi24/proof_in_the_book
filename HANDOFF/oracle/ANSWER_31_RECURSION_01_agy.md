# ANSWER_31_RECURSION_01_agy — induction invariant for delete-leaf = shift-decode

## Direct answer: the induction invariant

Let `L := finSuccAboveEquivCompl nL` (where `nL := nextLeaf0 (by omega) s`).
`L : Fin (m+1) ≃ {v : Fin (m+2) // v ∈ ({nL}ᶜ : Set _)}`.

The key invariant is **two parallel equalities** at every step `k ≤ m - 1`:

```
[INV-1]  (pruferDecodeAux _ (shiftedCode_v2 hm s) k _).val.1 =
         (pruferDecodeAux _ s (k+1) _).val.1.image L.symm_to_Fin

[INV-2]  (pruferDecodeAux _ (shiftedCode_v2 hm s) k _).val.2 =
         ((pruferDecodeAux _ s (k+1) _).val.2.erase s(nL, s ⟨0, _⟩)).image lift_Sym2
```

Here:
- `L.symm_to_Fin : Fin (m+2) → Fin (m+1)` is `L.symm ∘ ⟨·, _⟩` — but only defined
  on `{nL}ᶜ`. For the right-hand sets (which never contain nL after step 1), this
  is well-defined. Formally, use `Finset.attach` then map via a bijection
  `{v ∈ ... // v ≠ nL} → Fin (m+1)` via L.symm.
- `lift_Sym2 : Sym2 (Fin (m+2)) → Sym2 (Fin (m+1))` — same idea on edges, defined
  whenever both endpoints are ≠ nL.

## Why this works structurally

**Base k = 0:**
- LHS-1: `(pdAux shiftedCode 0 _).val.1 = Finset.univ : Finset (Fin (m+1))`
- RHS-1: `(pdAux s 1 _).val.1.image L.symm`. At step 1, `(pdAux s 1 _).val.1 = univ.erase nL`. Image of this under L.symm is `Finset.univ : Finset (Fin (m+1))`. ✓
- LHS-2: `(pdAux shiftedCode 0 _).val.2 = ∅`
- RHS-2: `({s(nL, s_0)}).erase s(nL, s_0)`.image lift = `∅.image lift = ∅`. ✓

**Inductive step k → k+1:**
Use `pruferDecodeAux_succ_val_2` (already proven) on BOTH sides:
- Shifted side: at step k+1, append `s(nextLeaf_k, (shiftedCode hm s) k)` and erase nextLeaf_k.
- Original side: at step k+2, append `s(nextLeaf'_{k+1}, s ⟨k+1, _⟩)` and erase nextLeaf'_{k+1}.

You need to show:
**(a)** `L.symm nextLeaf'_{k+1} = nextLeaf_k` (nextLeaf identification across L)
**(b)** `L.symm (s ⟨k+1, _⟩) = (shiftedCode hm s) k` (by definition of shiftedCode)

For (b): direct from `shiftedCode_v2` def. j' = k, j = k+1; `shiftedCode k = L.symm ⟨s ⟨k+1, _⟩, _⟩`. ✓

For (a): the nextLeaf at step k of shiftedCode is `min'` of `(state.1 ∩ never-future-appears-as-shiftedCode)`. Lift this through L: gives `min'` of `((image L.symm of (univ.erase nL minus past nextLeaves)) ∩ (never-future-appears-as-s-after-position-k+1))`. By the invariant, this matches.

Formally:
```
nextLeaf_k = (state_k.1.filter (fun v : Fin (m+1) => ∀ j' : Fin (m-1), k ≤ j'.val → (shiftedCode hm s) j' ≠ v)).min'

nextLeaf'_{k+1} = (state'_{k+1}.1.filter (fun v : Fin (m+2) => ∀ j : Fin m, k+1 ≤ j.val → s j ≠ v)).min'
```

Need: `L.symm (nextLeaf'_{k+1}) = nextLeaf_k`. Equivalently, `L nextLeaf_k = nextLeaf'_{k+1}` (as elements of Fin (m+2) via inclusion).

By the invariant, state_k.1 ↔ state'_{k+1}.1 under L. So the filter set on the left lifts to a Finset of Fin (m+2). The `min'` commutes with L (since L preserves order — it uses `succAbove` which is monotone modulo the skipped index).

**Key sub-lemma you might need to prove**:
```lean
lemma min'_image_L_symm {nL : Fin (m+2)} (s : Finset (Fin (m+2))) (hnL : nL ∉ s)
    (h : s.Nonempty) :
    (s.image (finSuccAboveEquivCompl nL).symm).min' (by ...) =
    (finSuccAboveEquivCompl nL).symm (s.min' h)
```
This requires L.symm to be monotone on `{nL}ᶜ`. Fin.succAbove IS monotone in the
appropriate sense — see Mathlib's `Fin.succAbove_strictMono`.

## Practical implementation strategy

1. **Define the lift functions explicitly** (~20 LOC):
   ```lean
   -- For Finset (Fin (m+2)) with elements ≠ nL → Finset (Fin (m+1)) via L.symm.
   noncomputable def liftFinset {m : ℕ} (nL : Fin (m+2))
       (s : Finset (Fin (m+2))) (h : nL ∉ s) : Finset (Fin (m+1)) := ...
   ```
2. **Prove the monotonicity / min' commutation lemma** (~30 LOC, uses Mathlib monotone results).
3. **State the invariant as a single combined `∧`** (~10 LOC for statement).
4. **Induction on k** (~80-150 LOC for the body):
   - Base case: direct calculation.
   - Succ case: use `pruferDecodeAux_succ_val_2` on both sides + the nextLeaf
     identification + the new-edge identification.
5. **Derive the graph equality** from the invariant on edges (~30 LOC) — both
   graphs are `fromEdgeSet` of corresponding sets.

Total: ~200-250 LOC if everything goes well; could go to 350 if Mathlib API
calls for `Fin.succAbove` order lemmas are missing.

## Pragmatic alternative if 200 LOC seems too much

State a WEAKER lemma that's easier:
```lean
-- Just the edge set equality, ignoring the "available" tracking.
-- This is enough to prove pruferDecodeEdges agree as Finset, which is what
-- we need for the tree equality.
theorem pruferDecodeEdges_shifted {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) :
    pruferDecodeEdges (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s) =
    (pruferDecodeEdges (by omega) s).erase s(nextLeaf0 _ s, s ⟨0, by omega⟩) |>.image lift_Sym2
```

Or even weaker — just prove the GRAPH equality directly via `ext a b` showing
Adj agrees. This bypasses tracking `available` Finsets and lets you reason
purely about edge memberships.

The `Adj`-based proof is probably the cleanest:

```lean
theorem deleteSmallestLeaf_pruferDecode_v2 {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    deleteSmallestLeafTreeSucc (m + 1) (by omega) (pruferDecode (by omega) s) =
    pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s) := by
  apply Subtype.ext
  ext a b
  -- Now case-split on Adj using fromEdgeSet_adj + the edge-set transports.
  sorry
```

## Recommendation

Try the `Adj`-based ext approach first. If you get stuck at some specific Adj
equivalence, file ANSWER_31_RECURSION_02 with the exact sub-goal — I can then
give a targeted strategy.

Go.
