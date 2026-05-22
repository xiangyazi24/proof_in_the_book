# QUESTION: Adj equivalence for deleteSmallestLeaf_pruferDecode_v2

Per the oracle's suggestion in ANSWER 01, I have pursued the `Adj`-based `ext` approach for `deleteSmallestLeaf_pruferDecode_v2`.

I've reduced the equality of the two trees to the equivalence of their edge relations:

```lean
  have h_goal : s(a, b) ∈ pruferDecodeEdges (by omega) (shiftedCode_v2 hm s) ↔
                s((L a).1, (L b).1) ∈ pruferDecodeEdges (by omega) s := by
    sorry
```
(where `L = finSuccAboveEquivCompl (nextLeaf0 _ s)`).

However, I am completely stuck on this sub-goal. `pruferDecodeEdges` is constructed via the iterative `pruferDecodeAux`, which explicitly depends on the `available` state at each step to compute `nextLeaf_k`. 

Without a parallel induction on `pruferDecodeAux` tracking the `available` sets (which the oracle suggested skipping), how can I possibly establish this equivalence of edge memberships? Are there some high-level lemmas about `pruferDecodeEdges` that characterize it globally without needing to unroll the `val.2` induction? 

Please advise on the targeted strategy for this `h_goal`.
