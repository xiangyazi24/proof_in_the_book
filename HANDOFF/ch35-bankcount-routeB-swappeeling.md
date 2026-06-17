# Ch35 BoundaryBankCount via Route B (swap-peeling) — ChatGPT Pro blueprint

Goal: `numCycles P = M.V − B + 2` where `P = M.φ * outerDualAlpha = M.σ * outerTau`
(proved equal by `ZinanCh35OuterSlack.phi_outerDualAlpha_eq_sigma_outerTau`), `outerTau` =
the involution = id off OuterDel, = M.α on OuterDel (B disjoint transpositions), B = C.darts.length.

## Landed toolkit (VERIFIED to exist, `ProofsInTheBook/PlanarMapCutCapCounts.lean`):
- `numCycles_mul_swap_of_sameCycle (p) {a b} (hne) (hsc : p.SameCycle a b) : numCycles (p * swap a b) = numCycles p + 1`  [SPLIT, :78]
- `sameCycle_mul_swap_of_cycle_avoids` [transport, :114]
- `numCycles_mul_listSwap_splits` [:125]
- `numCycles_mul_listSwap_merges (p) (l) (cond) : numCycles (p * swapProd l) + l.length = numCycles p` with cond = each prefix `¬ (p * swapProd (l.take j)).SameCycle (l.get j).1 (l.get j).2`  [MERGE, :182]
- `M.V_eq_numCycles : M.V = numCycles M.σ`  (PlanarMapEulerInequality:62)

## Swap order:
`q i := C.darts.get i`, `r i := M.α (q i)`, `last : Fin B := B-1`, `emb : Fin (B-1) → Fin B`.
Order: `(q 0,r 0),(q 1,r 1),…,(q (B-2),r (B-2))` [all MERGE], then `(q last, r last)` [SPLIT] LAST.
- `mergePairs := (finRange (B-1)).map (fun j => (q (emb j), r (emb j)))`
- `swapProd l := (l.map (fun w => swap w.1 w.2)).prod`
- `pPrefix k := M.σ * swapProd (mergePairs.take k)`, `pMerge := M.σ * swapProd mergePairs`
- `P_eq_pMerge_mul_last : P = pMerge * swap (q last) (r last)` (from `outerTau = swapProd (mergePairs ++ [lastPair])` + assoc).

## The running invariant (THE key, prove by induction on k):
```
pPrefix_same_q_q_iff (hk : k ≤ B-1) (i j) :
  (pPrefix k).SameCycle (q i) (q j) ↔ i = j ∨ (i.val ≤ k ∧ j.val ≤ k)
pPrefix_same_q_r_iff (hk : k ≤ B-1) (i j) :
  (pPrefix k).SameCycle (q i) (r j) ↔ i = next j ∨ (i.val ≤ k ∧ (next j).val ≤ k)
```
(r j is in the σ-cycle of q(next j) since M.σ(r j) = q(next j), from φ=σα + φ(q j)=q(next j).)

Generic engine lemma (prove once): a cross-cycle swap merges exactly two cycles:
```
sameCycle_mul_swap_merge_components_iff (p) {a b x y} (hab : a≠b) (hnsc : ¬ p.SameCycle a b) :
  (p * swap a b).SameCycle x y ↔ p.SameCycle x y ∨ (p.SameCycle x a ∧ p.SameCycle y b) ∨ (p.SameCycle x b ∧ p.SameCycle y a)
```
Base k=0: pPrefix 0 = M.σ, `σ.SameCycle (q i)(q j) ↔ i=j` (outer_simple). Step k→k+1: next swap (q k, r k); by IH q k is in merged block {0..k}, r k in untouched cycle of q(k+1); prove `¬ (pPrefix k).SameCycle (q k)(r k)` then apply the merge engine → block {0..k+1}.

## Counts:
- mergePairs all merge: `mergePairs_condition j : (get j).1 ≠ (get j).2 ∧ ¬ (M.σ * swapProd (mergePairs.take j)).SameCycle (get j).1 (get j).2` — via pPrefix_same_q_r_iff (next(emb j) = j+1 > j ⟹ RHS false). Then `numCycles_mul_listSwap_merges` ⟹ `numCycles pMerge + (B-1) = M.V`.
- final split: `final_pair_same : pMerge.SameCycle (q last) (r last)` — pPrefix_same_q_r_iff k=B-1: last.val=B-1≤B-1 ∧ (next last).val=0≤B-1 ⟹ true. Then `numCycles_mul_swap_of_sameCycle` ⟹ `numCycles P = numCycles pMerge + 1`.
- `omega` on `numCycles pMerge + (B-1) = M.V` ∧ `numCycles P = numCycles pMerge + 1` ⟹ `numCycles P = M.V − B + 2`.

## Disjointness facts needed (for the product decomposition):
`q i ≠ q j ↔ i≠j`, `r i ≠ r j ↔ i≠j`, `q i ≠ r j`, `q i ≠ r i` (α fixed-point-free + "reverse of boundary dart ∉ boundary darts").

## Note: do NOT prove "R is one cycle" by segment itinerary first — get the count by swaps, derive R-one-cycle as a corollary if needed. The count proof needs no segment/list-interval reasoning.
