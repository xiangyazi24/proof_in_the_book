# CutSigmaCounts (Ch35 cut-and-cap counts) — reply

**File:** `ProofsInTheBook/PlanarMapCutCapCounts.lean` (NEW, sole writer; no other
file touched). Imports `PlanarMapCutCapSigma` + `PlanarMapEulerInequality`.
**Branch:** `ch35-cutcapcounts-toolkit` (2 commits).
**Status:** compiles clean on uisai1 (`lake env lean` + full
`lake build ProofsInTheBook.PlanarMapCutCapCounts`, 8434 jobs). 418 lines.
0 sorry / 0 axiom / 0 admit / 0 native_decide. Every new declaration's
`#print axioms` = `{propext, Classical.choice, Quot.sound}`.

## Honest verdict

**PARTIAL.** The three `CutSigmaCounts` fields (`vertex_count` V'=V+k,
`face_count` F'=F+2, `connected_of_dual_path`) are **NOT discharged** — the bundle
remains the isolated core. What I delivered is the **complete, verified,
previously-nonexistent counting toolkit** that the design's transposition-counting
route reduces to, plus a precise de-risked roadmap (below) that removes the one
obstruction I had initially feared was a wall.

I deliberately did not ship an unverified multi-hundred-line count/connectivity
proof under the no-local-build constraint — that would have risked a broken or
vacuous "green" result. Everything in the file is verified.

## What is PROVED unconditionally (all `#print axioms` clean-3)

Reusable cycle-count machinery in `namespace CutCapCount`:

1. `numCycles_mul_swap_of_sameCycle` — the **split** (`+1`) half of the dichotomy
   (`PermTranspositionCycleCount` only exported the merge half explicitly).
2. `pow_mul_swap_apply_of_not_sameCycle` + `sameCycle_mul_swap_of_cycle_avoids`
   — **SameCycle transport across a disjoint swap**: if `a`'s `p`-cycle avoids the
   swap's two points, `p.SameCycle a b` lifts to `(p * swap u v)`. (Carries the
   per-step invariant through the partial products of disjoint swaps.)
3. `numCycles_mul_listSwap_splits` / `numCycles_mul_listSwap_merges` — count change
   for multiplying by a **list** of transpositions, each splitting (resp. merging)
   its running product: `numCycles (p * ∏ swaps) = numCycles p ± length`, with the
   per-step same/different-cycle side-conditions as hypotheses.
4. `listSwap_prod_apply_of_notMem` — a swap-product fixes any point disjoint from
   every pair (the engine for the merge-phase discharge).
5. `numCycles_sumCongr_one` : `numCycles (σ ⊕ 1) = numCycles σ + card β`, via an
   explicit orbit-quotient `Equiv` (`sumCongrOneOrbitEquiv`) and the
   `SameCycle` characterizations of `σ ⊕ 1`.

Cut-map bridges in `namespace SimplePrimalCycle`:

6. `sigmaLift := σ ⊕ 1` on `CutDart`, with `numCycles_sigmaLift : = M.V + 2k`
   (wires through `M.V_eq_numCycles`).
7. The named darts of the decomposition: `lEndPlus`/`lEndMinus` (`ℓ_i^± = σ⁻¹ p_i`,
   `σ⁻¹ q_i`), `capP`/`capM`.

## The verified-by-hand decomposition (the design's "reconcile σ' with a swap product")

`cutSigmaPerm = sigmaLift * (∏_i swap(ℓ_i^+,c_i^+) · swap(ℓ_i^-,c_i^-)) * (∏_i swap(c_i^+,c_i^-))`

checked on all five `CutDart` cases (trace in source/scratch):
- the first `2k` swaps **merge** each pair of fixed caps into the `σ`-orbit at
  `v_i` → `numCycles` drops by `2k` (`V+2k → V`);
- the last `k` swaps **split** each merged orbit into its two banks → rises by `k`
  (`V → V+k`).

The analogous decomposition of `φ' = σ'α'` gives the net `+2`.

## The obstruction I feared was a wall — and why it ISN'T (key finding for the follow-on)

The split-phase discharge needs `cutSigmaMerged.SameCycle c_i^+ c_i^-`. I initially
flagged this as requiring the "contiguous σ-interval" data the σ-file deliberately
avoided. **It does not.** `sigmaMerged(c_i^+) = inl(p_i)` and `c_i^-` is reached
from `inl(q_i)`; the two caps are co-cyclic iff `σ.SameCycle p_i q_i`, and since
`p_i = α(dart(prevIdx i))` and `q_i = dart i` are **both incident to v_i**, this is
exactly `M.tail p_i = M.tail q_i` (both `= v_i`). The repo's `tail`/`cycleSetoid`
correspondence (`tail d = Quotient.mk (cycleSetoid σ) d`, and `cycleSetoid σ` IS
`σ.SameCycle`) gives `σ.SameCycle p_i q_i` directly from the cycle's `consecutive`
field. **No interval enumeration needed.** This unblocks the whole split phase.

## Precise roadmap to close V' (and, mutatis mutandis, F')

With the toolkit above, what remains is mechanical (needs local-build iteration):

- **(a)** Build the concrete `L1 : List (CutDart×CutDart)` (the `2k` merge swaps,
  e.g. `(List.finRange k).flatMap (fun i => [(ℓ_i^+,c_i^+),(ℓ_i^-,c_i^-)])`) and
  `L2` (the `k` split swaps).
- **(b)** Prove the decomposition `ext` by isolating each vertex's swaps from the
  flatMap product via disjointness (caps/`ℓ` of distinct `i` are distinct), reusing
  `listSwap_prod_apply_of_notMem` for the off-vertex factors and
  `Equiv.swap_apply_*` for the on-vertex three swaps. (Five `CutDart` cases.)
- **(c)** Merge-phase hyps for `numCycles_mul_listSwap_merges`: each step's cap is a
  fixed point of the prefix (`listSwap_prod_apply_of_notMem` + `sigmaLift` fixes
  caps) ⟹ `SameCycle.eq_of_right` gives `¬ SameCycle` since `ℓ ≠ cap`.
- **(d)** Split-phase hyps for `numCycles_mul_listSwap_splits`: `SameCycle c_i^+
  c_i^-` in `sigmaMerged` from the σ-tail fact above, transported across the earlier
  (disjoint) split swaps by `sameCycle_mul_swap_of_cycle_avoids`.
- **(e)** Chain: `numCycles_sigmaLift` (V+2k) → merges (−2k) → splits (+k) = V+k;
  then `(cutCapMap).V = numCycles cutSigmaPerm` via `V_eq_numCycles` and
  `cutCapMap_sigma`.

F' is structurally identical on `φ' = cutSigmaPerm * cutAlphaPerm` vs
`phiLift = φ ⊕ 1`; the cap-reversal in `cutAlpha` (`c_i^- ↦ α(dart i) = p_{i+1}`,
next vertex) is what makes the net `+2` rather than `+k` — the swap signs differ
from the V' pattern accordingly, and that sign bookkeeping is the genuine F'
content. `connected_of_dual_path` (design §4 Part A/B) is a separate effort in the
`PlanarMapFanConnectivity` walk-rerouting style, independent of the counts.

## Verification commands

```
rsync -az .../PlanarMapCutCapCounts.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 '... lake env lean ProofsInTheBook/PlanarMapCutCapCounts.lean'   # no output = OK
ssh uisai1 '... lake build ProofsInTheBook.PlanarMapCutCapCounts'            # 8434 jobs OK
# #print axioms on all new decls -> {propext, Classical.choice, Quot.sound}
```
