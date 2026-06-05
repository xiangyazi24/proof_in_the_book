# CutSigmaCounts V' = V + k — reply (opus-ccv)

**File:** `ProofsInTheBook/PlanarMapCutCapV.lean` (NEW, sole writer; no other file
touched). Imports `PlanarMapCutCapCounts`.
**Branch:** `main` (as instructed; not committed/pushed — left for you to commit).
**Status:** compiles clean on uisai1 (`lake env lean`, 0 errors; full
`lake build ProofsInTheBook.PlanarMapCutCapV` — see verification). 963 lines.
0 sorry / 0 axiom / 0 admit / 0 native_decide.
`#print axioms` on the two headline results = `{propext, Classical.choice, Quot.sound}`.

## Verdict

**V' = V + k: DONE (FAITHFUL, unconditional).**  The `vertex_count` field of
`CutSigmaCounts` is fully discharged for the concrete cut map:

```
theorem cutCapMap_V (C : SimplePrimalCycle M) : (C.cutCapMap).V = M.V + C.len
```

**F' = F + 2: left cleanly for the next round** (honest scope; see below).

## What was proved (the full (a)–(e) roadmap, executed)

**Step 1 — the swap decomposition (roadmap (a)+(b)).**
```
theorem cutSigmaPerm_eq_sigmaLift_mul :
    C.cutSigmaPerm = C.sigmaLift * C.mergeProd * C.splitProd
```
with
* `mergeList = (finRange k).flatMap (fun i => [(ℓ_i^+,c_i^+),(ℓ_i^-,c_i^-)])`,
  `mergeProd = (mergeList.map swap).prod` (the `2k` insertion swaps);
* `splitList = (finRange k).map (fun i => (c_i^+,c_i^-))`,
  `splitProd = (splitList.map swap).prod` (the `k` split swaps).

Proved by `ext` + `divertKind` case split on each cut-dart class, after fully
characterizing the action of both swap products at every relevant point
(`splitProd_*`, `mergeProd_*` closed forms via `Nodup`-indexed inductions over the
flatMap / map, reusing the toolkit's `listSwap_prod_apply_of_notMem`).

**Step 2 — the counts (roadmap (c)+(d)+(e)).**
* Merge phase (`numCycles_merged_add`): `numCycles (sigmaLift*mergeProd) + 2k =
  numCycles sigmaLift`, via `numCycles_mul_listSwap_merges`.  Each step's cap is a
  fixed point of `sigmaLift` and of the prefix product (cap absent from the prefix,
  shown from `Nodup` of the second-component list `mergeList.map Prod.snd`), so
  `not_sameCycle_of_fixed` discharges the per-step `¬ SameCycle`.
* Split phase (`numCycles_split`): `numCycles (merged*splitProd) = numCycles merged
  + k`, via `numCycles_mul_listSwap_splits`.  The per-step `SameCycle c_i^+ c_i^-`
  is `merged.SameCycle (c_i^+) (c_i^-)`, transported across the disjoint prefix
  split swaps by a new orbit-fixed transport lemma `sameCycle_mul_of_orbit_fixed`.
* Chain (`numCycles_cutSigmaPerm`): `V + 2k − 2k + k = V + k`.

**The de-risked crux, executed exactly as you flagged.**  The key reductions
(`merged.SameCycle c_i^+ c_i^-` ⇒ `σ.SameCycle p_i q_i`, and the disjointness
`¬ merged.SameCycle c_i^+ c_j^±` for `i ≠ j` ⇒ distinct `σ`-orbits at distinct
cycle vertices) are handled by a single **projection semiconjugacy**:

```
proj : CutDart → D     (inl d ↦ d, c_i^+ ↦ p_i, c_i^- ↦ q_i)
proj_merged : proj (merged x) = σ (proj x)  ∨  proj (merged x) = proj x
```

i.e. under `Q = sigmaLift*mergeProd` the projection either advances one `σ`-step
(on `inl`-darts, including the divert-to-cap step) or stalls (on caps).  Iterating
gives both directions of `Q.SameCycle (inl a)(inl b) ↔ σ.SameCycle a b`, from which
every cap-`SameCycle` fact reduces to `σ` and then to the tail/`cycleSetoid`
correspondence `tail p_i = tail q_i = v_i` (and `tail`-injectivity of distinct
cycle vertices).  No interval enumeration, exactly as your roadmap predicted.

## New reusable lemmas (in `namespace CutCapCount`, beyond the existing toolkit)

* `pow_mul_apply_of_orbit_fixed` / `sameCycle_mul_of_orbit_fixed` — transport a
  `SameCycle` across a permutation that fixes the whole orbit (the list-level
  generalization of the toolkit's single-swap `sameCycle_mul_swap_of_cycle_avoids`;
  this is what makes the split-phase prefix discharge a one-liner).
* `not_sameCycle_of_fixed`, `pow_apply_of_fixed`, `listSwap_prod_apply_fst`.

## F' = F + 2 — honest scope (left for next round)

Not attempted in code.  As your prior reply noted, `φ' = cutSigmaPerm *
cutAlphaPerm` decomposes against `phiLift = φ ⊕ 1` with the **cap reversal** in
`cutAlpha` (`c_i^- ↦ α(dart i) = p_{i+1}`, the *next* vertex) flipping the swap
signs so the net is `+2` rather than `+k`.  That sign bookkeeping is a genuinely
different combinatorial argument (it is *not* a mechanical mutatis-mutandis of the
V' pattern — the `+2` is a global cycle-merge/split count, independent of `k`), so I
did not ship an unverified version under the no-local-build constraint.  The V'
machinery in this file (the `*_apply_*` swap-product evaluation lemmas, the
projection-semiconjugacy template, the orbit-fixed transport) is directly reusable
for it; the new content needed is the `cutAlpha`/`phiLift` decomposition and the
`+2` count.  `connected_of_dual_path` remains a separate connectivity effort.

## Verification commands

```
rsync -az .../PlanarMapCutCapV.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 '... lake env lean ProofsInTheBook/PlanarMapCutCapV.lean'   # no output = OK
ssh uisai1 '... lake build ProofsInTheBook.PlanarMapCutCapV'
# #print axioms cutCapMap_V  ->  {propext, Classical.choice, Quot.sound}
# #print axioms cutSigmaPerm_eq_sigmaLift_mul  ->  {propext, Classical.choice, Quot.sound}
```
