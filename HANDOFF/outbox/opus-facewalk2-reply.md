# Face-walk core — pass 4 reply (opus-facewalk2): DECISIVE FINDING

**File:** `ProofsInTheBook/PlanarMapFaceWalk2.lean` (NEW, sole writer).
Imports `ProofsInTheBook.PlanarMapFaceWalk` + `ProofsInTheBook.PlanarMapCutCapConn`.
**Branch:** `main` (untracked, NOT committed). Did **not** touch
`PlanarMapDualPathSep.lean` (parallel agent's untracked file).

## Status: the unconditional target is FALSE — proven by counterexample, not forced

The mandate was to prove `FaceChainClosureCount C : numCycles (phiLift * faceCorr) =
M.F + 2` unconditionally. **It is not a theorem.** The fourth pass disproves it by an
explicit, numerically verified counterexample and delivers the correct conditional
chain instead. No fake proof, no sorry, no axiom.

### The genuine arithmetic

`(C.cutCapMap).φ = phiLift * faceCorr` is a *proved* identity, so the open quantity
is exactly `(C.cutCapMap).F`. With the proved counts `V'=V+k`, `E'=E+k`, and the
surgery being genus-0 per component,

  **`numCycles (phiLift * faceCorr) = F' = M.F + 2·c − 2`**,  where `c` = number of
  `dartStep`-components of `C.cutCapMap`.

So `F' = F + 2` **iff `c = 2`**. That `c = 2` is the two-sided Jordan-separation
content (carried by `connected_of_dual_path` / `DualPathSeparation`) — it is **not**
recoverable from σ/φ data, which is exactly why the previous three passes could not
close it: there is nothing to close at that layer, the statement is simply false off
the two-component locus.

### Verified counterexamples (orbit-by-orbit, matching every proved `cutCapPhi_*`)

| sphere map (χ=2)              | V E F | comp c | F' actual | F+2 | F+2c−2 |
|-------------------------------|-------|--------|-----------|-----|--------|
| triangle, 3 vertices, k=3     | 3 3 2 |   4    |   **8**   |  4  |   8    |
| tetrahedron, cut 0→1→2→0      | 4 6 4 |   4    |  **10**   |  6  |  10    |
| triangular bipyramid, equator | 5 9 6 |   2    |   **8**   |  8  |   8    |

The "k=3 sphere-triangle anchor = F'=4" cited by passes 1–3 is wrong: that cut map
shatters into **c=4** components, so F'=**8**. The three `+`-caps become φ'-fixed
points (`σ(dart i)=p_j` ⇒ `φ'(capP i)=capP i`); FCore's three `inl(dart i)`
singletons, one reverse-dart face, three capped `+`-singletons, one capped `−`
3-cycle = 8 orbits. This matches the proved per-class action lemmas exactly — passes
1–3 only ever checked the *per-class* action, never the *global* orbit count, and
asserted F'=4 without computing it. (Classic "verify the numeric anchor before
banking" gap; faithfulness-audit §3.3 false-target class.)

## What this pass delivers (all clean-3, 0 sorry/axiom/admit/native_decide)

* `faceChainClosureCount_iff_cutCapMap_F` — the open Prop ⇔ `(cutCapMap).F = F+2`
  (proved reduction, makes the false-target visible and precise).
* `faceChainClosureCount_of_cutCapMap_F`, `cutCapMap_F_of_closure'` — honest
  reductions through the imported layer.
* `cutSigmaCounts_of_faceCount_of_dps` — full `CutSigmaCounts` with **`V'` discharged
  unconditionally** (`cutCapMap_V`), `F'` as the genuine two-component hypothesis
  `hF`, connectivity from the `DualPathSeparation` parameter `hsep`.
* `jordan_simple_cycle_narrowed` — Jordan lemma with **Euler inequality discharged
  unconditionally** (`chi_le_two_of_connected`); only `hF` + `hsep` remain.
* `separates_of_jordan_narrowed` — end-to-end chord separation, narrowest residue:
  just `hF` + `hsep` (+ standard chord data). V'✓ E'✓ internalised; χ-ineq✓.

Note on the chain's soundness: `hF` (F'=F+2 ⟺ c=2) and `Connected` (c=1) are jointly
unsatisfiable — that is *precisely* the engine of the Jordan contradiction
(`F'=F+2` ∧ connected ⇒ χ'=4≤2). So keeping `F'=F+2` as a standing hypothesis is
correct and non-vacuous on its intended (no-dual-path, c=2) locus; it is simply not a
free σ/φ identity. The downstream files already (correctly) take it as a hypothesis;
this pass confirms that is the *only* honest option and supplies the narrowed
assembly around it.

## Verification

```
rsync -az .../PlanarMapFaceWalk2.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=...elan/bin:$PATH \
  && lake build ProofsInTheBook.PlanarMapFaceWalk ProofsInTheBook.PlanarMapCutCapConn  # deps, 8439 OK
  && lake build ProofsInTheBook.PlanarMapFaceWalk2'   # 8440 jobs OK
ssh uisai1 '... lake env lean ProofsInTheBook/PlanarMapFaceWalk2.lean'   # EXIT 0, no errors/warnings
# #print axioms faceChainClosureCount_iff_cutCapMap_F, cutSigmaCounts_of_faceCount_of_dps,
#   jordan_simple_cycle_narrowed, separates_of_jordan_narrowed  ->  {propext, Classical.choice, Quot.sound}
```

## Recommendation

The previously-isolated `FaceChainClosureCount` (and FCore's `NumCyclesPhiLiftFaceCorr`,
`cutCapMap_F`'s `hcore`) should be re-labelled from "open topological core, to be
proved" to "the two-component Jordan-separation hypothesis `F' = F + 2·c − 2 with
c = 2`" — it is a genuine hypothesis equivalent to the separation, not a missing σ/φ
lemma. Closing it for real requires the `cutCapMap` component count (genus-0
per-component Euler), i.e. the same Jordan-separation machinery as `DualPathSeparation`,
not a transposition walk. The numeric anchor in the three prior handoffs (`F'=4` at
k=3) is incorrect and should be struck.
