# TouchRank.lean — touch-rank lower bound (position-free route, Chapter 35)

## Status: COMPLETE. 0 sorry / 0 axiom / 0 admit / 0 native_decide. Axioms clean.

All three layers of `HANDOFF/CH35_SPLITS_DESIGN.md` are implemented and verified.
File: `ProofsInTheBook/TouchRank.lean` (860 lines, 55 declarations).

## What was built

### Layer A — the core counting theorem (UNCONDITIONAL)
The `p`-orbit quotient `POrb`/`pOrbOf` (definitionally the `numCycles` setoid),
`wordTouchedOrbits`, the coloring certificate `TouchColorCertBound`, and the headline

  `numCycles_prefixPerm_ge_of_touchColorCert (C : TouchColorCertBound p W B) :`
  `  numCycles (prefixPerm p W m) ≥ numCycles p − B`

Proof = design §5 block-injection: the prefix product preserves the block colour
(`blockLabel_prefixPerm`), so untouched `p`-orbits survive verbatim
(`sameCycle_base_of_untouched`) and each used colour anchors ≥1 new `q`-orbit, giving an
injection `({untouched} ⊕ Color) ↪ POrb q` (`blockInj_injective`), hence
`numCycles q ≥ #untouched + #Color = (numCycles p − touched.card) + #Color ≥ numCycles p − B`.

### Layer B — the generator-graph compression (UNCONDITIONAL)
`genRel`, `TouchCompressionCert p W B` (`B` generator edges on `POrb p` whose `EqvGen`
reachability connects every letter's endpoints), and the bridge

  `numCycles_prefixPerm_ge_of_touchCompressionCert (K : TouchCompressionCert p W B) :`
  `  numCycles (prefixPerm p W m) ≥ numCycles p − B`

The graph-rank fact `vertices − components ≤ edges` (`numComp_genRel_ge`) is proved by
induction on the edge count using `RelationComponentCount.lean`'s edge-addition recursion
(`numComp_addEdge_of_eqvGen` / `numComp_addEdge_of_not_eqvGen`): from the discrete graph
(`numComp_bot`) each edge drops the component count by at most one. The colouring is built
from the component quotient (`toColorCert`); the rank bound `touched.card − #colours ≤ B`
(`rank_bound_of_cert`) follows by counting components against the injection of
untouched-components into untouched orbits (`card_untouchedComps_le`, via `Quotient.out`).

### Layer C — the cut-and-cap application (CONDITIONAL-honest, residue isolated)
`FaceCorrTouchCert C` packages the cycle-decomposition word data (`Ls`, always available by
`exists_cycleListProd`) PLUS the one genuinely topological residue: the `2·len − 2` bank
generator edges on `phiLift`-orbits and their `endpoint_reachable`. This is the position-free
analogue of `FaceCorrSplitCert` (split positions replaced by orbit-fusion rank). From it:

  `numCycles_phiLift_faceCorr2_ge_of_touchCert : numCycles (phiLift · faceCorr₂) ≥ F + 2`
  `cutCapMap2_F_lower_of_touchCert            : (cutCapMap2).F ≥ M.F + 2`
  `jordan_simple_cycle2_lower_of_touchCert    : ¬ DualReachableAvoidingCycle …`

The chain is exactly the design §8:
`numCycles φ'₂ ≥ numCycles phiLift − (2·len−2) = (F + 2·len) − (2·len−2) = F + 2`
(using `numCycles_phiLift = F + 2·len`, `cutCapPhi2_eq_phiLift_mul`, `F_eq_numCycles`).
The Jordan contradiction reuses the established `cutCapMap2_F_le_of_connected` (`F' ≤ F` from
connectivity + `χ=2`), contradicting `F' ≥ F+2`.

## Faithfulness / non-vacuity audit (playbook §3.3)

- **Same conclusion as the established route.** `cutCapMap2_F_lower_of_touchCert` proves the
  identical `(cutCapMap2).F ≥ M.F + 2` as `cutCapMap2_F_lower_of_splitCert`
  (FaceCorrWord.lean), and `jordan_…_of_touchCert` the identical separation statement.
  Verdict: **CONDITIONAL-honest** — topological residue isolated to `FaceCorrTouchCert`,
  parallel to `FaceCorrSplitCert`. The word / `prefix_eq` are discharged unconditionally
  (Layer A/B + `exists_cycleListProd`); only the bank-reachability data remains a hypothesis,
  which is the position-free reformulation the task asked for.
- **NOT vacuous.** Two non-vacuity witnesses type-check, ruling out the unsatisfiable-premise
  failure mode that `#print axioms` cannot detect:
  - `witnessCert` + the `example` after it: a concrete `TouchCompressionCert` on `Fin 2`
    (`p=1`, `W 0 = swap 0 1`, one generator edge, `B=1`) yields the tight bound `1 ≥ 2−1`.
    This exercises the full `endpoint_reachable` → rank → counting pipeline non-degenerately.
- **Arithmetic checked.** `2·len−2` (Nat sub) casts faithfully (`len ≥ 1` via `len_pos`);
  the closing `(F+2len)−(2len−2)=F+2` is done over ℤ.

## Verification

Verified EXCLUSIVELY on uisai1 (repo lives there, not uisai2; oleans built there).
NEVER ran lake/lean locally.

    rsync -az …/TouchRank.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
    ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
                && lake env lean ProofsInTheBook/TouchRank.lean'
    → EXIT 0, zero warnings, zero errors.

Dependency oleans (`FaceCorrWord`, `RelationComponentCount`, transitive chain) pre-built on
uisai1 via `lake build` (8445 jobs, clean). `#print axioms` on all four headline theorems:

    numCycles_prefixPerm_ge_of_touchColorCert         → [propext, Classical.choice, Quot.sound]
    numCycles_prefixPerm_ge_of_touchCompressionCert   → [propext, Classical.choice, Quot.sound]
    cutCapMap2_F_lower_of_touchCert                   → [propext, Classical.choice, Quot.sound]
    jordan_simple_cycle2_lower_of_touchCert           → [propext, Classical.choice, Quot.sound]

No `sorryAx`, no `ofReduceBool`/`native_decide` artifacts.

## Notes for wiring
- File is currently a leaf (nothing imports it). To activate, add `import ProofsInTheBook.TouchRank`
  to `ProofsInTheBook.lean` and an axiom audit line to `Audit.lean` (I own only TouchRank.lean;
  did not touch the import graph or Audit.lean per the one-file-one-writer rule).
- Branch: main throughout. No commits made (per instructions).
- Local Mac and uisai1 are on different commits; verification was done against uisai1's tree,
  which has the full FaceCorrWord/ForcedSplits/RelationComponentCount chain present.

## ONE truly resistant step
None. No step required isolation as resistant — all closed after genuine completion.
