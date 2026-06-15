# Ch35 ENDGAME — automode doctrine (2026-06-15)

## Goal (one sentence)
Close `ZinanCh35Cert.fiveColor_of_planarInputs` unconditionally (Ch35 = the last open Book proof), or reduce it to the single precisely-machine-isolated planar-orientation certificate if that is genuinely irreducible.

## State (all committed, clean-3)
- CHORD-branch confinement: UNCONDITIONAL by construction (`ZinanCh35Aligned.bothConfinements_normalized`, 143e8a1). All deep machinery done: coverage atom, general `SimpleCycleBankTheorem`, σ-star, edge_core, bank→ChordSplitAdj conversion.
- CHORDLESS branch: reduces to `OrientationCert` + `BaseCount` + `FanSurgeryReconstruction` (46d70e0). `incident_faces_exact` machine-checked NON-σ-derivable in the σ-FORWARD form (`forward_fanTriangle_forces_degree_two`); σ-algebra naturally gives the σ-BACKWARD pairing (`spokeFace_head_eq`).
- Recursion driver `thomassen_aux_chordRecursive` + dichotomy decision/packaging: already unconditional.

## Avenues (ranked)
- **(a) Chordless fan via σ-BACKWARD orientation.** R9 to ChatGPT Pro in flight: is the Thomassen `deleteVertex_neighborsConnected_of_fan` consumer rotation-direction-AGNOSTIC? If yes, restate `heads_eq`/the fan path in the σ-predecessor direction → `incident_faces_exact` closes from σ-algebra → chordless base σ-derivable → NO planar cert. Terminal: σ-backward fan + ChordlessOracle constructed clean-3, OR proof it needs global chirality.
- **(b) ChordBranchSupplier wiring** (independent of (a) — do in overlap per 统筹 rule e). Wire the normalized confinements (`bothConfinements_normalized`) → `ChordSideReconstruction` (`Cert.side₁/₂Reconstruction_of_certificateInputs`) → `ChordRecursionData` → feed `chordRecursiveDichotomy_of_suppliers`. Resolve the chordDart 2-valued orientation bit + `Separates` keystone. Terminal: `ChordBranchSupplier` clean-3.
- **(c) If (a) needs global chirality:** build `FanSurgeryReconstruction`/`OrientationCert` from the boundary-cycle φ-orientation (the global handedness is ONE certificate from `outerCycle`'s consistent φ-direction — derive it, don't posit). Terminal: orientation cert constructed from outerCycle, OR honest verdict it's the irreducible planar input with the exact missing field.
- **(d) Final assembly:** both suppliers → `ChordRecursiveDichotomy` → `PlanarInputs` → `fiveColor_of_planarInputs` unconditional. Terminal: Ch35 = 40/40.

## Fallback
If chordless genuinely needs a planar-orientation certificate not derivable from `outerCycle`'s φ-orientation, the honest end-state is `fiveColor_of_planarInputs` conditional on ONE named, non-vacuous, machine-isolated orientation cert — with everything else unconditional. That is a faithful close, not a wall.

## Terminal condition for the run
Ch35 fully unconditional (40/40), OR every avenue at its terminal verdict with the single irreducible certificate precisely named + the full integrated build green.

## RUN_LOG
## Run 2026-06-15 (automode, explicit /automode invocation after sustained 继续清 direction)
- doctrine: HANDOFF/ch35-ENDGAME-DOCTRINE.md
- starting: avenue (a) R9 in flight (chordless σ-backward), avenue (b) dispatched in overlap (统筹 rule e)
- end: <fill on close>
- final result: <fill on close>
