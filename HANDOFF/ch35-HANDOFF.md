# Ch35 (Five Color Theorem, planar instantiation) — HANDOFF

Last updated 2026-06-15. Branch state: ~60 commits this run, full integrated build GREEN (8873 jobs, 0 errors, 0 sorryAx). Everything below is clean-3 `[propext, Classical.choice, Quot.sound]` unless noted.

## TL;DR
`Chapter35.chapter35 : FiveColorReducible G → Colorable 5` was already proven. The open front is the planar instantiation. This run drove it to:
**`ZinanCh35Final.fiveColor_planar_of_recursionResiduals (hNT) (R : Ch35RecursionResiduals (ULift (Fin 5))) : M.toSimpleGraph.Colorable 5`** — every near-triangulation 5-colorable, UNCONDITIONAL on everything except ONE residue: the recursion's per-call boundary-cycle data `outer_simple` (boundary simplicity / no cut-vertex) + `inner_tri` for the strictly-smaller maps. NOT 40/40. The residue is sharply isolated + machine-characterized.

## WHAT IS DISCHARGED (unconditional clean-3)
The entire discrete-Schoenflies confinement layer + fan layer:
- §3.3 repair: `edge_core` was FALSE (unsatisfiable); repaired bounded (b1ae08f). 
- Coverage atom `numComp(OuterDualStep)=2` via genus-slack + route-B swap-peeling (ZinanCh35BankCount/OuterSlack/OuterDual/OuterCount, 5e622da).
- General `SimpleCycleBankTheorem` for ANY SimplePrimalCycle — numComp=2 + bank labels (ZinanCh35CycleBank + ZinanCh35BankLabels, 873cbe6).
- σ-star `SideRegionInterChordEnds` (ZinanCh35StarConn, 60d17bc); `edge_core`/`BoundedFacePartition`/`OuterDartArc₁` (ZinanCh35EdgeCoreFinal, 105ff26).
- BOTH side confinements UNCONDITIONAL by construction — arc↔side residue eliminated via normalizedChordSplitData (ZinanCh35Aligned.bothConfinements_normalized, 143e8a1); side-2 mirror (ZinanCh35Side2Confine, 1c61c96). [The chord∪path₂ bank route: ZinanCh35ArcSide 1c89696; the ChordArcBankOrientation→ArcSideIdentification chain: ZinanCh35BankOrient a6b33ec, ArcDartRun 5c6d1c7, Contiguity e2784ae.]
- σ-backward chordless fan: deletion connectivity σ-derivable, NO chirality (ZinanCh35FanBackward, 37b3963). FIXED the machine-certified repo bug in IncidentNonOuterFacesExactly (σ-forward triangle_of_pair forces degree≤2; exact_faces had a →/↔ precedence bug = True↔False at outerFace) — flipped to σ-predecessor + parenthesized (PlanarMapBoundaryFan + 5 consumers re-threaded, 76ef1fa). FanIncidenceData now σ-CONSTRUCTIBLE (ZinanCh35ChordlessClose, orientationCert_discharged).
- ChordSplitRegions cover/edge_confined (ZinanCh35Regions, b4919f9). ChordBranchSupplier ← recursion fuel (ZinanCh35ChordResidue, 02eb99e). Both ChordRecursiveDichotomy suppliers wired (ZinanCh35ChordBranch cc7c643, ZinanCh35ChordlessOracle 15bd7a6).
- Boundary-cycle FOUNDATION: nearTriangulation_of_explicit_boundary_classification + arcSplit_of_nodup_nonBoundaryEdge (chord case) (ZinanCh35BoundaryAssembler, 430fe53).
- Both boundary-cycle constructions BUILT: ContiguousInterval₁/₂ (ZinanCh35Contiguous, bd40df8) + DeletedOuterBoundary/MergedFaceSingleOrbit (ZinanCh35DeletedBoundary, 1110f57). The trace-φ itineraries discharge `outer_len` by pure orbit algebra.
- Final assembly: ZinanCh35Final (1cb72ea), ZinanCh35Recursion (ee62b28, the honest conditional endpoint).

## THE SINGLE REMAINING RESIDUE
For each strictly-smaller recursion map (chord side maps; the deleted map):
- `outer_simple` — the new boundary cycle's vertex list is `Nodup` (simple curve, no cut vertex).
- `inner_tri` — every non-outer face is a triangle.
(`arcSplit` FOLLOWS from `outer_simple` via `arcSplit_of_nodup_nonBoundaryEdge` for the chord case — NOT a separate residue.)
These are bundled as: chord side = `ChordSideNT.ContiguousInterval` inputs (+ one isolated CombMap non-degeneracy `Side₁/₂ChordIncidenceNonDegenerate`, ρa₀≠βa₁, satisfiable); deleted = `ZinanCh35DeletedBoundary.DeletedSeamData` (MergedOuterArcData + CleanFaceClass inner_tri + the φ'-cycle). Plus the legitimate recursion fuel (pullback lists Lₛ=L∘ι, precolored placement — Thomassen strong-induction, not a gap).

## MACHINE-CHECKED ACCOUNTING (why the easy routes fail)
- `ZinanCh35BoundaryAssembler.boundaryArcSplit_consecutive_unsatisfiable` — universal arcSplit-from-Nodup is FALSE (cut-vertex obstruction).
- `ZinanCh35DeletedBoundary.mergedFaceSingleOrbit_not_from_genusSlack_alone` — the merged cycle's arcSplit is genuine Jordan data, not a genus/Euler corollary.
- `CutFaceLabel.lean` — a genus-FREE closed-form face label FAILS at genus 1 (K₄ torus). So no all-genera label.
- ChatGPT Pro R10 (HANDOFF/ch35-boundaryCycle-genus0-R10.md): genus-slack closes the COUNT (surjectivity backstop) but cannot identify the φ-orbit or prove its simple boundary cycle.

## RESUME / NEXT ATTACK VECTOR (the open frontier)
Prove `outer_simple` + `inner_tri` for the SPECIFIC genus-0 chord/deletion smaller maps (NOT the universal form, which is refuted):
1. **Chord side `outer_simple`**: the side map's new boundary = chord {u,v} + the side arc. The side arc vertices are a `Nodup` sub-run of `hNT.outerCycle.vertices` (already Nodup, `outer_simple`); u,v are the endpoints. So the new boundary vertex list = [u, arc-internal…, v] should be `Nodup` — derivable from the outer cycle's Nodup + the arc being a contiguous proper sub-run (the chord endpoints don't recur). USE `boundaryArcDartRun` (the arc dart run) + `outer_simple` of hNT. This is list combinatorics, likely closable. `inner_tri`: untouched old faces keep faceLen 3 (hNT.inner_tri) + the chord triangle — `rg` `InnerFacesUntouched`/`chord_inner_tri`.
2. **Deleted map `outer_simple`**: the merged boundary = surviving outer arc + fan edge darts. Its Nodup needs: the fan neighbors are distinct + don't repeat the surviving arc vertices. The σ-backward fan (ZinanCh35FanBackward) + `BoundaryChordless` (no chord ⟹ fan neighbors are boundary-distinct). `inner_tri` already via CleanFaceClass.
3. If (1)/(2) close ⟹ discharge `ChordRecursionInputSupplier` + `ChordlessOracleResidual` ⟹ `Ch35RecursionResiduals` ⟹ `fiveColor_planar_of_recursionResiduals` UNCONDITIONAL ⟹ Ch35 = 40/40.
4. Consider R11 to ChatGPT Pro: "is outer_simple (boundary Nodup) for the chord side / deleted map derivable from hNT's outer_simple + the arc/fan structure (genus-0, 2-connected), the cut-vertex obstruction notwithstanding (it's about the universal case)?"

## REPO / BUILD NOTES
- Bare `lake` redirects to an unreachable remote (uisai1); use `$HOME/.elan/bin/lake build` for full builds.
- All new files wired into `ProofsInTheBook.lean`. Audit.lean needs `#print axioms` lines added for the new headlines if you want them in the audit.
- HANDOFF blueprints (ChatGPT Pro R4–R10): ch35-{bankcount-routeB-swappeeling, residual-collapse-R6, oppArcStarCore-direct-R7, lemma6-boundarybank-derivation, arcSide-via-bankTheorem-R8, chordless-sigma-backward-R9, boundaryCycle-genus0-R10}.md + this file + ch35-ENDGAME-DOCTRINE.md (RUN_LOG).
- Memory: ~/.claude/.../memory/project-ch35-status.md (full reduction history).

## DISCIPLINE NOTE (for the next driver)
This run had TWO over-claims ("all Jordan content done", "fan not irreducible") caught + corrected by agents that refused to fake and verified against source. Every "irreducible" verdict this run was eventually refuted by a new route — EXCEPT the current boundary-cycle residue, which has machine-checked obstructions only for the UNIVERSAL/genus-free form. So: try the genus-0-SPECIFIC chord/deletion derivation (vector 1/2 above) before concluding it's a genuine input. The pattern: walls fall to "use the sphere/genus-0 + the specific construction's structure."
