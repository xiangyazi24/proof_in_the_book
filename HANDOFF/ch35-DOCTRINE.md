# Ch35 (Five Color Theorem — planar instantiation) — attack doctrine

## Goal (one sentence)
Discharge the two genuine residuals blocking `ZinanCh35Cert.fiveColor_of_planarInputs`
so that `planar near-triangulation → Colorable 5` becomes unconditional clean-3.

## State (verified 2026-06-14)
- `Chapter35.chapter35 : FiveColorReducible G → G.Colorable 5` — PROVEN clean-3, unconditional.
- The entire `ZinanCh35*` discrete-Schoenflies tree (20 files) + the recursion driver tree
  (`ChordSplitNT`/`ChordSplitFinal`/`ChordDisk`) is ZERO-sorry, all clean-3, but CONDITIONAL on
  posited residual Props. `numCyclesCutPhi2_holds` (cut = exactly 2 dual components on the sphere)
  and `jordan_simple_cycle2_unconditional` (no-cross face separation) are PROVEN.

## The two genuine residuals (everything else reduces to these via proven theorems)

### Avenue (a) — `OppArcStarSeed` (the side-1 confinement; discharges the whole side-1 chain)
`ZinanCh35BankAnchor.OppArcStarSeed` (two fields). Closing it ⟹ `Side₁StarConfinement`
(via `starConfinement_of_oppArcStarSeed`) ⟹ `Side₁SchoenfliesConfinementInput`
(via `confinementInput_of_schoenflies`) ⟹ side-1 close — ALL reductions proven clean-3.
The chord∪arc cycle `C` is constructible via `ZinanCh35ChordCycle.chordCycleData`.
  - **edge_core** (the hard one): non-chord dart e with tail e, head e ∈ sideRegion₁ ⟹ dartFace e ∈ side₁.
    Engine (membership⟹reachability) provably can't do this back-direction. Needs the exactly-2-components
    completeness: side₁ ⊔ side₂ = all faces (from `numCyclesCutPhi2_holds`), then a vertex-region/face-side
    bridge. sideRegion₁ = {w | w = tail of some kept side-1 dart (∉ keptDel₁)}.
  - **oppArc_star_seed** (local): each path₂-internal vertex w, each non-chord star dart d → a seed star
    dart whose face dual-reaches face₂ avoiding C, joined to d by a cut-free rotation walk. The seed is
    LOCAL (one dart); `dualReach_face₂_of_starWalk` transports it to the whole star.
  Terminal: prove `OppArcStarSeed` (or `Side₁StarConfinement`) as a theorem, OR report the sharp
  sub-residual that genuinely needs new infrastructure.

### Avenue (b) — `ChordRecursiveDichotomy` supplier (the recursion driver)
`ChordSplitNT.ChordRecursiveDichotomy α` — per recursive near-triangulation: either a two-sided
`ChordSideReconstruction` pair (built from avenue (a)'s confinement on both sides) or a chordless oracle
(outer-fan base case). Needs: chord-existence/well-founded recursion + chordless base.
Depends on (a) for the side reconstructions.

### Fallback
If (a)'s `edge_core` two-component bridge is the wall: isolate the precise missing combinatorial-map
lemma (vertex-region ⟺ face-side correspondence) and grind it standalone; it is the reusable core.

## Terminal conditions
- (a) closed ⟹ side-1 (and by symmetry side-2) confinement unconditional; major progress, propagates up.
- (b) closed on top of (a) ⟹ `fiveColor_of_planarInputs` unconditional ⟹ Ch35 = 40/40.

## Discipline
§3.3 truth-first: both (a) fields are TRUE + non-vacuous (region inhabited, opposite arc has an internal
vertex). Verify truth before grinding; report sharp sub-residuals honestly; no faking; one file per writer;
self-verify `lake env lean`, never `lake build` while agents edit.

---

## §3.3 FINDINGS (2026-06-14, ChatGPT pbook e62f78cb + 2 Opus grinds) — the confinement residual is UNSATISFIABLE as stated

The whole side-1 confinement chain is mechanically clean-3 but reduces the SATISFIABLE
`Side₁SchoenfliesConfinement` to residuals that are FALSE / under-specified. `#print axioms`
cannot detect this (vacuously-valid conditional reductions). TWO concrete issues:

### Finding 1 — `edge_core` is FALSE as stated (too-strong field; missing bounded-dart hypothesis)
`Side₁StarConfinement.edge_core` (Schoenflies:182) claims: non-chord e, tail/head ∈ sideRegion₁ ⟹
`dartFace e ∈ side₁`. COUNTEREXAMPLE (ChatGPT, confirmed against defs): the outward dart of an
outer-arc₁ boundary edge has both endpoints in sideRegion₁, is non-chord, but `dartFace e = outerFace ∉ side₁`.
ROOT: `keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}` (PlanarMapChordSplit:412) — outer-arc₁ darts are
KEPT via `outerArc₁`, NOT via their face being in side₁. The consumer
`vertexStar_confined_of_starConfinement` (Schoenflies:228) derives `edge_confined` SOLELY through
edge_core (face∈side₁ ⟹ e∈sideDarts₁ ⟹ kept), ignoring the outerArc₁ route — so it forces edge_core
to prove a false thing on outer darts ⟹ `Side₁StarConfinement` UNSATISFIABLE.
**FIX (designed):** (a) add `M.dartFace e ≠ hNT.outerFace` to `edge_core` in Side₁StarConfinement +
OppArcStarSeed + Side₁StarBankAnchor; (b) rewrite `vertexStar_confined_of_starConfinement.edge_confined`
to CASE-SPLIT on `dartFace e = outerFace`: outer dart ⟹ `e ∈ outerArc₁ ⊆ keptSet₁` directly (needs:
an outer boundary edge between two sideRegion₁ vertices is on arc₁); bounded dart ⟹ corrected edge_core;
(c) prove the corrected (bounded) edge_core via ChatGPT's CLOSURE-INTERSECTION route, NOT vertex rotation:
  - `bounded_face_partition`: every non-outer face ∈ side₁ ∨ side₂ (needs the cut-component ↔ R-reachability
    bridge — `numCyclesCutPhi2` counts components; bridge them to R via "triangulated-disk dual is connected
    through non-boundary edges"). Disjointness = the proven separation.
  - `sideRegion_inter_subset_chordEnds`: w ∈ sideRegion₁ ∧ w ∈ sideRegion₂ ⟹ w = u ∨ w = v (vertex-level
    Schoenflies; the two closed side disks meet only at the chord ends).
  - `endpoints_mem_sideRegion₂_of_face`: dartFace e ∈ side₂ ⟹ both endpoints ∈ sideRegion₂.
  - `edge_eq_chord_of_endpoints_chordEnds`: endpoints ∈ {u,v}, non-loop ⟹ edge = chord (needs simple-map).
  Then bounded edge_core: assume dartFace e ∈ side₂ → endpoints ∈ sideRegion₂ ∩ sideRegion₁ = {u,v} →
  e = chord, contra. ~8 lines once the 4 lemmas land.
  NOTE: also fix the sideRegion₁ "kept-dart" def caveat (ChatGPT §3): incident_side1_face_has_kept_tail
  may fail if a side-1 triangle's darts are all boundary/chord-deleted; use closure-incidence or prove
  the witness lemma.

### Finding 2 — `oppArc_star_seed` needs the `path₂ ↔ boundary-dart` bridge (`OppArcSeedInput`)
COMMITTED a54ed0a. `data.arc` (from `BoundaryCycle.arcSplit`) is a pure vertex/edge-list with no darts and
no tie to the chordCycleData cycle C. Decisive witness: a path₁-internal w ALSO satisfies
`w ∈ outerCycle.vertices ∧ w ≠ u,v` yet reaches face₁ ≠ face₂ — so inert path₂ membership can't imply the
dual-reach conclusion. Missing geometry isolated as `OppArcSeedInput` (ZinanCh35OppArcSeed.lean), target
proved conditional on it clean-3. FIX: build the path₂↔dart identification (tie arcSplit's path₂ to the
actual boundary darts of M on the side-2 arc, then the seed = the side-2-pointing dart).

### Net
Closing Ch35 requires, in order: (1) correct edge_core (+ consumer case-split) and prove it via
closure-intersection [4 sublemmas + partition coverage bridge]; (2) the OppArcSeedInput path₂↔dart bridge;
(3) the recursion supplier ChordRecursiveDichotomy. This is genuine multi-piece planar topology, now
diagnosed to the sharpest residuals with proof routes designed — NOT a quick close. The current tree's
"reduction to OppArcStarSeed" must be REPAIRED (edge_core is false as stated) before it is a valid reduction.
