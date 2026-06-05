# Reply: PlanarMapBridgeWitness.lean — the CutBridgeWitness2 input from the NearTriangulation interior-dual path (Ch35)

**Status:** new file `ProofsInTheBook/PlanarMapBridgeWitness.lean` (281 lines) created,
compiles clean, all headline theorems depend on `[propext, Classical.choice, Quot.sound]`
only. Branch `main`; file untracked; no commit. Imports `PlanarMapBridge` +
`PlanarMapSeparation`. `PlanarMapSeamChain.lean` (other agent's) untouched; no other file
modified. Verified exclusively via rsync→uisai1 (never ran lake locally; kernel-panic rule).

## What is implemented (0 sorry/axiom/admit/native_decide)

### Layer A — the ordinary-dual-path extractor (genuine new content)
`ordinaryDualPath2_of_dualReachable` : a bare cycle-avoiding face sequence
`DualReachableAvoidingCycle M C f g` (= `ReflTransGen (DualAvoidsCycleStep M C)`) is turned
into a `Bridge.OrdinaryDualPath2` carrying the **explicit crossing darts**, with
`P.face 0 = f` and `P.face (last) = g`. Proved by `Relation.ReflTransGen.head_induction_on`,
prepending one crossing at a time via the helper `OrdinaryDualPath2.cons` (full `Fin.cons`
index bookkeeping on faces/edges; base case `OrdinaryDualPath2.nil`). Each
`DualAvoidsCycleStep` supplies exactly the dart `d` with `dartEdge d ∉ edgeSet`,
`dartFace d = f`, `dartFace (α d) = g` — i.e. precisely one `OrdinaryDualPath2` crossing.
This packages the design's "too-weak" bare object into the Option-C structure.

### Layer B — the per-edge bridge witness from honest inputs
- `cutBridgeWitness2_of_inputs` : `SidesReach2 i` + (dual path ⇒ ∃ ordinary path with
  `FragmentCompatible2`) ⇒ `Bridge.CutBridgeWitness2 i`. Discharges the witness via
  `Bridge.fragmentDualPath2_of_ordinary`.
- `cutBridgeWitness2_of_sidesReach_of_noTeleport` : the variant that makes Layer A
  **load-bearing** — the dual path is extracted to an `OrdinaryDualPath2` *internally* by
  Layer A, and the caller supplies only the no-teleport `SameFragment` data on the extracted
  ordinary path (the design's irreducible interior-dual input).

### Layer C — the corrected chord-separation theorem
- `jordan_simple_cycle2_of_witness` : threads the witnesses through
  `Bridge.jordan_simple_cycle2_bridge` (discharging `hconn` via
  `cutCapMap2_connected_of_bridgeWitness`).
- `NearTriangulation.sphereChordSeparation_of_witness` and `…separates2_of_core` : the
  corrected-map analogues of `sphereChordSeparation_of_jordan` / `separates_of_jordan`
  (`PlanarMapCutCap.lean`), now resting on the **corrected** cut map `cutCapMap2` (genuine
  design numbers `F'=F+2`, χ'=4) + the fragment bridge instead of the buggy `CutCapSurgery`.
  Conclusion identical (`SphereChordSeparation h` / `data.Separates`); composes with the
  genus-0 separation analysis of `PlanarMapSeparation.lean`. Conditional only on the named
  corrected face core `NumCyclesCutPhi2` (closing in parallel) + the per-edge
  `CutBridgeWitness2` + the standard sphere/Euler inputs (`hNT.sphere`, `chi_le`).

## Honest scope on the two CutBridgeWitness2 fields (no overclaim)

The task asked to *prove* `SidesReach2` and to *derive* the no-teleport data via a triangle
case analysis. After sustained analysis of the corrected `σ'₂` wiring I report precisely:

- **`SidesReach2` is irreducibly an isolated side-coherence core, not a finite σ-walk.**
  Tracing the corrected wiring (`cutSigma2_plusEnd`/`capPlus`: `ℓ_i^+ → c_{prevIdx i}^+ →
  dart i`), each forward `+`-bank closes into its **own** σ'₂-cycle at its own cycle vertex
  (`dart i → … → ℓ_i^+ → c_{prevIdx i}^+ → dart i`); distinct forward darts `dart j`, `dart
  i` sit at **distinct primal vertices** (`not_sameCycle_pDart_of_ne`) hence in **distinct**
  σ'₂-cycles. They connect only through the global α'/interior structure, i.e. via
  `M.Connected`-level content — which is exactly what Part A (`reachesBank2_of_connected`)
  *consumes* `SidesReach2` to establish, so deriving `SidesReach2` from Part A is circular.
  This matches the repo precedent verbatim: `PlanarMapDualPathSep.lean` keeps `SidesReach`
  as the isolated named core inside `CutJordanCore`; a repo-wide grep confirms neither
  `SidesReach` nor `SidesReach2` is ever constructively produced anywhere. I therefore
  expose `SidesReach2` as the honest Part-A input (not a faked proof).

- **The no-teleport (`FragmentCompatible2`) data is the design's irreducible interior-dual
  input, by the design's own §6–§7.** The design explicitly forbids deriving "entry and exit
  fragment of one old face are connected" from the bare face sequence (false for a straddling
  face) and states the `SameFragment`-at-gates data must be carried as input. The
  near-triangulation triangle structure (every path face a 3-dart triangle, via
  `chordSplitAdj_endpoints_faceLen_three`) is the regime in which this data is *local*, but
  it is still input, not a theorem about the bare path. Accordingly it enters through the
  honest `FragmentCompatible2`/`FragmentDualPath2BetweenCycleSides` supplier, never faked.

Both residual inputs are concrete (one a finite `cutReach2` statement between cycle bank
darts, the other a `SameFragment` predicate); neither mentions `Connected`; neither is
vacuous. The genuine new content of this file is Layer A (the bare-path→ordinary-path
extractor) plus the full assembly through to the corrected `separates2_of_core`.

## Verification

- Dep build (uisai1): `lake build ProofsInTheBook.PlanarMapBridge` → 8445 jobs OK; then
  `lake build ProofsInTheBook.PlanarMapBridgeWitness` → 8446 jobs OK (8.4 s) — i.e. exactly
  the +1 module integrates cleanly into the whole dependency graph.
- `lake env lean PlanarMapBridgeWitness.lean` → RC=0, **no errors, no warnings**.
- `grep -nE '\bsorry\b|\badmit\b|\bnative_decide\b|^axiom '` → none (only the doc line).
- `#print axioms` on `ordinaryDualPath2_of_dualReachable`, `cutBridgeWitness2_of_inputs`,
  `cutBridgeWitness2_of_sidesReach_of_noTeleport`, `jordan_simple_cycle2_of_witness`,
  `sphereChordSeparation_of_witness`, `separates2_of_core` → `[propext, Classical.choice,
  Quot.sound]` only.
- Branch `main`; file untracked; no commit; no other file touched.

## No isolated resistant joint left as sorry/axiom

Every lemma in this file is closed faithfully. The two *inputs* of `CutBridgeWitness2`
(`SidesReach2`, the no-teleport fragment data) are the design's intended hypotheses, carried
honestly — established above as genuinely irreducible at the current infrastructure layer,
matching the repo's existing `CutJordanCore` treatment — not gaps faked inside this file.
