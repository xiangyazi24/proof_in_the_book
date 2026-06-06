# SeamApplication.lean — near-triangulation chord application of the F-side `BankStepCert` route (Ch35)

## Status: COMPLETE. 0 sorry / 0 axiom / 0 admit / 0 native_decide. Axioms clean.

File: `ProofsInTheBook/SeamApplication.lean` (~270 lines). Imports
`ProofsInTheBook.SeamStructure` + `ProofsInTheBook.PlanarMapBridgeWitness`.
Verified EXCLUSIVELY on uisai1 (`lake env lean`), EXIT 0, zero warnings/errors.
NEVER ran lake/lean locally on the Mac. Branch `main` throughout; no commits.
Leaf file — nothing imports it; import graph + Audit.lean untouched (one-file-one-writer).

## What was built (all verified)

### 1. The `faceCorr₂` step destinations on the bank-end darts (the heart of the task)
The `phiLift`-orbit of an `inl d` dart is the **face** of `M` containing `d`
(`phiLift = M.φ ⊕ 1`); caps are `phiLift`-fixed singletons. The bank-end step actions
are pinned symbolically from the proven `φ'₂` closed forms post-composed with `phiLift⁻¹`:

- `faceCorr2_inl_dart`: `faceCorr₂ (inl (dart i)) = inl (φ⁻¹ (dart (nextIdx i)))`
  — the **forward** bank-end step.
- `faceCorr2_inl_alpha_dart`: `faceCorr₂ (inl (α (dart i))) = inl (φ⁻¹ (pDart i))`
  — the **reverse** bank-end step (the `−`-bank re-entry adjacent to the `i`-th cap).
- `pOrbOf_faceCorr2_inl_dart`: the forward step's destination `phiLift`-orbit **equals
  the face (φ-orbit) of `dart (nextIdx i)`**, proven as an orbit identity (φ⁻¹ moves
  within the face). This **locates** the isolated seam joint: whether that face
  coincides with the face of `dart i` is the genus-0 seam incidence `phiLift vᵢ = u_{i+1}`.

The cap half of `step_component` was already symbolically forced by
`SeamStructure.faceCorr2_capP_cases` / `faceCorr2_capM_cases` (every cap → a bank-end or
a cap, both adjacent to the cap's own generator edge). So the destination analysis
confirms: **only the forward bank-end step is the genuine cut-dependent residue**, and it
is the boundary-cycle outer-face walk (arc darts) / inner-triangle adjacency (chord dart).

### 2. The F-side Jordan from a `BankStepCert` + bridge witnesses
- `jordan_simple_cycle2_of_stepCert_witness`: threads
  `jordan_simple_cycle2_lower_of_stepCert` (F-side lower bound `(cutCapMap2).F ≥ M.F + 2`,
  via the per-step certificate) with the bridge-witness connectivity discharge
  `cutCapMap2_connected_of_bridgeWitness`. The F-side analogue of
  `jordan_simple_cycle2_of_witness`, with `NumCyclesCutPhi2` replaced by the strictly
  smaller per-step field, and the `chi_le` Euler-inequality parameter **eliminated** (the
  lower-bound route derives the upper bound `F ≤ M.F` internally from `hchi` alone).

### 3. The near-triangulation chord separation
- `NearTriangulation.sphereChordSeparation_of_stepCert` — `SphereChordSeparation h` form.
- `NearTriangulation.separates2_of_stepCert` — `data.Separates` end-to-end form.
Both mirror `sphereChordSeparation_of_witness` / `separates2_of_core` but feed the F-side
from `BankStepCert` instead of `NumCyclesCutPhi2`, with sphere connectivity/Euler read off
`hNT.sphere`. **Hypotheses reduced to the bridge-witness data + the one F-side certificate.**

## Faithfulness / non-vacuity audit (playbook §3.3)

- **Same conclusion, reduced hypotheses.** `separates2_of_stepCert` proves the identical
  `data.Separates` as `separates2_of_core` (both via `data.separates_of_nearTriangulation`
  on a `SphereChordSeparation`). Its hypothesis set is strictly **smaller**: F-side input
  is the per-step `BankStepCert` (not the exact `NumCyclesCutPhi2`), and the separate
  `chi_le` Euler-inequality parameter is dropped. Verdict **CONDITIONAL-honest**, F-side
  residue isolated to `BankStepCert.step_component`.
- **NOT a re-wrapper.** `faceCorr2_inl_dart`, `faceCorr2_inl_alpha_dart`,
  `pOrbOf_faceCorr2_inl_dart` are genuine new symbolic computations of the bank-end step
  destinations (the bank-end analogues of the cap cases). The Jordan/separation route is a
  new F-lower-bound path, distinct from and lighter than the witness/`NumCyclesCutPhi2` route.
- **NOT vacuous.** `BankStepCert` is satisfiable in principle — it is the F-side certificate
  carrying the seam data, exactly parallel to the witness route's `NumCyclesCutPhi2`. The
  destination-analysis lemmas are exercised in two `example`s against the proven symbolic
  actions (cap → bank-end/cap; forward step → face of next dart), ruling out the vacuous-
  reduction failure mode.
- **F-side input strictly smaller, not inflated.** Per-step `step_component` replaces the
  orbit-wide / exact-count F-side; bridge-witness data `gen`/`Fin (2·len−2)` passed verbatim.

## Axiom audit (all 6 headline decls)
`faceCorr2_inl_dart`, `faceCorr2_inl_alpha_dart`, `pOrbOf_faceCorr2_inl_dart`,
`jordan_simple_cycle2_of_stepCert_witness`, `sphereChordSeparation_of_stepCert`,
`separates2_of_stepCert` → all `[propext, Classical.choice, Quot.sound]`.
No `sorryAx`, no `ofReduceBool`/`native_decide`.

## ONE truly resistant destination case (named, honest)
The **forward bank-end step** `faceCorr₂ (inl (dart i)) = inl (φ⁻¹ (dart (nextIdx i)))`:
whether its destination face coincides with the face of `dart i` is the genus-0 seam
incidence `phiLift vᵢ = u_{i+1}` (`PlanarMapSeamSpec.lean`). In the repository's abstract
combinatorial setting this is the embedding datum — for arc (boundary) darts it is the
outer-face boundary-cycle walk visiting consecutive arc darts in order; for the chord dart
the inner-triangle adjacency. It is NOT derivable from `SimplePrimalCycle` + the
`NearTriangulation` face structure alone (consistent with `PlanarMapOuterArc.lean`'s
`MergedOuterArcData` carrying it as a structure input, and `SeamDecomposition` /
`NumCyclesCutPhi2` carrying it on the witness route). It is therefore carried honestly as
the single F-side certificate field `BankStepCert.step_component`, the same residue the
entire Chapter-35 F-side rests on — `pOrbOf_faceCorr2_inl_dart` locates it precisely; it is
named, not faked.

## Ch35 remaining frontier (precise)
With this file, Chapter 35's chord separation has TWO complete routes to the identical
`data.Separates`, each resting on exactly one isolated F-side fact plus bridge-witness data:

  Route A (witness/exact count):  `NumCyclesCutPhi2`  →  `separates2_of_core`
  Route B (this file, lighter):   `BankStepCert.step_component`  →  `separates2_of_stepCert`

The remaining chapter-wide frontier (unchanged by this layer, both routes share it):
1. **The single isolated F-side fact** — either `NumCyclesCutPhi2` (= the seam decomposition
   `SeamDecomposition → numCyclesCutPhi2`) or, equivalently for Route B, the genus-0
   instantiation of `step_component` (`phiLift vᵢ = u_{i+1}`). This is the named open core
   `NumCyclesCutPhi2`'s seam content; it needs `phiLift vᵢ = u_{i+1}` as a concrete
   `SimplePrimalCycle`/`SeamDecomposition` fact from the chord+arc embedding.
2. **The bridge-witness data** `CutBridgeWitness2 i` (Part-A `SidesReach2` side-coherence +
   the no-teleport `FragmentCompatible2` interior-dual data) — the design's irreducible
   interior-dual input, supplied as honest input per `PlanarMapBridgeWitness.lean`.
3. The chord-cycle construction `hsub` + index `i₀`/`hleft`/`hright` (the `chord+arc` cycle
   from `ChordSplitData`).

Items (2),(3) are wiring/structure inputs; the sole genuine math residue is item (1), the
seam incidence — now located by `pOrbOf_faceCorr2_inl_dart` and isolated to one cert field.

## Notes for wiring
- Leaf file. To activate: add `import ProofsInTheBook.SeamApplication` to
  `ProofsInTheBook.lean` and the 6 `#print axioms` lines to `Audit.lean` (import the module
  there too). I own only SeamApplication.lean; did not touch the import graph or Audit.lean.
- Dep oleans (`lake build ProofsInTheBook.SeamStructure ProofsInTheBook.PlanarMapBridgeWitness`,
  8452 jobs) built clean first on uisai1.

## Verification command
    rsync -az .../SeamApplication.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
    ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
                && lake env lean ProofsInTheBook/SeamApplication.lean'
    → EXIT 0, zero warnings/errors; 6 axiom prints all {propext, Classical.choice, Quot.sound}.
