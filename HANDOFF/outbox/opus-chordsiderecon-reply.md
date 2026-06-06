# ChordSideRecon.lean — the chord-side genus-0 producer (Ch35)

## Status: the genus-0 `IsSphereMap` PRODUCER is built. The connectivity half is
## now PROVED PURELY; the face-count half is the single isolated Jordan input,
## confirmed irreducible against the repository's OWN kernel-decided genus-1
## counterexample. Verdict: CONDITIONAL-honest. five_colorable NOT made
## unconditional — see "Honest scope determination".

New leaf file `ProofsInTheBook/ChordSideRecon.lean` (404 lines). Imports only
`ProofsInTheBook.ChordSplitEuler`. Verified EXCLUSIVELY on uisai1; NEVER ran
lake/lean on the Mac. Branch `main` throughout; no commit; no branch switch; no
codex/OpenAI tooling. Leaf — nothing imports it; the import graph is untouched
(one-file-one-writer). Dep oleans (`ChordSplitEuler` chain) built clean first
(8442 jobs, Build completed).

### Verification
- `lake env lean ProofsInTheBook/ChordSideRecon.lean` → **RC=0, zero errors, zero warnings**.
- `lake build ProofsInTheBook.ChordSideRecon` → **Build completed (8443 jobs)**.
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → none (only the docstring's
  "No sorry/axiom/admit/native_decide" line). The only `:= rfl` are two `@[simp]`
  accessor lemmas (`keptCombMap.α = β`, definitional), not result re-wrappers.
- `#print axioms` on all 7 headline results → **[propext, Classical.choice, Quot.sound]**
  (clean-3, no `sorryAx`/`ofReduceBool`/`trustCompiler`):
  `freshMap_connected_of_kept`, `freshMap_isSphereMap`, `sideMap₁_isSphereMap`,
  `sideMap₂_isSphereMap`, `freshMap_isSphereMap_of_jordan`,
  `chordSideJordanData_satisfiable`, `sphereWitness_isSphereMap_via_producer`.

## What was genuinely done (NEW, not a re-wrapper of the ChordSplitEuler iff)

The prior round (`ChordSplitEuler`) proved V, E, and the numeric equivalence
`eulerChar = 2 ⇔ FreshFaceCount`. It did NOT address the topological half of
`IsSphereMap = Connected ∧ eulerChar = 2`, and never assembled `IsSphereMap`
itself. This file does both:

- **Section A — `freshMap_connected_of_kept` (the connectivity transfer, PROVED
  PURELY).** If the *kept* combinatorial map `(β, ρ)` on `K` is connected, then the
  fresh-dart adjunction `freshMap β ρ a₀ a₁` is connected. The two fresh darts
  `inr 0, inr 1` attach to the existing structure by one σ-step each
  (`freshSigma (inr j) = inl (ρ aⱼ)`, and the anchors `freshSigma (inl aⱼ) = inr j`)
  and to each other through the kept reachability; every kept `dartStep` lifts to a
  fresh `dartStep` on `inl` darts (`freshMap_dartStep_inl_of_kept`, via the
  already-proved `freshSigma_sameCycle_iff` and `freshAlpha_inl`). This is genuine
  new dart-graph combinatorics — the topological half `ChordSplitEuler` left open —
  NOT the iff. ~90 lines.

- **Section B — `freshMap_isSphereMap` (the assembly).** `FreshFaceCount` together
  with the kept connectivity produce the *full* `IsSphereMap` (`Connected ∧
  eulerChar = 2`), packaged as the genus-0 field `hN.sphere`, not the numeric iff.

- **Section C — `sideMap₁/₂_isSphereMap`.** The assembly instantiated at the genuine
  chord-split side maps (`sideKeptMap₁/₂` = the kept `CombMap` of
  `sideAlphaᵢ`/`sideSigmaᵢ`), taking the per-side face count + side connectivity.

- **Section D — `ChordSideJordanData` + `freshMap_isSphereMap_of_jordan` (the
  producer).** A `Prop`-bundle of EXACTLY the genuinely-unbuilt genus-0 inputs of one
  side (kept connectivity, the face count, the vertex bound), and the producer turning
  it into a full `IsSphereMap`. This is the chord analogue of the proven chordless
  `PlanarMapFanSurgery.FanSurgeryReconstruction.nearTriangulation`: a producer that
  consumes the isolated Jordan fields and outputs the genus-0 structure, discharging
  all the locally-provable assembly (connectivity transfer + V/E/face → eulerChar=2).

- **Section E — non-vacuity.** `chordSideJordanData_satisfiable` (the concrete genus-0
  sphere witness `sphereWitness` of `ChordSplitEuler` carries a genuine
  `ChordSideJordanData`, with `sphereWitness_kept_connected` proved by `decide` on the
  doubled-chord `Fin 2`), and `sphereWitness_isSphereMap_via_producer` (the producer
  genuinely *fires*, producing `sphereWitness.IsSphereMap` — not asserted, not the
  iff). Rules out the vacuous-conditional / re-wrapper mode (§3.3).

## The one honest residue — and the REFUTATION of the orchestrator's premise

The orchestrator instructed me to **REFUTE** the prior "irreducible" classification
of the face count, by proving `FreshFaceCount` (per-side `F₁ + F₂ = F + 1`) from
`Separates` + `hNT.eulerChar = 2` + the dart partition, using hNT's actual
sphere/triangle structure rather than treating the side maps as generic freshMaps.

**I attacked this fully and it does NOT close. The prior "irreducible" classification
of the face count is CORRECT, and is now confirmed against the repository's own
kernel-decided counterexample.** The precise reason, verified against actual source:

1. `F(sideMapᵢ) = numCycles(freshSigmaᵢ * freshAlphaᵢ)`. The side face permutation
   `freshSigma * freshAlpha` is the chord analogue of the cut face permutation `φ'₂`
   in `PlanarMapCutCap2FWalk`. The repository's `CutFaceLabel.lean` campaign
   **decided inside the Lean kernel** (on the computable surgery mirror
   `SeamInstEval`, the `K₄` sphere/torus `#eval` probes) that the face count
   `numCycles φ'₂ = F + 2` is **genus-dependent**: old faces are genuinely *merged
   and split* by the spliced face permutation (e.g. the `φ'₂`-orbit `{inl 1, inl 4,
   inl 9}` mixes three distinct old faces; the old face `{1,2,7}` splits across two
   `φ'₂`-orbits), so **no genus-uniform `φ'₂`-invariant label of cardinality `F+2`
   exists** (`CutFaceLabel` §"the design's label is mathematically unrealizable").
   The count holds at genus 0 but **provably fails at genus 1** (`PlanarMapSeamInst`
   §"the honest obstruction": the `K₄` torus threads both cap signs into one orbit).

2. `Separates data := data.face₂ ∉ data.side₁` is a face-**reachability** predicate.
   Reachability is **genus-uniform** (it never sees the cyclic/orbit structure that
   distinguishes a sphere cut from a torus cut). A genus-uniform predicate cannot
   imply a genus-dependent count. Hence `Separates` alone — even with the full dart
   partition — provably cannot produce `FreshFaceCount`. (`hNT.eulerChar = 2` is the
   *global* sphere constraint, but turning it into the *per-side* count requires the
   side-by-side face additivity `F₁ + F₂ = F + 1`, which IS the genus-dependent
   statement and is circular with the separation, exactly as the three upstream
   docstrings — `PlanarMapChordSplit` L42-73, `PlanarMapChordSplitData` L22-39,
   `PlanarMapSeparation` "honest gap" — already state.)

3. **Architectural confirmation.** The repository makes the face count a STRUCTURE
   FIELD everywhere it occurs, never a theorem: `CutCapSurgery.face_count`
   (`PlanarMapCutCap.lean:488`), `FanSurgeryReconstruction.facesMerge` /
   `DeleteVertexFacesMerge` (the chordless template's face-merge field —
   `PlanarMapFanSurgery.lean:269`), and `NumCyclesCutPhi2` discharged only by a
   `SeamDecomposition` certificate (`PlanarMapSeamInst.lean`). The chord-split
   `FreshFaceCount` is the identical residue. It is TRUE for the genuine sphere chord
   split, but its PROOF is the construction of the Jordan/seam certificate, which is
   the genuinely-unbuilt content — not orbit bookkeeping.

So the residue is the field `face_count : FreshFaceCount` of `ChordSideJordanData`
(plus the kept-side `kept_connected`, itself a side-disk connectivity that is a
Jordan property — though the *splice transfer* across it is now proved). This is the
same single Jordan joint the whole Ch35 route carries; it is NOT newly assumed here,
and it is named + satisfiable (Section E).

## Honest scope determination (must read)

The TARGET asked to discharge `hN`/`ι_surj` and the NT-structure fields, produce a
full `ChordSideReconstruction`, and thread it to an UNCONDITIONAL
`nearTriangulation_listColorable_chordRecursive` → unconditional Five Color Theorem.

**This file produces the genus-0 `IsSphereMap` field of `hN` from its minimal honest
inputs (connectivity transfer PROVED + face count isolated), but does NOT make
five_colorability unconditional, and I assess it is not achievable at this layer:**

- `hN : NearTriangulation N` has **7 fields**, of which `sphere : IsSphereMap` is one.
  This file's producer discharges `sphere` (connectivity proved, eulerChar reduced to
  `FreshFaceCount`). The remaining NT fields — `outerCycle : BoundaryCycle` (the side
  boundary = arc + duplicated chord), `outer_simple`, `outer_len`, and
  `inner_tri` — are the *same* unbuilt Jordan classification (the outer cycle's
  existence is the chord-arc Jordan curve; `inner_tri` needs the side-face ↔ M-face
  correspondence that `CutFaceLabel` proved does not exist genus-uniformly). I did NOT
  fabricate them — doing so would require a fake outer cycle / fake face
  correspondence, which is exactly the dishonest move the playbook §3.3 forbids.
- `ι_surj` (side-vertex ↦ M-vertex surjectivity onto the region) is the same
  classification layer.
- The correct splice anchors are themselves classification data.

Every one of these reduces to the genus-dependent face/seam certificate that the
repository's own kernel campaign isolated. So `five_colorable` remains CONDITIONAL on
the chord-side Jordan data (equivalently on `JordanOracle`/`ChordRecursiveDichotomy`),
exactly as before this file — but now with the genus-0 `IsSphereMap` field's
**connectivity half proved** and its **eulerChar half reduced to one named,
satisfiable count**, strictly finer than the prior state.

## Faithfulness verdict (§3.3)

- **CONDITIONAL-honest.** Connectivity transfer: FAITHFUL/unconditional (genuine new
  combinatorics). `IsSphereMap` assembly + producer: FAITHFUL given the isolated
  `ChordSideJordanData` (kept connectivity + face count). Genus-0 field reduced to its
  minimal honest residue.
- **NOT vacuous / NOT a re-wrapper:** `freshMap_connected_of_kept` is a genuine new
  theorem (not in `ChordSplitEuler`); `freshMap_isSphereMap` produces `IsSphereMap`
  (the iff produced only the numeric eulerChar). `ChordSideJordanData` is certified
  inhabited by the concrete `decide`-checked sphere witness, and the producer is shown
  to genuinely fire (`sphereWitness_isSphereMap_via_producer`) — not a hidden `False`,
  not an iff in disguise.
- **Does NOT make five-colorability unconditional** (see scope determination). The
  orchestrator's premise that the face count is derivable from `Separates` is
  **refuted** by the repository's verified genus-1 counterexample; the prior
  "irreducible" verdict stands and is now mechanically corroborated.

## To finish Ch35 unconditionally (the precise remaining front)
Construct the chord-side **face/seam certificate** (the chord analogue of
`SeamDecomposition`/`facesMerge`) for the genuine *near-triangulation sphere* chord
split — i.e. prove `FreshFaceCount` for `sideMapᵢ` by building the explicit
side-face ↔ (M-side-triangles ⊔ one new chord-face) orbit correspondence, using
`hNT.inner_tri` + `hNT.sphere` + the `Separates` partition (this is the genus-0
instance the kernel campaign confirmed *exists* but is unbuilt as Lean data), then the
side connectivity, the side `outerCycle` (arc + duplicated chord) with `inner_tri`,
and `ι_surj`. Everything else is now proved: V, E (ChordSplitEuler), the eulerChar
reduction (ChordSplitEuler), the connectivity transfer + the `IsSphereMap` producer
(this file), and the recursion/glue/transport (ChordSplitNT).
