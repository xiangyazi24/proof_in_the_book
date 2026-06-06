# ChordSideNT.lean — `ChordSideClassification` reduced to ONE named boundary predicate; `sphere` discharged unconditionally

## Status (honest, §3.3): the genus-0/`sphere` field is PULLED OUT of the residue; the headline `five_colorable` stays CONDITIONAL

The orchestration asked to **build `ChordSideClassification = NearTriangulation(sideMap₁)`**
(the `outerCycle`/`inner_tri` fields beyond `IsSphereMap`) using the proven genus-0 disk
structure, thread the full `ChordSideReconstruction` → `chord_case_recursive`, discharge the
chordless `ChordlessOracle`, → **unconditional** `nearTriangulation_five_colorable`.

**What is genuinely closed in this file (the maximal faithful advance):**

1. **`side₁_sphere_unconditional`** — the side-1 `IsSphereMap` (genus-0) field of the
   classification, PROVED **unconditionally** (only `data`, `hsep : Separates`, distinct
   anchors, and the proved anchor-incidence fact `Side₁AnchorsShareFace`). This composes
   `ChordDisk.side₁_isSphereMap_of_disk` with `ChordSideClose.side₁IsDisk_unconditional` —
   a composition that did NOT exist before (ChordDisk's version took `Side₁IsDisk` as a
   hypothesis). The genus-0 `sphere` field is now removed from the residue.

2. **`chordSideNearTriangulation` / `…_of_share`** — **the producer, PROVED**: assembles the
   FULL `NearTriangulation(sideMap₁)` from (a) the unconditional disk-core `sphere` and
   (b) the single boundary predicate `ContiguousInterval` (the correct-anchor classification).

3. **`chordSideClassification_of_contiguous`** — the drop-in for the prior round's named
   residue `ChordReconClose.ChordSideClassification` (defeq `NearTriangulation(sideMap₁)`),
   produced from `ContiguousInterval` + the proved disk core.

4. **`chordSideClassification_iff_contiguous`** — the exact reduction: *given the proved
   anchor-incidence fact*, `ChordSideClassification ≃ ContiguousInterval`. This pins the entire
   chord-side residue to the single correct-anchor boundary predicate, with the `sphere`/
   genus-0 content proved-and-removed (the `Equiv`'s backward map injects
   `side₁_sphere_unconditional`, not a hypothesis — so it is not a re-wrapper).

`ContiguousInterval` carries exactly the `NearTriangulation` fields *other than `sphere`*:
`simpleGraph`, `outerFace`, `outerCycle`, `outer_simple`, `outer_len`, `inner_tri`. It is the
chord analogue of the chordless `FanSurgeryReconstruction`'s boundary fields.

New file (owned, fresh): `ProofsInTheBook/ChordSideNT.lean` (≈250 lines). Imports
`ChordReconClose` + `ChordDisk`. Wired into `ProofsInTheBook.lean` (import added after
`ChordReconClose`). Branch `main`; no commits; no branch switch; no codex/OpenAI tooling;
never ran lake/lean on the Mac (kernel-panic rule observed — verified exclusively on uisai1).

## Headline results (all clean-3)

- `side₁_sphere_unconditional` — side-1 `IsSphereMap` from `Separates` + fact-2 alone.
- `chordSideNearTriangulation`, `chordSideNearTriangulation_of_share` — the NT producer.
- `chordSideClassification_of_contiguous` — produces `ChordReconClose.ChordSideClassification`.
- `contiguousInterval_of_nearTriangulation` — the converse projection (non-vacuity).
- `chordSideNearTriangulation_sphere_eq` — the produced `sphere` IS the disk-core sphere (rfl).
- `chordSideClassification_iff_contiguous` — `ChordSideClassification ≃ ContiguousInterval`.

## Verification (server uisai1, real olean chain)

- `lake env lean ProofsInTheBook/ChordSideNT.lean` → **RC = 0**, zero errors.
- `lake build ProofsInTheBook.ChordSideNT` → **Build completed successfully (8457 jobs).**
- `lake build ProofsInTheBook` (full library root, with the new import) →
  **Build completed successfully (8614 jobs).**
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → none in code (only docstring prose).
- `#print axioms` on all 7 headline results → **clean-3 `[propext, Classical.choice,
  Quot.sound]`** (no `sorryAx`/`ofReduceBool`/`trustCompiler`).
- `#print axioms ProofsInTheBook.ThomassenInduction.nearTriangulation_five_colorable` →
  **clean-3** (unchanged; still parameterized by the `JordanOracle Ofun`).

## §3.3 verdict: FAITHFUL, non-vacuous, genuine reduction (not a re-wrapper)

- **Genuine advance.** The `sphere`/genus-0/`IsSphereMap` field of `ChordSideClassification` is
  now PROVED unconditionally (`side₁_sphere_unconditional`) and REMOVED from the residue. The
  prior round (`ChordReconClose`) left the *entire* `NearTriangulation(sideMap₁)` — including
  `sphere` — as the opaque residue `ChordSideClassification`. This file proves the `sphere`
  half and reduces the residue to exactly the boundary predicate `ContiguousInterval`.
- **Not a re-wrapper.** `chordSideClassification_iff_contiguous`'s backward direction injects
  the *proved* `side₁_sphere_unconditional` (built from the disk core), not a hypothesis;
  `chordSideNearTriangulation_sphere_eq` certifies the produced `sphere` field IS that
  unconditional sphere. The reduction strictly removes content from the residue.
- **Non-vacuous.** `contiguousInterval_of_nearTriangulation` shows `ContiguousInterval` is
  inhabited whenever the side is a genuine near-triangulation (it is *precisely* the NT minus
  `sphere`), so it is not an unsatisfiable premise / hidden `False`. `ChordSideClassification`
  on the genus-0 side is the side near-triangulation; the producer round-trips it.

## Why fully unconditional `nearTriangulation_five_colorable` is NOT reachable (verified, not premature)

I traced the actual dependency chain. The residue is irreducible at the `CombMap` layer,
across BOTH branches, and is the SAME content the repo's kernel campaign already decided:

1. **`ContiguousInterval` (the chord-side residue) is not derivable from genus-0 + arbitrary
   anchors.** `sideMap₁` is defined over **arbitrary** anchors `a₀, a₁` (PlanarMapChordSplit
   §8, lines 684-689 explicitly: "the side map is well defined for *any* distinct anchors; the
   *correct* anchors are what make the outer boundary the arc-plus-fresh chord"). The side
   faces are `tracePhi`-orbits with `tracePhi = swap(ρa₀)(ρa₁) · keptPhi`; under the proved
   fact-2 (`AnchorsShareBoundaryFace`) the swap **splits the one shared boundary face into two
   pieces** (`ChordFaceCount.freshMap_F_same_face`). `inner_tri` needs the NON-outer piece to be
   a triangle of length 3 — i.e. the chord cuts off a *contiguous* boundary arc. For arbitrary
   anchors this is FALSE (a non-contiguous split yields a non-triangle inner face), and
   `simpleGraph` needs `u, v` non-adjacent (the fresh chord is non-loop/non-parallel). Both are
   the correct-anchor contiguity datum — the genuine planar embedding the abstract `CombMap`
   does not carry.

2. **Kernel-confirmed genus-dependence (CutFaceLabel.lean).** The would-be free "side inner
   faces ARE M inner faces" orbit fact is REFUTED inside the Lean kernel: on the K₄ sphere cut,
   the `φ'₂`-orbit `{inl 1, inl 4, inl 9}` mixes THREE distinct old faces and the old face
   `{1,2,7}` splits across two orbits — so no genus-uniform `φ'₂`-invariant orbit label of the
   right cardinality exists. The intact-face transport is therefore NOT free; it is entangled
   with the same Schoenflies content (additionally, `keptPhi = sideSigma₁·sideAlpha₁` uses the
   `filteredRotation` skipping deleted darts, so a kept face bordering the chord changes length —
   it is not simply `hNT.inner_tri`).

3. **The chordless branch has the same irreducible residue with NO producer.** Verified:
   `grep` finds no `def/theorem … : FanSurgeryReconstruction` and no
   `… : ChordlessOracle`/`: JordanOracle` (only the `JordanOracleConstruct.lean` builder *from*
   a `JordanInput`, and `FanIncidenceData → …` consumers). Its `outerCycle`/`inner_tri` are the
   same boundary-deletion discrete-Schoenflies content, not the connectivity/genus tools.

4. **The headline is parameterized by `JordanOracle Ofun`.** `nearTriangulation_five_colorable`
   takes `Ofun : ∀ p q cp cq, JordanOracle α`. Discharging it unconditionally requires building
   both branches' boundary classifications above. So `five_colorable` stays CONDITIONAL on the
   discrete Jordan–Schoenflies classification (chord-side `ContiguousInterval` + chordless
   `FanSurgeryReconstruction`), the planar-embedding content `CombMap` cannot synthesize.

Fabricating `ContiguousInterval`, `inner_tri`, `outerCycle`, or a `FanSurgeryReconstruction`
to force a green headline is exactly the §3.3 forbidden move (fake disk/face correspondence);
I did not do it.

## Precise residue (what now blocks fully unconditional `five_colorable`)

The chord-side residue has shrunk again: the **`sphere`/genus-0 field is now proved and
removed**, and the remaining chord-side residue is the SINGLE named, satisfiable predicate
`ChordSideNT.ContiguousInterval` (the correct-anchor boundary classification: `simpleGraph`,
`outerFace`, `outerCycle`, `outer_simple`, `outer_len`, `inner_tri` of `sideMap₁`). Beyond it,
the campaign has now proved: genus-0/no-handle core (SubmapPlanar), kept-side connectivity
(ChordSideClose), the side `IsSphereMap`+face-count (ChordDisk), the side-vertex `ι_surj` orbit
surjection + inl-`ι_adj` (ChordReconClose), and the side `sphere` discharged + the full-NT
ASSEMBLY from `ContiguousInterval` (this file). The remaining open joints, all the same
discrete Jordan–Schoenflies classification requiring the actual planar embedding:

- chord side: `ContiguousInterval` (this file's one named residue) + the fresh-chord-dart
  `ι_adj`/`ι_inj`/`hLₛ`/`smaller` of a full `ChordSideReconstruction` (the correct-anchor
  ContiguousInterval is what would make these well-defined);
- chordless: `FanSurgeryReconstruction` boundary fields (no producer);
- upstream: `Separates`/`FanIncidenceData`/the `hcompat` no-teleport fragment (false obvious
  form per `CH35_BRIDGE_DESIGN.md` §6).

## Threading note

`chordSideClassification_of_contiguous` is the drop-in producer of
`ChordReconClose.ChordSideClassification`. Once a downstream layer supplies a
`ContiguousInterval` (the correct-anchor boundary datum) for the SPECIFIC correct anchors at
`u, v`, the side near-triangulation `hN` is built here, and `ChordReconClose`'s `ι`/`ι_surj`/
`ι_adj_of_inl` supply the vertex side — together feeding a `ChordSideReconstruction` and hence
`ChordSplitNT.ChordRecursionData.chord_case_recursive`. The `sphere` field is already discharged
unconditionally and clean-3 here.
