# Ch35 ContiguousInterval + chordless: chord-CHOICE contiguity PROVED, residue reduced to ONE genus-dependent field per branch; headline stays CONDITIONAL (kernel-decided, not premature)

## TL;DR (honest, §3.3)

The orchestration's KEY INSIGHT — that `ContiguousInterval` is dischargeable from the
chord-CHOICE because a boundary chord = two non-adjacent boundary vertices ⟹ contiguous
arc — is **correct at the `M`-boundary-cycle layer and is now PROVED unconditionally**.
But the hypothesis that the residue is therefore "likely NOT genus-dependent" is
**refuted by the Lean kernel itself** (`CutFaceLabel.lean`, the `#eval` probes on the K₄
sphere cut). `ContiguousInterval`'s fields are stated about the SIDE MAP `sideMap₁`'s own
`Face`/`BoundaryCycle`/`faceLen`, and the lone field the `M`-boundary contiguity cannot
reach — the side-map `inner_tri` — is exactly the kernel-refuted genus-dependent
side-face↔`M`-face correspondence.

So the **maximal faithful advance** is: prove the chord-CHOICE contiguity (the insight's
true core), and reduce the chord-side residue from the predicate `ContiguousInterval` to
its single genus-dependent field `SideInnerTriangulation`; do the parallel reduction for
the chordless branch (three structural fan fields PROVED unconditional from the fan, the
residue isolated to `DeletedOuterBoundary`'s `inner_tri` + the `φ`-seam-walk fact). Both
branches' residue is the SAME discrete-Schoenflies `inner_tri` content. The headline
`nearTriangulation_five_colorable` stays CONDITIONAL on the `JordanOracle` (unchanged
clean-3). Fabricating `ContiguousInterval`/`inner_tri`/a `FanSurgeryReconstruction` to
force a green headline is the §3.3 forbidden move; I did not do it.

## New files (owned, fresh)

- `ProofsInTheBook/ChordContiguous.lean` (~280 lines). Imports `ChordSideNT`.
- `ProofsInTheBook/ChordlessClose.lean` (~210 lines). Imports `PlanarMapFanFaces` +
  `ThomassenInduction`.
- Both wired into `ProofsInTheBook.lean` (after `ChordSideNT`). Branch `main`; no commits;
  no codex/OpenAI tooling; never ran lake/lean on the Mac (verified exclusively on uisai1).

## What is PROVED (the chord-CHOICE contiguity — the insight's true core)

`ChordContiguous.lean`, all unconditional (no Jordan/genus hypothesis), clean-3:

- `chordChoice_nonAdjacent` — `s(u,v)` is NOT a boundary edge (`Chord.not_boundary_edge`):
  the chord = two non-adjacent boundary vertices. This IS the chord-selection property.
- `chordChoice_endpoints_ne`, `chordChoice_boundary`, `chordChoice_adj` — `u≠v`, both
  boundary vertices, `M`-adjacent (the fresh chord edge is real).
- `chordChoice_contiguousArc` — **the chord ALWAYS cuts the boundary into two contiguous
  arcs**: both `path₁ : u→v` and `path₂ : v→u` are nontrivial (each has an internal
  boundary vertex), exactly because `u,v` non-adjacent (`path₁_internal_iff_proper`).
- `chordChoice_arc_covers` + `chordChoice_arc_internally_disjoint` — the two arcs cover the
  boundary vertex list and are internally disjoint (= contiguous, disjoint split).
- `chordChoice_arc_internal_witnesses` — each arc has a genuine boundary vertex strictly
  between `u,v` (non-vacuity of the contiguity; the strict-decrease witnesses).

This is the chord-CHOICE contiguity at the `M`-boundary layer, fully discharged. It
confirms the insight's core is real and NOT genus-dependent.

## The precise pinning (chord side)

`ChordContiguous.lean`, clean-3:

- `SideInnerTriangulation` (named Prop) — `∀ f ≠ outerFace, sideMap₁.faceLen f = 3`, the
  lone field of `ContiguousInterval` the `M`-boundary contiguity cannot synthesize.
- `contiguousInterval_of_boundary_and_innerTri` — **PROVED**: a `ContiguousInterval` is
  assembled from the side outer-boundary-cycle fields (`simpleGraph`/`outerFace`/
  `outerCycle`/`outer_simple`/`outer_len`) PLUS `SideInnerTriangulation`. So
  `ContiguousInterval`'s only genus-dependent content is this single field.
- `sideInnerTriangulation_of_contiguous` — converse: `ContiguousInterval` supplies the
  residue. So the residue is EXACTLY `SideInnerTriangulation` (+ the side boundary cycle).
- `sideInnerTriangulation_of_nearTriangulation`, `residue_round_trip` — non-vacuity +
  no-rewrapper (`rfl` certifies the assembly genuinely uses the residue field).

## The precise pinning (chordless branch)

`ChordlessClose.lean`, clean-3 — exact parallel to the chord side:

- `chordless_vertexQuotient`, `chordless_connected`, `chordless_facesMerge`,
  `fanSurgery_structural_fields` — **the three dart-rotation surgery fields of
  `FanSurgeryReconstruction` are PROVED unconditional from a `BoundaryVertexFan`** (via
  `deleteVertex_vertexQuotientEquiv` / `deleteVertex_connected_of_fan` /
  `deleteVertex_facesMerge_of_fan`, the latter modulo the single `φ`-seam-walk fact
  `DeleteVertexMergedFaceSingleOrbit`). These are the chordless analogue of the chord
  side's proved disk core — NOT in the residue.
- `chordlessRecon_of_bdry` — the full `FanSurgeryReconstruction` assembled (via
  `fanSurgeryReconstruction`) from the fan + the merged-orbit fact + the boundary datum
  `DeletedOuterBoundary` (whose lone genus-dependent field is `inner_tri`).
- `chordlessResidue_pins_recon`, `chordlessRecon_outerCycle_eq` — **PROVED** (`rfl`): the
  assembled recon's `inner_tri`/`outerCycle` ARE the boundary datum's (residue genuinely
  used, not bypassed). So the chordless residue is EXACTLY `DeleteVertexMergedFaceSingleOrbit`
  + `DeletedOuterBoundary` (the `inner_tri` field = the same genus-dependent content).
- `deletedOuterBoundary_of_nearTriangulation` — non-vacuity.

## Why fully unconditional `five_colorable` is NOT reachable (kernel-verified, not premature)

Traced the actual chain across BOTH branches; the residue is irreducible at the `CombMap`
layer and is kernel-decided:

1. **Kernel refutation of the genus-uniform face correspondence (`CutFaceLabel.lean`).**
   On the K₄ sphere cut `A→B→D` the `φ'₂` (= `tracePhi`-analogue) orbits genuinely MERGE
   and SPLIT old `M`-faces: orbit `{inl 1, inl 4, inl 9}` mixes THREE distinct old faces,
   and old face `{1,2,7}` splits across two orbits — so **no genus-uniform `φ'₂`-invariant
   orbit label of cardinality `F+2` exists** (verified by `#eval` inside the Lean kernel,
   lines 28–67). The side-map `inner_tri` (chord) and deleted-map `inner_tri` (chordless)
   both ask the surviving orbits to be length-3 triangles — exactly entangled with this
   refuted label. This is NOT "prior framing"; it is a kernel `#eval` disproof.
2. **`Separates` is a genuine Jordan input.** `WitnessFinal.separates_final` (the only path
   to `Separates`) takes `hcompat` (the interior-dual no-teleport fragment supplier) plus a
   pile of Jordan-curve `*_step` hypotheses; `CH35_BRIDGE_DESIGN.md` §6 records the obvious
   form of `hcompat` is FALSE. And `ContiguousInterval`/`sideMap₁` are stated OVER
   `hsep : data.Separates` — the residue sits on top of this input.
3. **No unconditional producer for either branch's boundary classification.** The chord
   side needs `ContiguousInterval` (= side boundary cycle + `SideInnerTriangulation`); the
   chordless side needs `DeletedOuterBoundary` (+ merged-orbit fact). Neither is derivable
   at the `CombMap` layer — both are the discrete Jordan–Schoenflies `inner_tri`/boundary
   normalization the abstract map cannot carry.
4. **Headline parameterization unchanged.** `nearTriangulation_five_colorable` still takes
   `Ofun : ∀ p q cp cq, JordanOracle α`; building `JordanOracle.decide` unconditionally
   requires the chord/chordless boundary classifications above. So `five_colorable` stays
   CONDITIONAL on the discrete Jordan–Schoenflies classification.

## Verification (server uisai1, real olean chain)

- `lake env lean ProofsInTheBook/ChordContiguous.lean` → **RC = 0**, zero errors;
  all 9 results clean-3 `[propext, Classical.choice, Quot.sound]`.
- `lake env lean ProofsInTheBook/ChordlessClose.lean` → **RC = 0**, zero errors;
  all 8 results clean-3.
- `lake build ProofsInTheBook` (full library root, both new imports wired) →
  **Build completed successfully (8618 jobs)**, 0 errors.
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → none in code (only docstring
  prose listing the forbidden tokens).
- `#print axioms ProofsInTheBook.ThomassenInduction.nearTriangulation_five_colorable` →
  **clean-3** (unchanged; still parameterized by `JordanOracle`).
- `#print axioms` on `chordChoice_contiguousArc`,
  `contiguousInterval_of_boundary_and_innerTri`, `chordlessRecon_of_bdry` → **clean-3**.

## §3.3 verdict: FAITHFUL, non-vacuous, genuine reduction (not a re-wrapper / not fabricated)

- **Genuine advance.** The chord-CHOICE contiguity (`chordChoice_contiguousArc` + the
  covering/disjointness/witness lemmas) is PROVED unconditionally — the insight's true core.
  The chord-side residue is reduced from the predicate `ContiguousInterval` to its single
  genus-dependent field `SideInnerTriangulation`; the chordless branch's three structural
  surgery fields are PROVED unconditional from the fan, isolating its residue to the same
  `inner_tri` content.
- **Not a re-wrapper.** The pinning lemmas inject genuine structure: `residue_round_trip`
  and `chordlessResidue_pins_recon` certify (`rfl`) the assemblies use the residue field,
  not a hidden hypothesis.
- **Non-vacuous.** Every residue Prop is shown inhabited from a genuine near-triangulation
  (`sideInnerTriangulation_of_nearTriangulation`, `deletedOuterBoundary_of_nearTriangulation`).
- **Not fabricated.** No fake side/deleted-map outer cycle, no fake face correspondence —
  the residue is isolated honestly and its non-derivability is the kernel-decided
  `CutFaceLabel` obstruction.

## Precise residue (what now blocks fully unconditional `five_colorable`)

ONE genus-dependent field per branch, plus the upstream Jordan input — all the SAME
discrete Jordan–Schoenflies `inner_tri`/face-survival content the kernel refuted as
genus-uniform:

- **chord side:** `ChordContiguous.SideInnerTriangulation` — the single side-map `inner_tri`
  field (`∀ f ≠ outerFace, sideMap₁.faceLen f = 3`). Concrete failing chain: `CutFaceLabel.lean`
  lines 28–67 (`φ'₂` orbits merge/split old faces on the K₄ sphere cut; `#eval`-verified).
  Plus the side boundary-cycle/`simpleGraph` data (needs the correct anchors) and the
  upstream `Separates` (`WitnessFinal.separates_final`'s `hcompat`, false-obvious-form).
- **chordless branch:** `DeletedOuterBoundary.inner_tri` (same `inner_tri` content) +
  `DeleteVertexMergedFaceSingleOrbit` (the `φ`-seam-walk fact). The three structural fan
  fields are PROVED unconditional (this file).
- **headline:** `JordanOracle.decide` cannot be built unconditionally without the two
  branch classifications above; `nearTriangulation_five_colorable` stays CONDITIONAL.

## Threading note

`ChordContiguous.contiguousInterval_of_boundary_and_innerTri` is the drop-in: once a
downstream layer supplies a `SideInnerTriangulation` (the one genus-dependent residue) for
the correct anchors plus the side boundary cycle, `ChordSideNT.chordSideNearTriangulation`
assembles the full `NearTriangulation(sideMap₁)` (sphere already discharged) — feeding a
`ChordSideReconstruction` → `ChordSplitNT.chord_case_recursive`. Symmetrically,
`ChordlessClose.chordlessRecon_of_bdry` produces the `FanSurgeryReconstruction` from a fan +
`DeletedOuterBoundary` + the merged-orbit fact, feeding `ChordlessOracle.recon`. Both
producers are PROVED here modulo exactly the one genus-dependent `inner_tri` field per branch.
