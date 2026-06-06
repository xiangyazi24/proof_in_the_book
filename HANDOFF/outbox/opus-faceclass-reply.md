# Ch35 InnerFacesSide₁ + chordless inner_tri: the FACE-level orbit surjection + clean-face SIZE machinery PROVED; residue per branch collapsed to ONE named correct-anchor classification; headline stays CONDITIONAL on JordanOracle (clean-3, unchanged)

## TL;DR (honest, §3.3)

The orchestration named `InnerFacesSide₁` as the FACE analogue of the proved vertex `ι_surj`,
to be attacked with the same orbit-bijection machinery, plus the chordless `inner_tri` via the
same face-SIZE route.  I realized BOTH:

- **Chord side (`ChordFaceClass.lean`):** the FACE-level orbit surjection is PROVED
  UNCONDITIONALLY (`sideFace_has_inl_rep` — every side face has a kept-`inl` representative,
  via `ChordFaceCount.freshPhi_sameCycle_inl_faceProj` used pointwise, exactly as `ι_surj` used
  the σ-orbit bijection pointwise).  The kept-dart face dichotomy is PROVED UNCONDITIONALLY
  (`keptDart_face_side₁_or_outer` — every kept dart's `M`-face is in `side₁` or is the
  `M`-outer face, from `keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`).  These two halves
  discharge two of the four `InnerFacesSide₁` ingredients; the residue collapses to ONE named
  correct-anchor predicate `BoundaryOrbitClass`, and `InnerFacesSide₁` is discharged from it
  (`innerFacesSide₁_of_boundaryOrbitClass`), proven *equivalent* to it
  (`boundaryOrbitClass_iff_innerFacesSide₁`).  Chaining `ChordInnerTri`'s face-SIZE machinery
  gives `SideInnerTriangulation` and a full `ContiguousInterval`
  (`sideInnerTriangulation_of_boundaryOrbitClass`, `contiguousInterval_of_boundaryOrbitClass`).

- **Chordless branch (`ChordlessFinal.lean`):** the `DeletedOuterBoundary.inner_tri` residue is
  discharged via the SAME face-SIZE-not-COUNT route.  The clean face-SIZE transfer is PROVED
  UNCONDITIONALLY (`deleteVertex_cleanFaceLen_eq_M` — a clean survivor's deleted face length =
  its `M`-face length, the deletion analogue of `sideKeptMap₁_faceLen_eq_M`), re-derived from
  the public `deleteVertex_phi_apply_of_next_kept`.  A clean `M`-non-outer face is then a
  triangle (`deleteVertex_cleanFace_eq_three`), and `inner_tri` is discharged from ONE named
  predicate `CleanFaceClass` (`deleteVertex_inner_tri_of_cleanFaceClass`), assembling a full
  `DeletedOuterBoundary` and `FanSurgeryReconstruction`
  (`deletedOuterBoundary_of_cleanFaceClass`, `chordlessRecon_of_cleanFaceClass`).

The headline `nearTriangulation_five_colorable` stays CONDITIONAL on `JordanOracle` (clean-3,
UNCHANGED).  The lone residue per branch — `BoundaryOrbitClass` (chord) / `CleanFaceClass`
(chordless) — is the genuine discrete Jordan–Schoenflies datum the prior three kernel-backed
rounds isolated as non-derivable at the `CombMap` layer (`CutFaceLabel.lean`: the
side-face/deleted-face↔`M`-face correspondence is genus-DEPENDENT; `chordChoice_contiguousArc`
is a fact about the `M`-boundary cycle and does NOT, at the `CombMap` layer, certify which
`tracePhi`/`φ'` orbit is the boundary).  I did NOT fabricate it.

## New files (owned, fresh; NOT wired into ProofsInTheBook.lean — one-writer rule)

- `ProofsInTheBook/ChordFaceClass.lean` — imports `ChordInnerTri`. 9 audited results.
- `ProofsInTheBook/ChordlessFinal.lean` — imports `PlanarMapFanFaces` + `ChordlessClose`.
  8 audited results.

Branch `main`; no commits; no branch switch; no codex/OpenAI tooling; never ran lake/lean on
the Mac (kernel-panic rule observed — verified exclusively on uisai1).

## The mathematical content (the face-level ι_surj, both branches)

### Chord side
`sideMap₁ = freshMap (sideAlpha₁) (sideSigma₁) a₀ a₁`; face perm traced as
`tracePhi = swap (ρ a₀) (ρ a₁) · keptPhi`.  `freshPhi_sameCycle_inl_faceProj` (ChordFaceCount):
EVERY dart `x` is `φ`-SameCycle to `inl (faceProj x)`.  So for any side face `f = ⟦x⟧`,
`f = dartFace (inl (faceProj x))` with `faceProj x ∈ {d // d ∉ keptDel₁}` a kept dart — the
exact face-level surjection (`sideFace_has_inl_rep`, UNCONDITIONAL).  `keptSet₁`'s definition
gives the kept-dart dichotomy (`keptDart_face_side₁_or_outer`, UNCONDITIONAL).  Together they
reduce the four-part `InnerFacesSide₁` (rep + `∈ side₁` + `≠ face₁` + splice-untouched) to the
two genuinely-geometric parts (`≠ M`-outer-face + `≠ face₁` + splice-untouched), bundled into
`BoundaryOrbitClass`; the `∈ side₁` half is *recovered* from `≠ M`-outer-face via the
dichotomy.

### Chordless branch
A survivor `x` is clean if `M.dartFace x.1 ∉ M.vertexFaces d0`.  On a clean dart, `φ'` agrees
with `M.φ` (`deleteVertex_phi_apply_of_next_kept`) and the successor stays clean (same
`M`-face) — so the whole `φ'`-orbit is the `M.φ`-orbit, *pointwise* (`cleanSameCycle_iff`).
Hence the deleted face length = `M`'s (`deleteVertex_cleanFaceLen_eq_M`, via a `Subtype.val`
filter bijection, exactly the chord side's `sideKeptMap₁_faceLen_eq_M`).  `hNT.inner_tri` then
makes a clean `M`-non-outer face a triangle.  The merged outer face captures exactly the
`v0`-incident orbit (`CleanFaceClass`), the chordless analogue of `BoundaryOrbitClass`.

## Verification (server uisai1, real olean chain)

- `lake env lean ProofsInTheBook/ChordFaceClass.lean` → **RC = 0**, zero errors;
  all 9 results **clean-3 `[propext, Classical.choice, Quot.sound]`**:
  `sideFace_has_inl_rep`, `keptDart_face_side₁_or_outer`, `keptDart_face_mem_side₁`,
  `innerFacesSide₁_of_boundaryOrbitClass`, `sideInnerTriangulation_of_boundaryOrbitClass`,
  `contiguousInterval_of_boundaryOrbitClass`, `boundaryOrbitClass_discharge_eq`,
  `boundaryOrbitClass_iff_innerFacesSide₁`, `sideFace_has_inl_rep_fires`.
- `lake env lean ProofsInTheBook/ChordlessFinal.lean` → **RC = 0**, zero errors (one harmless
  `push_neg` deprecation note); all 8 audited results **clean-3** (no `sorryAx`):
  `survives_of_clean`, `cleanSameCycle_iff`, `deleteVertex_cleanFaceLen_eq_M`,
  `deleteVertex_cleanFace_eq_three`, `deleteVertex_inner_tri_of_cleanFaceClass`,
  `deletedOuterBoundary_of_cleanFaceClass`, `chordlessRecon_of_cleanFaceClass`,
  `chordlessRecon_cleanFaceClass_inner_tri_eq`.
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → none in code.
- `#print axioms ProofsInTheBook.ThomassenInduction.nearTriangulation_five_colorable`
  → **clean-3, UNCHANGED** (still parameterized by `JordanOracle`; no upstream file edited —
  faithful advance, not a regression).

## §3.3 verdict: FAITHFUL, non-vacuous, genuine reduction (not a re-wrapper / not fabricated)

- **Genuine advance.** The FACE-level orbit surjection (`sideFace_has_inl_rep`) and the
  kept-dart dichotomy (`keptDart_face_side₁_or_outer`) are PROVED UNCONDITIONALLY — the face
  analogue of `ι_surj`, attacked with the same pointwise orbit-bijection.  The chordless clean
  face-SIZE transfer (`deleteVertex_cleanFaceLen_eq_M`) is PROVED UNCONDITIONALLY — the
  deletion analogue of the chord side's `sideKeptMap₁_faceLen_eq_M`.  These were the attackable
  cores; both are now THEOREMS.
- **Not a re-wrapper.** `boundaryOrbitClass_discharge_eq` / `chordlessRecon_cleanFaceClass_inner_tri_eq`
  certify (`rfl`) the assembled `ContiguousInterval` / `FanSurgeryReconstruction`'s `inner_tri`
  IS the face-SIZE discharge from the named classification — not a hidden hypothesis.
  `boundaryOrbitClass_iff_innerFacesSide₁` proves the named residue is *exactly*
  `InnerFacesSide₁`, restated in the unconditional-dichotomy form (carries the real `keptSet₁`
  structure).
- **Non-vacuous.** `sideFace_has_inl_rep_fires` (the surjection fires on a concrete face);
  `cleanFaceClass_nonvacuous_statement` (the chordless residue is the honest fan analogue).
- **Not fabricated.** No fake side/deleted outer cycle, no fake face correspondence.  The lone
  residue per branch is the honest correct-anchor boundary-orbit classification.

## The precise residue now (sharpened — ONE named correct-anchor predicate per branch)

- **chord side:** `ChordFaceClass.BoundaryOrbitClass data hsep a₀ a₁ hne outerFace` — *every
  non-outer side face has a kept-`inl` rep `k` with `M.dartFace k.1 ≠ M`-outer-face,
  `≠ face₁`, splice-untouched*.  Equivalent to `ChordInnerTri.InnerFacesSide₁`
  (`boundaryOrbitClass_iff_innerFacesSide₁`).  Concrete failing chain at the `CombMap` layer:
  the side-outer-face ↔ `M`-outer-arc orbit identification and the splice-untouchedness of all
  OTHER orbits are the discrete Jordan–Schoenflies content — `chordChoice_contiguousArc` is a
  fact about the `M`-boundary cycle and does NOT certify which `tracePhi`-orbit is the boundary
  (the side-face↔`M`-face correspondence is `CutFaceLabel`-refuted genus-dependent).
- **chordless branch:** `ChordlessFinal.CleanFaceClass outerFace` — *every non-outer deleted
  face has a clean (`M`-face avoids `v0`), `M`-non-outer survivor rep*.  The fan analogue;
  the merged outer face must capture exactly the `v0`-incident orbit — the same discrete
  Jordan datum.  Plus the merged-face boundary-cycle datum and `DeleteVertexMergedFaceSingleOrbit`.
- **headline:** `JordanOracle.decide` cannot be built without these classifications; so
  `nearTriangulation_five_colorable` stays CONDITIONAL.

## Threading note (the drop-ins)

`ChordFaceClass.contiguousInterval_of_boundaryOrbitClass` is the chord-side drop-in: once a
downstream layer supplies `BoundaryOrbitClass` for the correct anchors + the side boundary
cycle, it assembles the full `ContiguousInterval` →
`ChordSideNT.chordSideNearTriangulation` (sphere already discharged unconditionally) →
`ChordReconClose.ChordSideClassification` (vertex `ι_surj` already PROVED) →
`ChordSideReconstruction` → `ChordSplitNT.chord_case_recursive`.
Symmetrically `ChordlessFinal.chordlessRecon_of_cleanFaceClass` produces the
`FanSurgeryReconstruction` from a fan + `CleanFaceClass` + the merged outer-boundary cycle +
the merged-orbit seam fact, feeding `ChordlessOracle.recon`.  Both producers are PROVED here
modulo exactly the one named correct-anchor classification per branch — the genuine discrete
Jordan–Schoenflies residue the abstract `CombMap` cannot carry.
