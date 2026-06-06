# Ch35 SideInnerTriangulation: the face-SIZE machinery is FULLY PROVED via the sharp angle; residue collapsed to the correct-anchor face classification (NOT the CutFaceLabel COUNT)

## TL;DR

The SHARP NEW ANGLE is realized and **fully formalized**, clean-3: every INNER (non-outer)
face of `sideMap₁` is an *untouched* `M`-triangle because the chord splice reroutes ONLY
the chord-incident/outer-face orbit — **face SIZE is splice-invariant**, sidestepping
`CutFaceLabel`'s COUNT refutation exactly as genus-slack sidestepped it for `eulerChar`.

I PROVED, unconditionally (clean-3), the entire `faceLen = 3` computation:

1. (Sections 1–2, UNCONDITIONAL) for any kept dart `k` whose `keptPhi`-orbit avoids the
   chord predecessors `β a₀, β a₁` (**splice-untouched**), the side face of `inl k` has
   `faceLen sideMap₁ = faceLen (keptCombMap β ρ)` — the orbit contains no fresh dart and the
   swap acts trivially on it (`freshPhi_faceLen_inl_eq_keptPhi`).  This is the precise "the
   cut reroutes only the chord-dart orbit" statement, proved from the explicit `freshMap`
   face permutation `φ̃ = swap·(ρβ)` (`ChordFaceCount.freshFace_sameCycle_iff`).

2. (Section 3) on a kept dart whose `M.φ`-orbit stays kept (**`OrbitKept`**), the kept face
   length equals `M`'s: `faceLen sideKeptMap₁ (dartFace k) = M.faceLen (M.dartFace k.1)`
   (`sideKeptMap₁_faceLen_eq_M`).  The kept face perm `keptPhi = sideSigma₁·sideAlpha₁`
   coincides with `M.φ` on the orbit (`FilteredRotation.filteredRotation_apply_of_next_kept`
   takes one σ-step when the successor is kept).

3. (Section 4) chaining 1+2 with `hNT.inner_tri`: an untouched, kept-orbit, `M`-non-outer
   inner face is a triangle (`sideMap₁_faceLen_inl_eq_three`).

4. (Section 4) **`OrbitKept` is DISCHARGED** for genuine side-1 inner faces
   (`orbitKept_of_side₁`): if `k.1`'s `M`-face is in `side₁` and ≠ the chord face `face₁`,
   the whole `M.φ`-orbit keeps that face (`dartFace_phi`), hence lands in
   `sideDarts₁ \ {dart} ⊆ keptSet₁`.  `M`-non-outerness is likewise discharged
   (`side₁_subset_nonouter`).  So `sideMap₁_faceLen_inl_three_of_side₁` needs only
   side-1 membership + ≠`face₁` + `SpliceUntouched`.

5. (Section 5) `SideInnerTriangulation` is then **discharged** from a single named face-
   classification predicate (`sideInnerTriangulation_of_innerFacesSide₁`), and a full
   `ContiguousInterval` assembled from it + the side boundary cycle
   (`contiguousInterval_of_innerFacesUntouched`, wiring into
   `ChordContiguous.contiguousInterval_of_boundary_and_innerTri`).

The headline `nearTriangulation_five_colorable` stays CONDITIONAL on `JordanOracle`
(clean-3, unchanged): the ONE residue — the correct-anchor face classification
`InnerFacesSide₁` — is the genuine discrete Jordan–Schoenflies datum the prior kernel-backed
rounds isolated as non-derivable at the `CombMap` layer.  I did NOT fabricate it.

## New file (owned, only file touched)

`ProofsInTheBook/ChordInnerTri.lean` (593 lines).  Imports `ChordContiguous` +
`ChordFaceCount`.  Branch `main`; no commits; no branch switch; no codex/OpenAI tooling;
never ran lake/lean on the Mac (verified exclusively on uisai1).  Not wired into
`ProofsInTheBook.lean` (one-writer rule — that root file is not mine to edit); the file
builds standalone and against the full olean chain.

## Why this sidesteps CutFaceLabel (the COUNT-vs-SIZE distinction, realized)

`CutFaceLabel.lean` `#eval`-refutes a genus-uniform `φ'₂`-invariant orbit LABEL of
cardinality `F + 2` — for the **cut-and-cap double surgery** `cutCapMap2` (`φ'₂`), and about
the face **COUNT/label**.  `SideInnerTriangulation` is about a **different construction**
(the single-chord `freshMap`, face perm `φ̃ = swap·(ρβ)`) and a **different property** (each
inner face's **SIZE = 3**).  The angle uses `ChordFaceCount`'s already-proven explicit orbit
bijection POINTWISE on one untouched orbit: an orbit avoiding `β a₀, β a₁` is *identical* to
a `keptPhi`-orbit with the *same cardinality* (no fresh dart in it, swap trivial) — no
genus-uniform label needed.  This is the genus-essential structure (`M`'s `inner_tri` on
side-1 faces) used like genus-slack for `eulerChar`.

## Verification (server uisai1, real olean chain)

- `rsync … ChordInnerTri.lean ; ssh uisai1 'lake env lean ProofsInTheBook/ChordInnerTri.lean'`
  → **RC = 0**, zero errors, zero warnings, no `sorry`.
- `#print axioms` — **clean-3 `[propext, Classical.choice, Quot.sound]`** on ALL 11 audited
  results (the full chain: `freshPhi_faceLen_inl_eq_keptPhi`, `tracePhi_sameCycle_iff_keptPhi`,
  `sideKeptMap₁_faceLen_eq_M`, `sideMap₁_faceLen_inl_eq_M`, `sideMap₁_faceLen_inl_eq_three`,
  `orbitKept_of_side₁`, `sideMap₁_faceLen_inl_three_of_side₁`,
  `sideInnerTriangulation_of_innerFacesUntouched`, `sideInnerTriangulation_of_innerFacesSide₁`,
  `contiguousInterval_of_innerFacesUntouched`, `innerFacesUntouched_discharge_eq`).
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → none in code (only the docstring's
  "No `sorry` / `axiom` / `admit` / `native_decide`." disclaimer).
- `#print axioms ProofsInTheBook.ThomassenInduction.nearTriangulation_five_colorable`
  → **clean-3**, UNCHANGED (still parameterized by `JordanOracle`; this file is a faithful
  advance, not a regression — no upstream file edited).

## §3.3 verdict: FAITHFUL, genuine reduction (not a re-wrapper / not fabricated)

- **Genuine advance.** The entire face-SIZE `faceLen = 3` machinery is PROVED unconditionally
  (Sections 1–4), realizing the sharp angle. `OrbitKept` and `M`-non-outerness — two of the
  three per-face conditions — are PROVED from the side-1 classification (`orbitKept_of_side₁`,
  `side₁_subset_nonouter`), not assumed. The residue is reduced from the genus-refuted
  side-face↔`M`-face orbit-label entanglement to a clean face-classification predicate.
- **Not a re-wrapper.** `innerFacesUntouched_discharge_eq` certifies (`rfl`) the assembled
  `ContiguousInterval`'s `inner_tri` IS the discharged `SideInnerTriangulation`. The discharge
  injects the proved Sections 1–4 chain, not a hidden hypothesis.
- **Not fabricated.** No fake outer face, no fake side-face↔`M`-face correspondence. The lone
  residue `InnerFacesSide₁` is the honest correct-anchor boundary classification.

## The precise residue now (sharpened — face CLASSIFICATION, not the refuted COUNT)

ONE named predicate per branch, plus the upstream Jordan input:

- **chord side:** `ChordInnerTri.InnerFacesSide₁ data hsep a₀ a₁ hne outerFace` — *every
  non-outer side face is represented by an `inl k` with `M`-face in `side₁`, ≠ `face₁`, and
  `SpliceUntouched` (the orbit avoids the chord predecessors)*. This bundles exactly the
  correct-anchor / which-orbit-is-the-boundary datum. Concrete failing chain at the `CombMap`
  layer: (i) `SpliceUntouched` is genuinely anchor-dependent — `sideMap₁` is defined for
  ARBITRARY distinct anchors, and only the CORRECT anchors put `β a₀, β a₁` on the chord/outer
  orbit (for wrong anchors a non-contiguous split leaves a non-triangle inner face, the same
  kernel-decided contiguity of `CutFaceLabel`'s split-faces phenomenon); (ii) the inl-rep
  surjection onto non-outer faces (the side-face↔`M`-side₁-face correspondence + identifying
  the outer orbit) is the discrete Jordan–Schoenflies content not carried by the abstract
  `CombMap` (no face correspondence is proven upstream — only the vertex `ι_surj`). This is
  the SAME irreducible content `ContiguousInterval`/`Separates` isolate, now stated purely in
  face-SIZE / orbit-membership terms, manifestly NOT a `φ'₂`-invariant COUNT label.
- **headline:** `JordanOracle.decide` cannot be built without this classification; so
  `nearTriangulation_five_colorable` stays CONDITIONAL.

## FCT threading

`ChordInnerTri.contiguousInterval_of_innerFacesUntouched` (and the sharper
`sideInnerTriangulation_of_innerFacesSide₁`) is the drop-in: once a downstream layer supplies
`InnerFacesSide₁` for the correct anchors plus the side boundary cycle,
`ChordContiguous.contiguousInterval_of_boundary_and_innerTri` →
`ChordSideNT.chordSideNearTriangulation` (sphere already discharged unconditionally via
`side₁_sphere_unconditional`) → `ChordReconClose.ChordSideClassification` →
`ChordSideReconstruction` → `ChordSplitNT.chord_case_recursive` →
`nearTriangulation_five_colorable`. Everything between `InnerFacesSide₁` and the assembled
`SideInnerTriangulation` is PROVED here; the face-SIZE computation is now a THEOREM, no longer
entangled with the refuted orbit-count label.
