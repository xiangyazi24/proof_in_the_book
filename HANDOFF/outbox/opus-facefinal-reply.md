# Ch35 chord-side LAST residue: the TOUCHED chord-triangle face `face₁` discharged DIRECTLY via the explicit general side-face length formula — the `≠ face₁` carve-out is REMOVED. Headline stays CONDITIONAL on JordanOracle (clean-3, unchanged).

## TL;DR (honest, §3.3)

The prior chord-side residue `ChordInnerTri.InnerFacesSide₁` carried a `≠ face₁` carve-out:
it asked, for *every* non-outer side face, a representative whose `M`-face is `≠ face₁` AND
splice-untouched.  That carve-out is exactly the gap — when the side image of the chord
triangle `face₁` is itself a non-outer side face, NO such representative exists, so
`InnerFacesSide₁` is unsatisfiable in that case.  The prior round's `OuterAbsorbsChordOrbits`
tried to dodge this by *absorbing* both chord-dart orbits into the boundary.

This file closes the gap the way the task named: it proves the **general side-face length
formula** and uses it to discharge the touched `face₁` face **DIRECTLY** as a genuine inner
triangle — NOT "absorbed by the boundary".  Realized and FULLY FORMALIZED, clean-3, in the new
file `ProofsInTheBook/ChordFaceFinal.lean` (555 lines, 13 audited results, RC=0, all
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`/`admit`/`native_decide`).

## The genuinely-new derivable content (PROVED UNCONDITIONALLY)

- **The general side-face length formula** (`sideFaceLen_formula`, clean-3, NO splice-
  untouchedness): for ANY kept dart `k`,

  `faceLen sideMap₁ (dartFace (inl k))
     = tOrbitCard k + 𝟙[k ~ₜ β a₀] + 𝟙[k ~ₜ β a₁]`,

  the exact count of one side-face orbit — the `inl`-darts of the `tracePhi`-orbit of `k`
  (`tOrbitCard`), plus the fresh chord dart `inr 0` exactly when `k ~ₜ β a₀`, plus `inr 1`
  exactly when `k ~ₜ β a₁` (the `freshMap_phi_inl_b0/b1` splice positions).  Proved by
  splitting the dart universe `K ⊕ Fin 2` into the `inl`-image and the two `inr` darts and
  counting each via `freshFace_sameCycle_iff`.  This is valid for the chord-TOUCHED faces too
  — it is the formula the prior splice-untouched lemmas could not express.

- **Splice-untouched recovery** (`spliceUntouched_faceLen_eq_tOrbit`, `tOrbitCard_eq_keptFaceLen`):
  both indicators vanish on a splice-untouched orbit, so the formula collapses to the
  kept-map face length — recovering `freshPhi_faceLen_inl_eq_keptPhi`, no new assumption.

- **The DIRECT chord-triangle discharge** (`sideFaceLen_three_of_count`,
  `sideMap₁_faceLen_three_of_count`): if the side face's representative `k` has a
  `tracePhi`-orbit of exactly `2` kept darts and exactly one fresh chord dart joins it
  (`tOrbitCard = 2`, one indicator), the side face is a triangle — `2 + 1 + 0 = 3`.  This is
  the chord re-closing the deleted-dart gap of the `M`-triangle `face₁` with one fresh chord
  dart.  The TOUCHED face, discharged directly from the explicit trace, NOT via absorption.

- **The `face₁` chord-triangle structure is genuine — M-side UNCONDITIONAL**
  (`face₁_two_kept_darts`, `dart_mem_keptDel₁`): the `M`-triangle `face₁` has its chord dart
  `dart` DELETED (`∈ keptDel₁`) and its other two darts `M.φ dart`, `M.φ² dart` KEPT, DISTINCT,
  with `M`-face `face₁`.  So `face₁` contributes exactly the `2` kept darts of the count — the
  genuine chord-triangle structure, established with no correct-anchor input.

## The reframed residue (the `≠ face₁` carve-out REMOVED)

- `SideFaceTriangle f` (a per-face triangle witness: a rep with `faceLen f = 3`), produced by
  EITHER `sideFaceTriangle_of_spliceUntouched` (the inner-triangle route, the splice-untouched
  faces already proved triangles) OR `sideFaceTriangle_of_count` (the explicit chord-triangle
  count, the touched `face₁` face).
- `InnerFacesSide₁NoCarve outerFace`: every non-outer side face has a `SideFaceTriangle`
  witness.  **No `≠ face₁` carve-out.**
- `sideInnerTriangulation_of_noCarve` discharges `SideInnerTriangulation` from it (the touched
  `face₁` face INCLUDED); `contiguousInterval_of_noCarve` assembles the full
  `ChordSideNT.ContiguousInterval` (drop-in for the existing downstream chain →
  `ChordSideNT.chordSideNearTriangulation` → `ChordReconClose.ChordSideClassification` →
  `ChordSideReconstruction` → `ChordSplitNT.chord_case_recursive`).

`innerFacesSide₁NoCarve_of_innerFacesSide₁` proves the new residue is **no stronger** than the
old `InnerFacesSide₁` (each old splice-untouched rep is a `SideFaceTriangle` witness); it is
strictly more permissive — it additionally admits the direct chord-triangle count for the
touched face, which the old carve-out residue could not express.

## What stays a residue, and why it is irreducible (the honest §3.3 finding)

The face1 face's `tOrbitCard = 2` + one indicator is *equivalent* to the correct-anchor
orbit-isolation: walking `keptPhi` from the kept face1 dart `d1 = M.φ dart`, `keptPhi d1 = d2`,
but `keptPhi d2` SKIPS the deleted chord dart, so the kept face1 darts merge with the boundary
gap; `tracePhi` re-isolates them into a 2-dart orbit re-closed by one fresh chord dart **iff
the anchor is placed at `β aⱼ = d2`** — exactly the discrete Jordan–Schoenflies correct-anchor
datum the prior rounds isolated, NOT certified by the abstract `CombMap` (the anchors `a₀,a₁`
are universally quantified throughout the side machinery).  This file **exposes that residue as
a concrete face-SIZE count** (`tOrbitCard = 2` + one indicator), fully verified by the formula,
rather than an unsatisfiable `≠ face₁` carve-out or a black-box absorption.  Its M-side (2 kept
darts) is now a THEOREM; only the orbit-isolation remains, anchor-dependent.

This also resolves the task's branch question (`face₁` outer, or inner?): handled BOTH ways.
If the side image of `face₁` IS `outerFace`, `InnerFacesSide₁NoCarve` never asks for it
(it only quantifies over `f ≠ outerFace`).  If it is a genuine inner face, the direct count
discharges it.  No "absorbed by boundary" assumption is used.

## Chordless branch (`CleanFaceClass`) — NO analogue gap exists

The chordless deletion is the SINGLE-merged-orbit regime: deleting `v0` merges ALL `v0`-incident
faces into ONE merged outer face; every OTHER deleted face is **clean** (its `φ'`-orbit is an
untouched `M.φ`-orbit).  There is **no face1-analogue touched-inner face** — the sole touched
orbit is the merged outer face, which `ChordlessFinal.CleanFaceClass` already EXCLUDES
(it quantifies over `f ≠ outerFace`).  So `CleanFaceClass` has no `≠ face₁`-style carve-out to
remove; the chordless `inner_tri` is already discharged cleanly from it
(`deleteVertex_inner_tri_of_cleanFaceClass`, clean-3).  I did NOT edit `ChordlessFinal.lean`
(one-writer rule; no change is needed for the chordless analogue).

## New file (owned, fresh; NOT wired into ProofsInTheBook.lean — one-writer rule)

`ProofsInTheBook/ChordFaceFinal.lean` — imports `ChordBoundaryOrbit`.  13 audited results.
Branch `main`; no commits; no branch switch; no codex/OpenAI tooling; never ran lake/lean on
the Mac (kernel-panic rule observed — verified exclusively on uisai1).

## Verification (server uisai1, real olean chain)

- Dependency `nohup lake build ProofsInTheBook.ChordBoundaryOrbit` → Build completed
  successfully (8461 jobs).
- `lake env lean ProofsInTheBook/ChordFaceFinal.lean` → **RC = 0**, zero errors, zero
  warnings, no `sorry`/`sorryAx`.  All **13** `#print axioms` results
  **clean-3 `[propext, Classical.choice, Quot.sound]`**:
  `sideFaceLen_formula`, `spliceUntouched_faceLen_eq_tOrbit`, `sideFaceLen_three_of_count`,
  `tOrbitCard_eq_keptFaceLen`, `sideMap₁_faceLen_three_of_count`,
  `sideFaceTriangle_of_spliceUntouched`, `sideFaceTriangle_of_count`,
  `sideInnerTriangulation_of_noCarve`, `contiguousInterval_of_noCarve`, `noCarve_discharge_eq`,
  `innerFacesSide₁NoCarve_of_innerFacesSide₁`, `dart_mem_keptDel₁`, `face₁_two_kept_darts`.
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → none in code (only the docstring
  disclaimer).
- `#print axioms ProofsInTheBook.ThomassenInduction.nearTriangulation_five_colorable`
  → **clean-3, UNCHANGED** (still parameterized by the `JordanOracle`-valued hypothesis
  `Ofun : ∀ p q, ∀ cp cq, JordanOracle α`; no upstream file edited — faithful advance,
  not a regression).

## §3.3 verdict: FAITHFUL, non-vacuous, genuine reduction (not a re-wrapper / not fabricated)

- **Genuine advance.** The general side-face length formula and the DIRECT chord-triangle
  discharge are PROVED UNCONDITIONALLY — the touched `face₁` face is now a genuine inner
  triangle handled by the explicit trace, eliminating the `≠ face₁` carve-out from the residue.
  The M-side of the chord-triangle count (`face₁` has exactly 2 kept darts) is a THEOREM.
- **Not a re-wrapper.** `sideInnerTriangulation_of_noCarve` consumes the per-face
  `SideFaceTriangle.hlen` (either route), NOT a hidden hypothesis; `noCarve_discharge_eq`
  (`rfl`) certifies it IS the assembled `ContiguousInterval`'s `inner_tri`;
  `innerFacesSide₁NoCarve_of_innerFacesSide₁` proves the new residue is no stronger than the old.
- **Not vacuous.** The new `InnerFacesSide₁NoCarve` is satisfiable in the face1 case (via
  `sideFaceTriangle_of_count`) precisely where the old `InnerFacesSide₁` was UNSATISFIABLE; the
  count's M-side is exhibited unconditionally (`face₁_two_kept_darts`), so the residue is the
  honest correct-anchor orbit-isolation, not a disguised `False`.
- **Not fabricated.** No fake outer face, no fake face correspondence, no "absorbed by
  boundary" assumption.  The lone surviving residue is the correct-anchor orbit-isolation
  (`tOrbitCard = 2` + one indicator for the face1 face) + the surjection datum — the genuine
  discrete Jordan–Schoenflies content the abstract `CombMap` cannot carry.

## The precise residue now (sharpened)

- **chord side:** `InnerFacesSide₁NoCarve` = every non-outer side face has a `SideFaceTriangle`
  witness.  The face1-touched face's witness needs the explicit chord-triangle count
  (`tOrbitCard = 2` + one fresh chord dart) — the correct-anchor orbit-isolation, M-side proved
  unconditionally, orbit-isolation anchor-dependent.  Plus the side-face↔M-face surjection datum
  (`sideFace_has_inl_rep` proved; the which-orbit-is-outer identification is the Jordan datum).
- **chordless:** no analogue residue beyond the existing `CleanFaceClass` (single merged orbit;
  no touched-inner face).
- **headline:** `JordanOracle` cannot be built without the correct-anchor data;
  `nearTriangulation_five_colorable` stays CONDITIONAL (clean-3, unchanged).
