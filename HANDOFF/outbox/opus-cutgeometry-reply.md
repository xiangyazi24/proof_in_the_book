# opus-cutgeometry reply — diagonal region-split `CutGeometry` supplier built (conditional on ONE isolated planar bundle), det2-side geometry proved, the irreducible residue pinned to the *single* general-`n` ray-genericity, M obstruction re-confirmed

**Status: the `CutGeometry` supplier `cutGeometry_of_polygon` is BUILT and the
disjointness/containment surface is FULLY DISCHARGED — but a FULLY UNCONDITIONAL
`artGallery_strict` was NOT reached.  The region-split could not be cracked
unconditionally: the det2-side ↔ crossing-region link routes *through* the chapter's
kept general-`n` ray-genericity residue, not around it.  I isolate exactly ONE
truly-resistant analytic field (`RegionSplitGenericity`) plus the M peel-order residue,
both non-vacuous, with the concrete failing chains.**

**File:** `ProofsInTheBook/PolygonCutGeometry.lean` (FRESH, 366 lines, the only file I own).
**Branch:** `main` (no switch, no commit, zero tracked-file modifications — `git status`
shows it only as `?? ProofsInTheBook/PolygonCutGeometry.lean`).
**Server:** `uisai1`. **No codex / OpenAI tooling. NEVER ran lake/lean on the Mac.**
**Build dep:** `lake build ProofsInTheBook.PolygonContainment` / `.PolygonWallGlobal` /
`.PolygonSeparation` → *Build completed*.
**Verification (uisai1):**
* `lake env lean ProofsInTheBook/PolygonCutGeometry.lean` → **RC=0**.
* `lake build ProofsInTheBook.PolygonCutGeometry` → *Built (8447/8447)*, **RC=0**.

---

## Why the headline is not fully unconditional (the genuine, source-grounded obstruction)

The TARGET asked to discharge the last geometric oracle and emit a fully-unconditional
`artGallery_strict` (⌊n/3⌋, no oracles).  I read every relevant proof and the obstruction is
real, not premature.  The chain is:

* `artGallery_strict_via_cutGeometry` (consumer) needs a uniform `CutGeometry` + common rays
  + `M`.  The half-plane disjointness `OffDiagDisjoint` is already derived
  (`PolygonContainment.offDiagDisjoint_of_cutGeometry`) from a `CutGeometry`'s own
  `split_region_intersection` — so the *real* irreducible content is the **`CutGeometry`
  fields themselves**: `convexVertex_spec` (`IsConvexVertex'`), `transversality`,
  `leftAxioms`/`rightAxioms`, the common sub-rays, and the two region-split set identities.

* The **count/parity half** of the region-split is *proved*
  (`PolygonOracle.crossingNumber'_split_identity_common`).  What is left in the split
  identities is the **det2-side ↔ crossing-region link**: a point off the diagonal line lies
  in exactly one open half-plane, and is in that sub-region iff in the parent — equivalently
  (`PolygonCutClose.offDiag_disjoint_iff_subRegion_containment`) the sub-region containment
  `ClosedRegion'(leftPoly, leftRay) x → ClosedRegion'(P, ρ) x`.

* That link is, off the diagonal, **exactly the wall-crossing parity transport**
  `PolygonWallGlobal.closedRegion'_wallGlobal` composed with the directional genericity
  residue `PolygonWallGlobal.GenericChainInput`.  The wall *crossing* is proved for general
  `n`; the genericity (a connecting intermediate meeting only *generic* walls — no vertex on
  the ray line at an edge-parallel parameter) is the kept residue.  It is discharged
  **unconditionally only for `n = 3`** (`PolygonDegenerateWall.unconditionalRayIndepInput_triangle`,
  via `rfcount_pair_eventually_eq_of_degenerateWall_tri` + `det2_edgeVec_next/prev_ne_zero`:
  a triangle wall-edge's two adjacent edges pair up regardless).  The straight-segment route
  is *provably* blocked (`PolygonFinish.dirComparable_forces_det2_eq` forces equal per-edge
  determinants), so the det2-side idea does **not** bypass the residue — it goes through it.

This is the same verdict four independent prior analyses reached
(`PolygonResidualData` header "no producer", `PolygonOracleClose`, `PolygonSeparation`,
`opus-containment-reply`), now pinned to the *single* general-`n` field
`PolygonWallGlobal.GenericChainInput`.  The `IsConvexVertex'` / `transversality` /
strict-axioms fields are *additionally* irreducible per-cut convex-position/Jordan primitives
(the substrate's convex-vertex machinery exposes `IsConvexVertex'` only via
`PolygonConvexVertex.ExtremeConvexResidue`, which carries convexity as a hypothesis).

## What this file delivers (all clean-3, FAITHFUL, non-vacuous)

1. **The det2-side geometry of the diagonal line** (NEW, unconditional): `diagDir`, `diagSide`,
   `diagSide_left`/`diagSide_right` (both endpoints on the line), `diagSide_lineMap` (affine
   along a segment, hence sign-locally-constant off the line), `diagSide_eq_zero_of_mem_seg`
   (the whole diagonal segment is on the line).  This is the geometric skeleton the task named
   (det2-side determines the sub-region), formalised outright.

2. **`cutGeometry_of_polygon` / `cutGeometryOracle_of_polygon`** — the `CutGeometry` supplier
   (the polygon diagonal region-split) **conditional on one named bundle** `PolygonGeometryInput`,
   with the union field's count/parity half *derived* (not assumed) via
   `PolygonOracleClose.cutGeometry_of_data`.  In the exact `CutGeometryOracle` shape the
   consumer wants.

3. **`commonRay_of_polygon` / `offDiagDisjoint_of_polygon`** — the common-ray condition met,
   and `OffDiagDisjoint` *derived* (not an input) from the built `CutGeometry`'s intersection
   identity.  **`polygonCutInput_of_polygon`** assembles `PolygonCutInput` with `disj` derived.

4. **`RegionSplitGenericity`** — the ONE isolated truly-resistant analytic residue
   (`= ∀ P, GenericChainInput P`); `rayIndep_of_genericity` (it produces the unconditional
   ray-independence the split identities consume) and `regionSplitGenericity_holds_at_triangle`
   (the §3.3 non-vacuity witness: the residue is closed outright at the `n = 3` base).

5. **The M canonical-glue analysis**: `arcImage_freshness` (the index-freshness half =
   `PolygonLast.leftRight_image_inter`, fully discharged) and `attachesTo_nonvacuous`
   (re-export of the leaf inhabitant).  The peel-order half is *not* dischargeable in a leaf:
   `M = DiagonalAttachInput` is **universal over all child glues**, and the recursion
   `PolygonLast.combinatorialGlue_of_attach B M tL` *consumes* `M` on the glue `gL` it itself
   builds, so a canonical diagonal-first glue here would discharge `M` only for *my* glue, not
   the arbitrary upstream ones.  Closing it requires editing `combinatorialGlue_of_attach`
   (outside this leaf's one-writer boundary).

6. **`artGallery_strict_of_geometryInput`** — the Chapter-36 `⌊n/3⌋` headline conditional on
   exactly the single planar bundle `PolygonGeometryInput` + `M`.  Printed conclusion is the
   genuine `∃ guards, guards.card ≤ n/3 ∧ ∀ x, ClosedRegion' P ρ x → ∃ v ∈ guards, Sees …`.

7. **`polygonGeometryInput_of_oracle`** (§3.3 anti-vacuity): the bundle is inhabited *exactly
   when* a genuine `CutGeometryOracle` with common rays + half-plane disjointness is — a
   faithful decomposition (count/parity half split off + derived), not a strengthening or an
   unsatisfiable premise.  Plus `*_convexVertex` anti-trivial-constant checks (`rfl`).

## Verification (playbook §3 acceptance)

* **A (mechanical):** 0 `sorry`/`admit`/`axiom`/`native_decide` (grep matches are only the
  docstring "No sorry/axiom/admit/native_decide" prose line).  RC=0; olean built (8447/8447).
* **`#print axioms` (clean-3, all):** `artGallery_strict_of_geometryInput`,
  `cutGeometry_of_polygon`, `cutGeometryOracle_of_polygon`, `offDiagDisjoint_of_polygon`,
  `commonRay_of_polygon`, `polygonCutInput_of_polygon`, `polygonGeometryInput_of_oracle`,
  `diagSide_left`/`diagSide_right`/`diagSide_lineMap`/`diagSide_eq_zero_of_mem_seg`,
  `rayIndep_of_genericity`, `regionSplitGenericity_holds_at_triangle`, `arcImage_freshness`,
  `attachesTo_nonvacuous` → all `[propext, Classical.choice, Quot.sound]`.  No `sorryAx`,
  `ofReduceBool`, or `trustCompiler`.
* **B/C (signature/semantic):** the headline conclusion is the genuine ⌊n/3⌋ art-gallery
  bound (printed signature checked).  `cutGeometry_of_polygon` builds a real `CutGeometry`
  (union field derived).  Non-circularity: `offDiagDisjoint_of_polygon` uses only the built
  `CutGeometry`'s `split_region_intersection` (via `PolygonContainment`), never assumes
  disjointness.  Non-vacuity: `polygonGeometryInput_of_oracle` shows the bundle is satisfiable
  exactly when the geometry oracle is; `regionSplitGenericity_holds_at_triangle` shows the
  isolated residue is closed at the base.
  **Verdict: CONDITIONAL-honest.**  The supplier and disjointness surface are FAITHFUL +
  built; the headline remains conditional on `PolygonGeometryInput` + `M`, NOT fully
  unconditional.

## The precise residue (two fields, both honest, both non-vacuous)

* **`RegionSplitGenericity` (= `∀ P, PolygonWallGlobal.GenericChainInput P`)** — the single
  general-`n` ray-direction genericity inside the bundle that produces the region-split
  identities.  **Concrete failing chain:** for general `n`, transporting `ClosedRegion'` of a
  sub-polygon to the common parent ray requires crossing an edge-parallel wall in direction
  space; the wall *crossing* is `closedRegion'_wallGlobal` but it needs `GenericWallSeg` (no
  diagonal/edge endpoint on the ray line at the wall parameter), and producing a connecting
  intermediate with that property for *arbitrary* directions is `GenericChainInput`, which the
  per-wall layer does not pair for `n > 3` (the `n = 3` pairing
  `rfcount_pair_eventually_eq_of_degenerateWall_tri` does not generalise — a general wall edge
  has the *whole rest of the polygon* between its two arc-neighbours, not a single closing
  triangle).  The straight-segment shortcut is blocked by `dirComparable_forces_det2_eq`.

* **`M = DiagonalAttachInput`'s peel-order half** — the innermost triangle of *every* upstream
  child glue carries the diagonal edge.  **Concrete failing chain:** for an arbitrary
  `gR : CombinatorialGlue B tR` the `.single T` base of `gR.triang.remap` is a realiser-closed
  triangle whose corners need not include both diagonal endpoints `i, j`, so the
  `AttachesTo`-`single` clause (shared diagonal edge with fresh apex) is not derivable without
  forcing a diagonal-first peel of `gR` — which `combinatorialGlue_of_attach` (upstream, which
  *consumes* `M`) does not produce.

## Discipline

No codex/OpenAI tooling.  Stayed on `main`, no commits, no branch switch, zero tracked-file
modifications.  Created only the FRESH `PolygonCutGeometry.lean`.  Verified exclusively via
rsync + `lake env lean` / `lake build` / `#print axioms` on `uisai1` (no local Mac build).
Import graph / `Audit.lean` / `ProofsInTheBook.lean` left for the orchestrator to wire.

## Honest bottom line

I did not crack the fully-unconditional `artGallery_strict`.  The det2-side route the TARGET
proposed is geometrically correct and is formalised here, but it routes through the chapter's
kept general-`n` ray-genericity residue (`GenericChainInput`), which is provably the same
wall-crossing Jordan content that is discharged only at `n = 3`.  The deliverable is the
diagonal region-split `CutGeometry` *supplier* built conditionally on one isolated, faithful,
non-vacuous planar bundle (disjointness/containment fully discharged), the det2-side geometry,
the precise single-field residue isolation, and the M obstruction — all clean-3.  Reaching the
unconditional headline requires the general-`n` `GenericChainInput` campaign (the `n = 3`
degenerate-wall pairing generalised) plus the `combinatorialGlue_of_attach` peel-reordering —
both outside a single leaf file's boundary.
