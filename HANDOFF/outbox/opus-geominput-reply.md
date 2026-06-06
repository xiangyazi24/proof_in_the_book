# opus-geominput reply — `PolygonGeometryInput` convex-position bundle: general-`n` convex-vertex EXISTENCE + det2-side geometry PROVED; full reduction to ONE named non-vacuous Jordan residue; the bundle is NOT fully dischargeable (architectural, source-grounded)

**Status: the convex-position bundle was NOT fully discharged.  A fully-unconditional
`PolygonGeometryInput` is not constructible from the Chapter-36 substrate — the obstruction
is architectural (no Jordan curve theorem / no interior odd-crossing seed), not session-bound,
and re-confirmed at source this round with the newly-available ray-independence in hand.
What IS delivered, clean-3: the general-`n` convex-vertex EXISTENCE (combinatorial, proved),
the det2-side region-split geometry (proved), and the full reduction to a SINGLE named,
non-vacuous Jordan residue `PolygonGeomResidue`, with the headline unconditional given exactly
that one residue + `M`.**

**File:** `ProofsInTheBook/PolygonGeomInput.lean` (FRESH, ~380 lines, the only file I own).
**Branch:** `main` (no switch, no commit; `git status` shows it only as
`?? ProofsInTheBook/PolygonGeomInput.lean`).  **No codex / OpenAI tooling.  NEVER ran
lake/lean on the Mac.**  **Build dep:** `lake build ProofsInTheBook.PolygonMClose` → *Build
completed (8434 jobs)*.

## Verification (uisai1, playbook §3)

* `lake env lean ProofsInTheBook/PolygonGeomInput.lean` → **RC=0** (no errors, no warnings).
* `lake build ProofsInTheBook.PolygonGeomInput` → **"Build completed successfully (8449
  jobs)"**, **RC=0** — integrates, nothing downstream breaks.
* **Mechanical (A):** 0 `sorry` / `admit` / `native_decide` / `axiom` in the file (the only
  grep matches are docstring prose / the "No sorry/axiom/admit/native_decide" header line).
* **`#print axioms` (clean-3, ALL):** `exists_extreme_vertex`, `extreme_vertex_lowest`,
  `extreme_vertex_leftmost`, `baseSide_prev`, `baseSide_eq_zero_of_mem_seg`,
  `region_ray_independent`, `polygonGeometryInput_of_polygon`,
  `polygonGeometryInput_of_residue`, `polygonGeomResidue_of_oracle`,
  `artGallery_strict_of_residue`, `convexVertex_index_discharged`,
  `convexVertex_spec_is_containment` → **all `[propext, Classical.choice, Quot.sound]`**.  No
  `sorryAx`, `ofReduceBool`, `native_decide`.

## Per-field attack result (the brief's four fields)

| field | verdict |
|---|---|
| **general-`n` convex-vertex EXISTENCE** | the *index* is DISCHARGED (`exists_extreme_vertex` / `extremeVertex`: lex-min lowest-then-leftmost vertex, proved from finiteness + `3 ≤ n`; `extreme_vertex_lowest` / `extreme_vertex_leftmost` give the support-line orientation certificate). The *region-level spec* `IsConvexVertex' = closedTri ⊆ ClosedRegion'` is the irreducible residue (below). |
| **transversality** (`DiagonalTransversality'`) | irreducible Jordan content (boundary-freeness of the open ear/slide segment); det2-side geometry carries the *geometry* skeleton but not the parity bridge. |
| **cut strict-axioms** (`Left/RightStrictAxioms`) | irreducible per-cut planar axioms (noncollinearity at the cut + proper edge intersection); declared non-combinatorial at source (`PolygonCutOracle:250-255`). |
| **region-intersection / disjoint / boundary** | the count/parity half is PROVED upstream (`crossingNumber'_split_identity_common`); the ray-genericity half is PROVED upstream (`regionSplitGenericity_holds`, re-exported here as `region_ray_independent`); the remaining det2-side ↔ crossing-region bridge is the same single-edge-jump Jordan content. |

## Why the bundle is NOT fully dischargeable (the genuine, source-grounded obstruction)

`PolygonGeometryInput.data` requires, for **every** polygon/ray, a full `ResidualGeometryData`
whose `convexVertex_spec : IsConvexVertex' P ρ i` unfolds (def
`PolygonSideCrossing.IsConvexVertex'`) to the region containment
`closedTri (q prev) (q i) (q next) ⊆ {x | ClosedRegion' P ρ x}`.  `ClosedRegion'` is
**parity-defined** (`OnBoundary x ∨ Odd (CrossingNumber' P ρ x)`), so placing an *interior*
triangle point in the region needs an **interior odd-crossing seed** for some ray.

I checked whether the newly-PROVED ray-independence
(`regionSplitGenericity_holds = ∀ P, UnconditionalRayIndepInput P`, off-boundary
`ClosedRegion' P ρ x ↔ ClosedRegion' P σ x`) — which earlier analyses lacked — cracks this.
**It does not.**  Ray-independence transports a parity *between rays*; it creates no interior
seed.  The substrate's only odd-parity producer is `crossingNumber'_interior_eq_one`, a sum
over **all `n` polygon edges** that equals `1` only when the adjacent triangle *is* the whole
hull (`n = 3`, where the three triangle sides ARE the three polygon edges — exactly how
`triangleConvexLeaf_holds` closes the leaf via the closed-form barycentric `crossTau`-sign
identity).  For `n ≥ 4` the adjacent-triangle base is a *chord*; the full polygon's forward
crossings at an interior triangle point are not pinned by the three triangle sides, and **no
substrate lemma computes the per-edge `crossTau` sign** from the geometry.  This is precisely
the **single-edge-jump / half-plane Jordan content** the entire Chapter-36 stack keeps as a
named input (`PolygonSeparation` header, lines 42-49: the `loc`/`VertexSweepNeutral` residue
of `PolygonLocalConstancy` + the `SegmentChain` connectivity of `PolygonIccEngine`).
`transversality`, the cut strict-axioms, and the `disjoint`/`intersection`/`boundary` fields
bottom out in the same content (declared irreducible at their definition sites:
`PolygonResidualData` header; `PolygonOracle.OffDiagDisjoint`).

This matches five independent prior analyses (`PolygonResidualData`, `PolygonGeometryData` §5,
`PolygonOracleClose`, `PolygonSeparation`, `opus-cutgeometry-reply`) — now with the
ray-genericity sub-residue *eliminated* (proved) and the residue pinned to the single
interior-odd-seed Jordan fact.

## What this file delivers (faithful, non-vacuous, NOT a re-wrapper)

1. **General-`n` extreme-vertex existence** (`exists_extreme_vertex`, `extremeVertex`,
   `extremeVertex_le`, `extreme_vertex_lowest`, `extreme_vertex_leftmost`): the lex-min
   (lowest-then-leftmost) vertex of any `StrictSimplePolygon n`, proved outright via
   `Finset.exists_min_image` over the lexicographic order `ℝ ×ₗ ℝ`.  The orientation
   certificate (every vertex weakly above the support line) is the combinatorial heart of the
   convex turn — the general-`n` analogue of the `n = 3` template.

2. **The det2-side adjacent-triangle base geometry** (`baseSide`, `baseSide_prev/_next`,
   `baseSide_lineMap`, `baseSide_eq_zero_of_mem_seg`): the affine side functional cleanly
   splits a straight segment, both base endpoints on the line — the geometric carrier of the
   region-split (re-exported/specialised from `PolygonCutGeometry.diagSide`).

3. **Ray-independence, re-exported** (`region_ray_independent`): the genericity sub-residue is
   discharged (`regionSplitGenericity_holds`), so the residue below carries *only*
   convex-position Jordan content.

4. **THE TARGET, `polygonGeometryInput_of_polygon`** (the brief's named goal): a producer of
   the `PolygonGeometryInput` bundle, conditional on exactly ONE named non-vacuous Jordan
   residue `PolygonGeomResidue` (a uniform `ResidualGeometryData` supply).  Plus
   `polygonGeometryInput_of_residue` and the data-faithfulness `rfl` checks.

5. **`artGallery_strict_of_residue`** — the Chapter-36 `⌊n/3⌋` headline conditional on exactly
   `PolygonGeomResidue` + `M`, composing `polygonGeometryInput_of_residue` with the proved
   `PolygonCutGeometry.artGallery_strict_of_geometryInput`.  Printed conclusion is the genuine
   `∃ guards, guards.card ≤ n/3 ∧ ∀ x, ClosedRegion' P ρ x → ∃ v ∈ guards, Sees …`.

6. **Non-vacuity** (`polygonGeomResidue_of_oracle`, `*_convexVertex` `rfl` check): the residue
   is inhabited *exactly when* a genuine uniform `CutGeometry` with common rays + half-plane
   disjointness is — a faithful decomposition, not a strengthening or unsatisfiable premise.

7. **Precise residue isolation** (`convexVertex_index_discharged` — the index is proved;
   `convexVertex_spec_is_containment` — the spec is the genuine `closedTri ⊆ region`
   containment, a true planar Prop), pinning the exact discharged/residual boundary.

## Honest bottom line vs. the brief's hypothesis

The brief's framing — *"with regionSplitGenericity_holds + this bundle, cutGeometry_of_polygon
becomes unconditional → headline fully unconditional"* — **does not close**, because *this
bundle* (`PolygonGeometryInput`) is itself the irreducible Jordan/convex-position content, not
a thing the substrate produces.  `regionSplitGenericity_holds` closed the ray-genericity
sub-residue *inside* the bundle (and I re-export it), but the region-level `IsConvexVertex'`
containment + transversality + cut-axioms + half-plane disjointness remain the single
interior-odd-seed / single-edge-jump Jordan input.

**Genuinely closed:** general-`n` convex-vertex EXISTENCE (the index), the det2-side
region-split geometry, and the full reduction to ONE named non-vacuous residue.  **Residue:**
`PolygonGeomResidue` (the convex-position bundle), bottoming out in the single
interior-odd-crossing-seed Jordan fact the entire chapter keeps as a named input — confirmed
architectural, with the concrete failing chain above.  Reaching a fully-unconditional
general-`n` `artGallery_strict` requires building an interior-region-seed / Jordan layer
(the per-edge `crossTau`-sign computation generalised off the chord base) — a separate,
larger Jordan-curve campaign, outside a single leaf file's boundary.

## Discipline

No codex / OpenAI tooling.  Stayed on `main`, no commits, no branch switch, zero tracked-file
modifications.  Created only the FRESH `PolygonGeomInput.lean`.  Verified exclusively via
rsync + `lake env lean` / `lake build` / `#print axioms` on `uisai1` (no local Mac build).
Import-graph / `Audit.lean` / `ProofsInTheBook.lean` wiring left for the orchestrator.
