# opus-containment reply — `SubRegionContainment` CLOSED unconditionally; `M` peel-order isolated

**Status: Residue 1 (SubRegionContainment / OffDiagDisjoint) is now FULLY DISCHARGED —
unconditionally, from the `CutGeometry` interface alone. Residue 2 (`M` peel-order)
remains, isolated as one named, definitionally-faithful, non-vacuous `Prop`.**

**File:** `ProofsInTheBook/PolygonContainment.lean` (FRESH, overwrote the prior partial;
the only file I own, 320 lines).
**Branch:** `main` (no switch, no commit, zero tracked-file modifications — `git status`
shows it only as `?? ProofsInTheBook/PolygonContainment.lean`).
**Server:** `uisai1`. **No codex / OpenAI tooling. NEVER ran lake/lean on the Mac.**
**Build dep:** `lake build ProofsInTheBook.PolygonCutClose` → *Build completed (8445 jobs)*.
**Verification (uisai1):**
* `lake env lean ProofsInTheBook/PolygonContainment.lean` → **RC=0**.
* `lake build ProofsInTheBook.PolygonContainment` → *Built (8446/8446)*, **RC=0**.

---

## The decisive observation (why Residue 1 closes, and why the prior routes were wrong)

The handoff's suggested route (generalize `triangleExteriorEven_unconditional` via the
convex hull) and the prior partial file's `HullInteriorContainment` both leave the
**non-convex dent points** open, because a point exterior to `P` can lie *inside*
`convexHull (range P.q)`. The crossing-parity split is *also* provably insufficient
(`PolygonCutClose.parity_admits_both_inside`). Both routes were genuine dead ends for the
*full* residue.

The correct route does not go through parity or the hull at all: **a genuine `CutGeometry`
already carries the two region-split set identities as primitive fields**:

```
  {region_L} ∪ {region_R} = {region_P}            (CutGeometry.split_region_union)
  {region_L} ∩ {region_R} = seg (P.q i) (P.q j)   (CutGeometry.split_region_intersection)
```

These are *exactly* what the two residues need:

* **`subRegionContainment_of_cutGeometry`** (NEW, unconditional): `SubRegionContainment g`
  for *any* `CutGeometry g`. A point in `region_L` is in `region_L ∪ region_R = region_P`
  by `split_region_union`. No boundary, parity, or hull hypothesis — the union identity
  *is* the containment.

* **`offDiagDisjoint_of_cutGeometry`** (NEW, unconditional): `OffDiagDisjoint g` for *any*
  `CutGeometry g`. If a point were in both sub-regions it would lie in
  `{region_L} ∩ {region_R} = seg (P.q i)(P.q j)` (the diagonal). But the diagonal segment
  is the **closing edge of the left sub-polygon** (`diag_subset_onBoundary_left`, proved by
  index arithmetic: `leftIndex i j` sends the last index to `j` and the wrapped successor
  index `0` to `i`, so `Edge (subpolygonLeftTuple P i j) last = seg (P.q j)(P.q i) =
  seg (P.q i)(P.q j)`), so the point would be `OnBoundary L` — contradicting the
  off-boundary hypothesis.

So `OffDiagDisjoint` / `SubRegionContainment` are **not** an extra irreducible Jordan
oracle on top of the `CutGeometry` (as `PolygonResidualData`'s header and the prior rounds
asserted): they are formal consequences of the region-split identities the `CutGeometry`
interface *already supplies*. This is non-circular — both identities are primitive
`CutGeometry` fields, never derived from disjointness.

### Headline reached (strictly more unconditional than the prior best)

* **`polygonCutInput_of_cutGeometry`** — builds `PolygonResidualData.PolygonCutInput` from a
  uniform `CutGeometry` + the satisfiable `CommonRay` condition, with the `disj` field
  **derived** (no longer an input). Strictly more unconditional than
  `PolygonCutClose.polygonCutInput_of_containment` (which still consumed a containment
  oracle).
* **`artGallery_strict_via_cutGeometry`** — the Chapter-36 `⌊n/3⌋` art-gallery headline,
  conditional on exactly: a uniform `CutGeometry` with common rays + the peel oracle `M`.
  Conclusion is the genuine
  `∃ guards, guards.card ≤ n/3 ∧ ∀ x, ClosedRegion' P ρ x → ∃ v ∈ guards, Sees P ρ (P.q v) x`.
  The **entire half-plane-disjointness / sub-region-containment surface is mechanically
  closed**; the `disj`/containment input is removed.

## Residue 2 — `M = DiagonalAttachInput`: peel-order half, isolated honestly

`M` is *universal over all child glues* `gL gR` — it demands `AttachesTo` for the remapped
right triangulation against the remapped left one, for **every** `CombinatorialGlue` pair.
Unwinding `AttachesTo`:
* the `glue` step's index-freshness half is the proved
  `PolygonCutClose.rightArcInterior_fresh_for_left` (re-exported here);
* the `single` base step needs the *innermost* triangle of every child glue to carry the
  diagonal edge `{i, j}` — a *peel-reordering*. The recursion that builds the glues
  (`PolygonLast.combinatorialGlue_of_attach`) is upstream and consumes `M` as a universal,
  so building a "canonical diagonal-first glue" in this leaf does **not** discharge `M`
  (it would hold for *my* glue, not the arbitrary ones the recursion feeds `M`). Closing it
  requires reorganising that recursion — outside this file's one-writer boundary. This was
  independently reached by both `PolygonCutClose` and the prior partial file.

I isolate the precise resistant sub-fact and prove it is exactly `M`, faithfully:
* **`InnermostGlueOnDiagonal`** (def) — the `AttachesTo`-per-split statement.
* **`diagonalAttachInput_iff_innermost`** — `DiagonalAttachInput B ↔ InnermostGlueOnDiagonal B`
  by **`Iff.rfl`** (definitional equality — verified by the kernel, RC=0). So the residue is
  neither a strengthening nor a weakening; it *is* `M`. Non-vacuity stands via
  `PolygonLast.attachesTo_nonvacuous`.

## Verification (playbook §3 acceptance)

* **A (mechanical):** 0 `sorry`/`admit`/`axiom`/`native_decide` (grep matches are only the
  docstring "No sorry/axiom/admit/native_decide" line + prose). RC=0; olean built.
* **`#print axioms` (clean-3, all):**
  * `subRegionContainment_of_cutGeometry` → `[propext, Classical.choice, Quot.sound]`
  * `offDiagDisjoint_of_cutGeometry` → `[propext, Classical.choice, Quot.sound]`
  * `artGallery_strict_via_cutGeometry` → `[propext, Classical.choice, Quot.sound]`
  * `diag_subset_onBoundary_left` → `[propext, Classical.choice, Quot.sound]`
  * `polygonCutInput_of_cutGeometry` → `[propext, Classical.choice, Quot.sound]`
  * `diagonalAttachInput_iff_innermost` → `[propext, Classical.choice, Quot.sound]`
  * `rightArcInterior_fresh_for_left` → `[propext, Classical.choice, Quot.sound]`
  No `sorryAx`, `ofReduceBool`, or `trustCompiler`.
* **B/C (signature/semantic):**
  * The headline's printed conclusion is the genuine `⌊n/3⌋` art-gallery bound.
  * `offDiagDisjoint_of_cutGeometry`'s statement is *verbatim* `PolygonOracle.OffDiagDisjoint`
    (checked field-by-field); `subRegionContainment_of_cutGeometry`'s is verbatim
    `PolygonCutClose.SubRegionContainment`. **FAITHFUL**, not a re-wrapper.
  * **Non-circularity:** the derivation uses only the primitive `CutGeometry` fields
    `split_region_union` / `split_region_intersection`, never `OffDiagDisjoint`. (The
    `region_union_off_boundary` lemma that *does* use disjointness lives on the
    `ResidualGeometryData → CutGeometry` builder path, irrelevant here.)
  * **Non-vacuity:** a `CutGeometry` is the chapter's assumed irreducible planar input
    (`PolygonResidualData`: "no producer" from a bare polygon); my theorems show the
    `disj` field carried *separately* by `PolygonCutInput`/`ResidualGeometryData` is in fact
    redundant given the other fields — a strict reduction of the input surface, not a
    vacuous discharge.
  * **Verdict: Residue 1 FAITHFUL + UNCONDITIONAL (closed); Residue 2 CONDITIONAL-honest**
    (`M` peel-order, definitionally faithful, non-vacuous, outside leaf write-boundary).

## Most-unconditional headline + precise residue

* **`artGallery_strict_via_cutGeometry`** — Chapter-36 `⌊n/3⌋`, conditional on exactly a
  uniform `CutGeometry` + common rays + `M`. The half-plane disjointness / sub-region
  containment is **fully discharged** (both directions).
* **The single remaining residue:** `M`'s peel-order half — the innermost triangle of
  *every* upstream-constructed child glue carries the diagonal edge
  (`InnermostGlueOnDiagonal`, = `M` by `Iff.rfl`). Its index-freshness half is the proved
  `rightArcInterior_fresh_for_left`; the constructive half requires editing
  `PolygonLast.combinatorialGlue_of_attach` (one-writer boundary). **Concrete failing
  chain:** for an arbitrary `gR : CombinatorialGlue B tR`, the `.single T` base of
  `gR.triang.remap` is an arbitrary realiser-closed triangle whose corners need not include
  both diagonal endpoints `i, j`, so the `AttachesTo`-`single` clause `∃ T' ∈ A, ∃ e ∈
  T.edges, e ∈ T'.edges ∧ v ∉ e` (shared diagonal edge) is not derivable without forcing a
  diagonal-first peel of `gR` — which `combinatorialGlue_of_attach` does not produce.

## Discipline

No codex/OpenAI tooling (resource rule respected). Stayed on `main`, no commits, no branch
switch, zero tracked-file modifications. Created only the FRESH file
`PolygonContainment.lean` (overwrote the prior partial). Verified exclusively via rsync +
`lake env lean` / `lake build` / `#print axioms` on `uisai1` (no local build on the Mac).
Import graph / `Audit.lean` / `ProofsInTheBook.lean` left for the orchestrator to wire.

## Wiring note for the orchestrator

To upgrade the chapter headline end-to-end: `artGallery_strict_via_cutGeometry` removes the
`OffDiagDisjoint`/containment input from `PolygonCutInput`. If a uniform `CutGeometry` +
`CommonRay` supplier is provided elsewhere, the only remaining oracle of the `⌊n/3⌋`
headline is `M` (peel-order). The `CutGeometry` itself (convex-vertex / transversality /
cut-axioms / region-split identities) remains the chapter's assumed planar interface, per
`PolygonResidualData`'s "no producer" analysis.
