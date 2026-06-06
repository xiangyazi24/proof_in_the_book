# opus-polylast — Chapter 36 last three residuals: count bijection, half-plane disjointness, diagonal merge

**STATUS: The two reusable HARD CORES of the diagonal merge are PROVED
unconditionally; the merge is assembled into the art-gallery headline as an *honest
conditional* on the irreducible planar oracles plus a peel-ordering certificate whose
index-arithmetic half is discharged and whose non-vacuity is certified. Residuals (i)
count-bijection and (ii) half-plane disjointness are confirmed irreducibly-Jordan and
left inside the named `CutGeometryOracle` — not faked.**

New file `ProofsInTheBook/PolygonLast.lean` (518 lines), imports
`ProofsInTheBook.PolygonIccEngine`. Compiles clean on uisai1: **0 sorry / 0 axiom /
0 admit / 0 native_decide**. All 7 audited headlines/cores are **clean-3**
`{propext, Classical.choice, Quot.sound}` (verified from rebuilt oleans). Branch
`main`, no switches, no commits; only the one NEW file created, not wired into any
root (so no other build disturbed). Verified EXCLUSIVELY via rsync→uisai1
`lake env lean` / `lake build`; never ran lake locally (kernel-panic rule).

---

## Residual (iii) — the combinatorial diagonal merge

### PROVED unconditionally (the genuinely-new, reusable content)

* **`TriangulatedPolygon.mergeOnto`** — the fully general combinatorial glue of two
  triangulations along a shared edge: from an `AttachesTo` certificate (second
  triangulation's base attaches along a shared edge with a fresh apex; every later
  peeled apex avoids the first's vertices) it produces a `TriangulatedPolygon` of the
  *union* of the two triangle sets. Induction on the peel; each ear re-glued onto the
  accumulating set; the shared-edge and freshness obligations transfer.

* **`leftRight_image_inter`** — the arc-index disjointness keystone: the left- and
  right-arc images of a diagonal `i, j` meet *only* at the two endpoints `i, j`. Pure
  modular arithmetic (`mem_leftIndex_image`, `mem_rightIndex_image`, `j_val_eq_arcPos`,
  cancellation over `cyclicSteps i j + cyclicSteps j i = n`). This is exactly the
  index freshness the merge needs: a right-arc-*interior* apex is fresh for the whole
  left arc.

* **`mergedGlue`** — the per-split merged `CombinatorialGlue B (splitDiagonal …)`:
  remaps both children via `TriangulatedPolygon.remap` (from `PolygonIccEngine`,
  injective `leftIndex`/`rightIndex`), glues them with `mergeOnto`, and transfers
  realisers (`realisedBy_mapLeft`/`realisedBy_mapRight`). The geometric realisation is
  fully discharged (`gL.realise`/`gR.realise` + the index-remap transfer).

* **`combinatorialGlue_of_attach`** (recursion) and **`artGallery_strict_attach`**
  (headline) — wire the above into `PolygonFinish.artGallery_strict_finish`. The
  realisation half, the glue recursion, and the merge *index-freshness* are all
  discharged.

### Honest residual: `DiagonalAttachInput` (the peel-ordering)

What the cores do *not* supply is the *peel order*: a witness that the remapped right
sub-triangulation attaches along the diagonal edge `{i, j}` **first**. An arbitrary
realising `CombinatorialGlue` need not carry the diagonal as a triangle edge, so
`DiagonalAttachInput` (universal over all child glues) is a **strong** hypothesis; its
full discharge needs a triangulation peel-reordering into a diagonal-first linear peel.
We do *not* claim it dischargeable. Crucially (playbook §3.3 vacuity guard) we PROVE
the attach predicate is **non-vacuous** — `attachesTo_nonvacuous`: it holds for the
leaf configuration (two triangles sharing an edge, fresh apex), i.e. the exact shape
of every diagonal-merge leaf. So the conditional headline is *not* a vacuous-premise
impostor; the index-arithmetic half of the residual is fully discharged by
`leftRight_image_inter`, only the peel-reordering remains.

This is the sharpest honest form: `DiagonalMergeInput` (IccEngine's residual) is
*replaced* by the strictly index-discharged `DiagonalAttachInput`, with the two hard
cores proved and the residual reduced to pure peel-ordering combinatorics.

## Residuals (i) count bijection & (ii) half-plane disjointness — irreducibly Jordan

Confirmed (matching `PolygonIccEngine`'s assessment): these are the planar content of
the two `CutGeometry` fields `split_region_union` / `split_region_intersection`. The
sharpest honest reduction is already proved upstream: off all boundaries the parent
region is the *symmetric difference* of the two sub-regions
(`split_region_symmDiff_of_countSum` from `CountSummationDatum`); the *union* (vs
symm-diff) additionally needs the sub-regions disjoint off the diagonal (half-plane
separation). The count bijection as a literal per-edge identity does not close cleanly
because the three crossing numbers use *different* ray vectors (parent `ρ` vs the
subpolygons' fresh rays), so the per-edge `RawEdgeCrosses` match (the algebraic kernel
`edgeCrossesRay'_eq_raw`) requires a *common* ray — and the common-ray transfer is at
the region/parity level, not the raw count. Both stay named inside `CutGeometryOracle`;
we do not fake them.

## Faithfulness verdicts (playbook §3.1 Group C, §3.3 adversarial)

- **FAITHFUL (unconditional):** `TriangulatedPolygon.mergeOnto`, `leftRight_image_inter`
  (+ `mem_leftIndex_image`, `mem_rightIndex_image`, `j_val_eq_arcPos`),
  `triVerts_subset_vertices`, `corner_mem_edge_of_ne_apex`, `mergedGlue`,
  `realisedBy_mapLeft/Right`, `attachesTo_nonvacuous`.
- **CONDITIONAL-honest:** `combinatorialGlue_of_attach`, `artGallery_strict_of_attach`,
  `artGallery_strict_attach` on (`CutGeometryOracle`, `BaseTriangleFacts`,
  `DiagonalAttachInput`). The conclusion is the faithful art-gallery statement
  (`∃ guards, card ≤ n/3 ∧ ∀ region point, ∃ guard, Sees`), `Sees` = segment-in-region
  — not weakened.
- **NAMED RESIDUALS (not results):** `DiagonalAttachInput` (peel-ordering; index half
  discharged, non-vacuous); `CountSummationDatum` + half-plane disjointness (Jordan,
  inside `CutGeometryOracle`).
- **§3.3 vacuity check:** `DiagonalAttachInput` is *strong* but its predicate
  `AttachesTo` is proven *inhabited* (`attachesTo_nonvacuous`); the headline is NOT a
  vacuous conditional. Honestly flagged as a strong universal-over-glues hypothesis.

### Why NOT "unconditional headline (no named inputs)"

The unconditional `artGallery_strict` would require *constructing* a
`CutGeometryOracle` (convex-vertex existence + transversality + region
union/intersection) and `BaseTriangleFacts` (triangle region = hull) from nothing —
that IS the full planar Jordan/discrete-geometry content of the art-gallery theorem and
is not formalizable in the remaining substrate without the planar Jordan curve theorem.
The `DiagonalAttachInput` peel-reordering is the one combinatorial residual that genuinely
resisted full discharge; per the brief it is isolated, named, certified non-vacuous,
and its index-arithmetic core is proved.

## Verification
```
rsync -az .../PolygonLast.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
  && lake env lean ProofsInTheBook/PolygonLast.lean'              # exit 0
# nohup lake build ProofsInTheBook.PolygonLast                     # olean OK
# #print axioms on mergeOnto, leftRight_image_inter, mergedGlue,
#   combinatorialGlue_of_attach, artGallery_strict_attach,
#   attachesTo_nonvacuous, realisedBy_mapLeft
#   → all [propext, Classical.choice, Quot.sound]
# grep -E '\bsorry\b|\badmit\b|^axiom |native_decide' (code) → none
```
