# opus-generalwall reply — general-`n` degenerate-wall parity transport CLOSED (RegionSplitGenericity now a PROVED theorem); M peel-order index-freshness discharged, peel-order isolated

**Status: TARGET 1 FULLY DONE (unconditional, general `n`).**  The general-`n`
degenerate-wall parity transport is proved, giving `∀ P, UnconditionalRayIndepInput P`
**unconditionally** (no genericity hypothesis, no `n = 3` restriction).  This is the
genuine analytic core the diagonal region-split consumes.  `RegionSplitGenericity` in
`PolygonCutGeometry` — which the previous round defined as the *provably false*
`∀ P, GenericChainInput P` — is **redefined to its true content and PROVED**.

**TARGET 2 (M peel-order): the index-freshness half is FULLY DISCHARGED** as a proved
theorem (`PolygonLast.rightArc_vertex_fresh_for_left`, from the proved
`leftRight_image_inter`).  The remaining **peel-order half** (the innermost `.single`
triangle of the canonical right glue must carry the diagonal edge `{i,j}`) is **not**
discharged: it is a genuine triangulation peel-reordering theorem (the dual-tree
re-rooting), confirmed resistant by five independent prior analyses.  I did **not** break
the working build with a half-finished reorder; `combinatorialGlue_of_attach` is left
intact and `M = DiagonalAttachInput` remains the named, non-vacuous residue, now with its
index half proved and the peel-order half pinned to one concrete failing chain.

## Files

* **NEW** `ProofsInTheBook/PolygonGeneralWall.lean` (≈ 745 lines) — the general-`n`
  degenerate-wall parity transport.  Imports `PolygonDegenerateWall`.
* **EDIT** `ProofsInTheBook/PolygonCutGeometry.lean` — Part 3 rewritten: `RegionSplitGenericity`
  redefined to `∀ P, UnconditionalRayIndepInput P` (the true content) and **proved**
  (`regionSplitGenericity_holds`); `rayIndep_of_genericity`, `rayIndep_unconditional`,
  `regionSplitGenericity_holds_at_triangle` updated.  Added import of `PolygonGeneralWall`.
* **EDIT** `ProofsInTheBook/PolygonLast.lean` — added §A.6: `vertices_subset_triVerts`,
  `vertices_remap_subset_image`, `rightArc_vertex_fresh_for_left` (the proved
  index-freshness half), and the isolated `DiagonalPeelOrder` residue (the peel-order half).
  `combinatorialGlue_of_attach` **unchanged** (no `M` discharge — see residue below).
* **EDIT** `ProofsInTheBook.lean` — added `import ProofsInTheBook.PolygonGeneralWall`.

**Branch:** `main`.  No commits, no branch switch.  No codex / OpenAI tooling.  NEVER ran
lake/lean on the Mac.  Verified exclusively on `uisai1` via rsync + `lake env lean` /
`lake build` / `#print axioms`.

## The new math (general-`n` degenerate-wall pairing) — why `n = 3` did not generalise, and how it does now

`PolygonDegenerateWall` (the `n = 3` round) paired the wall edge `w`'s two *adjacent*
edges `cyclicNext w` and `cyclicNext (cyclicNext w) = cyclicPrev w`, proving they carry
**equal** counts.  That used `cyclicNext (cyclicNext w) = cyclicPrev w` (the two far
endpoints *coincide*), which is `n = 3`-only.  For `n ≥ 4` the two adjacent edges
`p = cyclicPrev w` and `j = cyclicNext w` are NOT adjacent (the whole rest of the polygon
sits between their far endpoints), so they do **not** carry equal counts.

The fix is a **parity** (not equality) pairing.  At a degenerate wall of `w`
(`dirDen w = 0`, both endpoints on the ray line, off boundary):

* the wall edge contributes `0` near `t₀` (`PolygonWall.rfcount_eventually_zero_of_wall`,
  already unconditional, any `n`);
* `p, j` are non-wall (no two consecutive walls: `det2 (edgeVec w) (edgeVec (cyclicNext w)) ≠ 0`
  from `noncollinear_consecutive`, generalised here as `dirDen_ne_zero_of_wall_of_nonpar`);
* the two on-line side values `ds0Of w = side(P.q w)` and `ds1Of w = side(P.q (cyclicNext w))`
  are **positively proportional** (`s₁ = μ·s₂`, `μ > 0`, from `exists_smul_of_det2_zero`
  + `x` off the wall segment), so in the forward region
  `[Span(A, s₁)] + [Span(s₂, B)] ≡ [Span(A, μ s₂)] + [Span(s₂, B)] ≡ [Span(A, s₂)] + [Span(s₂, B)] ≡ [Span(A, B)]  (mod 2)`
  by `span_mod_two_through_vertex` at the *collapsed* shared on-line value, where
  `A = side(P.q (cyclicPrev w))`, `B = side(P.q (cyclicNext (cyclicNext w)))` are the two
  far off-line endpoints — both locally **nonzero** (else `p` resp. `j` would itself be a
  wall, contradiction), so `[Span(A,B)]` is locally constant.

This is `rpair_count_eventually_const_degenWall` (the new lemma).  For `n = 3` the two far
endpoints coincide so `Span(A,A) = false ⇒ 0`, recovering the triangle's *equal counts*.

**The global assembly** (`rcrossSum_parity_eventually_const_general`, any `n`,
hypothesis-free): partition `Fin n` into walls `W`, R-events (`ds1Of = 0`), N-events
(`ds0Of = 0`), and `Rest`.  The wall-skipping partner map

  `pairNext i = if cyclicNext i is a wall then cyclicNext (cyclicNext i) else cyclicNext i`

is a **bijection `R → N`** (`hpairMemN` / `hpairInj` / `hpairSurj` / `hNimg`), and each
pair has locally-constant parity — standard vertex event
(`rpair_count_eventually_const_noWall`) or the degenerate-wall skip pair
(`rpair_count_eventually_const_degenWall`).  Walls contribute `0`, `Rest` is count-constant.
Glued on the preconnected `Icc 0 1` and chained through one antiparallel-avoiding
intermediate `μ = mkPt 1 s` (exactly the triangle's avoid-zero chain, already general `n`),
this gives `closedRegion'_chain_general` and `unconditionalRayIndepInput_general`.

## Verification (uisai1, playbook §3)

* `lake env lean ProofsInTheBook/PolygonGeneralWall.lean` → **RC=0**, no errors, no warnings.
* `lake env lean ProofsInTheBook/PolygonCutGeometry.lean` → **RC=0**.
* `lake env lean ProofsInTheBook/PolygonLast.lean` → **RC=0**.
* `lake build ProofsInTheBook.PolygonCutGeometry ProofsInTheBook.PolygonLast`
  (which rebuilds the whole downstream graph incl. `PolygonGeneralWall`) →
  **"Build completed successfully (8448 jobs)"**, RC=0.  **PolygonLast still builds clean
  after the edit** (confirmed: it is rebuilt as part of the 8448-job build).
* **Mechanical (A):** 0 `sorry` / `admit` / `native_decide` / `axiom` in the three files
  (grep matches are only docstring prose and the "No sorry/axiom/admit" header lines).
* **`#print axioms` (clean-3, all):**
  `PolygonGeneralWall.rpair_count_eventually_const_degenWall`,
  `.rcrossSum_parity_eventually_const_general`, `.closedRegion'_chain_general`,
  `.unconditionalRayIndepInput_general`;
  `PolygonCutGeometry.regionSplitGenericity_holds`, `.rayIndep_unconditional`,
  `.artGallery_strict_of_geometryInput`;
  `PolygonLast.rightArc_vertex_fresh_for_left`, `.vertices_remap_subset_image`;
  `PolygonDegenerateWall.artGallery_strict_unconditional` (the FULLY UNCONDITIONAL `n = 3`
  ⌊n/3⌋ art-gallery headline) — **all `[propext, Classical.choice, Quot.sound]`**.  No
  `sorryAx`, no `ofReduceBool`, no `native_decide`.

## Faithfulness verdict (playbook Group C)

* `unconditionalRayIndepInput_general` : **FAITHFUL**, unconditional, non-vacuous.  It is
  exactly `PolygonFinish.UnconditionalRayIndepInput P` for every `P` (the region/off-boundary
  form the region-split consumes), with hypotheses only the raw objects `ρ σ : RayDirection P`
  and `¬ OnBoundary P x`.  No genericity / no `n = 3`.  The degenerate-wall pairing was
  *derived*, not assumed.
* `RegionSplitGenericity` : the previous definition `∀ P, GenericChainInput P` was
  **provably false** for general `n` (`PolygonGenericRay.genericChainAt_false_of_straddle_on_line`:
  on the on-edge-line straddle stratum a single-intermediate generic chain cannot exist).
  It is now **redefined to its genuine content** `∀ P, UnconditionalRayIndepInput P` — the
  thing the region-split actually consumes (`rayIndep_of_genericity`) — and **proved**.  No
  vacuous conditional, no too-strong predicate: the new definition is strictly weaker than
  (implied by) the old false one, and is now a closed theorem.
* `rightArc_vertex_fresh_for_left` : **FAITHFUL** discharge of the index half of `M` — every
  vertex of the remapped right triangulation that also lies in the remapped left vertex set
  is `i` or `j` (a right-arc-interior apex is fresh for the left arc).  Derived from the
  proved `leftRight_image_inter`.

## The precise residue (ONE field, non-vacuous, concrete failing chain)

**`M = DiagonalAttachInput`'s peel-order half** — *the innermost `.single` triangle of the
canonical right combinatorial glue must carry the diagonal edge `{i, j}`*.

* **Index half: DISCHARGED.**  `AttachesTo` peels the right glue's layers, each needing only
  apex `∉ AV`; every right-glue vertex lies in the `rightIndex i j` image and every
  `AV`-vertex in the `leftIndex i j` image, so by `leftRight_image_inter` the only common
  values are `i, j` — every apex obligation reduces to "apex ≠ i ∧ apex ≠ j", i.e.
  right-arc-interior, which `rightArc_vertex_fresh_for_left` supplies.
* **Peel-order half: the residue.**  Tracing `combinatorialGlue_of_attach` on the right
  subpolygon: the `base` case (`n = 3`) gives a single triangle that *does* contain both arc
  endpoints — fine.  But the `splitDiagonal` case builds `mergedGlue …`, whose innermost
  `.single` is the innermost of `mergeOnto`'s **first** argument `tAL` = the right
  subpolygon's *own left child*'s triangulation base — a triangle deep in the recursion that
  need **not** contain the original arc endpoints `rightIndex 0 = j`, `rightIndex (last) = i`.
  **Concrete failing chain:** for the first split with a non-triangle right child (`n ≥ 5`),
  `gR.triang`'s innermost `.single T₀` carries the right child's *inner* diagonal, not the
  parent diagonal `{i, j}`, so the `AttachesTo .single` shared-edge clause (a `{i,j}` edge
  shared with the left set) is not derivable.  Discharging it requires **re-rooting** the
  triangulation's dual tree at the triangle carrying the chosen boundary edge — a
  triangulation peel-reordering theorem over the `TriangulatedPolygon` inductive that re-proves
  the `AttachesTo` / `mergeOnto` invariants under the new peel order.  This is a substantial
  standalone development (the `EarTriangulation'` recursion order is fixed by the cut oracle,
  not by the chosen diagonal), confirmed resistant by `PolygonResidualData`, `PolygonOracleClose`,
  `PolygonSeparation`, `opus-containment-reply`, and `opus-cutgeometry-reply`.  Editing
  `combinatorialGlue_of_attach` to discharge it without that theorem would break the
  downstream build; I left it intact and isolated the residue cleanly.

## Honest bottom line

The **central mathematical content the target asked for — the general-`n` degenerate-wall
parity transport (generalising the `n = 3` two-adjacent-edges pairing) — is fully proved,
unconditional, clean-3**, and wired in: `RegionSplitGenericity` is now a true, proved
theorem (the previous round's claimed residue `∀ P, GenericChainInput P` was provably false;
its genuine content `∀ P, UnconditionalRayIndepInput P` is closed for all `n`).  The triangle
`artGallery_strict` headline remains fully unconditional and clean-3; the general-`n`
cut-geometry headline `artGallery_strict_of_geometryInput` is conditional on exactly the
planar bundle `PolygonGeometryInput` + the `M` peel-order — with the ray-genericity
sub-residue *inside* the bundle now eliminated (proved).  The single remaining residue is
`M`'s **peel-order half** (index-freshness half discharged), a triangulation dual-tree
re-rooting that is outside a bounded session and was independently judged resistant by all
prior analyses.
