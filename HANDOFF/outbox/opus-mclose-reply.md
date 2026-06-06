# opus-mclose reply — M's peel-order REDUCED to one isolated atomic residue; canonical diagonal-first glue PROVED; honest verdict on headline conditionality

**Status: M's peel-order half is now fully reduced to ONE isolated, non-vacuous atomic residue
(`LastToFirstAll`), with the entire reduction chain — including the actual canonical diagonal-first
merged glue — PROVED unconditionally and clean-3.**  Two honest findings change the framing the
brief assumed; both are documented below and in the file header.

## Critical premise check (the brief asked for this first)

The brief's hypothesis — *"with RegionSplitGenericity + unconditionalRayIndepInput_general now
PROVED, ... ONLY M blocks the headline"* — **does not hold as stated.**  I traced it to source:

* `regionSplitGenericity_holds` (general-`n` ray-independence) is PROVED and closes the
  *genericity* sub-residue **inside** the planar bundle's region identities.  `triangleConvexLeaf_holds`
  (the leaf convex-vertex) and the per-3-gon ray-independence `H` are likewise discharged.
* **But the headline still consumes the irreducible planar bundle `PolygonGeometryInput` /
  `ResidualGeometryData`** — the general-`n` convex-vertex (`IsConvexVertex'`), transversality
  (`DiagonalTransversality'`), cut strict-axioms (`Left/RightStrictAxioms`), and region-intersection
  Jordan data.  `PolygonResidualData.lean` records a source-level exhaustion verdict: **no producer
  from the substrate** (these are convex-position / Jordan-transversality facts, *not* ray-independence
  facts; closing `RegionSplitGenericity` does not touch them).  Every assembled headline
  (`artGallery_strict_via_cutGeometry`, `artGallery_strict_of_geometryInput`, `chapter36_headline_separation`,
  `artGallery_strict_one_input`) still takes **both** a planar bundle **and** `M` — there is no
  `M`-only theorem.

So the faithful current conditionality is: **headline ⇐ `PolygonGeometryInput` (planar Jordan bundle)
+ the peel-order**, and this round reduces the second to a single atomic combinatorial residue.

## Second finding: universal `M = DiagonalAttachInput` is *too strong to be a theorem* (§3.3)

`M` quantifies over **every** `CombinatorialGlue B gR`, whose `.triang` is an *arbitrary*
`TriangulatedPolygon n tset` (only required to cover realised triangles — may carry extra triangles
or a non-tree dual).  The `TriangulatedPolygon.glue` freshness field is a **global vertex-elimination
order** (each glued triangle introduces one vertex fresh against *all* earlier triangles).  Re-rooting
such a structure at an arbitrary triangle need **not** preserve that freshness (e.g. a fan), so the
universal `M` is **false on the pathological glues the universal admits**.  `attachesTo_nonvacuous`
only inhabits one instance; it does not make the universal a theorem.  The correct deliverable is
therefore a glue-**producing** construction over the real residue, not a proof of universal `M`.

## What was PROVED (new file `ProofsInTheBook/PolygonMClose.lean`, ~485 lines, clean-3)

The reduction chain, all clean-3:

```
LastToFirstAll  ──reroot──▶  re-root any triangulation at any of its triangles
                ──attachesTo_of_innermost──▶  the AttachesTo certificate (diagonal innermost)
                ──rerootedAttaches / canonicalMergedGlue──▶  the diagonal-first merged glue
```

* **`reroot_interior` (PROVED, unconditional)** — moving any *interior* target triangle to innermost
  by recursing on the inner block and re-gluing the outer ear (its shared-edge/freshness fields are
  `S'`-stated, hence set-invariant under the re-root, and transport verbatim).
* **`attachesTo_of_innermost` (PROVED, unconditional)** — from a triangulation whose innermost base
  `T₀` carries the shared edge `e` (here the remapped diagonal `{i,j}`) with interior apex, and the
  index-freshness "every vertex in `AV` is an endpoint of `e`", derives `AttachesTo A AV t`.  The
  glued-apex-∉-`AV` clause is closed by the vertex-elimination freshness (an apex `∈ e` would be a
  corner of the base `T₀`, contradicting freshness).
* **`diag_hAVe` (PROVED, unconditional)** — the index-freshness for the diagonal merge is exactly
  `PolygonLast.rightArc_vertex_fresh_for_left` (a vertex in both remapped arc images is `i` or `j`).
* **`reroot` (PROVED from `LastToFirstAll`)** — full re-rooting at any triangle: interior case by
  `reroot_interior`, outermost case by the atomic step.  (Axioms: `[propext, Quot.sound]` — even cleaner.)
* **`rerootedAttaches` (PROVED from `LastToFirstAll`)** — a re-rooted triangulation of the *same set*
  carrying the peel-order `AttachesTo` — exactly what a diagonal-first merge consumes.
* **`canonicalMergedGlue` (PROVED from `LastToFirstAll` + structural witnesses)** — the **actual
  canonical diagonal-first `CombinatorialGlue B (splitDiagonal …)`**, built by merging the *re-rooted*
  remapped right triangulation onto the left (`mergeOnto`), with the realiser field transferred
  through the index remaps (same triangle set as `remap gR.triang`, so realiser-closure is preserved).
  **No universal `M`.**
* **`lastToFirst_nonvacuous` (PROVED)** — §3.3 anti-vacuity: the atomic residue is inhabited (the
  two-triangle leaf re-roots), so the reduction is not vacuous.  The obstruction is a *depth*
  phenomenon (global freshness over `≥ 2` inner layers), not unsatisfiability.

## The precise residue (ONE named non-vacuous Prop, concrete failing chain)

**`LastToFirstAll n`** — for every glue layer `glue h T v …`, the *outermost* ear `T` can be made the
innermost `.single` of a triangulation of the *same* set (`LastToFirst`).  Concrete failing chain:
re-pegging the inner block `S'` as ears hanging off `T` forces each re-glued apex to additionally
avoid `T`'s three corners; two of those (`T`'s shared-edge endpoints) *are* corners of inner
triangles, so the `mergeOnto`/`AttachesTo` freshness clause (apex `∉ {T.a,T.b,T.c}`) is violated at
the glue-neighbour `T'`.  The bare `TriangulatedPolygon` inductive records no dual-tree adjacency to
re-peel `S'` from `T'` while restoring global vertex-elimination freshness.  Non-vacuous
(`lastToFirst_nonvacuous`).  Discharging it is a standalone dual-tree development; wiring
`canonicalMergedGlue` into the headline additionally needs the per-split structural witnesses
(`hT₀`/`heT₀`/`hdiagL`: the right glue carries the diagonal triangle, the left carries a triangle on
the diagonal — true for the canonical `EarTriangulation'` glue since the right child's closing edge
*is* the diagonal, but a separate structural induction).

I did **not** edit `PolygonLast.lean` (the universal-`M` recursion is left intact; replacing it
correctly requires the structural induction above, outside a faithfully-verifiable session bound).
The new construction lives entirely in `PolygonMClose.lean`.

## Verification (uisai1, playbook §3)

* `lake env lean ProofsInTheBook/PolygonMClose.lean` → **RC=0** (only `push_neg`-deprecation /
  unused-variable warnings).
* **FULL `lake build`** → **"Build completed successfully (8621 jobs)"**, **0 errors** — the new module
  integrates and nothing downstream breaks.
* **Mechanical (A):** 0 `sorry` / `admit` / `native_decide` / `axiom` in `PolygonMClose.lean` (the only
  `sorry` token is the docstring "No sorry/axiom/admit"; the one `:= rfl` is a genuine `toGeom.tris`
  definitional unfold, not a trivial impostor).
* **`#print axioms` (clean-3):** `canonicalMergedGlue`, `rerootedAttaches`, `attachesTo_of_innermost`,
  `lastToFirst_nonvacuous`, `diag_hAVe` → `[propext, Classical.choice, Quot.sound]`;
  `reroot`, `reroot_interior` → `[propext, Quot.sound]`.  No `sorryAx`/`ofReduceBool`/`native_decide`.
* The FULLY-UNCONDITIONAL `n=3` headline `PolygonDegenerateWall.artGallery_strict_unconditional`
  remains clean-3 (re-checked): `[propext, Classical.choice, Quot.sound]`.

## Honest bottom line

* **Peel-order half of `M`: reduced from "a triangulation dual-tree re-rooting" to ONE isolated,
  non-vacuous atomic step `LastToFirstAll`**, with the *entire* surrounding reduction — including the
  real canonical diagonal-first merged glue `canonicalMergedGlue` — proved clean-3.  This is genuine,
  reusable combinatorial content (re-rooting + the certificate derivation), not a re-wrapper.
* **Universal `M` is too strong** (false on pathological glues); the faithful route is the
  glue-producing `canonicalMergedGlue`, which the brief explicitly authorised ("build a SEPARATE
  canonical diagonal-first glue construction alongside").
* **The headline is NOT blocked by `M` alone**: the irreducible planar bundle `PolygonGeometryInput`
  (general-`n` convex-vertex / transversality / cut-axioms / region-intersection Jordan content)
  remains, per the standing `PolygonResidualData` exhaustion verdict.  `RegionSplitGenericity` closed
  the genericity sub-residue inside that bundle, not the convex-position fields.
* **Remaining to a fully-unconditional general-`n` headline:** (i) discharge `LastToFirstAll` (dual-tree
  re-root with freshness restoration); (ii) the per-split structural diagonal-triangle witnesses to
  wire `canonicalMergedGlue` into the recursion; (iii) the `PolygonGeometryInput` Jordan bundle.  Items
  (i)/(ii) are the peel-order; (iii) is the separate, larger Jordan/convex-position campaign.

**Branch:** `main`.  No commits.  No codex / OpenAI tooling.  Never ran lake/lean on the Mac.
Verified exclusively on `uisai1`.
