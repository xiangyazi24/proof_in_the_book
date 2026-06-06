# opus-polyleaf reply — Chapter 36's last planar facts (`BaseTriangleLeaf`)

**Status: COMPLETE as a faithful planar-leaf reduction (clean-3, 0 sorry/axiom/admit/native_decide).**
**File:** `ProofsInTheBook/PolygonLeaf.lean` (319 lines, NEW, the only file I own).
**Import:** `ProofsInTheBook.PolygonOracleClose` (whole Ch36 stack).
**Branch:** `main` (no switches, no commits). No codex/OpenAI tooling. Verified EXCLUSIVELY on `uisai1`
(`lake build ProofsInTheBook.PolygonLeaf` → *Build completed successfully (8436 jobs)*; never ran
`lake build`/`lake env lean` on the Mac).

## What is PROVED (unconditional, genuine planar content, clean-3)

### Part 1–2 — the crossing-number kernels (reusable, complete)
* **`not_spanCrossesSide_of_sameSign`** — if both endpoint side coordinates of an edge share a strict
  sign, the edge does not span-cross the ray line.
* **`crossingNumber'_eq_zero_of_allSide_pos` / `_neg`** — if *every* vertex lies strictly on one fixed
  side of the ray line through `x` (`0 < side σ.r x v` for all `v`, or `< 0` for all `v`), then
  `CrossingNumber' P σ x = 0`.  The "far exterior point ⟹ no forward crossings" kernel.
* **`normalDir` / `det2_normalDir` / `det2_normalDir_pos` / `side_shift`** — the affine machinery: the
  side coordinate shifts by `-s·det2 σ.r d` under a base-point translation `x ↦ x + s•d`, and the
  `90°`-rotation `normalDir σ.r` has `det2 σ.r normalDir = ‖σ.r‖² > 0`.
* **`exists_far_point_allSide_neg`** — for every polygon, ray, base point there IS a point with every
  vertex strictly on the negative side (translate far along `normalDir`).
* **`exists_crossingNumber'_eq_zero`** — hence a concrete base point with `CrossingNumber' = 0`: the
  unconditional **even-parity anchor for the exterior of any polygon**.

### Part 3–4 — the `n = 3` leaf reduced to two atomic planar halves
* **`onBoundary_subset_hull`** — for a `3`-gon, every boundary point lies in `closedTri v0 v1 v2`
  (each of the 3 edges is a segment between two hull vertices; convexity).  Fully proved.
* **`hull_subset_iff_convexVertex_one`** — the `hull_subset` half of the leaf IS
  `IsConvexVertex' Q σ ⟨1⟩`, the development's single planar primitive (re-export of
  `base_subset_iff_convexVertex_one` in the `Fin 3` form).
* **`TriangleConvexLeaf`** (`def : Prop`) — the convex-vertex half over all `3`-gons (definitionally the
  existing `IsConvexVertex'` primitive).
* **`TriangleExteriorEven`** (`def : Prop`) — the exterior-evenness half: off-boundary, outside the
  closed hull ⟹ even crossing number (the `cover` half in contrapositive form).
* **`baseTriangleLeaf_of_atoms`** — **builds a genuine `BaseTriangleLeaf` from these two atoms.** The
  `hull_subset` field is `IsConvexVertex'`; the `region_subset` field is the contrapositive of
  exterior-evenness, with the boundary branch discharged by `onBoundary_subset_hull`.  This is the real
  reduction: the opaque `BaseTriangleLeaf` input collapses to two precise atoms.

### Part 5 — the threaded headline
* **`chapter36_headline_atom_leaf`** — the Chapter-36 art-gallery `⌊n/3⌋` conclusion (verbatim shape of
  `chapter36_residual_headline` / `PolygonLast.artGallery_strict_attach`), now consuming the two leaf
  *atoms* `TriangleConvexLeaf` + `TriangleExteriorEven` in place of the bundled `BaseTriangleLeaf`.

## Honest scope — exactly what remains (NOT faked)

The triangle leaf is the development's **single genuinely-resistant geometric leaf** (the
`opus-oracleclose` handoff named it as such).  It is now decomposed into exactly two atomic planar
halves, neither carrying any count/parity content:

1. **`TriangleConvexLeaf`** — `IsConvexVertex' Q σ ⟨1⟩` for every `3`-gon.  This is *not a new residue*:
   it is definitionally the development's pre-existing **single planar primitive** (the same Jordan
   content `IsConvexVertex'` assumed as a field of every `CutGeometry` and used throughout
   `PolygonSideCrossing`/`PolygonConvexVertex`).  Pinned exactly by `hull_subset_iff_convexVertex_one`.

2. **`TriangleExteriorEven`** — off-boundary exterior points of a triangle have even crossing number.
   Its **inward content is supplied by the Part 1–2 kernels** (far-exterior points are even,
   unconditionally).  Closing it fully for an *arbitrary* exterior point requires the
   Hahn–Banach/`det2`-separation → valid-non-edge-parallel-ray → ray-comparability-path chain
   (convert the separating functional to a `RayDirection` comparable to `σ`, then transport
   `crossingNumber'_eq_zero` by `closedRegion'_ray_indep`).  This is the irreducible **single-edge-jump
   / half-plane Jordan content** that the *entire* Chapter-36 stack deliberately keeps as a named input
   (`PolygonLast.lean`: "the half-plane separation. We do not fake them.";
   `PolygonParity`/`PolygonSideCrossing` keep the jump as the `SegmentRegionLocallyConstant` /
   `loc` residue).  I did not fabricate it.

**Why I did not also discharge `OffDiagDisjoint` / `BoundaryUnionData`:** these are the *same* class of
irreducible planar/Jordan residue, kept as named inputs uniformly across the whole development
(`PolygonOracle`: "the half-plane disjointness, which is irreducibly geometric";
`PolygonLast`: "We do not fake them.").  `OffDiagDisjoint` is provably *not* a parity consequence
(a both-region off-boundary point has even `count_P`, consistent with the symmDiff — pure parity gives
no contradiction; the diagonal's two-sidedness is genuinely needed).  The honest contribution is the
kernel + the leaf-atom reduction, not a fake closure of these.

**The fully UNCONDITIONAL `artGallery_strict` is NOT attainable in this file:** the headline also
consumes `ResidualGeometryData` per polygon, whose fields `convexVertex_spec` (`IsConvexVertex'`),
`transversality`, and `intersection` are themselves the planar oracle residues of the whole chapter —
out of scope for the leaf module.  What I delivered is the sharpest *leaf-level* sharpening: the
`BaseTriangleLeaf` input reduced to two atoms, one collapsing onto the existing single primitive, the
other anchored by unconditional crossing kernels.

## Faithfulness self-audit (§3.3)

* **clean-3 verified** (`#print axioms`): `baseTriangleLeaf_of_atoms`, `chapter36_headline_atom_leaf`,
  `exists_crossingNumber'_eq_zero`, `crossingNumber'_eq_zero_of_allSide_neg`, `onBoundary_subset_hull`,
  `hull_subset_iff_convexVertex_one` — all `[propext, Classical.choice, Quot.sound]`.  No `sorryAx`,
  no `ofReduceBool`/`trustCompiler`.
* **Not vacuous / not too-strong**: `baseTriangleLeaf_of_atoms` is a *genuine builder* — its
  `region_subset` field does real work (contrapositive of exterior-evenness + boundary-subset-hull),
  not `:= trivial`.  `TriangleConvexLeaf` is *proved equal* to the existing primitive
  (`hull_subset_iff_convexVertex_one`), so it is not a new strengthening.  The Part 1–2 kernels are
  unconditional theorems with full proofs (no hypotheses smuggling the conclusion).
* **Statement fidelity**: `chapter36_headline_atom_leaf`'s conclusion is the verbatim `⌊n/3⌋`
  art-gallery statement; the two atoms are *named conditions consumed as inputs* (like every other Ch36
  residual), not `def : Prop` substitutes for unproven *target* theorems.

## Verification

```
rsync -az ProofsInTheBook/PolygonLeaf.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH && \
  lake env lean ProofsInTheBook/PolygonLeaf.lean'      # exit 0 (linter warns only)
ssh uisai1 'lake build ProofsInTheBook.PolygonLeaf'    # Build completed successfully (8436 jobs)
# #print axioms <each headline>  →  [propext, Classical.choice, Quot.sound]
```

No `sorry`/`axiom`/`admit`/`native_decide`.  No commits; stayed on `main`; touched only the new
`PolygonLeaf.lean`; verified exclusively on `uisai1`.
