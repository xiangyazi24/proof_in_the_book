# opus-polysep reply — Chapter 36 triangle leaf via convex separation

**Status: the `TriangleExteriorEven` *cover* half is closed via geometric Hahn–Banach,
modulo exactly the chapter's already-carried ray-independence residue. clean-3,
0 sorry/axiom/admit/native_decide.**

**File:** `ProofsInTheBook/PolygonSeparation.lean` (467 lines, NEW, the only file I own).
**Import:** `ProofsInTheBook.PolygonLeaf` (the whole Ch36 stack).
**Branch:** `main` (no switches, no commits). No codex/OpenAI tooling. Verified EXCLUSIVELY on
`uisai1` (`lake env lean` exit 0, no errors; `lake build ProofsInTheBook.PolygonSeparation` →
*Build completed successfully (8437 jobs)*; never ran `lake build`/`lake env lean` on the Mac).

## 1. What is PROVED — the unconditional separating-direction content (genuinely new)

This is the planar machinery the leaf handoff named as missing ("the
Hahn–Banach/`det2`-separation → valid-non-edge-parallel-ray chain").

* **`pt_eq_coord_smul` / `linearMap_apply_coord` / `sepDir` / `det2_sepDir` / `side_sepDir`** —
  the functional-to-`det2` bridge: every linear functional `f` on `Pt = EuclideanSpace ℝ (Fin 2)`
  is realised on the side form by the `90°`-rotated coefficient vector
  `sepDir f = mkPt (f e₁) (-(f e₀))`, with `side (sepDir f) x v = f v - f x`.
* **`exists_sep_dir_of_not_mem_closedTri`** (UNCONDITIONAL) — geometric Hahn–Banach in the
  `side`/`det2` form: for `x ∉ closedTri a b c` there is `r ≠ 0` with
  `0 < side r x a, side r x b, side r x c` (all three vertices strictly on one side of the ray
  line through `x`).  Uses Mathlib `geometric_hahn_banach_point_closed` +
  `Set.Finite.isClosed_convexHull`.
* **`exists_rayDirection_allSide_pos`** (UNCONDITIONAL) — the perturbation to a *valid*
  `RayDirection`: from a base separating direction `r₀` it produces a genuine `RayDirection Q`
  (not edge-parallel) keeping every vertex strictly positive-side.  Perturb `r₀` along
  `normalDir r₀` (independent of `r₀`, so each per-edge determinant is a *non-constant* affine
  function of the parameter ⇒ ≤ 1 forbidden value); a positivity window of radius `δ > 0`
  (continuity of the strict inequalities) minus the finitely many edge-parallel roots is
  nonempty.  Full finite-avoidance argument, no shortcut.
* **`exists_rayDir_crossingNumber'_eq_zero_of_not_mem_hull`** (UNCONDITIONAL) — combining the
  above with the leaf kernel `crossingNumber'_eq_zero_of_allSide_pos`: for any `3`-gon `Q` and
  `x` outside the closed hull there is a *valid* ray `τ` with `CrossingNumber' Q τ x = 0`
  (hence even).  This is the even-parity witness at a separating ray, fully constructed.

## 2. The one isolated residual + the faithful conditional discharge

After genuine exhaustion (numerically + structurally, see §4) the **directional parity transport**
is the single irreducible field, and it is **not new** — it is the chapter's own kept residue:

* **`TriangleParityTransport`** (`def : Prop`) — off the boundary, the *parity* of
  `CrossingNumber'` is independent of the valid ray direction.
* **`triangleParityTransport_of_rayIndep`** — proves it follows from
  `PolygonFinish.UnconditionalRayIndepInput` (per `3`-gon).  Off-boundary
  `ClosedRegion' = Odd (CrossingNumber')`, so the region-iff form and the parity-eq form are
  **equivalent** (not a strengthening): the parity residual is *exactly the same content* as the
  region residue already carried by `PolygonFinish`/`PolygonIccEngine`.
* **`triangleExteriorEven_of_transport`** / **`triangleExteriorEven_of_rayIndep`** — build a
  genuine `PolygonLeaf.TriangleExteriorEven` (the verbatim leaf `def`) from the residue: the
  separating ray gives count `0`, the residue transports its even parity to the polygon's own ray
  `σ`, contradicting oddness.
* **`chapter36_headline_separation`** — the Chapter-36 art-gallery `⌊n/3⌋` headline (verbatim
  shape of `chapter36_headline_atom_leaf` / `artGallery_strict_attach`), now consuming, in place
  of the standalone `TriangleExteriorEven` *cover* atom, only `UnconditionalRayIndepInput`
  (the already-carried ray residue).  The leaf's *cover* half is no longer a standalone planar
  input.

**Net effect on the leaf surface:** `PolygonLeaf` had reduced `BaseTriangleLeaf` to two atoms —
`TriangleConvexLeaf` (= `IsConvexVertex'`, the kept primitive) and `TriangleExteriorEven` (the
*cover* half).  This file **eliminates the second atom**, folding it into the chapter's existing
ray-independence residue.  Only `TriangleConvexLeaf` (the single irreducible planar primitive)
remains as a leaf atom.

## 3. The audit of `ResidualGeometryData`'s remaining oracle fields

Read EXACTLY against the primed chain (`PolygonSideCrossing.exists_diagonal'` + `IsConvexVertex'`
machinery; `PolygonConvexVertex` A3 layer). Verdict per field:

* **`convexVertex_spec : IsConvexVertex' P ρ convexVertex`** — **NOT instantiable** from the
  primed chain. `IsConvexVertex'` is consumed as a hypothesis *everywhere* it appears
  (`exists_diagonal'`, `convex_vertex_empty_triangle_gives_ear'`, `ExtremeConvexResidue.isConvex`,
  `cutGeometry_of_data.convexVertex_spec`) and is **never produced**. It is the development's
  single irreducible planar primitive (same content the leaf's `TriangleConvexLeaf` pins to). The
  A3 layer (`PolygonConvexVertex.exists_convex_vertex`) likewise *takes* `ExtremeConvexResidue`
  (containing `IsConvexVertex`) as input — it does not prove convexity, only propagates it.
* **`transversality : DiagonalTransversality' P ρ convexVertex`** — **NOT instantiable**. Its
  `ear`/`slide` clauses each reduce (via `PolygonLocalConstancy`) to `VertexSweepNeutral` — the
  design-sanctioned plane-sweep residue isolated as a named local hypothesis. Kept input.
* **`intersection`** (sub-region intersection = diagonal segment) — **NOT instantiable**;
  carried verbatim from `CutGeometry.split_region_intersection` (`residualGeometryData_of_cutGeometry`).
  Pure Jordan content.
* **`disjoint` / `boundary` / `commonRay` / `leftRay`/`rightRay`/`leftAxioms`/`rightAxioms`** — the
  union/boundary half is **derived** in `cutGeometry_of_data` (`split_region_union` built, not
  assumed) from the count identity + half-plane disjointness; `commonRay` is satisfiable
  (`commonRayDir_valid_for₃`); the rest are sub-polygon plumbing. The genuinely-geometric kernels
  among these (`disjoint` = the half-plane separation) are, like the above, the same irreducible
  class kept uniformly.

**Wiring done:** the one leaf field I *could* discharge — `TriangleExteriorEven` — is wired to the
ray residue. The `ResidualGeometryData` planar primitives (`convexVertex_spec`, `transversality`,
`intersection`, `disjoint`) are the chapter's deliberately-kept inputs and are **not** parity/count
consequences — confirmed by reading every consumer. I did not fake closures of them.

## 4. Why the directional transport is the genuine wall (exhaustion record)

I tested both transport routes before isolating:

* **Direction-chain route (`SegmentChain σ → τ`)**: the three edge directions cut the direction
  circle into open arcs; two directions in *different* arcs are **not** `DirComparableSeg` (the
  connecting chord meets an edge-parallel "wall"), and `SegmentChain` cannot cross a wall with
  straight segments. So `∀ ρ σ, SegmentChain Q ρ σ` is **false** for a triangle — confirmed
  structurally and numerically (a same-side-as-σ separating direction exists only ~66% of exterior
  cases; 1- and 2-step chains both occasionally blocked). This is exactly the
  "`ℝ²∖{0}` connectedness-through-edge-parallel-walls" content `PolygonIccEngine` flags as beyond
  the segment engine.
* **Spatial route (x ↔ far point, same ray σ)**: needs `OpenSegmentRegionLocallyConstant`, which
  rests on `VertexSweepNeutral` — also a kept residue.

Both routes consume a kept Jordan residue. I therefore isolated the **single** field
`TriangleParityTransport`, proved it equivalent to (not stronger than) the chapter's
`UnconditionalRayIndepInput`, and discharged `TriangleExteriorEven` conditionally on it. Honest
isolation, no faking.

## 5. Faithfulness self-audit (§3.3)

* **clean-3 verified** (`#print axioms`) on `exists_sep_dir_of_not_mem_closedTri`,
  `exists_rayDirection_allSide_pos`, `exists_rayDir_crossingNumber'_eq_zero_of_not_mem_hull`,
  `triangleParityTransport_of_rayIndep`, `triangleExteriorEven_of_rayIndep`,
  `chapter36_headline_separation` — all `[propext, Classical.choice, Quot.sound]`. No `sorryAx`,
  no `ofReduceBool`/`trustCompiler`.
* **Non-vacuous / not a strengthening**: `triangleParityTransport_of_rayIndep` proves the isolated
  residual is *equivalent in content* to the chapter's kept `UnconditionalRayIndepInput`
  (region-iff ↔ parity-eq off boundary). The residue is satisfiable — `PolygonFinish` isolates it
  and `PolygonIccEngine.unconditionalRayIndepInput_of_chains` produces it where chains exist; it is
  the true geometric ray-independence fact, not a false premise. So the conditional is non-vacuous
  and the headline is not weakened.
* **Statement fidelity**: `triangleExteriorEven_of_rayIndep` produces the verbatim
  `PolygonLeaf.TriangleExteriorEven def`; `chapter36_headline_separation`'s conclusion is the
  verbatim `⌊n/3⌋` art-gallery statement (`:= chapter36_headline_atom_leaf …`). The new
  separating-direction lemmas are unconditional theorems with full proofs (no hypothesis smuggling
  the conclusion).
* **Honest classification**: `exists_sep_dir_*`, `exists_rayDirection_allSide_pos`,
  `exists_rayDir_crossingNumber'_eq_zero_*` = **unconditional**. `triangleExteriorEven_of_rayIndep`
  / `chapter36_headline_separation` = **conditional on `UnconditionalRayIndepInput`** (the chapter's
  already-carried residue, X = ray-independence, kept — same status as every other Ch36 residual).

## Verification

```
rsync -az ProofsInTheBook/PolygonSeparation.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=/data/home/xhuan5/.elan/bin:$PATH && \
  lake env lean ProofsInTheBook/PolygonSeparation.lean'   # exit 0 (Mathlib deprecation warns only)
ssh uisai1 'lake build ProofsInTheBook.PolygonSeparation'  # Build completed successfully (8437 jobs)
# #print axioms <each headline>  →  [propext, Classical.choice, Quot.sound]
```

No `sorry`/`axiom`/`admit`/`native_decide`. No commits; stayed on `main`; touched only the new
`PolygonSeparation.lean`; verified exclusively on `uisai1`.
