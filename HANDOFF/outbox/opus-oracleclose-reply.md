# opus-oracleclose reply — closing Chapter 36's oracle residuals

**Status: COMPLETE as a residual-reduction (clean-3, 0 sorry/axiom/admit).**
**File:** `ProofsInTheBook/PolygonOracleClose.lean` (456 lines, NEW, the only file I own).
**Build dep:** `ProofsInTheBook.PolygonOracle` (whole Ch36 stack). Verified on `uisai1`:
`lake build ProofsInTheBook.PolygonOracleClose` → *Build completed successfully (8435 jobs)*.

This builds *on top of* `PolygonOracle` (which already DERIVED the count/parity split at the
common ray). It closes / sharply isolates the three named residuals — CommonRay,
BaseTriangleFacts, OffDiagDisjoint + boundary bookkeeping — working from the EXACT consumer
fields, and assembles the sharpest Chapter-36 headline.

## What is PROVED (unconditional, clean-3: {propext, Classical.choice, Quot.sound})

### Part A — `CommonRay` satisfiability (the §3.3 anti-vacuity obligation)
The `CommonRay` premise consumed by `countSummationDatum_of_commonRay` is a *named condition
consumed as input*; `#print axioms` cannot see whether it is satisfiable. We exhibit the
witness:
- **`commonRayDir_valid_for₃`** — for parent `P` and both sub-polygons `L,R`, a single slope
  `t*` outside the (finite) union `edgeSlopes P ∪ edgeSlopes L ∪ edgeSlopes R` yields one
  `mkPt 1 t*` that is simultaneously a genuine `RayDirection` for all three, with
  `ρL.r = ρP.r ∧ ρR.r = ρP.r` — exactly the `CommonRay` equation. So `CommonRay` is a real
  selectable equation, **not** a vacuous/false premise. (`commonDir_exists`,
  `commonRayDir_valid_for`, `commonSlope_exists` are the supporting atoms.) ℝ is never
  exhausted by finitely many bad slopes; the "parent direction parallel to the diagonal"
  obstruction is sidestepped because `t*` is chosen fresh for the *union*.

### Part B — `BaseTriangleFacts` (the n=3 leaf) reduced to the planar primitive
For a 3-gon the three vertices `v0,v1,v2` are the consecutive triple at the middle vertex `⟨1⟩`
(`cyclicPrev ⟨1⟩ = ⟨0⟩`, `cyclicNext ⟨1⟩ = ⟨2⟩`). Hence:
- **`base_hull_eq_adjacentTri`** — base hull `= closedTri(prev⟨1⟩, ⟨1⟩, next⟨1⟩)`.
- **`base_subset_iff_convexVertex_one`** — the `subset` half of the leaf IS *definitionally*
  `IsConvexVertex' Q σ ⟨1⟩`, the development's **single planar primitive** (the same Jordan
  content assumed as a residual field of *every* `CutGeometry`). So the n=3 `subset` residual is
  pinned exactly onto that primitive — no count/parity content remains in it.
- **`BaseTriangleLeaf`** (`structure : Prop`) — bundles the two genuine, cast-free Jordan facts
  for a 3-gon (hull ⊆ region; region ⊆ hull). **`baseTriangleFacts_of_leaf`** builds a genuine
  `BaseTriangleFacts` from it (the two fields ARE the two conjuncts).
- **`base_tri_nondegenerate`** (re-export) — the base triple is genuinely noncollinear, so the
  leaf datum is over a real triangle, not a degenerate impostor.

### Part C — boundary bookkeeping: off-boundary union → full `split_region_union` set equality
- **`region_symmDiff_pieces`** / **`region_union_offBoundary_pieces`** — the symmetric-difference
  split and (with disjointness) the union, OFF all boundaries, stated at the **raw-fields level**
  (no `CutGeometry` parameter) directly from `crossingNumber'_split_identity_common` +
  `parity_xor_of_count_sum`. This is what breaks the construction circularity below.
- **`BoundaryUnionData`** (`def : Prop`) — the named residual for the *boundary* points (the only
  geometric residue of the union field beyond the count/parity half).
- **`region_union_everywhere`** / **`splitUnion_of_residuals`** — the full set equality
  `{region_P} = {region_L} ∪ {region_R}` (the exact shape `CutGeometry.split_region_union`
  consumes) derived from `CommonRay + OffDiagDisjoint + BoundaryUnionData`.

### Part D — the assembled headline + faithfulness certificate
- **`ResidualGeometryData`** (`structure`) — the per-polygon planar primitives a `CutGeometry`
  needs *except* the union field: convex extreme vertex (`IsConvexVertex'`), transversality,
  sub-polygon strictness axioms, the *common* sub-rays, half-plane disjointness, the boundary
  datum, the intersection-equals-diagonal datum. **No count/parity content.**
- **`cutGeometry_of_data`** — builds a genuine `CutGeometry` from it, with `split_region_union`
  **DERIVED** (via `region_union_offBoundary_pieces` glued with the boundary datum), not assumed.
- **`residualGeometryData_of_cutGeometry`** — the **§3.3 anti-vacuity / faithfulness certificate**:
  a genuine `CutGeometry` with common rays + disjointness *yields* a `ResidualGeometryData` (the
  `boundary` field is a true consequence of the real `split_region_union`). So
  `ResidualGeometryData` is a **faithful decomposition**, not a strengthening — satisfiable exactly
  when the underlying geometry oracle is.
- **`cutGeometryOracle_of_data`**, **`chapter36_residual_headline`** — the Chapter-36 art-gallery
  `⌊n/3⌋` conclusion (`∃ guards, guards.card ≤ n/3 ∧ ∀ x ∈ region, ∃ v ∈ guards, Sees …`),
  identical strength to `PolygonLast.artGallery_strict_attach`, now over the reduced residual
  surface (union field's count/parity half derived).

## Honest scope — exactly what remains (NOT faked)

The Chapter-36 headline's residual surface is now precisely the irreducibly-planar **Jordan**
data, with the **count/parity half mechanically closed**:

1. **`BaseTriangleLeaf`** — the single n=3 Jordan leaf (hull = region for a triangle). Its
   `subset` half is exactly the development's `IsConvexVertex'` primitive (Part B); its `cover`
   half is the exterior-evenness Jordan fact. This is the one genuinely-resistant geometric leaf,
   honestly isolated (it was already a residual in every prior file; I pinned it onto the
   existing primitive rather than re-deriving Jordan content from scratch).
2. **`ResidualGeometryData` fields** — `IsConvexVertex'` (convex extreme vertex),
   transversality, sub-polygon strictness axioms, `OffDiagDisjoint` (half-plane disjointness —
   irreducibly geometric, the count identity provably gives symmDiff not union), the
   `BoundaryUnionData` boundary datum, and intersection-equals-diagonal. All are pure planar
   primitives; **none carries count/parity content** (that half is discharged in `PolygonOracle`
   + Parts A/C here). Certified faithful/non-vacuous by `residualGeometryData_of_cutGeometry`.
3. **`DiagonalAttachInput`** — peel-ordering (from `PolygonLast`, satisfiability already certified
   there). Unchanged.

`OffDiagDisjoint` could NOT be eliminated: a both-region off-boundary point has even `count_P`
(consistent with the symmDiff), but pure parity gives no contradiction — the diagonal's
two-sidedness / half-plane separation is genuinely needed. This matches the prior assessment.

## Faithfulness self-audit (§3.3)

- All headline + key theorems `#print axioms` clean-3 (verified: `chapter36_residual_headline`,
  `cutGeometry_of_data`, `cutGeometryOracle_of_data`, `baseTriangleFacts_of_leaf`,
  `commonRayDir_valid_for₃`, `region_union_offBoundary_pieces`, `region_symmDiff_pieces`,
  `region_union_everywhere`, `splitUnion_of_residuals`, `residualGeometryData_of_cutGeometry`,
  `base_subset_iff_convexVertex_one`). No `sorryAx`, no `ofReduceBool`/`trustCompiler`.
- **Anti-vacuity**: `CommonRay` shown satisfiable (`commonRayDir_valid_for₃`);
  `ResidualGeometryData` shown a faithful decomposition of a genuine oracle
  (`residualGeometryData_of_cutGeometry`), so not a vacuous/too-strong premise; `BaseTriangleLeaf`
  is the true Jordan fact (satisfiable in principle), and its `subset` half is *proved equal* to
  the existing `IsConvexVertex'` primitive.
- **Statement fidelity**: `chapter36_residual_headline`'s conclusion is the verbatim `⌊n/3⌋`
  art-gallery statement of `PolygonLast.artGallery_strict_attach` (re-exported, no weakening). The
  `BaseTriangleLeaf`/`BoundaryUnionData`/`OffDiagDisjoint` residuals are *named conditions
  consumed as inputs* (like the existing oracle fields), not `def : Prop` substitutes for
  unproven *target* theorems — the substantive results (Parts A,B,C reductions) are real
  `theorem`/`def`s with full proofs.
- **No trivially-true**: no `:= rfl`/`:= trivial`/placeholder headline; the reductions do genuine
  work (count identity, parity XOR, hull/primitive identification, union assembly).

## Verification

```
rsync -az ProofsInTheBook/PolygonOracleClose.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH && \
  lake env lean ProofsInTheBook/PolygonOracleClose.lean'    # exit 0, no errors (linter warns only)
ssh uisai1 'lake build ProofsInTheBook.PolygonOracleClose'  # Build completed successfully (8435 jobs)
# #print axioms <each headline>  →  [propext, Classical.choice, Quot.sound]
```

No `sorry`/`axiom`/`admit`/`native_decide` in the file. No commits; stayed on `main`; touched
only the new `PolygonOracleClose.lean`; no codex/OpenAI tooling; never ran `lake build`/
`lake env lean` on the Mac (verified exclusively on `uisai1`).
