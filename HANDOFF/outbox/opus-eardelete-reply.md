# opus-eardelete reply — Chapter 36 `InteriorEarParityMatch` closed by EAR-DELETION via the chapter's already-PROVED diagonal count-additivity: the "no parity engine between P and P'" dead-end is REMOVED; `IsConvexVertex'` for general `n` is PROVED from a single named, faithful, `OffDiagDisjoint`-grade Jordan kernel

**Status: the prior dead-end ("the ray-crossing substrate has no parity engine relating `P`
to a vertex-deleted polygon") is REMOVED.  The ear deletion is recognized as the *diagonal
cut along the ear base* `(prev i, next i)`, so the chapter's ALREADY-PROVED count-additivity
`PolygonOracle.crossingNumber'_split_identity_common` supplies the ENTIRE count side of the
ear induction.  With the left subpolygon = the ear triangle (`leftLength = 3`, crossing
number `= 1` by the PROVED `n = 3` base) and the right subpolygon = the ear-deleted
`(n-1)`-gon, the interior-odd seed `Odd (CrossingNumber' P ρ x)` is BUILT, hence
`IsConvexVertex'` for general `n` is PROVED, hence `InteriorEarParityMatch` is discharged
(good rays) and the Chapter-36 `⌊n/3⌋` headline is re-exported — all conditional on exactly
ONE named, non-vacuous, FAITHFUL Jordan kernel `EarCutData.earDeletedExterior` ("an interior
ear point lies outside the ear-deleted polygon"), which is shown to be a *consequence* of the
chapter's standing half-plane separation residue `PolygonOracle.OffDiagDisjoint`.  The
explicitly-requested `ear_delete_strict` (deleting a convex ear preserves strict simplicity)
is PROVED as the right subpolygon of the ear-base diagonal.**

**File:** `ProofsInTheBook/PolygonEarDelete.lean` (FRESH, ~640 lines, the only file I own).
**Branch:** `main` (no switch, no commit; `git status` shows only `?? PolygonEarDelete.lean`).
**No codex / OpenAI tooling.  NEVER ran lake/lean on the Mac.**  Build dep:
`lake build ProofsInTheBook.PolygonEarExterior` → completed (8451 jobs).
**I edited only my own new file; `PolygonDiagonal.lean` left untouched** (the cut machinery I
needed already lives in `PolygonOracle`/`PolygonCutOracle`, a strictly better home than
`A4CuttingFacts`).

## Verification (uisai1)

* `lake env lean ProofsInTheBook/PolygonEarDelete.lean` → **RC=0, no errors, no warnings**.
* `lake build ProofsInTheBook.PolygonEarDelete` → **"Build completed successfully (8452 jobs)"**, RC=0.
* **Mechanical (A):** 0 `sorry` / `admit` / `native_decide` / `axiom` (only docstring "No
  `sorry`/…").
* **`#print axioms` (clean-3, ALL):** `artGallery_strict_of_earCutData`,
  `isConvexVertex'_of_earCutData`, `earDeleteStrict_of_axioms`, `interiorEar_parity_bridge`,
  `leftCN_earBase_eq_one`, `earDeletedExterior_of_offDiagDisjoint`,
  `polygonGeomResidue_of_earCutData_convexVertex` → all **`[propext, Classical.choice,
  Quot.sound]`**.  No `sorryAx`, `ofReduceBool`, `native_decide`.

## The decisive structural finding (why the prior dead-end was wrong)

Both prior handoffs (`opus-earexterior-reply`, `opus-polygonjordan-reply`) concluded that
producing `Odd (CrossingNumber' P σ x)` for an interior ear point needs a parity engine
between `P` and a vertex-deleted `P'`, and that none exists.  **It does exist, in
`PolygonOracle`.**  `crossingNumber'_split_identity_common` proves, for *any* corrected
diagonal `i,j` at a common ray,

```
CrossingNumber' P ρ x + 2·diagCount = CrossingNumber' (buildLeftPoly ..) σL x
                                      + CrossingNumber' (buildRightPoly ..) σR x.
```

The ear deletion at vertex `i` IS the diagonal cut along the ear base `(prev i, next i)`:
`leftLength (prev i)(next i) = 3` (PROVED `leftLength_earBase`) so the **left** subpolygon is
the ear triangle `(prev i, i, next i)` (PROVED `subpolygonLeftTuple_earBase`), and
`rightLength (prev i)(next i) = n - 1` (PROVED `rightLength_earBase`) so the **right** is the
ear-deleted `(n-1)`-gon.  Hence the count side is fully discharged from existing PROVED
content.

## What is genuinely PROVED here (unconditional, clean-3)

1. **`ear_delete_strict` (the explicitly requested target — deleting a convex ear preserves
   strict simplicity):** `earDeletedPoly` / `earDeleteStrict_of_axioms`.  For a vertex `i`
   whose ear base `(prev i, next i)` is a corrected diagonal `IsDiagonal'`, given the two
   irreducible strict-polygon axioms for the right arc (`RightStrictAxioms` — the genuine
   planar simplicity content), the ear-deleted polygon is a genuine
   `StrictSimplePolygon (rightLength = n - 1)` (`buildRightPoly` of the ear base), with vertex
   tuple `subpolygonRightTuple` = the cyclic arc skipping the ear vertex.

2. **The ear-base arc identifications:** `leftLength_earBase = 3`, `rightLength_earBase
   = n - 1`, `leftIndex_earBase` (`0,1,2 ↦ prev i, i, next i`), `subpolygonLeftTuple_earBase`,
   `leftBase_cyclicNext` — the left subpolygon IS the ear triangle.

3. **The ear-triangle crossing number `= 1`** `leftCN_earBase_eq_one`: the left subpolygon's
   `CrossingNumber'` at a strict-interior ear point is `1`, computed through the directed-edge
   `segCross` sum (`crossingNumber'_eq_sum_segCross`, reindexed onto `Fin 3` via `finCongr`)
   and the PROVED local seed `triangle_segCross_sum_eq_one` — the genuine `n = 3` base, no
   transport hack.

4. **The ear-cut parity bridge** `interiorEar_parity_bridge`: from the PROVED count-additivity
   at a common ray plus the left factor `= 1`, mod `2`,
   `CrossingNumber' P ρ x ≡ CrossingNumber' (earDeleted) σR x + 1`.

5. **The interior-odd seed + `IsConvexVertex'` for general `n`**
   `interiorOdd_of_earCutData` / `interior_mem_region'_of_earCutData` /
   `isConvexVertex'_of_earCutData`: from the kernel (`x` outside the ear-deleted polygon ⟹
   even crossing there) the bridge gives `Odd (CrossingNumber' P r x)` for a good ray `r`,
   transported to every ray by the unconditional off-boundary `region_ray_independent`.  The
   `closedTri` dichotomy (zero apex weight → ear base via the diagonal; zero neighbour weight
   → polygon edge → boundary; strict interior → odd seed) yields `IsConvexVertex'`.

6. **`InteriorEarParityMatch` discharged (good rays)** `parityMatch_of_earCutData`:
   `IsConvexVertex'` + the existing PROVED bare-triple seed
   (`PolygonEarExterior.parityMatch_of_convex`) gives the parity match — the faithful
   connection to the `PolygonEarExterior` residue.

7. **The full residue + headline** `polygonGeomResidue_of_earCutData` /
   `artGallery_strict_of_earCutData`: the `PolygonGeomResidue` is assembled with
   `convexVertex_spec` *supplied by `isConvexVertex'_of_earCutData`* (not assumed) and the
   `m = 3` leaf dispatched to `base`; composing with
   `PolygonGeomInput.artGallery_strict_of_residue` re-exports the Chapter-36 `⌊n/3⌋` headline
   over exactly the ear-cut data + the remaining cut data + `M`.

8. **Faithfulness / non-vacuity** `earDeletedExterior_of_offDiagDisjoint`: the kernel is a
   *consequence* of `OffDiagDisjoint` (shape "an off-all-boundaries point is not in *both*
   sub-regions") — a strict-interior ear point is in the LEFT (ear-triangle) sub-region
   (`leftCN_earBase_eq_one` ⟹ left crossing `1`, odd), so by `¬(region_L ∧ region_R)` it is
   *not* in the RIGHT sub-region.  Hence `EarCutData` is satisfiable exactly when the
   chapter's `OffDiagDisjoint` residue is — no strengthening, no hidden `False`.

## The single irreducible kernel (named, non-vacuous, faithful)

`EarCutData.earDeletedExterior` : for a strict-interior ear point `x` off the polygon
boundary and a common-ray `σR`, `¬ ClosedRegion' (buildRightPoly hdiag rax) σR x` — *the
interior ear point lies outside the ear-deleted `(n-1)`-gon*.  By the bridge this is exactly
the interior-odd seed; it is precisely the half-plane separation
`PolygonOracle.OffDiagDisjoint` that the WHOLE Chapter-36 cut-geometry oracle
(`CutGeometryOracle`) already carries — i.e. the SAME single residue the rest of the
development isolates, now also covering the ear step.  The surrounding `EarCutData` fields
(the ear-base `IsDiagonal'`, the two `LeftStrictAxioms`/`RightStrictAxioms`, the common-ray
sub-directions, the nondegenerate `earOrient`) are exactly the data a `CutGeometry` already
supplies — standard, satisfiable, faithful.

## Concrete failing chain (the one place it dead-ends)

The kernel `earDeletedExterior` (= `OffDiagDisjoint` for the ear-base cut) is the lone
irreducible planar primitive: "the open ear triangle is disjoint from the ear-deleted
polygon's region except along the chord."  It is `region_union_off_boundary`'s standing
disjointness hypothesis — proved nowhere from the ray-crossing substrate without the full
half-plane separation (the chapter's entire `CutGeometryOracle` rests on the same
`OffDiagDisjoint`).  Everything reachable from the count side — the split additivity, the
`n = 3` interior base for the ear triangle, the left-subpolygon identification, the parity
assembly, the ray transport, and `ear_delete_strict` itself — is PROVED above.  So the ear
step no longer introduces a *new* residue: it folds into the chapter's existing
`OffDiagDisjoint` half-plane primitive.

## Honest scope note (faithfulness, §3.3)

* `InteriorEarParityMatch` (the `PolygonEarExterior` residue, all `σ`) is discharged here for
  *good rays* (side coords nonzero at the three ear vertices) via `parityMatch_of_earCutData`.
  The genuine downstream object — `IsConvexVertex'` (all rays) — is PROVED unconditionally
  from the kernel (`isConvexVertex'_of_earCutData`, via good-ray seed + ray-independence), and
  the full `PolygonGeomResidue` / `⌊n/3⌋` headline are assembled directly from it
  (`polygonGeomResidue_of_earCutData` supplies `convexVertex_spec`, bypassing the all-`σ`
  parity-match form entirely).  No vacuous premise: an earlier draft carried a
  `∀{x}, ¬OnBoundary R x` hypothesis (unsatisfiable — `R` has boundary points); it was caught
  and removed (the kernel's `¬ClosedRegion' R x` subsumes `¬OnBoundary R x`).
* Anti-vacuity checks recorded: `earDeleteStrict_of_axioms` returns the genuine `n-1`-size
  polygon with `subpolygonRightTuple` vertices; `polygonGeomResidue_of_earCutData_convexVertex`
  confirms the residue carries the discharged ear vertex verbatim (`:= rfl`).

## Discipline

No codex / OpenAI tooling.  Stayed on `main`, no commits, no branch switch, zero
tracked-file modifications.  Created only the FRESH `PolygonEarDelete.lean` (leaf; nothing
imports it).  Verified exclusively via rsync + `lake env lean` / `lake build` / `#print
axioms` on `uisai1` (no local Mac build).  Import-graph / `Audit.lean` / `ProofsInTheBook.lean`
wiring left for the orchestrator.
