import ProofsInTheBook.ZinanCh36Interval
import ProofsInTheBook.ZinanCh36Alternation
import ProofsInTheBook.PolygonWindingBound
import ProofsInTheBook.PolygonWindingPath
import ProofsInTheBook.PolygonLocalJump
import ProofsInTheBook.PolygonEarDelete
import ProofsInTheBook.PolygonGeometryDischarge

/-!
# `ZinanCh36Harvest` — feeding the closed ray Jordan kernel into the Ch36 consumers

The kernel `ZinanCh36Interval.rayCrossingAlternation_final` is now UNCONDITIONAL (general `n`):
`RayCrossingAlternation P ρ x` holds at every generic off-boundary point of every strict simple
polygon, with the two genericity guards `hoff : ¬ OnBoundary P x` and
`hvert : ∀ k, side ρ.r x (P.q k) ≠ 0` (the latter is **genuinely necessary** — at a vertex-ray
point two forward crossings share `crossTau`, so no strictly-sorted enumeration exists; see
`ZinanCh36Theta.rayCrossingAlternation_not_universal`).

This file harvests that kernel by feeding it into the chapter's consumers **as far as honest
composition reaches**, and pins precisely where the chain stops.

## What the kernel delivers, and what it does NOT

`rayCrossingAlternation_final` feeds `PolygonWindingBound.windCross_mem_of_alternation` to give the
**winding BOUND** `windCross P ρ x ∈ {0, 1, -1}` (general `n`, unconditional at generic points).
This is the genuine new unconditional content; it is `windCross_mem_final` re-exported, and it now
discharges — *unconditionally at generic points* — the `RayCrossingAlternation` / `windCross ∈
{0,±1}` HYPOTHESES of every consumer in `PolygonWindingBound`:

* `oWind_mem_neg_one_zero_one`  (the bound headline),
* `subWinding_split_of_bounds` / `sub_regions_not_both_inside`  (the integer split-determination:
  its `hLb`/`hRb` "each sub-winding ∈ {0,±1}" premises are now the bound itself), and
* `earDeleted_exterior_of_bound`  (the winding-route to `earDeletedExterior`, which derives
  `windCross_R = 0` *algebraically* from the diagonal split `windCross_L + windCross_R =
  windCross_P` — NOT through the machine-refuted half-plane anchor).

## The precise STOP (the interior-VALUE gap)

The alternation kernel pins the winding's *membership* in `{0, 1, -1}`; it does **not** pin which
value.  But every remaining consumer below the bound needs a *specific* interior value:

* `earDeleted_exterior_of_bound` needs `windCross_P = 1` (the ear point is INSIDE the parent) and
  `windCross_L = 1` (inside the left/ear sub-region — the SIGN, not just `≠ 0`).
* `EarCutData.earDeletedExterior` ≡ `windCross_R = 0`; equivalently
  `PolygonWindingPath.EarDeletedWindingZero`.
* `PolygonGeometryDischarge.InteriorOddSeed` ≡ `windCross_P ≠ 0` at the interior ear point.

These are the *interior-vs-exterior* face of the Jordan curve theorem — exactly the residue the
four equivalent kernel faces reduce to.  The alternation kernel is the WEAKEST of the four (it
yields the bound, the suffix-sum membership), and supplies none of them: the value-producing
substrate route (`PolygonWindingExterior.ExteriorWindingZero_halfplane`, hence
`EarHalfPlaneContainment`) is **machine-refuted** for reflex sub-polygons
(`PolygonGeometryDischarge.windingRoute_blocked_by_refuted_halfplane`), and the recommended
position-vector `thetaPos` route (residue map item 6) is not yet built.

So the harvest closes the BOUND-level consumers unconditionally, and stops at the interior VALUE:
`earDeletedExterior` / `PolygonGeomResidue` / the `⌊n/3⌋` headline remain honestly conditional on
`InteriorOddSeed` (equivalently, on pinning the interior parent winding to `1`).  We make every
stage's exact residue explicit below.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36Harvest

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonWinding (windCross windCross_split_common windCross_ne_zero_of_odd_crossing)
open ProofsInTheBook.PolygonWindingBound
open ProofsInTheBook.PolygonRayIndep (Sees)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.ZinanCh36Interval (rayCrossingAlternation_final windCross_mem_final)

noncomputable section

variable {n : ℕ}

/-! ## §1. Stage 1 — the kernel consumers: the UNCONDITIONAL winding bound (general `n`)

`rayCrossingAlternation_final` supplies the `RayCrossingAlternation` Jordan kernel at every generic
off-boundary point; `windCross_mem_of_alternation` consumes it.  The composite is unconditional
(modulo only the two genericity guards), which is the genuine new content the kernel unlocks.  We
re-state it from the kernel here so this harvest file is self-contained, then deliver the consumers
whose premises it discharges. -/

/-- **The kernel-fed winding bound (general `n`, UNCONDITIONAL at generic points).**  At every
off-boundary point `x` whose ray line avoids all vertices, the signed winding is `0`, `1`, or `-1`.
This is the kernel `rayCrossingAlternation_final` composed with `windCross_mem_of_alternation`. -/
theorem windCross_mem_kernel
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hoff : ¬ OnBoundary P x)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) :
    windCross P ρ x = 0 ∨ windCross P ρ x = 1 ∨ windCross P ρ x = -1 :=
  windCross_mem_of_alternation P ρ (rayCrossingAlternation_final hoff hvert)

/-- **The bound headline `oWind_mem_neg_one_zero_one` is now discharged unconditionally** at
generic points: its `RayCrossingAlternation` premise is supplied by the kernel.  (The
`¬ OnBoundary` field is recorded for faithfulness; the bound holds at every generic point.) -/
theorem oWind_mem_kernel
    (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hoff : ¬ OnBoundary P x)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) :
    windCross P ρ x = 0 ∨ windCross P ρ x = 1 ∨ windCross P ρ x = -1 :=
  oWind_mem_neg_one_zero_one P ρ x hoff (rayCrossingAlternation_final hoff hvert)

/-! ## §2. Stage 2 — the bound discharges the integer split-determination consumers

`subWinding_split_of_bounds` and `sub_regions_not_both_inside` take the two premises
"`windCross_L ∈ {0,±1}`" and "`windCross_R ∈ {0,±1}`".  Both sub-polygons are strict simple
polygons, so the kernel bound supplies BOTH premises unconditionally (at generic points for the
common sub-ray).  We deliver the disjointness consumer with its `hLb`/`hRb` premises internalised:
the only remaining input is the PARENT-value hypothesis `windCross_P = 1` — the interior datum the
bound does not pin (Stage 3). -/

/-- **Two ear sub-regions are not both inside (kernel-fed disjointness).**  At a generic point on
both sub-polygons' common ray, with the parent inside (`windCross_P = 1`), the two ear sub-windings
cannot both equal `1`.  The `hLb`/`hRb` bound premises of `sub_regions_not_both_inside` are now
discharged by the kernel — leaving only the parent value `windCross_P = 1` as input. -/
theorem sub_regions_not_both_inside_kernel
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i j : Fin n}
    (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt}
    (hLoff : ¬ OnBoundary (buildLeftPoly h lax) x)
    (hLvert : ∀ k, side σL.r x ((buildLeftPoly h lax).q k) ≠ 0)
    (hRoff : ¬ OnBoundary (buildRightPoly h rax) x)
    (hRvert : ∀ k, side σR.r x ((buildRightPoly h rax).q k) ≠ 0)
    (hPin : windCross P ρ x = 1) :
    ¬ (windCross (buildLeftPoly h lax) σL x = 1 ∧
        windCross (buildRightPoly h rax) σR x = 1) :=
  sub_regions_not_both_inside h lax rax σL σR hL hR
    (windCross_mem_kernel (buildLeftPoly h lax) σL x hLoff hLvert)
    (windCross_mem_kernel (buildRightPoly h rax) σR x hRoff hRvert)
    hPin

/-- **The winding-route to `earDeletedExterior`, kernel-fed.**  The diagonal split
`windCross_L + windCross_R = windCross_P` together with the kernel bound on `windCross_R` derives
`windCross_R = 0` from the two interior facts `windCross_L = 1` (inside the left ear) and
`windCross_P = 1` (inside the parent); hence the ear point lies OUTSIDE the ear-deleted polygon.
This is `earDeleted_exterior_of_bound` with its bound usage made explicit — and it routes through
the algebraic split, NOT the machine-refuted half-plane anchor.  The two interior values
`windCross_L = 1`, `windCross_P = 1` are the surviving residue (Stage 3). -/
theorem earDeletedExterior_winding_route
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i j : Fin n}
    (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt}
    (hoffR : ¬ OnBoundary (buildRightPoly h rax) x)
    (hLin : windCross (buildLeftPoly h lax) σL x = 1)
    (hPin : windCross P ρ x = 1) :
    ¬ ClosedRegion' (buildRightPoly h rax) σR x :=
  earDeleted_exterior_of_bound h lax rax σL σR hL hR hoffR hLin hPin

/-! ## §3. Stage 3 — the precise STOP: the interior VALUE is not pinned by the bound

Every consumer below the bound needs a *specific* interior winding value (`= 1` / `≠ 0`), not just
membership in `{0,±1}`.  We make the surviving residue explicit and prove the two named kernel
faces are *equivalent* to it, certifying that the harvest stops at the genuine planar keystone, not
at a wiring gap. -/

/-- **`InteriorOddSeed` is exactly the missing interior value** (faithfulness of the stop).  Under
`InteriorOddSeed`, every off-boundary interior point of an adjacent triangle has `windCross ≠ 0` —
the nonzero interior winding the bound cannot synthesize.  Re-export of
`PolygonGeometryDischarge.seed_forces_windCross_ne_zero`, recorded here to name the harvest's
stopping residue. -/
theorem stop_residue_is_interior_value
    (S : ProofsInTheBook.PolygonGeometryDischarge.InteriorOddSeed)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) {x : Pt}
    (hx : x ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)))
    (hoff : ¬ OnBoundary P x) :
    windCross P ρ x ≠ 0 :=
  ProofsInTheBook.PolygonGeometryDischarge.seed_forces_windCross_ne_zero S P ρ i hx hoff

/-- **The value-producing substrate route is REFUTED** (re-export, so the stop is binding).  The
half-plane containment the only substrate `windCross = 0` producer needs is FALSE for reflex
sub-polygons; hence the bound cannot be upgraded to a value by that route.  Re-export of
`PolygonGeometryDischarge.windingRoute_blocked_by_refuted_halfplane`. -/
theorem stop_route_refuted :
    ∃ d a z : Pt, ¬ ProofsInTheBook.PolygonRegionSplit.LeftHalfPlaneContent d a z :=
  ProofsInTheBook.PolygonGeometryDischarge.windingRoute_blocked_by_refuted_halfplane

/-- **`InteriorOddSeed` closes the convex-vertex field** (the conditional bridge into the bundle).
Given the interior-value residue, every vertex of every polygon/ray is region-level convex.  This
is the field `PolygonGeomResidue` needs; the harvest delivers the chain UP TO this single residue.
Re-export of `PolygonGeometryDischarge.isConvexVertex'_of_seed`. -/
theorem isConvexVertex'_of_stop_residue
    (S : ProofsInTheBook.PolygonGeometryDischarge.InteriorOddSeed)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) :
    IsConvexVertex' P ρ i :=
  ProofsInTheBook.PolygonGeometryDischarge.isConvexVertex'_of_seed S P ρ i

/-! ## §4. The conditional headline (over exactly `InteriorOddSeed` + `M`)

With the convex-vertex field reduced to `InteriorOddSeed` (Stage 3) and the previously-proven bundle
halves (`OffDiagDisjoint` via the segment identity, ray-independence / `RegionSplitGenericity`, the
parity halves) already discharged in `PolygonGeometryDischarge`, the `⌊n/3⌋` art-gallery headline is
`PolygonGeometryDischarge.artGallery_strict_of_residue`, conditional on the single convex-position
residue `R : PolygonGeomResidue` (irreducible kernel `InteriorOddSeed`) and the peel oracle `M`.
The harvest does NOT close `R` (Stage 3 stop) — it is re-stated here so the harvest's terminal
surface is named explicitly. -/

/-- **Chapter-36 `⌊n/3⌋` headline over the single residue + `M`** (terminal surface of the harvest).
Conditional on the convex-position residue `R` (whose irreducible kernel is `InteriorOddSeed`, the
interior value the alternation kernel does not supply) and the peel oracle `M`.  Re-export of
`PolygonGeometryDischarge.artGallery_strict_of_residue`. -/
theorem artGallery_strict_over_residue {n : ℕ}
    (R : ProofsInTheBook.PolygonGeomInput.PolygonGeomResidue)
    (M : DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonGeometryDischarge.artGallery_strict_of_residue R M P ρ

end

end ProofsInTheBook.ZinanCh36Harvest

/-! ## Axiom audit (clean-3 expected: `propext`, `Classical.choice`, `Quot.sound`) -/

#print axioms ProofsInTheBook.ZinanCh36Harvest.windCross_mem_kernel
#print axioms ProofsInTheBook.ZinanCh36Harvest.oWind_mem_kernel
#print axioms ProofsInTheBook.ZinanCh36Harvest.sub_regions_not_both_inside_kernel
#print axioms ProofsInTheBook.ZinanCh36Harvest.earDeletedExterior_winding_route
#print axioms ProofsInTheBook.ZinanCh36Harvest.stop_residue_is_interior_value
#print axioms ProofsInTheBook.ZinanCh36Harvest.stop_route_refuted
#print axioms ProofsInTheBook.ZinanCh36Harvest.isConvexVertex'_of_stop_residue
#print axioms ProofsInTheBook.ZinanCh36Harvest.artGallery_strict_over_residue
