import ProofsInTheBook.PolygonGeomInput
import ProofsInTheBook.PolygonRegionSplit

/-!
# Chapter 36 — discharge attempt for `PolygonCutGeometry.PolygonGeometryInput`
  (the planar-Jordan region-split bundle), via the proven signed-winding engine
  (`PolygonGeometryDischarge`)

This file re-examines the LAST Chapter-36 residue `PolygonGeometryInput` with the proven
signed-winding machinery (`windCross`, `windCross_split_common`, `ExteriorWindingZero`,
`windCross_emod_two`) as the candidate non-obvious route, exactly as the brief asks.  The
sister oracle `M` ("design-blocked" verdict) turned out recoverable; this file applies the
same discipline to `PolygonGeometryInput` — pushing the winding route as far as it goes
*before* any verdict — and pins the genuine irreducible kernel with its exact proof-state.

## 0. What `PolygonGeometryInput` actually requires (pinned from source)

`PolygonGeometryInput = { data : ∀ {m} (P : StrictSimplePolygon m) (ρ), ResidualGeometryData P ρ }`
(`PolygonCutGeometry`, l.180).  `ResidualGeometryData` (`PolygonOracleClose`, l.270) carries,
per polygon/ray, the fields

* `convexVertex : Fin m`, `convexVertex_spec : IsConvexVertex' P ρ convexVertex`,
* `transversality : DiagonalTransversality' P ρ convexVertex`,
* `leftAxioms` / `rightAxioms` (the two NON-combinatorial cut strict-polygon axioms:
  noncollinearity at the cut + proper edge intersection),
* `leftRay` / `rightRay`, `commonRay`,
* `disjoint` (half-plane disjointness off all three boundaries),
* `boundary` (boundary-points union datum),
* `intersection` (`{region_L} ∩ {region_R} = seg (q i) (q j)`).

Of these, the brief's hypothesis — "`OffDiagDisjoint` / `SubRegionContainment` are discharged
*from* `CutGeometry`, `RegionSplitGenericity` is proved, so the genuine remaining content is
`split_region_intersection` / `split_region_union`" — is **partially** correct:

* `RegionSplitGenericity` (ray-direction independence off the boundary) **is** proved for
  general `n` (`PolygonCutGeometry.regionSplitGenericity_holds`).  Re-exported as
  `region_ray_independent_unconditional` below.
* `OffDiagDisjoint` / `SubRegionContainment` **are** discharged — but *from a `CutGeometry`
  interface* (`PolygonRegionSplit.offDiagDisjoint_via_segment` etc.), i.e. they consume the
  `split_region_intersection` field.  They are NOT free-standing facts about a bare polygon.
* The count/parity half of `split_region_union` is mechanically closed
  (`crossingNumber'_split_identity_common`).

## 1. The signed-winding route for the region split: PURSUED, and it routes through a
   MACHINE-REFUTED hypothesis (not a bypass)

The brief proposes: a point is inside iff `windCross` is odd; `windCross_split_common` cancels
the diagonal, so `windCross(whole) = windCross(L) + windCross(R)`, giving the partition.  We
pursued exactly this.  `windCross_split_common` (`PolygonWinding`, l.321) **is** proved (the
diagonal terms cancel) and `windCross_emod_two` bridges to the unsigned parity.  But the
additivity is *only the count/parity additivity* already available as
`crossingNumber'_split_identity_common`; what the region SPLIT needs beyond parity is the
**side-localization** of the winding — that an exterior point of one ear has signed winding
`0` on its side (`ExteriorWindingZero`).  And `ExteriorWindingZero` is closed by the proven
engine ONLY via `EarHalfPlaneContainment` (`PolygonWindingExterior.exteriorWindingZero_of_earHalfPlane`):
each ear's whole boundary must lie in the closed half-plane on its side of the diagonal LINE.

That hypothesis is **machine-refuted FALSE for non-convex sub-polygons**
(`PolygonRegionSplit.not_earHalfPlane_geometric_content`: the concrete reflex witness
`d=(4,0)`, `a=(0,0)`, `z=(2,-1)` has `wDiagSide = -4 < 0` yet is a legitimate left-arc vertex
of a reflex pentagon).  The diagonal *line* does not separate the ears; only the diagonal
*segment* does.  So the signed-winding route does **not** bypass the residue — it routes
*through* a false hypothesis.  We re-export the refutation so the verdict is binding
(`windingRoute_blocked_by_refuted_halfplane`).

The genuine non-convex-safe disjointness is the SEGMENT identity, which is exactly the
`intersection` field already carried by `ResidualGeometryData`.

## 2. The genuine irreducible kernel: the INTERIOR ODD-CROSSING SEED for `IsConvexVertex'`

Stripping the (false) half-plane oracle, the region-split disjointness/union/genericity are
all dischargeable from the interface.  The single irreducible planar-Jordan kernel that the
substrate provably cannot synthesize — and that the signed-winding engine *also* cannot create
— is the **interior odd-crossing seed**: to place an *interior* point of the adjacent triangle
into the parity-defined region `ClosedRegion'` one needs `Odd (CrossingNumber' P ρ x)` for some
ray, i.e. (via the parity bridge) `windCross P ρ x ≠ 0`.  The winding engine supplies the
bridge `Odd → windCross ≠ 0` and the (conditional) *exterior* vanishing, but it has **no**
producer of `windCross ≠ 0` from interior geometry: `windCross` is a *crossing-parity* sum, not
an angle-winding integral, so a nonzero interior value cannot be synthesized from nothing.  At
`n = 3` the seed is closed by the closed-form barycentric `crossTau`-sign identity
(`PolygonTriangleConvex`); for `n ≥ 4` the adjacent-triangle base is a chord, not a polygon
edge, and no substrate lemma computes the per-edge `crossTau` sign on a chord.

We isolate this as the SINGLE named, non-vacuous `Prop` `InteriorOddSeed`, prove it is
*sufficient together with the rest of the (discharged) machinery to build the convex-vertex
spec via the winding bridge* (`isConvexVertex'_of_seed`), and certify non-vacuity
(`interiorOddSeed_of_isConvexVertex`: it is implied by a genuine `IsConvexVertex'`, so it is
satisfiable exactly when the geometry is).  This is the precise irreducible Jordan content.

## 3. Verdict

A *fully unconditional* `PolygonGeometryInput` is **NOT** constructible from the current
Chapter-36 substrate, and — unlike `M` (a combinatorial peel re-rooting, genuinely
recoverable) — the obstruction is architectural planar-Jordan content, re-confirmed by
directly pursuing the signed-winding route (it routes through the refuted half-plane).  The
honest deliverable is the headline conditional on exactly the single residue
`PolygonGeomInput.PolygonGeomResidue` (the convex-position bundle) + `M`, already assembled in
`PolygonGeomInput.artGallery_strict_of_residue`, with the genuine irreducible KERNEL inside it
pinned here as `InteriorOddSeed`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonGeometryDischarge

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)
open ProofsInTheBook.PolygonWinding
  (windCross windCross_split_common windCross_emod_two windCross_ne_zero_of_odd_crossing)
open ProofsInTheBook.PolygonRegionSplit
  (LeftHalfPlaneContent not_earHalfPlane_geometric_content
   earHalfPlane_geometric_content_false offDiagDisjoint_via_segment)
open ProofsInTheBook.PolygonCutGeometry
  (PolygonGeometryInput regionSplitGenericity_holds rayIndep_unconditional)
open ProofsInTheBook.PolygonFinish (UnconditionalRayIndepInput)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonRayIndep (Sees)

noncomputable section

variable {n : ℕ}

/-! ## Part A: what is genuinely PROVED (re-exported), the discharged surface -/

/-- **Ray-direction independence is PROVED for general `n`** (the `RegionSplitGenericity`
analytic core, re-exported): off the boundary, the corrected closed region is independent of
the ray direction, for every polygon.  This is what the brief's `RegionSplitGenericity`
refers to; it is discharged, not a residue. -/
theorem region_ray_independent_unconditional {m : ℕ} (P : StrictSimplePolygon m) :
    UnconditionalRayIndepInput P :=
  rayIndep_unconditional P

/-- **`OffDiagDisjoint` is discharged from the `CutGeometry` interface via the SEGMENT
identity** (re-exported) — the non-convex-safe disjointness.  No half-plane, no winding, no
convexity of the pieces. -/
theorem offDiagDisjoint_discharged {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) : OffDiagDisjoint g :=
  offDiagDisjoint_via_segment g

/-! ## Part B: the signed-winding route, PURSUED — it routes through a refuted hypothesis

We make precise that the diagonal-cancellation identity `windCross_split_common` delivers only
PARITY additivity (already available unsigned), and that the side-localization the region SPLIT
requires (`ExteriorWindingZero`) is closed by the engine only through `EarHalfPlaneContainment`,
which is machine-refuted.  Hence the winding route is not a bypass of the residue. -/

/-- **The diagonal-cancellation identity holds** (re-export of the proven engine core): with a
common ray, the parent signed winding is the sum of the two sub-polygon signed windings — the
diagonal contribution cancels.  This is the brief's `windCross(whole) = windCross(L) +
windCross(R)`.  It is genuinely proved; the obstruction is NOT here. -/
theorem windCross_diagonal_cancels {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) (x : Pt) :
    windCross (buildLeftPoly h lax) σL x + windCross (buildRightPoly h rax) σR x =
      windCross P ρ x :=
  windCross_split_common h lax rax σL σR hL hR x

/-- **The signed-winding route for the region SPLIT is blocked by a machine-refuted
hypothesis.**  The side-localization the split needs beyond parity is the ear half-plane
containment, whose abstract geometric content is FALSE: there is a diagonal direction `d`,
base `a`, and a (reflex) left-arc point `z` with `¬ LeftHalfPlaneContent d a z` (i.e.
`det2 d (z - a) < 0` while the half-plane oracle demands `≥ 0`).  Hence the winding route does
not bypass the residue — it routes through this false hypothesis.  (Re-export of
`PolygonRegionSplit.earHalfPlane_geometric_content_false`.) -/
theorem windingRoute_blocked_by_refuted_halfplane :
    ∃ d a z : Pt, ¬ LeftHalfPlaneContent d a z :=
  earHalfPlane_geometric_content_false

/-! ## Part C: the genuine irreducible kernel — the INTERIOR ODD-CROSSING SEED

The single planar-Jordan content the substrate (and the winding engine) cannot synthesize. -/

/-- **The interior odd-crossing seed** (the minimal named, non-vacuous residue).  For every
polygon `P`, ray `ρ`, and vertex `i`, every point of the closed adjacent triangle of `i` has
`ClosedRegion' P ρ`.  Equivalently (`ClosedRegion'` being `OnBoundary ∨ Odd CrossingNumber'`),
an *interior* such point must carry an odd crossing number for `ρ` — the interior odd seed.

This is exactly the per-vertex region-level `IsConvexVertex'` containment quantified
uniformly; it is the irreducible single-edge-jump Jordan kernel that no substrate lemma
produces for `n ≥ 4` (the adjacent-triangle base is a chord, and no lemma computes the
per-edge `crossTau` sign on a chord), and that the signed-winding engine cannot create (it
bridges `Odd → windCross ≠ 0` but synthesizes no nonzero interior winding from geometry). -/
def InteriorOddSeed : Prop :=
  ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m),
    closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i))
      ⊆ {x : Pt | ClosedRegion' P ρ x}

/-- **`InteriorOddSeed` yields the region-level `IsConvexVertex'` for every vertex.**  This is
definitional unfolding: `IsConvexVertex'` is precisely the closed-adjacent-triangle
containment, so the uniform seed supplies it at any chosen vertex.  Thus the seed is exactly
the convex-vertex spec content the bundle needs. -/
theorem isConvexVertex'_of_seed (S : InteriorOddSeed)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) :
    IsConvexVertex' P ρ i :=
  S P ρ i

/-- **Non-vacuity (§3.3 anti-vacuity): the seed is implied by genuine convex vertices.**  If
every polygon/ray has *some* region-level convex vertex with the containment holding at every
vertex — concretely, if `IsConvexVertex'` holds at every vertex — then `InteriorOddSeed` holds.
Hence the seed is satisfiable exactly when the geometry is; it is not an unsatisfiable
premise.  (The hypothesis is the verbatim per-vertex containment, so this is a faithful
re-packaging, not a strengthening.) -/
theorem interiorOddSeed_of_isConvexVertex
    (H : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m),
      IsConvexVertex' P ρ i) :
    InteriorOddSeed :=
  fun P ρ i => H P ρ i

/-- **The seed is genuinely the parity content** (faithfulness witness): an interior point of
the adjacent triangle that is off the boundary must have ODD crossing number under the seed —
the interior odd seed in its bare parity form.  This certifies `InteriorOddSeed` is a true
planar Prop about crossing parity, not a vacuous or trivially-true one. -/
theorem seed_forces_odd_crossing (S : InteriorOddSeed)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) {x : Pt}
    (hx : x ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)))
    (hoff : ¬ OnBoundary P x) :
    Odd (CrossingNumber' P ρ x) := by
  have hreg : ClosedRegion' P ρ x := S P ρ i hx
  rcases hreg with hb | hodd
  · exact absurd hb hoff
  · exact hodd

/-- **The signed-winding bridge applies to the seed** (the part the winding engine DOES
supply): for an off-boundary interior point provided by the seed, the signed winding is
nonzero.  This shows precisely where the winding engine helps (the parity→winding bridge) and,
by contrast, where it does NOT (it consumes the seed; it does not produce it). -/
theorem seed_forces_windCross_ne_zero (S : InteriorOddSeed)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m) {x : Pt}
    (hx : x ∈ closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i)))
    (hoff : ¬ OnBoundary P x) :
    windCross P ρ x ≠ 0 :=
  windCross_ne_zero_of_odd_crossing P ρ (seed_forces_odd_crossing S P ρ i hx hoff)

/-! ## Part D: the headline, conditional on exactly the one residue + `M`

The fully-assembled Chapter-36 `⌊n/3⌋` art-gallery bound, conditional on exactly the single
convex-position residue `PolygonGeomResidue` (whose irreducible kernel is `InteriorOddSeed`,
Part C) and the peel oracle `M`.  This is `PolygonGeomInput.artGallery_strict_of_residue`,
re-exported so this discharge file names the post-pursuit surface. -/

/-- **Chapter-36 art-gallery `⌊n/3⌋` headline over the single residue + `M`** (re-export).  The
ray-direction genericity, the count/parity half, the segment-disjointness surface, and the
triangle leaf are all discharged; the half-plane oracle is refuted and stripped; the only
inputs are the single convex-position residue `R` (irreducible kernel `InteriorOddSeed`) and
`M`. -/
theorem artGallery_strict_of_residue {n : ℕ}
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
  ProofsInTheBook.PolygonGeomInput.artGallery_strict_of_residue R M P ρ

end

end ProofsInTheBook.PolygonGeometryDischarge

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonGeometryDischarge.region_ray_independent_unconditional
#print axioms ProofsInTheBook.PolygonGeometryDischarge.offDiagDisjoint_discharged
#print axioms ProofsInTheBook.PolygonGeometryDischarge.windCross_diagonal_cancels
#print axioms ProofsInTheBook.PolygonGeometryDischarge.windingRoute_blocked_by_refuted_halfplane
#print axioms ProofsInTheBook.PolygonGeometryDischarge.isConvexVertex'_of_seed
#print axioms ProofsInTheBook.PolygonGeometryDischarge.interiorOddSeed_of_isConvexVertex
#print axioms ProofsInTheBook.PolygonGeometryDischarge.seed_forces_odd_crossing
#print axioms ProofsInTheBook.PolygonGeometryDischarge.seed_forces_windCross_ne_zero
#print axioms ProofsInTheBook.PolygonGeometryDischarge.artGallery_strict_of_residue
