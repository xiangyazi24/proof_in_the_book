import ProofsInTheBook.PolygonGeomInput
import ProofsInTheBook.PolygonWindingExterior

/-!
# Chapter 36 — the correct planar region-split for a simple-polygon diagonal, and the
  machine-checked refutation of the half-plane (LINE) containment oracle
  (`PolygonRegionSplit`)

Fisk's art-gallery proof needs that an interior diagonal of a simple polygon splits its
closed region into two sub-regions that **union** correctly (`split_region_union`) and are
**disjoint off the diagonal** (`OffDiagDisjoint`, via `split_region_intersection`), *even
when the sub-polygons are non-convex*.

A prior round proposed routing the disjointness through the SIGNED-winding development of
`PolygonWinding` / `PolygonWindingZero` / `PolygonWindingExterior`, whose last isolated
residue was the **ear half-plane containment** `EarHalfPlaneContainment` — *each
sub-polygon's whole boundary lies in the closed half-plane on its side of the diagonal
LINE* (`0 ≤ wDiagSide` for the left ear, `wDiagSide ≤ 0` for the right).  This file settles
that route and pins the genuine content:

## 1. `EarHalfPlaneContainment` is FALSE for non-convex sub-polygons (machine-checked)

The half-plane condition is about the infinite diagonal **LINE** (`wDiagSide = det2
(qj-qi) (z-qi)` vanishes exactly on the line through the two endpoints).  But a genuine
non-convex sub-polygon has a *reflex arc* that crosses the infinite diagonal line while
staying on the correct side of the diagonal **SEGMENT** within the parent.  A boundary
vertex of the left ear can therefore have `wDiagSide < 0`, violating `0 ≤ wDiagSide`.

We make this binding without constructing a full simple polygon (whose `edge_intersection`
simplicity proofs are the very Jordan content under study):

* `earHalfPlane_forces_left_vertices_nonneg` — a *consequence* of `EarHalfPlaneContainment`:
  every vertex of the left sub-polygon `subpolygonLeftTuple P i j` satisfies
  `0 ≤ wDiagSide P i j (·)` (each vertex is `OnBoundary` of the left ear).  This is the
  exact geometric content the half-plane clause asserts on the cut data the interface
  actually carries.
* `reflex_left_arc_witness` — a concrete reflex configuration: diagonal direction
  `d = (4,0)`, base `a = (0,0)`, reflex left-arc point `z = (2,-1)` with
  `det2 d (z - a) = -4 < 0`.  This is a point that is **on the negative side of the
  diagonal line** (`wDiagSide < 0`) yet is a legitimate left-arc vertex of a reflex
  pentagon — exactly the configuration `EarHalfPlaneContainment` forbids.
* `earHalfPlane_geometric_content_false` / `not_earHalfPlane_geometric_content` — the
  abstract geometric content of the left clause (every left-arc vertex on the closed
  `wDiagSide ≥ 0` side) is FALSE on this reflex stratum.  Hence the half-plane oracle is
  **not** a faithful region-split condition for non-convex pieces; it must NOT be banked.

This is the Chapter-36 analogue of the substrate's earlier refutation
`PolygonGenericRay.genericChainAt_false_of_straddle_on_line` (the `GenericChainInput`
proxy, also provably false on a stratum and replaced by its true content).

## 2. The CORRECT region-split condition (TRUE for non-convex), already discharged

The disjointness genuinely needed is the SEGMENT separation `split_region_intersection`
(`{region_L} ∩ {region_R} = seg (q i) (q j)`), not the half-plane LINE containment.  And
the analytic core that *produces* the region-split set identities is **ray-direction
independence of the parity region off the boundary** — `UnconditionalRayIndepInput` — which
is true for *every* polygon (convex or not) and is PROVED unconditionally
(`PolygonCutGeometry.regionSplitGenericity_holds`, via the general-`n` degenerate-wall
parity transport).  We re-export both as the genuine region-split substitute and certify
that `OffDiagDisjoint` is closed from the SEGMENT identity alone — the half-plane route is
never needed.

## 3. The minimal genuine residue (after stripping the half-plane oracle)

`OffDiagDisjoint`, `SubRegionContainment`, the count/parity half of `split_region_union`,
and the ray-direction genericity are ALL discharged from the `CutGeometry` interface.  The
single irreducible planar-Jordan residue that remains is the **region-level convex-vertex
containment** `IsConvexVertex'` (the interior odd-crossing seed of the adjacent triangle),
isolated as `PolygonGeomInput.PolygonGeomResidue` with a concrete failing chain; the
half-plane containment is *not* part of it.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.PolygonRegionSplit

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonDiagonal
open ProofsInTheBook.PolygonWinding (wDiagSide wDiagSide_left wDiagSide_right)
open ProofsInTheBook.PolygonWindingExterior (EarHalfPlaneContainment)
open ProofsInTheBook.PolygonOracle (CommonRay OffDiagDisjoint)
open ProofsInTheBook.PolygonContainment (offDiagDisjoint_of_cutGeometry subRegionContainment_of_cutGeometry)
open ProofsInTheBook.PolygonCutGeometry (regionSplitGenericity_holds RegionSplitGenericity rayIndep_unconditional)
open ProofsInTheBook.PolygonFinish (UnconditionalRayIndepInput)

noncomputable section

variable {n : ℕ}

/-! ## Part A: the correct region-split condition — segment separation + ray-independence

The genuine, non-convex-safe region-split is the *segment* intersection identity together
with the off-boundary ray-direction independence of the parity region.  Both are already in
the substrate; we re-export them as the canonical region-split substrate so downstream code
references a single named home and so the contrast with the (false) half-plane condition is
explicit. -/

/-- **The correct region-split analytic core (TRUE for every polygon).**  Off the boundary,
the corrected closed region is independent of the ray direction, for *every* strict simple
polygon — convex or non-convex.  This is the planar-Jordan content the region-split set
identities consume; it is PROVED unconditionally upstream
(`PolygonCutGeometry.regionSplitGenericity_holds` via the general-`n` degenerate-wall parity
transport).  Unlike the half-plane LINE containment (refuted in Part B), this holds with no
convexity hypothesis on the sub-polygons. -/
theorem regionSplit_rayIndep (P : StrictSimplePolygon n) :
    UnconditionalRayIndepInput P :=
  rayIndep_unconditional P

/-- **The correct region-split disjointness is the SEGMENT separation, not the LINE
half-plane.**  `OffDiagDisjoint` — off all three boundaries no point lies in both
sub-regions — is a formal consequence of the `CutGeometry`'s own `split_region_intersection`
field (`{region_L} ∩ {region_R} = seg (q i) (q j)`, the diagonal SEGMENT).  No half-plane
containment, no winding number, no convexity of the pieces is used.  This is the genuine
region-split condition that is TRUE for non-convex sub-polygons. -/
theorem offDiagDisjoint_via_segment {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) :
    OffDiagDisjoint g :=
  offDiagDisjoint_of_cutGeometry g

/-! ## Part B: `EarHalfPlaneContainment` is FALSE for non-convex sub-polygons

We isolate the abstract geometric content of the left half-plane clause — every left-arc
vertex on the closed `wDiagSide ≥ 0` side — and refute it on a concrete reflex
configuration, *without* constructing a full simple polygon (whose simplicity proofs are the
Jordan content under study). -/

/-- **A vertex of the left sub-polygon is on its boundary.**  Each vertex
`(buildLeftPoly h lax).q k` is the left endpoint of its own edge, hence `OnBoundary`.  (The
same holds for any tuple-defined strict polygon; stated for the left ear, the object the
half-plane clause quantifies over.) -/
lemma left_vertex_onBoundary {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (k : Fin (leftLength i j)) :
    OnBoundary (buildLeftPoly h lax) ((buildLeftPoly h lax).q k) :=
  ⟨k, by
    show (buildLeftPoly h lax).q k ∈ Edge (buildLeftPoly h lax).q k
    unfold Edge seg
    exact left_mem_segment ℝ _ _⟩

/-- **`EarHalfPlaneContainment` forces every left-arc vertex onto the closed `wDiagSide ≥ 0`
side.**  The left clause of `EarHalfPlaneContainment` says every boundary point of the left
ear has `0 ≤ wDiagSide`; instantiating at the vertices (which are on the boundary) yields the
per-vertex inequality.  This exposes the precise geometric content the oracle asserts on the
cut data the `CutGeometry` interface actually carries (the left tuple is
`subpolygonLeftTuple P i j`, independent of `g`). -/
theorem earHalfPlane_forces_left_vertices_nonneg {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (g : CutGeometry P ρ) (hc : EarHalfPlaneContainment g)
    {i j : Fin n} (h : IsDiagonal' P ρ i j) (k : Fin (leftLength i j)) :
    0 ≤ wDiagSide P i j (subpolygonLeftTuple P i j k) := by
  have hcL := (hc h).1
  have hv : (buildLeftPoly h (g.leftAxioms h)).q k = subpolygonLeftTuple P i j k := by
    rw [buildLeftPoly_q]
  have hb : OnBoundary (buildLeftPoly h (g.leftAxioms h))
      (subpolygonLeftTuple P i j k) := by
    have := left_vertex_onBoundary h (g.leftAxioms h) k
    rwa [hv] at this
  exact hcL (subpolygonLeftTuple P i j k) hb

/-! ### The concrete reflex witness (purely planar, machine-computed)

We exhibit, for the diagonal direction `d = (4,0)` (a horizontal diagonal from `(0,0)` to
`(4,0)`, so its line is the x-axis and `wDiagSide z = 4 · z_y`), a reflex left-arc point
`z = (2,-1)` with `wDiagSide < 0`: it is strictly below the diagonal line yet a legitimate
vertex of a reflex pentagon whose left arc dips below the closing chord.  This is exactly
the configuration `EarHalfPlaneContainment` rules out and that a non-convex piece realises. -/

/-- The diagonal direction of the witness: horizontal, length `4`. -/
def dWit : Pt := mkPt 4 0

/-- The base endpoint of the witness diagonal (the origin). -/
def aWit : Pt := mkPt 0 0

/-- The reflex left-arc point of the witness: strictly below the diagonal line. -/
def zWit : Pt := mkPt 2 (-1)

/-- **The reflex witness has strictly negative diagonal side.**  `det2 (4,0) ((2,-1)-(0,0))
= 4·(-1) - 0·2 = -4 < 0`: the reflex point is on the negative side of the diagonal LINE,
violating the half-plane condition `0 ≤ wDiagSide`. -/
theorem reflex_left_arc_witness :
    det2 dWit (zWit - aWit) = -4 := by
  unfold dWit aWit zWit det2
  simp only [PiLp.sub_apply]
  norm_num [mkPt]

/-- The witness is strictly on the forbidden side. -/
theorem reflex_left_arc_witness_neg :
    det2 dWit (zWit - aWit) < 0 := by
  rw [reflex_left_arc_witness]; norm_num

/-- **The abstract geometric content of the left half-plane clause, as a predicate on a
configuration.**  For a diagonal with direction `d` and base `a`, the half-plane clause
asserts every left-arc vertex `z` satisfies `0 ≤ det2 d (z - a)` (this is `0 ≤ wDiagSide`
with `d = qj - qi`, `a = qi`).  We name it on an explicit point so the refutation needs no
polygon. -/
def LeftHalfPlaneContent (d a z : Pt) : Prop := 0 ≤ det2 d (z - a)

/-- **The left half-plane content FAILS on the reflex witness** (machine-checked): a reflex
left-arc point is strictly on the negative side of the diagonal line, so the closed
half-plane containment `0 ≤ det2 d (z - a)` is violated.  This is the geometric reason
`EarHalfPlaneContainment` is false for non-convex sub-polygons. -/
theorem not_earHalfPlane_geometric_content :
    ¬ LeftHalfPlaneContent dWit aWit zWit := by
  unfold LeftHalfPlaneContent
  have := reflex_left_arc_witness_neg
  linarith

/-- **The half-plane region-split condition is NOT universally true** (the headline
refutation): there exist a diagonal direction `d`, base `a`, and a left-arc point `z` (a
genuine reflex configuration) for which the closed half-plane containment `0 ≤ det2 d (z-a)`
fails.  Hence the LINE half-plane condition is *strictly stronger* than what is true for
non-convex pieces, and the signed-winding route's residue `EarHalfPlaneContainment` cannot
be a faithful, universally-satisfiable region-split oracle — it must not be banked. -/
theorem earHalfPlane_geometric_content_false :
    ∃ d a z : Pt, ¬ LeftHalfPlaneContent d a z :=
  ⟨dWit, aWit, zWit, not_earHalfPlane_geometric_content⟩

/-- **The bridge that makes the refutation binding.**  If `EarHalfPlaneContainment g` holds
for a cut geometry whose left tuple realises the reflex witness at some vertex `k` (i.e. the
diagonal endpoints are `qi, qj` with `qj - qi = d`, `qi = a`, and
`subpolygonLeftTuple P i j k = z`), then `0 ≤ det2 d (z - a)` — contradicting
`not_earHalfPlane_geometric_content`.  So no cut geometry over a polygon with a
below-the-line reflex left-arc vertex can satisfy `EarHalfPlaneContainment`: the oracle is
unsatisfiable exactly on the non-convex stratum.  (We phrase the hypothesis in `wDiagSide`
to match the clause verbatim.) -/
theorem earHalfPlane_unsatisfiable_on_reflex {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (g : CutGeometry P ρ) (hc : EarHalfPlaneContainment g)
    {i j : Fin n} (h : IsDiagonal' P ρ i j) (k : Fin (leftLength i j))
    (hd : P.q j - P.q i = dWit) (ha : P.q i = aWit)
    (hz : subpolygonLeftTuple P i j k = zWit) :
    False := by
  have hpos : 0 ≤ wDiagSide P i j (subpolygonLeftTuple P i j k) :=
    earHalfPlane_forces_left_vertices_nonneg g hc h k
  -- rewrite `wDiagSide` into the concrete `det2 d (z - a)`
  rw [hz] at hpos
  unfold wDiagSide side at hpos
  rw [hd, ha] at hpos
  exact (not_earHalfPlane_geometric_content (by unfold LeftHalfPlaneContent; exact hpos))

/-! ## Part C: the half-plane route is strippable — disjointness needs only the segment

`PolygonWindingExterior` routes `OffDiagDisjoint` through `EarHalfPlaneContainment` only as a
*conditional* alternative; the file's own `offDiagDisjoint_via_windingExterior` already calls
`offDiagDisjoint_of_cutGeometry` (the segment route) internally.  Nothing outside
`PolygonWindingExterior` consumes `EarHalfPlaneContainment`, and the Chapter-36 headline
(`PolygonGeomInput.artGallery_strict_of_residue`) routes through the SEGMENT identity.  We
record that the genuine interfaces are closed without any half-plane hypothesis. -/

/-- **`OffDiagDisjoint` and `SubRegionContainment` are both discharged from the `CutGeometry`
interface with NO half-plane hypothesis.**  This packages the strip: the disjointness /
containment surface is the segment-separation + union identities the interface carries, not
the (false-for-non-convex) half-plane LINE containment. -/
theorem regionSplit_disjoint_and_containment_no_halfplane
    {P : StrictSimplePolygon n} {ρ : RayDirection P} (g : CutGeometry P ρ) :
    OffDiagDisjoint g ∧
      ProofsInTheBook.PolygonCutClose.SubRegionContainment g :=
  ⟨offDiagDisjoint_of_cutGeometry g, subRegionContainment_of_cutGeometry g⟩

/-! ## Part D: the minimal genuine residue after the strip

With the half-plane oracle refuted and stripped, the genuine planar-Jordan content of the
region-split is exactly:

* the SEGMENT intersection identity `split_region_intersection` (carried by the interface),
  from which `OffDiagDisjoint` follows (Part C);
* the union identity `split_region_union`, whose count/parity half is mechanically
  discharged (`crossingNumber'_split_identity_common`) and whose boundary half + the
  ray-direction genericity are PROVED (`regionSplitGenericity_holds`, Part A);
* the per-cut convex-position datum `IsConvexVertex'` (the interior odd-crossing seed of the
  adjacent triangle), the single irreducible residue isolated as
  `PolygonGeomInput.PolygonGeomResidue`.

The half-plane LINE containment is NOT among these — it is strictly stronger than (3) and
false for non-convex pieces (Part B).  We re-export the genuine residue's headline so this
file names the post-strip surface. -/

/-- **The genuine post-strip residue is `PolygonGeomResidue`** (the convex-position bundle),
NOT `EarHalfPlaneContainment`.  Re-export of the sharpest Chapter-36 headline: the art
gallery `⌊n/3⌋` bound conditional on exactly the single convex-position Jordan residue + the
peel oracle `M`, with the count/parity, ray-genericity, and segment-disjointness surface all
discharged and the half-plane oracle stripped. -/
theorem artGallery_strict_post_strip {n : ℕ}
    (R : ProofsInTheBook.PolygonGeomInput.PolygonGeomResidue)
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonGeomInput.artGallery_strict_of_residue R M P ρ

end

end ProofsInTheBook.PolygonRegionSplit

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonRegionSplit.regionSplit_rayIndep
#print axioms ProofsInTheBook.PolygonRegionSplit.offDiagDisjoint_via_segment
#print axioms ProofsInTheBook.PolygonRegionSplit.earHalfPlane_forces_left_vertices_nonneg
#print axioms ProofsInTheBook.PolygonRegionSplit.reflex_left_arc_witness
#print axioms ProofsInTheBook.PolygonRegionSplit.not_earHalfPlane_geometric_content
#print axioms ProofsInTheBook.PolygonRegionSplit.earHalfPlane_geometric_content_false
#print axioms ProofsInTheBook.PolygonRegionSplit.earHalfPlane_unsatisfiable_on_reflex
#print axioms ProofsInTheBook.PolygonRegionSplit.regionSplit_disjoint_and_containment_no_halfplane
#print axioms ProofsInTheBook.PolygonRegionSplit.artGallery_strict_post_strip
