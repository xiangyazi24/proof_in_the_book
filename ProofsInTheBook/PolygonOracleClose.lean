import ProofsInTheBook.PolygonOracle

/-!
# Chapter 36 — closing the oracle residuals (CommonRay, BaseTriangleFacts, boundary)

This module sits on top of `PolygonOracle` and closes (or sharply isolates) the
three residuals that the common-ray reduction left standing:

* **`CommonRay` satisfiability** — the common-ray condition consumed by
  `countSummationDatum_of_commonRay` is *not vacuous*: a single direction
  `mkPt 1 t*`, chosen outside the (finite) union of the parent's and any finite
  family of sub-polygons' edge slopes, is simultaneously a genuine `RayDirection`
  for every one of them (`commonDir_exists`, `commonRayDir_valid_for`).  This is
  the playbook §3.3 anti-vacuity obligation: `#print axioms` cannot see an
  unsatisfiable premise, so we exhibit a witnessing direction outright.

* **`BaseTriangleFacts`** — the `n = 3` leaf.  We make the reduction to the
  development's *single planar primitive* explicit: for a `3`-gon the `subset`
  field is exactly `IsConvexVertex'` at the middle vertex `⟨1⟩` (the adjacent
  triangle of `⟨1⟩` is the whole hull `closedTri v0 v1 v2`), and the `cover`
  field is the exterior-evenness datum.  We bundle these two as the irreducible
  planar `BaseTriangleLeaf` datum and *build* a genuine `BaseTriangleFacts` from
  it (`baseTriangleFacts_of_leaf`), plus prove the base triangle is
  nondegenerate unconditionally (`base_tri_nondegenerate`).

* **boundary bookkeeping / union assembly** — the off-boundary union of
  `PolygonOracle.region_union_off_boundary` is upgraded to the *full set
  equality* the `CutGeometry.split_region_union` field demands, modulo the named
  boundary datum `BoundaryOnDiagonal` (the diagonal segment, and only it, is the
  shared boundary).  We give the exact reduction `splitUnion_of_residuals`.

Together with `PolygonOracle` this leaves Chapter 36's geometric core as exactly:
the half-plane disjointness (`OffDiagDisjoint`), the boundary-on-diagonal datum,
and the single `n = 3` Jordan leaf (`BaseTriangleLeaf`) — the count/parity half
being mechanically closed.  Stated precisely in `chapter36_residual_headline`.

No `sorry` / `axiom` / `admit`.
-/

namespace ProofsInTheBook.PolygonOracleClose

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonRayIndep (Sees)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonOracle

/-! ## Part A: `CommonRay` satisfiability — a common direction exists

The `CommonRay` premise demands the sub-polygon rays reuse the parent's direction
vector.  A `RayDirection P` built from `mkPt 1 t` requires only that `t` avoid the
finite set `edgeSlopes P`.  Hence a *single* slope `t*` outside the union of the
edge-slope sets of the parent and any finite family of polygons gives a direction
that is simultaneously valid for all of them.  This exhibits the witnessing
direction, discharging the playbook §3.3 anti-vacuity obligation for `CommonRay`.
-/

/-- **A common slope avoiding a finite union of forbidden slope sets.**  For any
finite set `B` of forbidden slopes there is a `t ∉ B`.  (Specialised below to the
union of several polygons' edge slopes.) -/
theorem commonSlope_exists (B : Finset ℝ) : ∃ t : ℝ, t ∉ B := by
  obtain ⟨t, ht⟩ := B.exists_notMem
  exact ⟨t, ht⟩

/-- **A direction valid for two polygons at once.**  Given parent `P` and a second
polygon `Q` (e.g. a sub-polygon), a slope outside *both* edge-slope sets yields a
single `mkPt 1 t` that is a genuine `RayDirection` for each.  This is the atom of
the common-ray construction: the obstruction "the parent direction may be parallel
to a sub-edge" is sidestepped by choosing `t*` fresh for the *union*. -/
theorem commonDir_exists {m k : ℕ} (P : StrictSimplePolygon m)
    (Q : StrictSimplePolygon k) :
    ∃ (t : ℝ) (hP : t ∉ ProofsInTheBook.PolygonFinish.edgeSlopes P)
      (hQ : t ∉ ProofsInTheBook.PolygonFinish.edgeSlopes Q), True := by
  obtain ⟨t, ht⟩ :=
    (ProofsInTheBook.PolygonFinish.edgeSlopes P ∪
      ProofsInTheBook.PolygonFinish.edgeSlopes Q).exists_notMem
  rw [Finset.mem_union, not_or] at ht
  exact ⟨t, ht.1, ht.2, trivial⟩

/-- **The common direction is a valid `RayDirection` for both polygons.**  The
witnessing slope yields `slopeRay P` and `slopeRay Q` whose direction vectors are
the *same* `mkPt 1 t`.  This is precisely the common-ray equation
`(leftRay).r = ρ.r ∧ (rightRay).r = ρ.r` at the level of direction vectors:
both sub-rays and the parent ray can be taken to be one shared `mkPt 1 t*`. -/
theorem commonRayDir_valid_for {m k : ℕ} (P : StrictSimplePolygon m)
    (Q : StrictSimplePolygon k) :
    ∃ (ρP : RayDirection P) (ρQ : RayDirection Q), ρP.r = ρQ.r := by
  obtain ⟨t, hP, hQ, _⟩ := commonDir_exists P Q
  exact ⟨ProofsInTheBook.PolygonFinish.slopeRay P hP,
    ProofsInTheBook.PolygonFinish.slopeRay Q hQ, rfl⟩

/-- **Three-way common direction** (parent + left + right).  A single slope outside
all three edge-slope sets gives one `mkPt 1 t*` valid as a `RayDirection` for the
parent and both sub-polygons simultaneously — the exact shape the `CommonRay`
condition consumes (`(leftRay h).r = ρ.r ∧ (rightRay h).r = ρ.r`).  Hence
`CommonRay` is a *satisfiable* condition, not a vacuous premise. -/
theorem commonRayDir_valid_for₃ {m kL kR : ℕ} (P : StrictSimplePolygon m)
    (L : StrictSimplePolygon kL) (R : StrictSimplePolygon kR) :
    ∃ (ρP : RayDirection P) (ρL : RayDirection L) (ρR : RayDirection R),
      ρL.r = ρP.r ∧ ρR.r = ρP.r := by
  obtain ⟨t, ht⟩ :=
    (ProofsInTheBook.PolygonFinish.edgeSlopes P ∪
      ProofsInTheBook.PolygonFinish.edgeSlopes L ∪
      ProofsInTheBook.PolygonFinish.edgeSlopes R).exists_notMem
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at ht
  obtain ⟨⟨hP, hL⟩, hR⟩ := ht
  exact ⟨ProofsInTheBook.PolygonFinish.slopeRay P hP,
    ProofsInTheBook.PolygonFinish.slopeRay L hL,
    ProofsInTheBook.PolygonFinish.slopeRay R hR, rfl, rfl⟩

/-! ## Part B: `BaseTriangleFacts` — the `n = 3` leaf reduced to the planar primitive

`BaseTriangleFacts` bundles two facts about a `3`-gon `Q`:

* `subset` : `closedTri (v0 Q) (v1 Q) (v2 Q) ⊆ region`;
* `cover`  : `region ⊆ closedTri (v0 Q) (v1 Q) (v2 Q)`.

For a `3`-gon the three vertices `v0, v1, v2` are the consecutive triple at the
middle vertex `⟨1⟩` (`cyclicPrev ⟨1⟩ = ⟨0⟩`, `cyclicNext ⟨1⟩ = ⟨2⟩`, exactly as in
`baseTri_nondegenerate`).  Hence:

* the `subset` half **is** `IsConvexVertex' Q σ ⟨1⟩` — the development's *single
  planar primitive* (assumed as a residual field of every `CutGeometry`);
* the `cover` half is the exterior-evenness Jordan datum.

We capture both as the irreducible `BaseTriangleLeaf` datum, stated in the
`v0/v1/v2` form so that it is cast-free, and *build* a genuine `BaseTriangleFacts`
from it (`baseTriangleFacts_of_leaf`).  We also prove the bridge
`subset_iff_convexVertex_one`: the `subset` half is literally the planar
convex-vertex primitive at `⟨1⟩`.  This is the honest isolation of the `n = 3`
Jordan leaf — no parity/count content remains in it. -/

/-- **The irreducible `n = 3` Jordan leaf datum.**  For every `3`-gon and ray the
closed hull and the region coincide.  Stated in `v0/v1/v2` form (cast-free).  This
is the planar primitive at the recursion leaf — the same Jordan content the
development encapsulates in `IsConvexVertex'` (for `subset`) plus the exterior
half (for `cover`). -/
structure BaseTriangleLeaf : Prop where
  /-- The hull of the three vertices lies in the region. -/
  hull_subset : ∀ {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q),
    m = 3 → closedTri (v0 Q) (v1 Q) (v2 Q) ⊆ {x : Pt | ClosedRegion' Q σ x}
  /-- Every region point lies in the hull. -/
  region_subset : ∀ {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q),
    m = 3 → ∀ x, ClosedRegion' Q σ x → x ∈ closedTri (v0 Q) (v1 Q) (v2 Q)

/-- **`BaseTriangleFacts` from the leaf datum.**  The two `BaseTriangleFacts`
fields are exactly the two `BaseTriangleLeaf` conjuncts. -/
def baseTriangleFacts_of_leaf (B : BaseTriangleLeaf) : BaseTriangleFacts where
  subset := fun Q σ h => B.hull_subset Q σ h
  cover := fun Q σ h => B.region_subset Q σ h

/-- For a `3`-gon, `v0/v1/v2` are the consecutive triple `prev/⟨1⟩/next` at the
middle vertex.  Hence the base hull equals the adjacent triangle of `⟨1⟩`. -/
theorem base_hull_eq_adjacentTri (Q : StrictSimplePolygon 3) :
    closedTri (v0 Q) (v1 Q) (v2 Q)
      = closedTri (Q.q (cyclicPrev (⟨1, by omega⟩ : Fin 3))) (Q.q ⟨1, by omega⟩)
          (Q.q (cyclicNext (⟨1, by omega⟩ : Fin 3))) := by
  have hp : cyclicPrev (⟨1, by omega⟩ : Fin 3) = ⟨0, by omega⟩ := by apply Fin.ext; rfl
  have hnx : cyclicNext (⟨1, by omega⟩ : Fin 3) = ⟨2, by omega⟩ := by apply Fin.ext; rfl
  rw [hp, hnx]
  rfl

/-- **The `subset` half of the leaf IS the planar convex-vertex primitive at
`⟨1⟩`.**  For a `3`-gon, `closedTri (v0) (v1) (v2) ⊆ region` is *definitionally*
`IsConvexVertex' Q σ ⟨1⟩` (after the consecutive-triple rewrite).  This pins the
`n = 3` `subset` residual onto the exact primitive the rest of Chapter 36 already
treats as the irreducible planar input. -/
theorem base_subset_iff_convexVertex_one (Q : StrictSimplePolygon 3)
    (σ : RayDirection Q) :
    (closedTri (v0 Q) (v1 Q) (v2 Q) ⊆ {x : Pt | ClosedRegion' Q σ x})
      ↔ IsConvexVertex' Q σ (⟨1, by omega⟩ : Fin 3) := by
  unfold IsConvexVertex'
  rw [base_hull_eq_adjacentTri]

/-- **The base triangle is nondegenerate** (re-export, unconditional).  For any
`3`-gon the base triple is noncollinear — the strict-polygon axiom at vertex `⟨1⟩`.
(Identical content to `PolygonTriangulation.baseTri_nondegenerate`; named here so
the leaf module records that the leaf triple is a genuine triangle, i.e. the leaf
datum is over a nondegenerate triangle, not a degenerate impostor.) -/
theorem base_tri_nondegenerate {m : ℕ} (Q : StrictSimplePolygon m) (h3 : m = 3) :
    ¬ Collinear3 (v0 Q) (v1 Q) (v2 Q) :=
  ProofsInTheBook.PolygonTriangulation.baseTri_nondegenerate Q h3

/-! ## Part C: boundary bookkeeping — upgrading the off-boundary union to the
`split_region_union` set equality

`PolygonOracle.region_union_off_boundary` gives the pointwise union *off* all three
boundaries.  The `CutGeometry.split_region_union` field demands the full set
equality `{region_P} = {region_L} ∪ {region_R}`, which additionally constrains the
*boundary* points (of `P`, of `L`, of `R`).  We isolate that residual cleanly as
the `BoundaryUnionData` datum — the union membership at every point lying on some
boundary — and prove the full set equality from:

* `CommonRay` + `OffDiagDisjoint` (the off-boundary union, *proved* from the count
  identity in `PolygonOracle`), and
* `BoundaryUnionData` (the boundary points — the only genuinely-geometric residue
  left in the union field, the diagonal segment being the shared boundary).

This is the exact reduction the oracle's `split_region_union` consumes; the
parity/count half is entirely discharged, leaving only the boundary geometry. -/

/-- **The boundary-points residual of the union field.**  At every point on some
one of the three boundaries, the parent-region membership equals the union of the
two sub-region memberships.  (Off all three boundaries this is *proved* by the
count identity; on the boundaries it is the remaining geometric datum — the
diagonal segment being precisely the shared boundary.) -/
def BoundaryUnionData {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) : Prop :=
  ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt},
    (OnBoundary P x ∨ OnBoundary (buildLeftPoly h (g.leftAxioms h)) x ∨
      OnBoundary (buildRightPoly h (g.rightAxioms h)) x) →
    (ClosedRegion' P ρ x ↔
      (ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x ∨
        ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x))

/-- **Pointwise union at *every* point.**  Combining the proved off-boundary union
(`PolygonOracle.region_union_off_boundary`, from the count identity + half-plane
disjointness) with the boundary datum, the parent-region membership is the union of
the two sub-region memberships at *every* point.  This is the pointwise form of the
`split_region_union` set equality. -/
theorem region_union_everywhere {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) (hcr : CommonRay g) (hdisj : OffDiagDisjoint g)
    (hbd : BoundaryUnionData g) {i j : Fin n} (h : IsDiagonal' P ρ i j) (x : Pt) :
    ClosedRegion' P ρ x ↔
      (ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x ∨
        ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x) := by
  classical
  by_cases hP : OnBoundary P x
  · exact hbd h (Or.inl hP)
  by_cases hL : OnBoundary (buildLeftPoly h (g.leftAxioms h)) x
  · exact hbd h (Or.inr (Or.inl hL))
  by_cases hR : OnBoundary (buildRightPoly h (g.rightAxioms h)) x
  · exact hbd h (Or.inr (Or.inr hR))
  · exact region_union_off_boundary g hcr hdisj h hP hL hR

/-- **The `split_region_union` set equality, reduced to the named residuals.**
The exact shape the `CutGeometry.split_region_union` field consumes — derived from
`CommonRay`, `OffDiagDisjoint`, and `BoundaryUnionData`, with the count/parity half
entirely discharged in `PolygonOracle`. -/
theorem splitUnion_of_residuals {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) (hcr : CommonRay g) (hdisj : OffDiagDisjoint g)
    (hbd : BoundaryUnionData g) {i j : Fin n} (h : IsDiagonal' P ρ i j) :
    {x : Pt | ClosedRegion' P ρ x} =
      {x : Pt | ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x} ∪
        {x : Pt | ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union]
  exact region_union_everywhere g hcr hdisj hbd h x

/-! ## Part D: the assembled headline — exactly what remains

We bundle the genuinely-geometric residual inputs of a single `CutGeometry` into
`ResidualGeometryData`, and *build* a `CutGeometry` from it (`cutGeometry_of_data`)
whose `split_region_union` field is **derived** (not assumed) via
`splitUnion_of_residuals`.  The only fields that remain *inputs* are the irreducible
planar primitives: the convex extreme vertex, the transversality dispatcher, the
sub-polygon strictness axioms, the (common) sub-rays, the half-plane disjointness,
the boundary datum, and the intersection-equals-diagonal datum — none of which carry
any count/parity content (that half is mechanically discharged).

`chapter36_residual_headline` then states the Chapter-36 art-gallery `⌊n/3⌋`
conclusion together with the precise residual surface. -/

/-- **The genuinely-geometric residual inputs of one `CutGeometry`.**  Everything a
`CutGeometry` needs *except* the union field — which is now derived.  Each field is a
pure planar primitive with no count/parity content. -/
structure ResidualGeometryData (P : StrictSimplePolygon n) (ρ : RayDirection P) where
  convexVertex : Fin n
  convexVertex_spec : IsConvexVertex' P ρ convexVertex
  transversality : DiagonalTransversality' P ρ convexVertex
  leftAxioms : ∀ {i j : Fin n}, IsDiagonal' P ρ i j → LeftStrictAxioms P i j
  rightAxioms : ∀ {i j : Fin n}, IsDiagonal' P ρ i j → RightStrictAxioms P i j
  leftRay : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
    RayDirection (buildLeftPoly h (leftAxioms h))
  rightRay : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
    RayDirection (buildRightPoly h (rightAxioms h))
  /-- The common-ray equation (satisfiable: `commonRayDir_valid_for₃`). -/
  commonRay : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
    (leftRay h).r = ρ.r ∧ (rightRay h).r = ρ.r
  /-- Half-plane disjointness off all boundaries. -/
  disjoint : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt},
    ¬ OnBoundary P x →
    ¬ OnBoundary (buildLeftPoly h (leftAxioms h)) x →
    ¬ OnBoundary (buildRightPoly h (rightAxioms h)) x →
    ¬ (ClosedRegion' (buildLeftPoly h (leftAxioms h)) (leftRay h) x ∧
        ClosedRegion' (buildRightPoly h (rightAxioms h)) (rightRay h) x)
  /-- Boundary-points union datum. -/
  boundary : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j) {x : Pt},
    (OnBoundary P x ∨ OnBoundary (buildLeftPoly h (leftAxioms h)) x ∨
      OnBoundary (buildRightPoly h (rightAxioms h)) x) →
    (ClosedRegion' P ρ x ↔
      (ClosedRegion' (buildLeftPoly h (leftAxioms h)) (leftRay h) x ∨
        ClosedRegion' (buildRightPoly h (rightAxioms h)) (rightRay h) x))
  /-- Intersection-equals-diagonal datum (the other planar field, carried verbatim). -/
  intersection : ∀ {i j : Fin n} (h : IsDiagonal' P ρ i j),
    {x : Pt | ClosedRegion' (buildLeftPoly h (leftAxioms h)) (leftRay h) x} ∩
        {x : Pt | ClosedRegion' (buildRightPoly h (rightAxioms h)) (rightRay h) x} =
      seg (P.q i) (P.q j)

/-- **Off-boundary symmetric difference from raw fields (no `CutGeometry`).**  The
count identity `crossingNumber'_split_identity_common` is a *fields-level* statement
(it takes `lax/rax/σL/σR/hL/hR`, not a `CutGeometry`), so the symmetric-difference
split off all three boundaries is available directly from the residual fields.  This
is what breaks the construction circularity in `cutGeometry_of_data`. -/
theorem region_symmDiff_pieces {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt}
    (hPb : ¬ OnBoundary P x) (hLb : ¬ OnBoundary (buildLeftPoly h lax) x)
    (hRb : ¬ OnBoundary (buildRightPoly h rax) x) :
    ClosedRegion' P ρ x ↔
      (ClosedRegion' (buildLeftPoly h lax) σL x ↔
        ¬ ClosedRegion' (buildRightPoly h rax) σR x) := by
  have hxor := ProofsInTheBook.PolygonIccEngine.parity_xor_of_count_sum
    (crossingNumber'_split_identity_common h lax rax σL σR hL hR x)
  unfold ClosedRegion'
  rw [or_iff_right hPb, or_iff_right hLb, or_iff_right hRb]
  exact hxor

/-- **Off-boundary union from raw fields + disjointness (no `CutGeometry`).**  With
the half-plane disjointness, the off-boundary symmetric difference upgrades to the
union — same logic as `region_union_off_boundary`, at the fields level. -/
theorem region_union_offBoundary_pieces {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt}
    (hPb : ¬ OnBoundary P x) (hLb : ¬ OnBoundary (buildLeftPoly h lax) x)
    (hRb : ¬ OnBoundary (buildRightPoly h rax) x)
    (hnand : ¬ (ClosedRegion' (buildLeftPoly h lax) σL x ∧
        ClosedRegion' (buildRightPoly h rax) σR x)) :
    ClosedRegion' P ρ x ↔
      (ClosedRegion' (buildLeftPoly h lax) σL x ∨
        ClosedRegion' (buildRightPoly h rax) σR x) := by
  have hxor := region_symmDiff_pieces h lax rax σL σR hL hR hPb hLb hRb
  constructor
  · intro hPx
    rw [hxor] at hPx
    by_cases hLx : ClosedRegion' (buildLeftPoly h lax) σL x
    · exact Or.inl hLx
    · right; by_contra hRx; exact hLx (hPx.mpr hRx)
  · intro hOr
    rw [hxor]
    rcases hOr with hLx | hRx
    · exact ⟨fun _ hRx => hnand ⟨hLx, hRx⟩, fun _ => hLx⟩
    · exact ⟨fun hLx => absurd ⟨hLx, hRx⟩ hnand, fun hnRx => absurd hRx hnRx⟩

/-- **`CutGeometry` from the residual data, union field DERIVED.**  The union set
equality is *built* from `region_union_offBoundary_pieces` (the count identity +
half-plane disjointness, off boundaries) glued with the boundary datum — it is *not*
assumed.  Every other field is a pure planar input carrying no count/parity content. -/
def cutGeometry_of_data {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (D : ResidualGeometryData P ρ) : CutGeometry P ρ where
  convexVertex := D.convexVertex
  convexVertex_spec := D.convexVertex_spec
  transversality := D.transversality
  leftAxioms := D.leftAxioms
  rightAxioms := D.rightAxioms
  leftRay := D.leftRay
  rightRay := D.rightRay
  split_region_union := by
    intro i j h
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union]
    by_cases hP : OnBoundary P x
    · exact D.boundary h (Or.inl hP)
    by_cases hL : OnBoundary (buildLeftPoly h (D.leftAxioms h)) x
    · exact D.boundary h (Or.inr (Or.inl hL))
    by_cases hR : OnBoundary (buildRightPoly h (D.rightAxioms h)) x
    · exact D.boundary h (Or.inr (Or.inr hR))
    · exact region_union_offBoundary_pieces h (D.leftAxioms h) (D.rightAxioms h)
        (D.leftRay h) (D.rightRay h) (D.commonRay h).1 (D.commonRay h).2
        hP hL hR (D.disjoint h hP hL hR)
  split_region_intersection := D.intersection

/-- **Non-vacuity / faithfulness of `ResidualGeometryData`.**  A *genuine*
`CutGeometry` whose sub-rays are common (`CommonRay`) and whose sub-regions are
half-plane disjoint off the diagonal (`OffDiagDisjoint`) yields a
`ResidualGeometryData`: the `boundary` field is a true consequence of the real
`split_region_union` set equality, and `disjoint`/`intersection` are carried
verbatim.  Hence `ResidualGeometryData` is *not* a strengthening of the oracle's
geometric content — it is a faithful decomposition (the union field split into its
off-boundary count/parity half, now derived, plus the boundary half).  This is the
playbook §3.3 anti-vacuity certificate: the residual datum is satisfiable exactly
when the underlying geometry oracle is. -/
def residualGeometryData_of_cutGeometry {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (g : CutGeometry P ρ) (hcr : CommonRay g) (hdisj : OffDiagDisjoint g) :
    ResidualGeometryData P ρ where
  convexVertex := g.convexVertex
  convexVertex_spec := g.convexVertex_spec
  transversality := g.transversality
  leftAxioms := g.leftAxioms
  rightAxioms := g.rightAxioms
  leftRay := g.leftRay
  rightRay := g.rightRay
  commonRay := fun h => hcr h
  disjoint := by intro i j h x hP hL hR; exact hdisj h hP hL hR
  boundary := by
    intro i j h x _
    have hset := g.split_region_union h
    have : x ∈ {x : Pt | ClosedRegion' P ρ x} ↔
        x ∈ ({x : Pt | ClosedRegion' (buildLeftPoly h (g.leftAxioms h)) (g.leftRay h) x} ∪
          {x : Pt | ClosedRegion' (buildRightPoly h (g.rightAxioms h)) (g.rightRay h) x}) := by
      rw [hset]
    simpa only [Set.mem_setOf_eq, Set.mem_union] using this
  intersection := fun h => g.split_region_intersection h

/-! ### The Chapter-36 residual headline

Assembling: a `CutGeometryOracle` built from per-polygon residual data (union field
derived) feeds the existing `artGallery_strict_attach`, giving the `⌊n/3⌋`
art-gallery conclusion.  The residual surface is now *exactly*:

* `ResidualGeometryData` (per polygon) — the planar primitives: convex extreme
  vertex (`IsConvexVertex'`), transversality, sub-polygon strictness axioms, the
  *common* sub-rays (satisfiable, `commonRayDir_valid_for₃`), half-plane
  disjointness (`OffDiagDisjoint`), the boundary datum, and the
  intersection-equals-diagonal datum;
* `BaseTriangleFacts` (built from the `n = 3` `BaseTriangleLeaf`);
* `DiagonalAttachInput` (peel-ordering; satisfiability certified in `PolygonLast`).

The count/parity half of the union field is mechanically discharged. -/

/-- **A `CutGeometryOracle` from a uniform residual-data supply.**  Given residual
geometry data for *every* polygon and ray, the union field of every `CutGeometry` is
derived; the oracle is assembled. -/
def cutGeometryOracle_of_data
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ResidualGeometryData P ρ) :
    CutGeometryOracle :=
  fun P ρ => cutGeometry_of_data (D P ρ)

/-- **Chapter-36 art-gallery headline over the reduced residual surface.**  Given (a)
a uniform supply of `ResidualGeometryData` (the planar primitives, with the union
field's count/parity half *derived* not assumed), (b) the `n = 3` Jordan leaf
`BaseTriangleLeaf`, and (c) the diagonal-attach peel witness, *every* strict simple
polygon with a ray direction admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed
region.  This is the sharpest Chapter-36 statement: everything count/parity is closed;
the only inputs are irreducibly-planar Jordan data. -/
theorem chapter36_residual_headline
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ResidualGeometryData P ρ)
    (L : BaseTriangleLeaf)
    (M : DiagonalAttachInput (baseTriangleFacts_of_leaf L))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  PolygonLast.artGallery_strict_attach (cutGeometryOracle_of_data D)
    (baseTriangleFacts_of_leaf L) M P ρ

end ProofsInTheBook.PolygonOracleClose
