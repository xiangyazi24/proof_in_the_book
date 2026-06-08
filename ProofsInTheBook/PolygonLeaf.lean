import ProofsInTheBook.PolygonOracleClose

/-!
# Chapter 36 — the planar leaf facts (`BaseTriangleLeaf` and friends)

This module sits on top of `PolygonOracleClose` and attacks the last *planar*
residuals of Chapter 36: the `n = 3` Jordan leaf `BaseTriangleLeaf`, together with
the reusable crossing-number kernels that drive it.

The headline residual reduction (`PolygonOracleClose.chapter36_residual_headline`)
consumes three named geometric inputs — `BaseTriangleLeaf`, the half-plane
disjointness `OffDiagDisjoint`, and the boundary datum `BoundaryUnionData` — that
all live below the count/parity layer (which is mechanically closed in
`PolygonOracle`).  This file develops the genuine planar machinery for the first of
these, the single recursion *leaf*.

## The crossing-number kernel

The side-coordinate crossing number `CrossingNumber' P σ x` counts the edges whose
endpoints straddle the ray line `x + ℝ•σ.r` (the half-open `Span` rule of
`PolygonSideCrossing`) *and* whose unique ray parameter is nonnegative (forward).
Two unconditional kernels:

* **`crossingNumber'_eq_zero_of_allSide_pos` / `_neg`** — if *every* vertex lies
  strictly on one fixed side of the ray line (`0 < side σ.r x v` for all `v`, or
  `< 0` for all `v`), then no edge spans the line, so `CrossingNumber' P σ x = 0`.
  This is the "far exterior point" kernel: a point so far in the `-σ.r` normal
  direction that the whole polygon is on one side casts *no* forward crossings.

* **`exists_far_point_allSide_neg` / `exists_crossingNumber'_eq_zero`** — such a base
  point exists for every polygon and ray: translate any base point far along the
  normal of `σ.r` (`normalDir`) until all vertices share a strict side, yielding
  `CrossingNumber' = 0`.

These give a *concrete even off-boundary point* unconditionally; combined with the
unconditional region-indicator local constancy of `PolygonSideCrossing`, they are
the kernel of the `cover` half of the triangle leaf.

No `sorry` / `axiom` / `admit`.
-/

namespace ProofsInTheBook.PolygonLeaf

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonTriangulation
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonRayIndep (Sees)
open ProofsInTheBook.PolygonLast (DiagonalAttachInput)
open ProofsInTheBook.PolygonOracleClose

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the all-one-side crossing kernel

If every polygon vertex is on the *same strict side* of the ray line through `x`,
then for every edge `i` the two endpoint side coordinates have the same strict sign,
so `Span` fails (`Span a b` requires opposite signs by `span_iff_opp_sign`), hence
no edge is span-crossed and `CrossingNumber' P σ x = 0`. -/

/-- **No span when both endpoints share a strict sign.**  If the two endpoint side
coordinates of edge `i` are both `> 0` or both `< 0`, edge `i` does not span-cross. -/
lemma not_spanCrossesSide_of_sameSign (P : StrictSimplePolygon n) (σ : RayDirection P)
    (x : Pt) (i : Fin n)
    (h : (0 < side σ.r x (P.q i) ∧ 0 < side σ.r x (P.q (cyclicNext i))) ∨
         (side σ.r x (P.q i) < 0 ∧ side σ.r x (P.q (cyclicNext i)) < 0)) :
    ¬ SpanCrossesSide P σ x i := by
  unfold SpanCrossesSide Span
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact span_false_same_pos h0 h1
  · exact span_false_same_nonpos h0.le h1.le

/-- **All vertices strictly positive side ⟹ crossing number zero.**  If every
vertex `v` has `0 < side σ.r x v`, no edge spans the ray line, so
`CrossingNumber' P σ x = 0`. -/
lemma crossingNumber'_eq_zero_of_allSide_pos (P : StrictSimplePolygon n)
    (σ : RayDirection P) (x : Pt)
    (hall : ∀ k : Fin n, 0 < side σ.r x (P.q k)) :
    CrossingNumber' P σ x = 0 := by
  classical
  unfold CrossingNumber' CrossingEdges'
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  unfold EdgeCrossesRay'
  rintro ⟨hspan, _⟩
  exact not_spanCrossesSide_of_sameSign P σ x i
    (Or.inl ⟨hall i, hall (cyclicNext i)⟩) hspan

/-- **All vertices strictly negative side ⟹ crossing number zero.** -/
lemma crossingNumber'_eq_zero_of_allSide_neg (P : StrictSimplePolygon n)
    (σ : RayDirection P) (x : Pt)
    (hall : ∀ k : Fin n, side σ.r x (P.q k) < 0) :
    CrossingNumber' P σ x = 0 := by
  classical
  unfold CrossingNumber' CrossingEdges'
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  unfold EdgeCrossesRay'
  rintro ⟨hspan, _⟩
  exact not_spanCrossesSide_of_sameSign P σ x i
    (Or.inr ⟨hall i, hall (cyclicNext i)⟩) hspan

/-! ## Part 2: a far point with all vertices on one side exists

The side coordinate is affine in the base point: shifting `x` by `s•d` shifts every
`side σ.r x v` by `-s·det2 σ.r d`.  Choosing `d = normalDir σ.r` with
`det2 σ.r d = ‖σ.r‖² > 0`, a large positive `s` drives *every* vertex side value
strictly negative.  This produces a concrete off-boundary even point. -/

/-- A vector with `det2 σ.r normalDir = (σ.r 0)^2 + (σ.r 1)^2 > 0`: the `90°`
rotation of `σ.r`. -/
def normalDir (r : Pt) : Pt := mkPt (- r 1) (r 0)

lemma det2_normalDir (r : Pt) : det2 r (normalDir r) = r 0 ^ 2 + r 1 ^ 2 := by
  unfold det2 normalDir mkPt
  simp [EuclideanSpace.equiv]
  ring

lemma det2_normalDir_pos {r : Pt} (hr : r ≠ 0) : 0 < det2 r (normalDir r) := by
  rw [det2_normalDir]
  have h : r 0 ^ 2 + r 1 ^ 2 ≠ 0 := by
    intro hz
    apply hr
    have h0 : r 0 = 0 := by nlinarith [sq_nonneg (r 0), sq_nonneg (r 1)]
    have h1 : r 1 = 0 := by nlinarith [sq_nonneg (r 0), sq_nonneg (r 1)]
    exact pt_ext_zero_one h0 h1
  have hnn : 0 ≤ r 0 ^ 2 + r 1 ^ 2 := by positivity
  exact lt_of_le_of_ne hnn (Ne.symm h)

/-- **Side of a shifted base point.**  `side r (x + s•d) v = side r x v - s·det2 r d`. -/
lemma side_shift (r x d v : Pt) (s : ℝ) :
    side r (x + s • d) v = side r x v - s * det2 r d := by
  unfold side
  have : v - (x + s • d) = (v - x) - s • d := by
    ext k; simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  rw [this, det2_sub_right, det2_smul_right]

/-- **A far point with every vertex strictly on the negative side.**  For every
polygon `P`, ray `σ`, and base point `x₀`, there is a base point `x` with
`side σ.r x (P.q k) < 0` for all `k`.  Hence `CrossingNumber' P σ x = 0` and, being
strictly off every vertex's side, `x` is *not* on the boundary. -/
lemma exists_far_point_allSide_neg (P : StrictSimplePolygon n) (σ : RayDirection P)
    (x₀ : Pt) :
    ∃ x : Pt, ∀ k : Fin n, side σ.r x (P.q k) < 0 := by
  classical
  set c := det2 σ.r (normalDir σ.r) with hc
  have hcpos : 0 < c := det2_normalDir_pos σ.r_ne_zero
  -- choose s larger than every (side σ.r x₀ v)/c
  set M : ℝ := (Finset.univ.image fun k : Fin n => side σ.r x₀ (P.q k) / c).max'
    (by
      refine Finset.image_nonempty.mpr ?_
      exact Finset.univ_nonempty_iff.mpr ⟨⟨0, by have := P.hthree; omega⟩⟩) with hM
  refine ⟨x₀ + (M + 1) • normalDir σ.r, ?_⟩
  intro k
  rw [side_shift]
  have hle : side σ.r x₀ (P.q k) / c ≤ M := by
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  -- side x₀ v ≤ M*c, and (M+1)*c > M*c, so side x₀ v - (M+1)*c < 0
  have h1 : side σ.r x₀ (P.q k) ≤ M * c := by
    rw [div_le_iff₀ hcpos] at hle; exact hle
  have h2 : M * c < (M + 1) * c := by nlinarith
  rw [← hc]; linarith

/-- **A base point with crossing number `0` exists.**  Every polygon and ray admit a
base point whose side-coordinate crossing number vanishes (the "far exterior" point:
all vertices strictly on one side of the ray line through it).  Concrete, complete,
and unconditional — the even-parity anchor for the exterior of any polygon. -/
theorem exists_crossingNumber'_eq_zero (P : StrictSimplePolygon n) (σ : RayDirection P)
    (x₀ : Pt) :
    ∃ x : Pt, CrossingNumber' P σ x = 0 := by
  obtain ⟨x, hx⟩ := exists_far_point_allSide_neg P σ x₀
  exact ⟨x, crossingNumber'_eq_zero_of_allSide_neg P σ x hx⟩

/-! ## Part 3: the `n = 3` leaf — `hull_subset` is the convex-vertex primitive

For a `3`-gon the `hull_subset` half of `BaseTriangleLeaf`
(`closedTri (v0) (v1) (v2) ⊆ region`) is *definitionally* the development's single
planar primitive `IsConvexVertex' Q σ ⟨1⟩` at the middle vertex (the adjacent
triangle of `⟨1⟩` is the whole hull): this is `PolygonOracleClose`'s
`base_subset_iff_convexVertex_one`.  We re-export the bridge in the `Fin 3` /
`v0,v1,v2` form so the leaf module records the exact reduction of its `hull` half. -/

/-- **`hull_subset` (for a fixed `3`-gon) ⟺ the convex-vertex primitive at `⟨1⟩`.**
The `closedTri (v0) (v1) (v2) ⊆ region` half of the triangle leaf is exactly
`IsConvexVertex' Q σ ⟨1⟩` — the irreducible planar primitive assumed throughout
Chapter 36.  (Re-export of `base_subset_iff_convexVertex_one`.) -/
theorem hull_subset_iff_convexVertex_one (Q : StrictSimplePolygon 3) (σ : RayDirection Q) :
    (closedTri (v0 Q) (v1 Q) (v2 Q) ⊆ {x : Pt | ClosedRegion' Q σ x})
      ↔ IsConvexVertex' Q σ (⟨1, by omega⟩ : Fin 3) :=
  base_subset_iff_convexVertex_one Q σ

/-! ## Part 4: assembling `BaseTriangleLeaf` from its two atomic planar residues

The triangle leaf has exactly two halves, each a pure planar (Jordan) fact at the
level the rest of Chapter 36 already keeps as input:

* **`TriangleConvexLeaf`** — for every `3`-gon and ray, the convex-vertex primitive
  at the middle vertex holds (`IsConvexVertex' Q σ ⟨1⟩`).  By
  `hull_subset_iff_convexVertex_one` this *is* the `hull_subset` half.

* **`TriangleExteriorEven`** — for every `3`-gon, ray, and *off-boundary* point
  outside the closed hull, the side-coordinate crossing number is even (so the
  point is not in the region).  This is the `region_subset` half in contrapositive
  form: a region point off the boundary must be in the hull (a boundary point is in
  the hull by the edge/segment containment of the triangle).

Both are bundled as `Prop`-valued named data (exactly the style of every other
Chapter-36 residual — `OffDiagDisjoint`, `BoundaryUnionData`, the `CutGeometry`
fields).  `baseTriangleLeaf_of_atoms` *builds* a genuine `BaseTriangleLeaf` from
them, so the headline's `BaseTriangleLeaf` input is reduced to these two atoms, with
the `hull` half pinned onto the development's single primitive and the `cover` half
reduced to exterior-evenness — for which Parts 1–2 supply the unconditional kernel
(`crossingNumber'_eq_zero_of_allSide_*`, the all-one-side ⟹ even fact). -/

/-- The convex-vertex half of the triangle leaf, as named data over all `3`-gons. -/
def TriangleConvexLeaf : Prop :=
  ∀ (Q : StrictSimplePolygon 3) (σ : RayDirection Q),
    IsConvexVertex' Q σ (⟨1, by omega⟩ : Fin 3)

/-- The exterior-evenness half of the triangle leaf, as named data.  Off the
boundary and outside the closed hull, the crossing number is even. -/
def TriangleExteriorEven : Prop :=
  ∀ (Q : StrictSimplePolygon 3) (σ : RayDirection Q) (x : Pt),
    ¬ OnBoundary Q x → x ∉ closedTri (v0 Q) (v1 Q) (v2 Q) →
    ¬ Odd (CrossingNumber' Q σ x)

/-- **Every boundary point of a `3`-gon lies in the closed hull.**  Each of the three
edges is a segment between two of the hull vertices `v0,v1,v2`, hence contained in
`closedTri v0 v1 v2` by convexity. -/
lemma onBoundary_subset_hull (Q : StrictSimplePolygon 3) {x : Pt}
    (hb : OnBoundary Q x) : x ∈ closedTri (v0 Q) (v1 Q) (v2 Q) := by
  obtain ⟨i, hi⟩ := hb
  -- vertices of the hull
  have hv0 : v0 Q ∈ closedTri (v0 Q) (v1 Q) (v2 Q) :=
    ProofsInTheBook.PolygonConvexVertex.mem_closedTri_left _ _ _
  have hv1 : v1 Q ∈ closedTri (v0 Q) (v1 Q) (v2 Q) :=
    ProofsInTheBook.PolygonConvexVertex.mem_closedTri_mid _ _ _
  have hv2 : v2 Q ∈ closedTri (v0 Q) (v1 Q) (v2 Q) :=
    ProofsInTheBook.PolygonConvexVertex.mem_closedTri_right _ _ _
  -- identify edge i with a segment between two hull vertices
  have hsub : Edge Q.q i ⊆ closedTri (v0 Q) (v1 Q) (v2 Q) := by
    have hcvx : Convex ℝ (closedTri (v0 Q) (v1 Q) (v2 Q)) := closedTri_convex _ _ _
    fin_cases i
    · -- edge 0: seg (q0) (q1) = seg v0 v1
      have : Edge Q.q ⟨0, by omega⟩ = seg (v0 Q) (v1 Q) := by
        unfold Edge v0 v1; norm_num [cyclicNext]
      rw [this, seg]; exact hcvx.segment_subset hv0 hv1
    · -- edge 1: seg (q1) (q2) = seg v1 v2
      have : Edge Q.q ⟨1, by omega⟩ = seg (v1 Q) (v2 Q) := by
        unfold Edge v1 v2; norm_num [cyclicNext]
      rw [this, seg]; exact hcvx.segment_subset hv1 hv2
    · -- edge 2: seg (q2) (q0) = seg v2 v0
      have : Edge Q.q ⟨2, by omega⟩ = seg (v2 Q) (v0 Q) := by
        unfold Edge v2 v0; norm_num [cyclicNext]
      rw [this, seg]; exact hcvx.segment_subset hv2 hv0
  exact hsub hi

/-- **`BaseTriangleLeaf` from the two planar atoms.**  Given the convex-vertex datum
(the `hull` half) and the exterior-evenness datum (the `cover` half), a genuine
`BaseTriangleLeaf` is built.  The `hull_subset` field is `IsConvexVertex'` via
`base_subset_iff_convexVertex_one`; the `region_subset` field is the contrapositive
of exterior-evenness (a region point is either on the boundary — handled by the
boundary clause — or has odd crossing number, hence in the hull). -/
def baseTriangleLeaf_of_atoms
    (hconv : TriangleConvexLeaf) (hext : TriangleExteriorEven) :
    BaseTriangleLeaf where
  hull_subset := by
    intro m Q σ h3
    subst h3
    exact (base_subset_iff_convexVertex_one Q σ).mpr (hconv Q σ)
  region_subset := by
    intro m Q σ h3 x hx
    subst h3
    by_contra hxnot
    -- x in region but not in hull.  If on boundary, the boundary lies in the hull.
    rcases hx with hb | hodd
    · -- on the boundary of a triangle: x ∈ some edge ⊆ hull.
      exact hxnot (onBoundary_subset_hull Q hb)
    · -- odd crossing number off the boundary, outside hull: contradicts exterior-evenness.
      have hbfree : ¬ OnBoundary Q x := by
        intro hbb; exact hxnot (onBoundary_subset_hull Q hbb)
      exact hext Q σ x hbfree hxnot hodd

/-! ## Part 5: the Chapter-36 headline over the reduced leaf surface

Threading `baseTriangleLeaf_of_atoms` through `chapter36_residual_headline`: the
art-gallery `⌊n/3⌋` conclusion now consumes, in place of the opaque
`BaseTriangleLeaf`, exactly its two atomic planar halves — `TriangleConvexLeaf`
(the development's `IsConvexVertex'` primitive, pinned by
`hull_subset_iff_convexVertex_one`) and `TriangleExteriorEven` (the exterior-evenness
half, with the unconditional crossing-number kernels of Parts 1–2 supplying its
inward content).  Everything count/parity is mechanically closed; the `BaseTriangleLeaf`
input is reduced to these two named planar atoms. -/

/-- **Chapter-36 art-gallery headline over the atom-reduced leaf surface.**  Given (a)
the uniform residual geometry data `D` (the planar primitives; union field's
count/parity half already derived), (b) the two triangle-leaf atoms
`TriangleConvexLeaf` + `TriangleExteriorEven` (in place of the bundled
`BaseTriangleLeaf`), and (c) the diagonal-attach peel witness, every strict simple
polygon with a ray direction admits `≤ ⌊n/3⌋` vertex guards seeing its whole closed
region.  Identical strength to `chapter36_residual_headline`, with the leaf input
further decomposed into its two atomic planar halves. -/
theorem chapter36_headline_atom_leaf
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ResidualGeometryData P ρ)
    (hconv : TriangleConvexLeaf) (hext : TriangleExteriorEven)
    (M : DiagonalAttachInput (baseTriangleFacts_of_leaf (baseTriangleLeaf_of_atoms hconv hext)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, Sees P ρ (P.q v) x :=
  chapter36_residual_headline D (baseTriangleLeaf_of_atoms hconv hext) M P ρ

end

end ProofsInTheBook.PolygonLeaf
