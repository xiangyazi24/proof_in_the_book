import Mathlib

/-!
# Tetrahedral decomposition substrate + the Pearls partition (Chapter 9, geometry layer)

This file implements the *simplices-only* geometric substrate for the Pearl/Bricard route to
Hilbert's third problem, as specified in `HANDOFF/CH09_GEOMETRY_DESIGN.md` (sections 1–3).  It is a
self-contained new module: it does **not** touch the abstract algebraic Dehn-invariant layer in
`Chapter09.lean`, nor the planar sector-sum layer in `SectorSum.lean`, nor `PearlLemma.lean` /
`ConeLemma.lean`.  Those layers consume the data produced here.

## Contents

* `Pt3` — ambient `EuclideanSpace ℝ (Fin 3)`.
* `Tet` — a nondegenerate tetrahedron (4 affinely independent vertices); `carrier`, `interior`,
  `relInterior`.  We *define* `Tet.relInterior := interior carrier` and record
  `Tet.relativeInterior_eq_interior` as the definitional unfolding — see the design note below.
* `TetSolid` — a finite family of tetrahedra with pairwise disjoint interiors; `carrier`.
* `TetEquidecomp` — a piece bijection together with per-piece Euclidean isometries (reflections
  allowed) carrying piece carriers to piece carriers.
* `Segment3` — a nondegenerate closed segment; `carrier`, `relInterior`, and the affine coordinate
  `Segment3.coord`.
* `PieceEdges` — the six edges of every tetrahedron, collected over a solid.
* `segmentIntersectionPoints` — a *finite* set capturing the relative-boundary of the intersection
  of two segments (the two extreme points of `e ∩ r` along `e`); designed so that the
  incidence-constancy property below holds.
* `BreakpointsOnEdge`, `Pearls`, and the four partition lemmas:
  - `pearls_finite`
  - `raw_edge_covered_by_pearls`
  - `pearl_interiors_disjoint_on_same_edge`
  - `incidence_constant_on_pearl`  (the heart: incidence into any `r ∈ R` is constant on a pearl).
* `VolumeTetFormula` — the volume formula `|det|/6` as a named proposition.  See the volume design note: Mathlib has no
  off-the-shelf simplex-volume lemma, so this single named statement is isolated as the permitted
  gap and stated as a named `Prop` (no `sorry` in this repo); everything else in the file is proved.

## Design note: relative interior vs. interior

A nondegenerate tetrahedron in `ℝ³` is full-dimensional, so its relative interior (in the sense of
Mathlib's `intrinsicInterior`) coincides with its topological `interior`.  Proving
`intrinsicInterior ℝ T.carrier = interior T.carrier` from the Mathlib API requires showing
`affineSpan ℝ (Set.range T.v) = ⊤`, then transporting along an affine isometry — a real detour.
Since every downstream lemma only ever needs the *topological* interior, we adopt that as the
definition of `Tet.relInterior` and document the identification, exactly as the brief permits.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open scoped Classical
open Set

namespace ProofsInTheBook.TetPearls

/-- Ambient Euclidean 3-space. -/
abbrev Pt3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ## Tetrahedra -/

/-- A (nondegenerate) tetrahedron: four affinely independent points of `Pt3`. -/
structure Tet where
  v : Fin 4 → Pt3
  affIndep : AffineIndependent ℝ v

namespace Tet

/-- The closed carrier of a tetrahedron: the convex hull of its four vertices. -/
def carrier (T : Tet) : Set Pt3 := convexHull ℝ (Set.range T.v)

/-- The topological interior of the carrier.  For a nondegenerate (full-dimensional) tetrahedron
this coincides with the relative interior; we take it as the definition of `relInterior`. -/
def interior (T : Tet) : Set Pt3 := _root_.interior T.carrier

/-- The relative interior of a tetrahedron.  Definitionally the topological interior; see the
module design note for why we do not route through `intrinsicInterior`. -/
def relInterior (T : Tet) : Set Pt3 := T.interior

/-- The relative interior equals the topological interior (here by definition). -/
theorem relativeInterior_eq_interior (T : Tet) :
    T.relInterior = _root_.interior T.carrier := rfl

theorem carrier_convex (T : Tet) : Convex ℝ T.carrier := convex_convexHull _ _

theorem range_finite (T : Tet) : (Set.range T.v).Finite := Set.finite_range _

theorem carrier_compact (T : Tet) : IsCompact T.carrier :=
  (T.range_finite).isCompact_convexHull ℝ

theorem carrier_closed (T : Tet) : IsClosed T.carrier := T.carrier_compact.isClosed

theorem vertex_mem_carrier (T : Tet) (i : Fin 4) : T.v i ∈ T.carrier :=
  subset_convexHull ℝ _ ⟨i, rfl⟩

end Tet

/-! ## Tetrahedral solids -/

/-- A tetrahedral solid: a finite family of tetrahedra with pairwise disjoint interiors. -/
structure TetSolid where
  pieces : Finset Tet
  interior_disjoint :
    ∀ A ∈ pieces, ∀ B ∈ pieces, A ≠ B → Disjoint A.interior B.interior

namespace TetSolid

/-- The carrier of a solid: the union of the carriers of its pieces. -/
def carrier (S : TetSolid) : Set Pt3 := ⋃ T ∈ S.pieces, T.carrier

theorem carrier_closed (S : TetSolid) : IsClosed S.carrier := by
  refine Set.Finite.isClosed_biUnion ?_ (fun T _ => T.carrier_closed)
  exact S.pieces.finite_toSet

theorem carrier_compact (S : TetSolid) : IsCompact S.carrier := by
  refine (S.pieces.finite_toSet).isCompact_biUnion ?_
  exact fun T _ => T.carrier_compact

end TetSolid

/-! ## Equidecomposability (with reflections allowed) -/

/-- An equidecomposition of `P` into `Q`: a bijection of pieces together with, for each piece, a
Euclidean isometry of `Pt3` (a `≃ᵢ`, so reflections are allowed) carrying the carrier of the piece
to the carrier of its image. -/
structure TetEquidecomp (P Q : TetSolid) where
  e : P.pieces ≃ Q.pieces
  iso : P.pieces → (Pt3 ≃ᵢ Pt3)
  maps_piece : ∀ T : P.pieces, (iso T) '' (T : Tet).carrier = ((e T : Tet)).carrier

/-! ## Segments and their affine coordinate -/

/-- A nondegenerate closed segment in `Pt3`. -/
structure Segment3 where
  a : Pt3
  b : Pt3
  hne : a ≠ b

namespace Segment3

/-- Closed carrier of a segment. -/
def carrier (s : Segment3) : Set Pt3 := segment ℝ s.a s.b

/-- Relative (open) interior of a segment. -/
def relInterior (s : Segment3) : Set Pt3 := openSegment ℝ s.a s.b

theorem relInterior_subset_carrier (s : Segment3) : s.relInterior ⊆ s.carrier :=
  openSegment_subset_segment ℝ s.a s.b

theorem a_mem_carrier (s : Segment3) : s.a ∈ s.carrier := left_mem_segment ℝ s.a s.b

theorem b_mem_carrier (s : Segment3) : s.b ∈ s.carrier := right_mem_segment ℝ s.a s.b

/-- The squared length `‖b - a‖² = ⟪b-a, b-a⟫`, which is strictly positive. -/
theorem sub_inner_pos (s : Segment3) :
    0 < (inner ℝ (s.b - s.a) (s.b - s.a) : ℝ) := by
  have hne : s.b - s.a ≠ 0 := sub_ne_zero.mpr (Ne.symm s.hne)
  exact real_inner_self_pos.mpr hne

/-- The affine coordinate of a point along the segment: `coord x = ⟪x - a, b - a⟫ / ‖b-a‖²`.  On the
carrier this returns the barycentric parameter `t ∈ [0,1]` with `x = (1-t)•a + t•b`. -/
def coord (s : Segment3) (x : Pt3) : ℝ :=
  (inner ℝ (x - s.a) (s.b - s.a) : ℝ) / (inner ℝ (s.b - s.a) (s.b - s.a) : ℝ)

/-- The point at coordinate `t` along the segment: `point t = a + t•(b-a) = (1-t)•a + t•b`. -/
def point (s : Segment3) (t : ℝ) : Pt3 := s.a + t • (s.b - s.a)

theorem point_zero (s : Segment3) : s.point 0 = s.a := by simp [point]

theorem point_one (s : Segment3) : s.point 1 = s.b := by
  simp [point]

/-- `coord` is a left inverse of `point`. -/
theorem coord_point (s : Segment3) (t : ℝ) : s.coord (s.point t) = t := by
  have hpos := s.sub_inner_pos
  simp only [coord, point]
  rw [add_sub_cancel_left, real_inner_smul_left]
  field_simp

theorem point_coord_of_mem (s : Segment3) {x : Pt3} (hx : x ∈ s.carrier) :
    s.point (s.coord x) = x := by
  rw [carrier, segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  simp only
  have hpt : (1 - t) • s.a + t • s.b = s.point t := by
    simp only [point]; module
  rw [hpt, coord_point]

/-- `point` maps `[0,1]` into the carrier. -/
theorem point_mem_carrier (s : Segment3) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    s.point t ∈ s.carrier := by
  rw [carrier, segment_eq_image]
  refine ⟨t, ht, ?_⟩
  simp only [point]
  module

/-- On the carrier, `coord` lands in `[0,1]`. -/
theorem coord_mem_Icc (s : Segment3) {x : Pt3} (hx : x ∈ s.carrier) :
    s.coord x ∈ Set.Icc (0:ℝ) 1 := by
  rw [carrier, segment_eq_image] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  simp only
  have h : (1 - t) • s.a + t • s.b = s.point t := by simp only [point]; module
  rw [h, coord_point]; exact ht

/-- `point` is continuous. -/
theorem continuous_point (s : Segment3) : Continuous s.point := by
  unfold point
  fun_prop

/-- `coord` is continuous. -/
theorem continuous_coord (s : Segment3) : Continuous s.coord := by
  unfold coord
  fun_prop

/-- `point` is injective (nondegenerate segment). -/
theorem point_injective (s : Segment3) : Function.Injective s.point := by
  intro t₁ t₂ h
  have := congrArg s.coord h
  rwa [coord_point, coord_point] at this

/-- A segment carrier is compact. -/
theorem carrier_compact (s : Segment3) : IsCompact s.carrier := by
  rw [carrier, ← convexHull_pair]
  exact (Set.toFinite ({s.a, s.b} : Set Pt3)).isCompact_convexHull ℝ

theorem carrier_closed (s : Segment3) : IsClosed s.carrier := s.carrier_compact.isClosed

/-- The intersection of two segment carriers is compact. -/
theorem carrier_inter_compact (e r : Segment3) : IsCompact (e.carrier ∩ r.carrier) :=
  e.carrier_compact.inter_right r.carrier_closed

/-- `carrier` is convex. -/
theorem carrier_convex (s : Segment3) : Convex ℝ s.carrier := convex_segment _ _

/-- The set of coordinates `t ∈ [0,1]` along `e` whose point lies in `r.carrier`.  This is the
preimage description of `e.carrier ∩ r.carrier` in coordinate space. -/
def coordSet (e r : Segment3) : Set ℝ := {t | e.point t ∈ r.carrier} ∩ Set.Icc 0 1

theorem coordSet_subset_Icc (e r : Segment3) : e.coordSet r ⊆ Set.Icc 0 1 :=
  Set.inter_subset_right

/-- A coordinate `t` lies in `coordSet` iff its point lies in both carriers. -/
theorem mem_coordSet_iff (e r : Segment3) (t : ℝ) :
    t ∈ e.coordSet r ↔ e.point t ∈ e.carrier ∩ r.carrier := by
  constructor
  · rintro ⟨hr, ht⟩
    exact ⟨e.point_mem_carrier ht, hr⟩
  · rintro ⟨hc, hr⟩
    refine ⟨hr, ?_⟩
    have : e.coord (e.point t) ∈ Set.Icc (0:ℝ) 1 := e.coord_mem_Icc hc
    rwa [coord_point] at this

/-- `coordSet` is exactly the image of `e.carrier ∩ r.carrier` under `coord`. -/
theorem coord_image_inter (e r : Segment3) :
    e.coord '' (e.carrier ∩ r.carrier) = e.coordSet r := by
  ext t
  constructor
  · rintro ⟨x, ⟨hxe, hxr⟩, rfl⟩
    refine ⟨?_, e.coord_mem_Icc hxe⟩
    show e.point (e.coord x) ∈ r.carrier
    rwa [e.point_coord_of_mem hxe]
  · intro ht
    exact ⟨e.point t, (e.mem_coordSet_iff r t).mp ht, e.coord_point t⟩

/-- `coord` is affine: it respects convex (affine) combinations. -/
theorem coord_affine_comb (e : Segment3) (x y : Pt3) (p q : ℝ) (hpq : p + q = 1) :
    e.coord (p • x + q • y) = p * e.coord x + q * e.coord y := by
  have hden : (inner ℝ (e.b - e.a) (e.b - e.a) : ℝ) ≠ 0 := ne_of_gt e.sub_inner_pos
  simp only [coord]
  have hvec : p • x + q • y - e.a = p • (x - e.a) + q • (y - e.a) := by
    match_scalars <;> linarith [hpq]
  have hnum : (inner ℝ (p • x + q • y - e.a) (e.b - e.a) : ℝ)
      = p * (inner ℝ (x - e.a) (e.b - e.a) : ℝ) + q * (inner ℝ (y - e.a) (e.b - e.a) : ℝ) := by
    rw [hvec, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  rw [hnum]
  field_simp

/-- `coordSet` is convex. -/
theorem coordSet_convex (e r : Segment3) : Convex ℝ (e.coordSet r) := by
  rw [← coord_image_inter]
  have hconv : Convex ℝ (e.carrier ∩ r.carrier) := e.carrier_convex.inter r.carrier_convex
  intro x hx y hy p q hp hq hpq
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨p • x' + q • y', hconv hx' hy' hp hq hpq, ?_⟩
  rw [e.coord_affine_comb _ _ _ _ hpq]
  simp [smul_eq_mul]

/-- `coordSet` is compact. -/
theorem coordSet_compact (e r : Segment3) : IsCompact (e.coordSet r) := by
  rw [← coord_image_inter]
  exact (e.carrier_inter_compact r).image e.continuous_coord

/-- `coordSet` is closed. -/
theorem coordSet_closed (e r : Segment3) : IsClosed (e.coordSet r) :=
  (e.coordSet_compact r).isClosed

/-- `coordSet` is order-connected (a subinterval of `[0,1]`): if `t₁, t₂ ∈ coordSet` with
`t₁ ≤ t₂`, then `[t₁,t₂] ⊆ coordSet`. -/
theorem coordSet_ordConnected (e r : Segment3) : (e.coordSet r).OrdConnected :=
  (convex_iff_ordConnected).mp (e.coordSet_convex r)

/-- If `coordSet` is nonempty it attains a minimum coordinate. -/
theorem exists_min_coord (e r : Segment3) (h : (e.coordSet r).Nonempty) :
    ∃ tmin ∈ e.coordSet r, ∀ t ∈ e.coordSet r, tmin ≤ t := by
  obtain ⟨tmin, hmem, hmin⟩ := (e.coordSet_compact r).exists_isMinOn h continuousOn_id
  exact ⟨tmin, hmem, fun t ht => hmin ht⟩

/-- If `coordSet` is nonempty it attains a maximum coordinate. -/
theorem exists_max_coord (e r : Segment3) (h : (e.coordSet r).Nonempty) :
    ∃ tmax ∈ e.coordSet r, ∀ t ∈ e.coordSet r, t ≤ tmax := by
  obtain ⟨tmax, hmem, hmax⟩ := (e.coordSet_compact r).exists_isMaxOn h continuousOn_id
  exact ⟨tmax, hmem, fun t ht => hmax ht⟩

/-- The finite set of relative-boundary intersection points of two segments along `e`:
the points of `e` at the minimum and maximum coordinate of the (convex, compact) intersection
`e.carrier ∩ r.carrier`, when nonempty; `∅` otherwise.

In the transverse (single-point) case `tmin = tmax`, so this is a singleton.  In the
collinear-overlap case it is the two ends of the overlap.  In every case the coordinates of these
points are exactly the relative boundary of `coordSet`, which is what makes incidence constant on
each pearl. -/
def segmentIntersectionPoints (e r : Segment3) : Finset Pt3 := by
  classical
  exact if h : (e.coordSet r).Nonempty then
    { e.point (e.exists_min_coord r h).choose, e.point (e.exists_max_coord r h).choose }
  else ∅

/-- The minimum-coordinate boundary point lies in `segmentIntersectionPoints`. -/
theorem point_min_mem_intersectionPoints (e r : Segment3) (h : (e.coordSet r).Nonempty) :
    e.point (e.exists_min_coord r h).choose ∈ e.segmentIntersectionPoints r := by
  classical
  simp only [segmentIntersectionPoints, dif_pos h, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- The maximum-coordinate boundary point lies in `segmentIntersectionPoints`. -/
theorem point_max_mem_intersectionPoints (e r : Segment3) (h : (e.coordSet r).Nonempty) :
    e.point (e.exists_max_coord r h).choose ∈ e.segmentIntersectionPoints r := by
  classical
  simp only [segmentIntersectionPoints, dif_pos h, Finset.mem_insert, Finset.mem_singleton]
  tauto

end Segment3

/-! ## Piece edges -/

namespace Tet

/-- A vertex map of a tetrahedron is injective. -/
theorem v_injective (T : Tet) : Function.Injective T.v :=
  T.affIndep.injective

/-- The (ordered, `i < j`) index pairs giving the six edges of a tetrahedron. -/
def edgePairs : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter (fun p => p.1 < p.2)

theorem edgePairs_card : (edgePairs).card = 6 := by decide

/-- The segment of an edge given by an index pair `p` with `p.1 ≠ p.2`. -/
def edgeSeg (T : Tet) (p : Fin 4 × Fin 4) (h : p.1 ≠ p.2) : Segment3 :=
  ⟨T.v p.1, T.v p.2, fun he => h (T.v_injective he)⟩

theorem edgePairs_ne {p : Fin 4 × Fin 4} (hp : p ∈ edgePairs) : p.1 ≠ p.2 :=
  ne_of_lt (Finset.mem_filter.mp hp).2

/-- The six edges of a tetrahedron, as a finite set of segments. -/
def edges (T : Tet) : Finset Segment3 :=
  edgePairs.attach.image (fun p => T.edgeSeg p.1 (edgePairs_ne p.2))

end Tet

/-- All edges of all pieces of a solid (the raw 1-skeleton). -/
def PieceEdges (S : TetSolid) : Finset Segment3 :=
  S.pieces.biUnion (fun T => T.edges)

/-! ## Breakpoints and pearls -/

/-- The breakpoints on a raw edge `e` relative to a finite family `R` of raw edges: the two
endpoints of `e` together with all relative-boundary intersection points with the segments of `R`. -/
def BreakpointsOnEdge (R : Finset Segment3) (e : Segment3) : Finset Pt3 :=
  insert e.a (insert e.b (R.biUnion (fun r => e.segmentIntersectionPoints r)))

theorem a_mem_breakpoints (R : Finset Segment3) (e : Segment3) :
    e.a ∈ BreakpointsOnEdge R e := Finset.mem_insert_self _ _

theorem b_mem_breakpoints (R : Finset Segment3) (e : Segment3) :
    e.b ∈ BreakpointsOnEdge R e :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

/-- The coordinates (along `e`) of the breakpoints on `e`.  Always contains `0` and `1`. -/
def breakCoords (R : Finset Segment3) (e : Segment3) : Finset ℝ :=
  (BreakpointsOnEdge R e).image e.coord

theorem zero_mem_breakCoords (R : Finset Segment3) (e : Segment3) :
    (0 : ℝ) ∈ breakCoords R e := by
  rw [breakCoords]
  refine Finset.mem_image.mpr ⟨e.a, a_mem_breakpoints R e, ?_⟩
  rw [show e.a = e.point 0 by rw [e.point_zero], e.coord_point]

theorem one_mem_breakCoords (R : Finset Segment3) (e : Segment3) :
    (1 : ℝ) ∈ breakCoords R e := by
  rw [breakCoords]
  refine Finset.mem_image.mpr ⟨e.b, b_mem_breakpoints R e, ?_⟩
  rw [show e.b = e.point 1 by rw [e.point_one], e.coord_point]

theorem breakCoords_mem_Icc (R : Finset Segment3) (e : Segment3) {c : ℝ}
    (hc : c ∈ breakCoords R e) : c ∈ Set.Icc (0:ℝ) 1 := by
  rw [breakCoords, Finset.mem_image] at hc
  obtain ⟨x, hx, rfl⟩ := hc
  -- every breakpoint lies on `e.carrier`, so its coord is in `[0,1]`.
  rw [BreakpointsOnEdge] at hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · rw [show e.coord e.a = 0 by rw [show e.a = e.point 0 by rw [e.point_zero], e.coord_point]]
    exact ⟨le_refl 0, zero_le_one⟩
  rcases Finset.mem_insert.mp hx with rfl | hx
  · rw [show e.coord e.b = 1 by rw [show e.b = e.point 1 by rw [e.point_one], e.coord_point]]
    exact ⟨zero_le_one, le_refl 1⟩
  · obtain ⟨r, _, hxr⟩ := Finset.mem_biUnion.mp hx
    -- intersection points have coords in coordSet ⊆ [0,1]
    have hne : (e.coordSet r).Nonempty := by
      by_contra hcon
      simp only [Segment3.segmentIntersectionPoints, dif_neg hcon] at hxr
      exact absurd hxr (Finset.notMem_empty x)
    simp only [Segment3.segmentIntersectionPoints, dif_pos hne, Finset.mem_insert,
      Finset.mem_singleton] at hxr
    rcases hxr with rfl | rfl
    · rw [e.coord_point]
      exact ((e.exists_min_coord r hne).choose_spec.1).2
    · rw [e.coord_point]
      exact ((e.exists_max_coord r hne).choose_spec.1).2

/-- A pearl: a subsegment of a raw edge between two of its breakpoints. The defining data are the
source edge and the two boundary coordinates `lo < hi`; the validity predicate `IsPearlOf` requires
them to be *consecutive* breakpoints. -/
structure Pearl where
  sourceEdge : Segment3
  lo : ℝ
  hi : ℝ

namespace Pearl

/-- The two endpoints of the pearl as points of `Pt3`. -/
def aPt (p : Pearl) : Pt3 := p.sourceEdge.point p.lo
def bPt (p : Pearl) : Pt3 := p.sourceEdge.point p.hi

/-- The closed carrier of a pearl. -/
def carrier (p : Pearl) : Set Pt3 := segment ℝ p.aPt p.bPt

/-- The relative (open) interior of a pearl. -/
def relInterior (p : Pearl) : Set Pt3 := openSegment ℝ p.aPt p.bPt

end Pearl

/-- The validity predicate: `p` is a pearl of the refinement `R` if its source edge is in `R`, its
boundary coordinates are consecutive breakpoints (`lo < hi`, both breakpoints, none strictly
between). -/
def IsPearlOf (R : Finset Segment3) (p : Pearl) : Prop :=
  p.sourceEdge ∈ R ∧
  p.lo ∈ breakCoords R p.sourceEdge ∧
  p.hi ∈ breakCoords R p.sourceEdge ∧
  p.lo < p.hi ∧
  ∀ c ∈ breakCoords R p.sourceEdge, ¬ (p.lo < c ∧ c < p.hi)

/-- The finite set of all pearls of `R`: candidates range over edges of `R` and pairs of their
breakpoint coordinates; we keep the valid (consecutive) ones. -/
def Pearls (R : Finset Segment3) : Finset Pearl := by
  classical
  exact (R.biUnion (fun e =>
    (breakCoords R e ×ˢ breakCoords R e).image (fun c => ⟨e, c.1, c.2⟩))).filter (IsPearlOf R)

theorem mem_Pearls {R : Finset Segment3} {p : Pearl} :
    p ∈ Pearls R ↔ IsPearlOf R p := by
  classical
  unfold Pearls
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨hsrc, hlo, hhi, _, _⟩ := h
    refine Finset.mem_biUnion.mpr ⟨p.sourceEdge, hsrc, ?_⟩
    refine Finset.mem_image.mpr ⟨(p.lo, p.hi), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨hlo, hhi⟩

/-- **Partition lemma (finiteness).** There are finitely many pearls. -/
theorem pearls_finite (R : Finset Segment3) : (Pearls R : Set Pearl).Finite :=
  (Pearls R).finite_toSet

/-- The point of the source edge at coordinate `aPt + θ•(bPt - aPt)` equals `point (lo+θ(hi-lo))`. -/
theorem Pearl.point_combo (p : Pearl) (θ : ℝ) :
    p.aPt + θ • (p.bPt - p.aPt) = p.sourceEdge.point (p.lo + θ * (p.hi - p.lo)) := by
  simp only [Pearl.aPt, Pearl.bPt, Segment3.point]
  match_scalars <;> ring

/-- A point in a pearl's relative interior has source-edge coordinate strictly between `lo` and
`hi`. -/
theorem coord_mem_Ioo_of_mem_relInterior {p : Pearl} {x : Pt3} (hlt : p.lo < p.hi)
    (hx : x ∈ p.relInterior) :
    p.sourceEdge.coord x ∈ Set.Ioo p.lo p.hi := by
  rw [Pearl.relInterior, openSegment_eq_image'] at hx
  obtain ⟨θ, hθ, rfl⟩ := hx
  simp only
  rw [p.point_combo θ, p.sourceEdge.coord_point]
  obtain ⟨hθ0, hθ1⟩ := hθ
  constructor
  · nlinarith [hθ0, hlt]
  · nlinarith [hθ1, hlt]

/-- Conversely, points in a pearl's relative interior lie in the source edge's carrier. -/
theorem relInterior_subset_sourceEdge_carrier (p : Pearl) {R : Finset Segment3}
    (hp : IsPearlOf R p) : p.relInterior ⊆ p.sourceEdge.carrier := by
  obtain ⟨_, hlo, hhi, hlt, _⟩ := hp
  have hloI := breakCoords_mem_Icc R p.sourceEdge hlo
  have hhiI := breakCoords_mem_Icc R p.sourceEdge hhi
  intro x hx
  rw [Pearl.relInterior, openSegment_eq_image'] at hx
  obtain ⟨θ, hθ, rfl⟩ := hx
  simp only
  rw [p.point_combo θ]
  apply p.sourceEdge.point_mem_carrier
  obtain ⟨hθ0, hθ1⟩ := hθ
  obtain ⟨hlo0, hlo1⟩ := hloI
  obtain ⟨hhi0, hhi1⟩ := hhiI
  constructor
  · nlinarith
  · nlinarith

/-- **Partition lemma (ii): disjoint relative interiors.** Distinct pearls of the *same* source
edge have disjoint relative interiors. -/
theorem pearl_interiors_disjoint_on_same_edge {R : Finset Segment3} {p q : Pearl}
    (hp : IsPearlOf R p) (hq : IsPearlOf R q)
    (hedge : p.sourceEdge = q.sourceEdge) (hne : p ≠ q) :
    Disjoint p.relInterior q.relInterior := by
  rw [Set.disjoint_left]
  intro x hxp hxq
  obtain ⟨hp_lo, hp_hi, hp_lt, hp_cons⟩ := hp.2
  obtain ⟨hq_lo, hq_hi, hq_lt, hq_cons⟩ := hq.2
  have hcp := coord_mem_Ioo_of_mem_relInterior hp_lt hxp
  have hcq := coord_mem_Ioo_of_mem_relInterior hq_lt hxq
  rw [hedge] at hcp
  -- the open coord intervals (p.lo,p.hi) and (q.lo,q.hi) overlap at coord x
  obtain ⟨hcp1, hcp2⟩ := hcp
  obtain ⟨hcq1, hcq2⟩ := hcq
  -- Since p ≠ q but same edge, the endpoints differ.
  have hpair : p.lo ≠ q.lo ∨ p.hi ≠ q.hi := by
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    apply hne
    cases p; cases q
    simp_all
  -- transport p's breakpoint facts onto q's source edge
  have hp_lo' : p.lo ∈ breakCoords R q.sourceEdge := hedge ▸ hp_lo
  have hp_hi' : p.hi ∈ breakCoords R q.sourceEdge := hedge ▸ hp_hi
  have hp_cons' : ∀ c ∈ breakCoords R q.sourceEdge, ¬ (p.lo < c ∧ c < p.hi) := by
    intro c hc; exact hp_cons c (hedge ▸ hc)
  rcases hpair with hlo | hhi
  · -- WLOG order the two lo's; the strictly larger lo is a breakpoint strictly inside the other
    rcases lt_or_gt_of_ne hlo with h | h
    · -- p.lo < q.lo : q.lo is a breakpoint with p.lo < q.lo < p.hi (since q.lo < t < p.hi)
      exact hp_cons' q.lo hq_lo ⟨h, lt_trans hcq1 hcp2⟩
    · -- q.lo < p.lo : p.lo is a breakpoint with q.lo < p.lo < q.hi
      exact hq_cons p.lo hp_lo' ⟨h, lt_trans hcp1 hcq2⟩
  · rcases lt_or_gt_of_ne hhi with h | h
    · -- p.hi < q.hi : p.hi is breakpoint with q.lo < p.hi < q.hi
      exact hq_cons p.hi hp_hi' ⟨lt_trans hcq1 hcp2, h⟩
    · -- q.hi < p.hi : q.hi is breakpoint with p.lo < q.hi < p.hi
      exact hp_cons' q.hi hq_hi ⟨lt_trans hcp1 hcq2, h⟩

/-- A point of the source edge lies in `r.carrier` iff its coordinate lies in `coordSet`. -/
theorem point_mem_carrier_iff_coord_mem_coordSet (e r : Segment3) {t : ℝ}
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    e.point t ∈ r.carrier ↔ t ∈ e.coordSet r := by
  constructor
  · intro h; exact ⟨h, ht⟩
  · rintro ⟨h, _⟩; exact h

/-- The minimum coordinate of `coordSet` (when nonempty) is a breakpoint. -/
theorem min_coord_mem_breakCoords {R : Finset Segment3} {e r : Segment3} (hr : r ∈ R)
    (hne : (e.coordSet r).Nonempty) :
    (e.exists_min_coord r hne).choose ∈ breakCoords R e := by
  rw [breakCoords]
  refine Finset.mem_image.mpr ⟨e.point (e.exists_min_coord r hne).choose, ?_, ?_⟩
  · rw [BreakpointsOnEdge]
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    exact Finset.mem_biUnion.mpr ⟨r, hr, e.point_min_mem_intersectionPoints r hne⟩
  · rw [e.coord_point]

/-- The maximum coordinate of `coordSet` (when nonempty) is a breakpoint. -/
theorem max_coord_mem_breakCoords {R : Finset Segment3} {e r : Segment3} (hr : r ∈ R)
    (hne : (e.coordSet r).Nonempty) :
    (e.exists_max_coord r hne).choose ∈ breakCoords R e := by
  rw [breakCoords]
  refine Finset.mem_image.mpr ⟨e.point (e.exists_max_coord r hne).choose, ?_, ?_⟩
  · rw [BreakpointsOnEdge]
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)
    exact Finset.mem_biUnion.mpr ⟨r, hr, e.point_max_mem_intersectionPoints r hne⟩
  · rw [e.coord_point]

/-- **Partition lemma (iii): incidence constancy.** For a pearl `p` of `R` and any raw edge
`r ∈ R`, the relative interior of `p` is either entirely inside `r.carrier` or entirely outside it.

This is the defining property of breakpoints: the set of coordinates whose point lies in `r.carrier`
is a closed subinterval `[tmin,tmax]` whose endpoints are breakpoints; since the pearl interval
`(lo,hi)` contains no breakpoint strictly inside, it lies wholly inside or wholly outside. -/
theorem incidence_constant_on_pearl {R : Finset Segment3} {p : Pearl}
    (hp : IsPearlOf R p) {r : Segment3} (hr : r ∈ R) :
    p.relInterior ⊆ r.carrier ∨ Disjoint p.relInterior r.carrier := by
  obtain ⟨hsrc, hlo, hhi, hlt, hcons⟩ := hp
  have hpFull : IsPearlOf R p := ⟨hsrc, hlo, hhi, hlt, hcons⟩
  set e := p.sourceEdge with he
  by_cases hne : (e.coordSet r).Nonempty
  · -- coordSet = [tmin, tmax] with tmin, tmax breakpoints
    set tmin := (e.exists_min_coord r hne).choose with htmin
    set tmax := (e.exists_max_coord r hne).choose with htmax
    have hmin_mem : tmin ∈ e.coordSet r := (e.exists_min_coord r hne).choose_spec.1
    have hmin_le : ∀ t ∈ e.coordSet r, tmin ≤ t := (e.exists_min_coord r hne).choose_spec.2
    have hmax_mem : tmax ∈ e.coordSet r := (e.exists_max_coord r hne).choose_spec.1
    have hmax_ge : ∀ t ∈ e.coordSet r, t ≤ tmax := (e.exists_max_coord r hne).choose_spec.2
    have htmin_bp : tmin ∈ breakCoords R e := min_coord_mem_breakCoords hr hne
    have htmax_bp : tmax ∈ breakCoords R e := max_coord_mem_breakCoords hr hne
    have hord := e.coordSet_ordConnected r
    -- Decide using whether some relInterior coordinate is in coordSet.
    by_cases hin : (p.lo + (p.hi - p.lo)/2) ∈ e.coordSet r
    · -- midpoint coord in coordSet ⇒ tmin ≤ lo and hi ≤ tmax ⇒ whole interval inside
      left
      -- tmin ≤ lo : otherwise lo < tmin < hi gives breakpoint inside
      have hmid : p.lo < p.lo + (p.hi - p.lo)/2 ∧ p.lo + (p.hi - p.lo)/2 < p.hi := by
        constructor <;> [nlinarith; nlinarith]
      have htmin_le_lo : tmin ≤ p.lo := by
        by_contra hcon
        rw [not_le] at hcon
        have : tmin < p.hi := lt_of_le_of_lt (hmin_le _ hin) hmid.2
        exact hcons tmin htmin_bp ⟨hcon, this⟩
      have htmax_ge_hi : p.hi ≤ tmax := by
        by_contra hcon
        rw [not_le] at hcon
        have : p.lo < tmax := lt_of_lt_of_le hmid.1 (hmax_ge _ hin)
        exact hcons tmax htmax_bp ⟨this, hcon⟩
      intro x hx
      have hco := coord_mem_Ioo_of_mem_relInterior (p := p) hlt hx
      rw [← he] at hco
      obtain ⟨hco1, hco2⟩ := hco
      -- coord x ∈ [tmin,tmax] ⊆ coordSet ⇒ x ∈ r.carrier
      have hcoord_in : e.coord x ∈ e.coordSet r :=
        hord.out hmin_mem hmax_mem ⟨le_trans htmin_le_lo (le_of_lt hco1),
          le_trans (le_of_lt hco2) htmax_ge_hi⟩
      have hxc : x ∈ e.carrier := relInterior_subset_sourceEdge_carrier p hpFull hx
      have := e.point_coord_of_mem hxc
      rw [← this]
      exact hcoord_in.1
    · -- midpoint not in coordSet ⇒ entire interval disjoint
      right
      rw [Set.disjoint_left]
      intro x hxp hxr
      have hco := coord_mem_Ioo_of_mem_relInterior (p := p) hlt hxp
      rw [← he] at hco
      obtain ⟨hco1, hco2⟩ := hco
      have hxc : x ∈ e.carrier := relInterior_subset_sourceEdge_carrier p hpFull hxp
      have hpc := e.point_coord_of_mem hxc
      have hcoord_in : e.coord x ∈ e.coordSet r := by
        refine ⟨?_, e.coord_mem_Icc hxc⟩
        show e.point (e.coord x) ∈ r.carrier
        rw [hpc]; exact hxr
      -- both coord x and midpoint lie in (lo,hi) which is breakpoint-free; coordSet ordConnected
      -- midpoint between tmin..tmax? Show midpoint ∈ coordSet via ordConnected from coord x and bounds.
      -- tmin ≤ coord x and coord x ≤ tmax (membership), so tmin ≤ coord x.
      have htmin_le : tmin ≤ e.coord x := hmin_le _ hcoord_in
      have htmax_ge : e.coord x ≤ tmax := hmax_ge _ hcoord_in
      -- Show tmin ≤ lo and hi ≤ tmax as before (using coord x as witness)
      have htmin_le_lo : tmin ≤ p.lo := by
        by_contra hcon
        rw [not_le] at hcon
        exact hcons tmin htmin_bp ⟨hcon, lt_of_le_of_lt htmin_le hco2⟩
      have htmax_ge_hi : p.hi ≤ tmax := by
        by_contra hcon
        rw [not_le] at hcon
        exact hcons tmax htmax_bp ⟨lt_of_lt_of_le hco1 htmax_ge, hcon⟩
      -- midpoint ∈ [tmin,tmax] ⊆ coordSet, contradicting hin
      apply hin
      refine hord.out hmin_mem hmax_mem ⟨?_, ?_⟩
      · have : p.lo < p.lo + (p.hi - p.lo)/2 := by nlinarith
        linarith [htmin_le_lo]
      · have : p.lo + (p.hi - p.lo)/2 < p.hi := by nlinarith
        linarith [htmax_ge_hi]
  · -- coordSet empty ⇒ no source-edge point lies in r.carrier ⇒ disjoint
    right
    rw [Set.disjoint_left]
    intro x hxp hxr
    have hxc : x ∈ e.carrier := relInterior_subset_sourceEdge_carrier p hpFull hxp
    have hpc := e.point_coord_of_mem hxc
    apply hne
    refine ⟨e.coord x, ?_, e.coord_mem_Icc hxc⟩
    show e.point (e.coord x) ∈ r.carrier
    rw [hpc]; exact hxr

/-- For any coordinate `t ∈ [0,1]` on a raw edge `e ∈ R`, there is a pearl of `R` on `e` whose
coordinate interval `[lo,hi]` contains `t`.  This is the consecutive-breakpoint covering: the
breakpoints (which always include `0` and `1`) cut `[0,1]` into the pearl intervals. -/
theorem exists_pearl_interval_mem {R : Finset Segment3} {e : Segment3} (he : e ∈ R)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ p : Pearl, IsPearlOf R p ∧ p.sourceEdge = e ∧ t ∈ Set.Icc p.lo p.hi := by
  classical
  set B := breakCoords R e with hB
  have h0 : (0:ℝ) ∈ B := zero_mem_breakCoords R e
  have h1 : (1:ℝ) ∈ B := one_mem_breakCoords R e
  have hBIcc : ∀ c ∈ B, c ∈ Set.Icc (0:ℝ) 1 := fun c hc => breakCoords_mem_Icc R e hc
  obtain ⟨ht0, ht1⟩ := ht
  by_cases htlt : t < 1
  · -- lo = greatest breakpoint ≤ t ; hi = least breakpoint > lo
    set Lo := B.filter (fun c => c ≤ t) with hLo
    have hLoNe : Lo.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨h0, ht0⟩⟩
    set lo := Lo.max' hLoNe with hlo
    have hlo_mem : lo ∈ Lo := Finset.max'_mem _ _
    have hlo_B : lo ∈ B := (Finset.mem_filter.mp hlo_mem).1
    have hlo_le_t : lo ≤ t := (Finset.mem_filter.mp hlo_mem).2
    set Hi := B.filter (fun c => lo < c) with hHi
    have hHiNe : Hi.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨h1, lt_of_le_of_lt hlo_le_t htlt⟩⟩
    set hi := Hi.min' hHiNe with hhi
    have hhi_mem : hi ∈ Hi := Finset.min'_mem _ _
    have hhi_B : hi ∈ B := (Finset.mem_filter.mp hhi_mem).1
    have hlo_lt_hi : lo < hi := (Finset.mem_filter.mp hhi_mem).2
    -- t ≤ hi : else hi ≤ t and hi > lo contradicts lo being the max ≤ t
    have ht_le_hi : t ≤ hi := by
      by_contra hcon
      rw [not_le] at hcon
      have : hi ∈ Lo := Finset.mem_filter.mpr ⟨hhi_B, le_of_lt hcon⟩
      exact absurd (Finset.le_max' _ _ this) (not_le.mpr hlo_lt_hi)
    refine ⟨⟨e, lo, hi⟩, ⟨he, hlo_B, hhi_B, hlo_lt_hi, ?_⟩, rfl, ⟨hlo_le_t, ht_le_hi⟩⟩
    intro c hc ⟨hc1, hc2⟩
    -- a breakpoint strictly between lo and hi contradicts hi being least > lo
    have : c ∈ Hi := Finset.mem_filter.mpr ⟨hc, hc1⟩
    exact absurd (Finset.min'_le _ _ this) (not_le.mpr hc2)
  · -- t = 1 : hi = 1, lo = greatest breakpoint < 1
    have ht_eq : t = 1 := le_antisymm ht1 (not_lt.mp htlt)
    set Lo := B.filter (fun c => c < 1) with hLo
    have hLoNe : Lo.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨h0, by norm_num⟩⟩
    set lo := Lo.max' hLoNe with hlo
    have hlo_mem : lo ∈ Lo := Finset.max'_mem _ _
    have hlo_B : lo ∈ B := (Finset.mem_filter.mp hlo_mem).1
    have hlo_lt_one : lo < 1 := (Finset.mem_filter.mp hlo_mem).2
    refine ⟨⟨e, lo, 1⟩, ⟨he, hlo_B, h1, hlo_lt_one, ?_⟩, rfl, ?_⟩
    · intro c hc ⟨hc1, hc2⟩
      have : c ∈ Lo := Finset.mem_filter.mpr ⟨hc, hc2⟩
      exact absurd (Finset.le_max' _ _ this) (not_le.mpr hc1)
    · rw [ht_eq]; exact ⟨le_of_lt hlo_lt_one, le_refl 1⟩

/-- The closed carrier of a pearl, in coordinate terms: it is the image under `point` of `[lo,hi]`.
-/
theorem Pearl.point_mem_carrier_of_mem_Icc (p : Pearl) {t : ℝ}
    (ht : t ∈ Set.Icc p.lo p.hi) : p.sourceEdge.point t ∈ p.carrier := by
  rw [Pearl.carrier, segment_eq_image']
  obtain ⟨hlo, hhi⟩ := ht
  by_cases hdeg : p.hi = p.lo
  · -- degenerate; t = lo = hi
    have : t = p.lo := le_antisymm (hdeg ▸ hhi) hlo
    refine ⟨0, ⟨le_refl 0, zero_le_one⟩, ?_⟩
    simp only [Pearl.aPt, Pearl.bPt, this, zero_smul, add_zero]
  · set θ := (t - p.lo) / (p.hi - p.lo) with hθ
    have hden : 0 < p.hi - p.lo := by
      rcases lt_or_gt_of_ne (Ne.symm hdeg) with h | h
      · linarith
      · exfalso; have := le_trans hlo hhi; linarith
    refine ⟨θ, ⟨?_, ?_⟩, ?_⟩
    · apply div_nonneg (by linarith) (le_of_lt hden)
    · rw [hθ, div_le_one hden]; linarith
    · simp only [Pearl.aPt, Pearl.bPt, Segment3.point]
      have hθval : θ * (p.hi - p.lo) = t - p.lo := by
        rw [hθ]; field_simp
      match_scalars <;> nlinarith [hθval]

/-- **Partition lemma (i): pearls cover the raw edge.** Every raw edge `e ∈ R` is the union of the
closed carriers of its pearls. -/
theorem raw_edge_covered_by_pearls {R : Finset Segment3} {e : Segment3} (he : e ∈ R) :
    e.carrier = ⋃ (p ∈ Pearls R) (_ : p.sourceEdge = e), p.carrier := by
  apply Set.Subset.antisymm
  · -- every edge point lies in a pearl carrier
    intro x hx
    have hxc : e.coord x ∈ Set.Icc (0:ℝ) 1 := e.coord_mem_Icc hx
    obtain ⟨p, hpval, hpedge, hmem⟩ := exists_pearl_interval_mem he hxc
    have hpt : p.sourceEdge.point (e.coord x) = x := by
      rw [hpedge]; exact e.point_coord_of_mem hx
    refine Set.mem_iUnion₂.mpr ⟨p, mem_Pearls.mpr hpval, ?_⟩
    refine Set.mem_iUnion.mpr ⟨hpedge, ?_⟩
    rw [← hpt]
    exact p.point_mem_carrier_of_mem_Icc hmem
  · -- pearl carriers lie inside the edge carrier
    refine Set.iUnion₂_subset (fun p hp => Set.iUnion_subset (fun hpedge => ?_))
    have hpval := mem_Pearls.mp hp
    obtain ⟨_, hlo, hhi, hlt, _⟩ := hpval
    have hloI := breakCoords_mem_Icc R p.sourceEdge hlo
    have hhiI := breakCoords_mem_Icc R p.sourceEdge hhi
    intro x hx
    rw [Pearl.carrier, segment_eq_image'] at hx
    obtain ⟨θ, hθ, rfl⟩ := hx
    simp only
    rw [p.point_combo θ, ← hpedge]
    apply p.sourceEdge.point_mem_carrier
    obtain ⟨hθ0, hθ1⟩ := hθ
    obtain ⟨hlo0, hlo1⟩ := hloI
    obtain ⟨hhi0, hhi1⟩ := hhiI
    exact ⟨by nlinarith, by nlinarith⟩

/-! ## Volume of a tetrahedron

The volume of a nondegenerate tetrahedron is `|det| / 6`, where `det` is the determinant of the
`3 × 3` matrix of the three edge vectors `v₁ - v₀`, `v₂ - v₀`, `v₃ - v₀` (in coordinates).

**Design note (isolated gap).** Mathlib provides volume formulas for *parallelepipeds*
(`MeasureTheory.volume_parallelepiped` / `addHaar_parallelepiped`) and the change-of-variables
`MeasureTheory.addHaar_image_linearMap` (volume scales by `|det|`), but it has **no** off-the-shelf
lemma for the volume of a *simplex* / the convex hull of an affine basis.  Deriving
`volume (simplex) = volume (parallelepiped) / n!` requires the `n`-fold iterated-integral argument
(the standard simplex `{x ≥ 0, ∑ xᵢ ≤ 1}` has volume `1/n!`), which is a substantial standalone
development.  Per the task brief this is the single permitted named-statement gap; everything else in
this file is proved with `0 sorry`.  Downstream, only the *consequence* (the regular tetrahedron and
an equal-volume cube have equal `volume`) is needed, and that is stated against this lemma. -/

/-- The 3×3 matrix of edge vectors `v i - v 0` (rows `i = 1,2,3`, columns the Euclidean
coordinates). -/
def Tet.edgeMatrix (T : Tet) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (T.v i.succ - T.v 0) j

/-- **Volume of a tetrahedron** is `|det of the three edge vectors| / 6`.

Isolated gap, stated as a named proposition (this repo never commits `sorry`) — see the design
note above: Mathlib has no simplex-volume lemma, and the `simplex = parallelepiped / 3!`
reduction is a separate development.  A future file proves this statement and consumes it
where the Chapter 9 headline needs equal volumes. -/
def VolumeTetFormula : Prop :=
  ∀ T : Tet,
    MeasureTheory.volume T.carrier = ENNReal.ofReal (|T.edgeMatrix.det| / 6)

end ProofsInTheBook.TetPearls
