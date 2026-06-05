import Mathlib

/-!
# Polygon substrate for Chapter 36

This file contains the first three layers of a strict polygon substrate for
the art gallery chapter.  The region is defined by a fixed ray direction and
a half-open crossing convention: an edge contributes once when the ray from
`x` meets the affine edge parameter `u` with `0 ≤ u < 1`.  The endpoint at
`u = 1` is deliberately excluded, so a ray through a polygon vertex is counted
on exactly one incident edge.  Boundary points are added separately to the
closed region.
-/

namespace ProofsInTheBook.PolygonSubstrate

open scoped BigOperators

noncomputable section

/-- The concrete Euclidean plane used by the polygon substrate. -/
abbrev Pt : Type := EuclideanSpace ℝ (Fin 2)

/-- Construct a point from its two coordinates. -/
def mkPt (x y : ℝ) : Pt :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x, y]

/-- Closed segment between two points. -/
def seg (a b : Pt) : Set Pt :=
  segment ℝ a b

/-- Closed triangle spanned by three points. -/
def closedTri (a b c : Pt) : Set Pt :=
  convexHull ℝ ({a, b, c} : Set Pt)

/-- Relative interior of a closed triangle. -/
def relIntTri (a b c : Pt) : Set Pt :=
  interior (closedTri a b c)

/-- The two-by-two determinant in the coordinate basis of `Pt`. -/
def det2 (u v : Pt) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- Oriented area determinant of the triangle `(a,b,c)`. -/
def orient (a b c : Pt) : ℝ :=
  det2 (b - a) (c - a)

/-- Three points are collinear when their oriented area determinant vanishes. -/
def Collinear3 (a b c : Pt) : Prop :=
  orient a b c = 0

lemma det2_antisymm (u v : Pt) :
    det2 u v = -det2 v u := by
  unfold det2
  ring

lemma orient_antisymm (a b c : Pt) :
    orient a c b = -orient a b c := by
  simpa [orient] using det2_antisymm (c - a) (b - a)

lemma orient_eq_zero_iff_collinear (a b c : Pt) :
    orient a b c = 0 ↔ Collinear3 a b c :=
  Iff.rfl

lemma collinear3_iff_orient_eq_zero (a b c : Pt) :
    Collinear3 a b c ↔ orient a b c = 0 :=
  Iff.rfl

lemma closedTri_convex (a b c : Pt) :
    Convex ℝ (closedTri a b c) := by
  exact convex_convexHull ℝ _

lemma segment_convex_subset_triangle {a b c x : Pt}
    (hx : x ∈ closedTri a b c) :
    seg a x ⊆ closedTri a b c := by
  have ha : a ∈ closedTri a b c := by
    exact subset_convexHull ℝ ({a, b, c} : Set Pt) (by simp)
  exact (closedTri_convex a b c).segment_subset ha hx

/--
Finite algebraic data witnessing that two closed segments meet: parameters
`s,t ∈ [0,1]` whose affine line-map points agree.
-/
def SegmentIntersectionParameters (a b c d : Pt) : Prop :=
  ∃ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧ t ∈ Set.Icc (0 : ℝ) 1 ∧
    AffineMap.lineMap a b s = AffineMap.lineMap c d t

lemma segment_intersection_basic (a b c d : Pt) :
    (seg a b ∩ seg c d).Nonempty ↔
      SegmentIntersectionParameters a b c d := by
  constructor
  · rintro ⟨x, hxab, hxcd⟩
    rw [seg, segment_eq_image_lineMap] at hxab
    rw [seg, segment_eq_image_lineMap] at hxcd
    rcases hxab with ⟨s, hs, rfl⟩
    rcases hxcd with ⟨t, ht, hxt⟩
    exact ⟨s, t, hs, ht, hxt.symm⟩
  · rintro ⟨s, t, hs, ht, hst⟩
    refine ⟨AffineMap.lineMap a b s, ?_, ?_⟩
    · rw [seg, segment_eq_image_lineMap]
      exact ⟨s, hs, rfl⟩
    · rw [seg, segment_eq_image_lineMap]
      exact ⟨t, ht, hst.symm⟩

/-- Cyclic successor on `Fin n`, defined without requiring a global `NeZero n`. -/
def cyclicNext {n : ℕ} (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩
  else ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt⟩

/-- Cyclic predecessor on `Fin n`, defined without requiring a global `NeZero n`. -/
def cyclicPrev {n : ℕ} (i : Fin n) : Fin n :=
  if _h : i.val = 0 then
    ⟨n - 1, by omega⟩
  else
    ⟨i.val - 1, by omega⟩

lemma cyclicNext_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    cyclicNext i ≠ i := by
  intro hEq
  unfold cyclicNext at hEq
  split_ifs at hEq with hnext
  · have hv := congrArg Fin.val hEq
    simp at hv
  · have hv := congrArg Fin.val hEq
    simp at hv
    omega

/-- The undirected polygon edge starting at index `i`. -/
def Edge {n : ℕ} (q : Fin n → Pt) (i : Fin n) : Set Pt :=
  seg (q i) (q (cyclicNext i))

/-- Cyclic adjacency of two vertex indices. -/
def CyclicAdjacent {n : ℕ} (i j : Fin n) : Prop :=
  cyclicNext i = j ∨ cyclicNext j = i

/--
Explicit simplicity condition for two polygon edges.  Equal edges intersect
as the same edge, adjacent edges intersect exactly at their shared endpoint,
and nonincident edges are disjoint.
-/
def EdgeIntersectionCondition {n : ℕ} (q : Fin n → Pt) (i j : Fin n) : Prop :=
  if _hsame : i = j then Edge q i ∩ Edge q j = Edge q i
  else if _hnext : cyclicNext i = j then Edge q i ∩ Edge q j = {q j}
  else if _hprev : cyclicNext j = i then Edge q i ∩ Edge q j = {q i}
  else Disjoint (Edge q i) (Edge q j)

/--
A strict simple polygon: a cyclic tuple of distinct vertices, no consecutive
collinearity, and explicit pairwise edge-intersection behavior.
-/
structure StrictSimplePolygon (n : ℕ) where
  hthree : 3 ≤ n
  q : Fin n → Pt
  injective_q : Function.Injective q
  noncollinear_consecutive :
    ∀ i : Fin n, orient (q (cyclicPrev i)) (q i) (q (cyclicNext i)) ≠ 0
  edge_intersection :
    ∀ i j : Fin n, EdgeIntersectionCondition q i j

/-- A point lies on one of the polygon edges. -/
def OnBoundary {n : ℕ} (P : StrictSimplePolygon n) (x : Pt) : Prop :=
  ∃ i : Fin n, x ∈ Edge P.q i

/-- Edge vector from a vertex to its cyclic successor. -/
def edgeVec {n : ℕ} (P : StrictSimplePolygon n) (i : Fin n) : Pt :=
  P.q (cyclicNext i) - P.q i

/-- The slope excluded by a nonvertical edge for directions of the form `(1,t)`. -/
def badSlope (v : Pt) : ℝ :=
  if v 0 = 0 then 0 else v 1 / v 0

lemma det2_mkPt_one (t : ℝ) (v : Pt) :
    det2 (mkPt 1 t) v = v 1 - t * v 0 := by
  unfold det2
  simp [mkPt]

lemma pt_ext_zero_one {v : Pt} (h0 : v 0 = 0) (h1 : v 1 = 0) :
    v = 0 := by
  ext k
  fin_cases k <;> simp [h0, h1]

lemma slope_eq_badSlope_of_det2_mkPt_one_eq_zero {t : ℝ} {v : Pt}
    (hv : v ≠ 0) (hdet : det2 (mkPt 1 t) v = 0) :
    t = badSlope v := by
  rw [det2_mkPt_one] at hdet
  unfold badSlope
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 = 0 := by
      rw [hv0] at hdet
      simpa using hdet
    exact False.elim (hv (pt_ext_zero_one hv0 hv1))
  · simp [hv0]
    field_simp [hv0]
    linarith

lemma edgeVec_ne_zero {n : ℕ} (P : StrictSimplePolygon n) (i : Fin n) :
    edgeVec P i ≠ 0 := by
  intro hzero
  have hpts : P.q (cyclicNext i) = P.q i := sub_eq_zero.mp hzero
  have hind : cyclicNext i = i := P.injective_q hpts
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  exact cyclicNext_ne_self htwo i hind

/-- A ray direction not parallel to any polygon edge. -/
structure RayDirection {n : ℕ} (P : StrictSimplePolygon n) where
  r : Pt
  r_ne_zero : r ≠ 0
  no_edge_parallel :
    ∀ i : Fin n, det2 r (P.q (cyclicNext i) - P.q i) ≠ 0

lemma mkPt_one_ne_zero (t : ℝ) :
    mkPt 1 t ≠ (0 : Pt) := by
  intro h
  have h0 := congrArg (fun p : Pt => p 0) h
  simp [mkPt] at h0

theorem rayDirection_exists {n : ℕ} (P : StrictSimplePolygon n) :
    Nonempty (RayDirection P) := by
  classical
  let bad : Finset ℝ :=
    Finset.univ.image fun i : Fin n => badSlope (edgeVec P i)
  obtain ⟨t, ht⟩ := bad.exists_notMem
  refine ⟨{ r := mkPt 1 t
            r_ne_zero := mkPt_one_ne_zero t
            no_edge_parallel := ?_ }⟩
  intro i hdet
  apply ht
  refine Finset.mem_image.mpr ?_
  refine ⟨i, Finset.mem_univ i, ?_⟩
  exact (slope_eq_badSlope_of_det2_mkPt_one_eq_zero
    (edgeVec_ne_zero P i) hdet).symm

/--
Half-open ray/edge crossing.  The ray starts at `x` and follows direction
`r`; the edge is parameterized from `a` to `b` and contributes only for
`0 ≤ u < 1`.
-/
def RayProperlyCrossesHalfOpenEdge (r x a b : Pt) : Prop :=
  ∃ τ u : ℝ, 0 ≤ τ ∧ 0 ≤ u ∧ u < 1 ∧
    x + τ • r = AffineMap.lineMap a b u

/-- An edge crosses the ray from `x`, excluding the case where `x` is already on it. -/
def EdgeCrossesRay {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (x : Pt) (i : Fin n) : Prop :=
  x ∉ Edge P.q i ∧
    RayProperlyCrossesHalfOpenEdge ρ.r x (P.q i) (P.q (cyclicNext i))

/-- The finite set of edges crossing the fixed half-open ray. -/
def CrossingEdges {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (x : Pt) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => EdgeCrossesRay P ρ x i

/-- The half-open ray crossing number. -/
def CrossingNumber {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (x : Pt) : ℕ :=
  (CrossingEdges P ρ x).card

/-- Closed polygonal region: boundary points plus odd ray-crossing parity. -/
def ClosedRegion {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (x : Pt) : Prop :=
  OnBoundary P x ∨ Odd (CrossingNumber P ρ x)

lemma closedRegion_boundary {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) {x : Pt} (hx : OnBoundary P x) :
    ClosedRegion P ρ x :=
  Or.inl hx

lemma closedRegion_edge_segment {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (i : Fin n) :
    Edge P.q i ⊆ {x : Pt | ClosedRegion P ρ x} := by
  intro x hx
  exact closedRegion_boundary P ρ ⟨i, hx⟩

/--
A diagonal is a nonadjacent vertex pair whose closed segment is contained in
the closed region and whose boundary intersection is exactly its endpoints.
-/
def IsDiagonal {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (i j : Fin n) : Prop :=
  i ≠ j ∧
  ¬ CyclicAdjacent i j ∧
  seg (P.q i) (P.q j) ⊆ {x : Pt | ClosedRegion P ρ x} ∧
  seg (P.q i) (P.q j) ∩ {x : Pt | OnBoundary P x}
    = ({P.q i, P.q j} : Set Pt)

lemma diagonal_segment_subset_region {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j) :
    seg (P.q i) (P.q j) ⊆ {x : Pt | ClosedRegion P ρ x} :=
  hdiag.2.2.1

lemma diagonal_no_boundary_crossing {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j) :
    seg (P.q i) (P.q j) ∩ {x : Pt | OnBoundary P x}
      = ({P.q i, P.q j} : Set Pt) :=
  hdiag.2.2.2

/-- Clockwise edge count from `i` to `j` in the cyclic order. -/
def cyclicSteps {n : ℕ} (i j : Fin n) : ℕ :=
  if i.val ≤ j.val then j.val - i.val else n - i.val + j.val

lemma cyclicSteps_add_reverse {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    cyclicSteps i j + cyclicSteps j i = n := by
  unfold cyclicSteps
  by_cases hle : i.val ≤ j.val
  · have hlt : i.val < j.val := by
      have hne_val : i.val ≠ j.val := by
        intro hv
        exact hij (Fin.ext hv)
      omega
    have hnot : ¬ j.val ≤ i.val := by omega
    simp [hle, hnot]
    omega
  · have hle' : j.val ≤ i.val := by omega
    simp [hle, hle']

lemma cyclicSteps_pos_of_ne {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    0 < cyclicSteps i j := by
  unfold cyclicSteps
  by_cases hle : i.val ≤ j.val
  · have hlt : i.val < j.val := by
      have hne_val : i.val ≠ j.val := by
        intro hv
        exact hij (Fin.ext hv)
      omega
    simp [hle]
    omega
  · simp [hle]

/--
The index-level boundary split supplied by a diagonal: the two cyclic arcs
have positive edge counts, those counts add to the full cycle, and therefore
each arc is smaller than the original boundary cycle.
-/
structure BoundaryIndexSplit {n : ℕ} (i j : Fin n) where
  endpoints_distinct : i ≠ j
  not_adjacent : ¬ CyclicAdjacent i j
  leftSteps : ℕ
  rightSteps : ℕ
  leftSteps_eq : leftSteps = cyclicSteps i j
  rightSteps_eq : rightSteps = cyclicSteps j i
  leftSteps_pos : 0 < leftSteps
  rightSteps_pos : 0 < rightSteps
  steps_add : leftSteps + rightSteps = n
  leftSteps_lt_total : leftSteps < n
  rightSteps_lt_total : rightSteps < n

def diagonalBoundaryIndexSplit {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j) :
    BoundaryIndexSplit i j := by
  let leftSteps := cyclicSteps i j
  let rightSteps := cyclicSteps j i
  have hij : i ≠ j := hdiag.1
  have hnotadj : ¬ CyclicAdjacent i j := hdiag.2.1
  have hleft_pos : 0 < leftSteps := by
    exact cyclicSteps_pos_of_ne i j hij
  have hright_pos : 0 < rightSteps := by
    exact cyclicSteps_pos_of_ne j i hij.symm
  have hadd : leftSteps + rightSteps = n := by
    exact cyclicSteps_add_reverse i j hij
  refine
    { endpoints_distinct := hij
      not_adjacent := hnotadj
      leftSteps := leftSteps
      rightSteps := rightSteps
      leftSteps_eq := rfl
      rightSteps_eq := rfl
      leftSteps_pos := hleft_pos
      rightSteps_pos := hright_pos
      steps_add := hadd
      leftSteps_lt_total := ?_
      rightSteps_lt_total := ?_ }
  · omega
  · omega

lemma diagonal_splits_boundary_indices {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j) :
    Nonempty (BoundaryIndexSplit i j) :=
  ⟨diagonalBoundaryIndexSplit hdiag⟩

end

end ProofsInTheBook.PolygonSubstrate
