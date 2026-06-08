import ProofsInTheBook.PolygonSubstrate

/-!
# Polygon diagonals and cutting targets for Chapter 36

This file is the A3/A4 continuation point for `PolygonSubstrate`.  The
substrate currently proves the ray-crossing region definition and the
definition of a geometric diagonal.  The genuine planar geometry facts needed
for ear clipping are recorded here as exact named target statements, while the
formally derivable API around them is kept theorem-level and proof-checked.
-/

namespace ProofsInTheBook.PolygonDiagonal

open ProofsInTheBook.PolygonSubstrate
open scoped BigOperators

noncomputable section

/-- A vertex is convex when the closed triangle on its adjacent vertices lies
inside the polygon's closed ray-crossing region. -/
def IsConvexVertex {n : ℕ} (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (i : Fin n) : Prop :=
  closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i))
    ⊆ {x : Pt | ClosedRegion P ρ x}

/-- The closed adjacent triangle at a vertex. -/
def adjacentTriangle {n : ℕ} (P : StrictSimplePolygon n) (i : Fin n) : Set Pt :=
  closedTri (P.q (cyclicPrev i)) (P.q i) (P.q (cyclicNext i))

lemma convex_vertex_triangle_subset_closedRegion {n : ℕ}
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i : Fin n}
    (hconv : IsConvexVertex P ρ i) :
    adjacentTriangle P i ⊆ {x : Pt | ClosedRegion P ρ x} := by
  simpa [IsConvexVertex, adjacentTriangle] using hconv

/-- Vertices other than the convex vertex and its two neighbors that lie in the
closed adjacent triangle. -/
def verticesInAdjacentTriangle {n : ℕ} (P : StrictSimplePolygon n) (i : Fin n) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun z =>
    z ≠ i ∧ z ≠ cyclicPrev i ∧ z ≠ cyclicNext i ∧ P.q z ∈ adjacentTriangle P i

lemma mem_verticesInAdjacentTriangle_iff {n : ℕ} (P : StrictSimplePolygon n)
    (i z : Fin n) :
    z ∈ verticesInAdjacentTriangle P i ↔
      z ≠ i ∧ z ≠ cyclicPrev i ∧ z ≠ cyclicNext i ∧ P.q z ∈ adjacentTriangle P i := by
  classical
  simp [verticesInAdjacentTriangle]

/-- Height functional used by the slide argument.  It is the oriented area
against the base `B C`, normalized by the height of `A`; points on `B C` have
height `0`, and `A` has height `1` when the denominator is nonzero. -/
def heightTowardA (A B C Z : Pt) : ℝ :=
  orient B C Z / orient B C A

@[simp]
lemma orient_base_left (B C : Pt) :
    orient B C B = 0 := by
  unfold orient det2
  simp

@[simp]
lemma orient_base_right (B C : Pt) :
    orient B C C = 0 := by
  unfold orient det2
  simp
  ring

@[simp]
lemma heightTowardA_base_left (A B C : Pt) :
    heightTowardA A B C B = 0 := by
  unfold heightTowardA
  simp

@[simp]
lemma heightTowardA_base_right (A B C : Pt) :
    heightTowardA A B C C = 0 := by
  unfold heightTowardA
  simp

lemma heightTowardA_apex {A B C : Pt} (hA : orient B C A ≠ 0) :
    heightTowardA A B C A = 1 := by
  unfold heightTowardA
  field_simp [hA]

/-- Exact A3 target: every strict simple polygon has a convex vertex. -/
def exists_convex_vertex_statement {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) : Prop :=
  ∃ i : Fin n, IsConvexVertex P ρ i

/-- Exact A3 target: an empty convex adjacent triangle makes the opposite side
an ear diagonal. -/
def convex_vertex_empty_triangle_gives_ear_statement {n : ℕ}
    (P : StrictSimplePolygon n) (ρ : RayDirection P) : Prop :=
  ∀ i : Fin n,
    IsConvexVertex P ρ i →
    (∀ z : Fin n,
      z ≠ i → z ≠ cyclicPrev i → z ≠ cyclicNext i →
        P.q z ∉ adjacentTriangle P i) →
    IsDiagonal P ρ (cyclicPrev i) (cyclicNext i)

/-- Exact A3 finite-maximum target for the slide argument. -/
def slide_last_vertex_exists_statement {n : ℕ}
    (P : StrictSimplePolygon n) (i : Fin n) : Prop :=
  (verticesInAdjacentTriangle P i).Nonempty →
    ∃ z ∈ verticesInAdjacentTriangle P i,
      ∀ w ∈ verticesInAdjacentTriangle P i,
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
          heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)

lemma slide_last_vertex_exists {n : ℕ}
    (P : StrictSimplePolygon n) (i : Fin n)
    (hS : (verticesInAdjacentTriangle P i).Nonempty) :
    ∃ z ∈ verticesInAdjacentTriangle P i,
      ∀ w ∈ verticesInAdjacentTriangle P i,
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
          heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z) := by
  exact Finset.exists_max_image (verticesInAdjacentTriangle P i)
    (fun z =>
      heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)) hS

/-- Exact A3 target: the last vertex under the slide sees the convex vertex by
a diagonal. -/
def slide_last_vertex_gives_diagonal_statement {n : ℕ}
    (P : StrictSimplePolygon n) (ρ : RayDirection P) : Prop :=
  ∀ i z : Fin n,
    IsConvexVertex P ρ i →
    z ∈ verticesInAdjacentTriangle P i →
    (∀ w ∈ verticesInAdjacentTriangle P i,
      heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)) →
    IsDiagonal P ρ i z

/-- Exact A3 target: a strict simple polygon with at least four vertices has a
diagonal. -/
def exists_diagonal_statement {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) : Prop :=
  4 ≤ n → ∃ i j : Fin n, IsDiagonal P ρ i j

/-- Bundle of A3 geometry facts not supplied by `PolygonSubstrate`.  This is a
conditional interface: no fact is assumed globally, but downstream code can ask
for the exact geometry package it needs. -/
structure A3GeometryFacts {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) where
  exists_convex_vertex : exists_convex_vertex_statement P ρ
  convex_vertex_empty_triangle_gives_ear :
    convex_vertex_empty_triangle_gives_ear_statement P ρ
  slide_last_vertex_exists : ∀ i : Fin n, slide_last_vertex_exists_statement P i
  slide_last_vertex_gives_diagonal : slide_last_vertex_gives_diagonal_statement P ρ
  exists_diagonal : exists_diagonal_statement P ρ

lemma exists_convex_vertex_of_facts {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A3GeometryFacts P ρ) :
    ∃ i : Fin n, IsConvexVertex P ρ i :=
  G.exists_convex_vertex

lemma exists_convex_vertex {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A3GeometryFacts P ρ) :
    ∃ i : Fin n, IsConvexVertex P ρ i :=
  exists_convex_vertex_of_facts G

lemma convex_vertex_empty_triangle_gives_ear_of_facts {n : ℕ}
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : A3GeometryFacts P ρ) (i : Fin n)
    (hconv : IsConvexVertex P ρ i)
    (hempty :
      ∀ z : Fin n,
        z ≠ i → z ≠ cyclicPrev i → z ≠ cyclicNext i →
          P.q z ∉ adjacentTriangle P i) :
    IsDiagonal P ρ (cyclicPrev i) (cyclicNext i) :=
  G.convex_vertex_empty_triangle_gives_ear i hconv hempty

lemma convex_vertex_empty_triangle_gives_ear {n : ℕ}
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : A3GeometryFacts P ρ) (i : Fin n)
    (hconv : IsConvexVertex P ρ i)
    (hempty :
      ∀ z : Fin n,
        z ≠ i → z ≠ cyclicPrev i → z ≠ cyclicNext i →
          P.q z ∉ adjacentTriangle P i) :
    IsDiagonal P ρ (cyclicPrev i) (cyclicNext i) :=
  convex_vertex_empty_triangle_gives_ear_of_facts G i hconv hempty

lemma slide_last_vertex_exists_of_facts {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A3GeometryFacts P ρ) (i : Fin n)
    (hS : (verticesInAdjacentTriangle P i).Nonempty) :
    ∃ z ∈ verticesInAdjacentTriangle P i,
      ∀ w ∈ verticesInAdjacentTriangle P i,
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
          heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z) :=
  G.slide_last_vertex_exists i hS

lemma slide_last_vertex_gives_diagonal_of_facts {n : ℕ}
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : A3GeometryFacts P ρ) (i z : Fin n)
    (hconv : IsConvexVertex P ρ i)
    (hz : z ∈ verticesInAdjacentTriangle P i)
    (hmax :
      ∀ w ∈ verticesInAdjacentTriangle P i,
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
          heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)) :
    IsDiagonal P ρ i z :=
  G.slide_last_vertex_gives_diagonal i z hconv hz hmax

lemma slide_last_vertex_gives_diagonal {n : ℕ}
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : A3GeometryFacts P ρ) (i z : Fin n)
    (hconv : IsConvexVertex P ρ i)
    (hz : z ∈ verticesInAdjacentTriangle P i)
    (hmax :
      ∀ w ∈ verticesInAdjacentTriangle P i,
        heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q w) ≤
          heightTowardA (P.q i) (P.q (cyclicPrev i)) (P.q (cyclicNext i)) (P.q z)) :
    IsDiagonal P ρ i z :=
  slide_last_vertex_gives_diagonal_of_facts G i z hconv hz hmax

lemma exists_diagonal_of_facts {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A3GeometryFacts P ρ) (hn : 4 ≤ n) :
    ∃ i j : Fin n, IsDiagonal P ρ i j :=
  G.exists_diagonal hn

lemma exists_diagonal {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A3GeometryFacts P ρ) (hn : 4 ≤ n) :
    ∃ i j : Fin n, IsDiagonal P ρ i j :=
  exists_diagonal_of_facts G hn

/-- Length of the left cyclic subpolygon, including both diagonal endpoints. -/
def leftLength {n : ℕ} (i j : Fin n) : ℕ :=
  cyclicSteps i j + 1

/-- Length of the right cyclic subpolygon, including both diagonal endpoints. -/
def rightLength {n : ℕ} (i j : Fin n) : ℕ :=
  cyclicSteps j i + 1

lemma leftLength_add_rightLength {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    leftLength i j + rightLength i j = n + 2 := by
  unfold leftLength rightLength
  have hsteps := cyclicSteps_add_reverse i j hij
  omega

lemma leftLength_add_rightLength_of_diagonal {n : ℕ}
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j) :
    leftLength i j + rightLength i j = n + 2 :=
  leftLength_add_rightLength i j hdiag.1

lemma leftLength_le_total_of_diagonal {n : ℕ}
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j) :
    leftLength i j ≤ n := by
  unfold leftLength
  have hright_pos : 0 < cyclicSteps j i := cyclicSteps_pos_of_ne j i hdiag.1.symm
  have hsteps := cyclicSteps_add_reverse i j hdiag.1
  omega

lemma rightLength_le_total_of_diagonal {n : ℕ}
    {P : StrictSimplePolygon n} {ρ : RayDirection P} {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j) :
    rightLength i j ≤ n := by
  unfold rightLength
  have hleft_pos : 0 < cyclicSteps i j := cyclicSteps_pos_of_ne i j hdiag.1
  have hsteps := cyclicSteps_add_reverse i j hdiag.1
  omega

/-- Vertex map for the left subpolygon.  The last vertex is the diagonal
endpoint `j`; earlier vertices follow the cyclic arc from `i`. -/
def leftIndex {n : ℕ} (i j : Fin n) (k : Fin (leftLength i j)) : Fin n :=
  if _hk : k.val < cyclicSteps i j then
    ⟨(i.val + k.val) % n,
      Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩
  else j

/-- Vertex map for the right subpolygon. -/
def rightIndex {n : ℕ} (i j : Fin n) (k : Fin (rightLength i j)) : Fin n :=
  if _hk : k.val < cyclicSteps j i then
    ⟨(j.val + k.val) % n,
      Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le j.val) j.isLt)⟩
  else i

/-- Vertex tuple of the left subpolygon along a diagonal. -/
def subpolygonLeftTuple {n : ℕ} (P : StrictSimplePolygon n) (i j : Fin n) :
    Fin (leftLength i j) → Pt :=
  fun k => P.q (leftIndex i j k)

/-- Vertex tuple of the right subpolygon along a diagonal. -/
def subpolygonRightTuple {n : ℕ} (P : StrictSimplePolygon n) (i j : Fin n) :
    Fin (rightLength i j) → Pt :=
  fun k => P.q (rightIndex i j k)

/-- Delete one vertex from the cyclic vertex tuple.  The new tuple is indexed
by `Fin (n - 1)`, so this is useful when `4 ≤ n`. -/
def deleteVertexTuple {n : ℕ} (P : StrictSimplePolygon n) (i : Fin n) :
    Fin (n - 1) → Pt :=
  fun k =>
    if hk : k.val < i.val then
      P.q ⟨k.val, by omega⟩
    else
      P.q ⟨k.val + 1, by
        have hklt : k.val < n - 1 := k.isLt
        omega⟩

/-- Exact A4 target: the left vertex tuple carries a strict simple polygon. -/
def diagonal_split_left_strict_statement {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (i j : Fin n) : Type :=
  IsDiagonal P ρ i j → StrictSimplePolygon (leftLength i j)

/-- Exact A4 target: the right vertex tuple carries a strict simple polygon. -/
def diagonal_split_right_strict_statement {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (i j : Fin n) : Type :=
  IsDiagonal P ρ i j → StrictSimplePolygon (rightLength i j)

/-- Exact A4 target: deleting an ear vertex carries a strict simple polygon. -/
def ear_delete_strict_statement {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (i : Fin n) : Type :=
  IsDiagonal P ρ (cyclicPrev i) (cyclicNext i) → StrictSimplePolygon (n - 1)

/-- Exact A4 target: the original region is the union of the two regions cut
by a diagonal. -/
def diagonal_split_region_union_statement {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (i j : Fin n) : Prop :=
  ∀ (_hdiag : IsDiagonal P ρ i j)
    (PL : StrictSimplePolygon (leftLength i j))
    (PR : StrictSimplePolygon (rightLength i j))
    (ρL : RayDirection PL) (ρR : RayDirection PR),
    PL.q = subpolygonLeftTuple P i j →
    PR.q = subpolygonRightTuple P i j →
    {x : Pt | ClosedRegion P ρ x} =
      {x : Pt | ClosedRegion PL ρL x} ∪ {x : Pt | ClosedRegion PR ρR x}

/-- Exact A4 target: the two subpolygon regions meet exactly along the
diagonal segment. -/
def diagonal_split_region_intersection_statement {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (i j : Fin n) : Prop :=
  ∀ (_hdiag : IsDiagonal P ρ i j)
    (PL : StrictSimplePolygon (leftLength i j))
    (PR : StrictSimplePolygon (rightLength i j))
    (ρL : RayDirection PL) (ρR : RayDirection PR),
    PL.q = subpolygonLeftTuple P i j →
    PR.q = subpolygonRightTuple P i j →
    {x : Pt | ClosedRegion PL ρL x} ∩ {x : Pt | ClosedRegion PR ρR x} =
      seg (P.q i) (P.q j)

/-- Exact A4 target: deleting an ear leaves the deleted polygon plus the ear
triangle as a region union. -/
def ear_delete_region_union_statement {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (i : Fin n) : Prop :=
  ∀ (_hdiag : IsDiagonal P ρ (cyclicPrev i) (cyclicNext i))
    (PD : StrictSimplePolygon (n - 1)) (ρD : RayDirection PD),
    PD.q = deleteVertexTuple P i →
    {x : Pt | ClosedRegion P ρ x} =
      adjacentTriangle P i ∪ {x : Pt | ClosedRegion PD ρD x}

/-- Bundle of A4 cutting facts.  As with A3, this is a conditional interface
for the geometric facts not derivable from the current substrate alone. -/
structure A4CuttingFacts {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) where
  diagonal_split_left_strict :
    ∀ i j : Fin n, diagonal_split_left_strict_statement P ρ i j
  diagonal_split_right_strict :
    ∀ i j : Fin n, diagonal_split_right_strict_statement P ρ i j
  ear_delete_strict :
    ∀ i : Fin n, ear_delete_strict_statement P ρ i
  diagonal_split_region_union :
    ∀ i j : Fin n, diagonal_split_region_union_statement P ρ i j
  diagonal_split_region_intersection :
    ∀ i j : Fin n, diagonal_split_region_intersection_statement P ρ i j
  ear_delete_region_union :
    ∀ i : Fin n, ear_delete_region_union_statement P ρ i

def subpolygonLeft {n : ℕ} {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : A4CuttingFacts P ρ) {i j : Fin n} (hdiag : IsDiagonal P ρ i j) :
    StrictSimplePolygon (leftLength i j) :=
  G.diagonal_split_left_strict i j hdiag

def subpolygonRight {n : ℕ} {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : A4CuttingFacts P ρ) {i j : Fin n} (hdiag : IsDiagonal P ρ i j) :
    StrictSimplePolygon (rightLength i j) :=
  G.diagonal_split_right_strict i j hdiag

def deleteVertex {n : ℕ} {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : A4CuttingFacts P ρ) {i : Fin n}
    (hdiag : IsDiagonal P ρ (cyclicPrev i) (cyclicNext i)) :
    StrictSimplePolygon (n - 1) :=
  G.ear_delete_strict i hdiag

def diagonal_split_left_strict_of_facts {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A4CuttingFacts P ρ) {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j) :
    StrictSimplePolygon (leftLength i j) :=
  G.diagonal_split_left_strict i j hdiag

def diagonal_split_left_strict {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A4CuttingFacts P ρ) {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j) :
    StrictSimplePolygon (leftLength i j) :=
  diagonal_split_left_strict_of_facts G hdiag

def diagonal_split_right_strict_of_facts {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A4CuttingFacts P ρ) {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j) :
    StrictSimplePolygon (rightLength i j) :=
  G.diagonal_split_right_strict i j hdiag

def diagonal_split_right_strict {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A4CuttingFacts P ρ) {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j) :
    StrictSimplePolygon (rightLength i j) :=
  diagonal_split_right_strict_of_facts G hdiag

def ear_delete_strict_of_facts {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A4CuttingFacts P ρ) {i : Fin n}
    (hdiag : IsDiagonal P ρ (cyclicPrev i) (cyclicNext i)) :
    StrictSimplePolygon (n - 1) :=
  G.ear_delete_strict i hdiag

def ear_delete_strict {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A4CuttingFacts P ρ) {i : Fin n}
    (hdiag : IsDiagonal P ρ (cyclicPrev i) (cyclicNext i)) :
    StrictSimplePolygon (n - 1) :=
  ear_delete_strict_of_facts G hdiag

lemma diagonal_split_region_union_of_facts {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A4CuttingFacts P ρ) {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j)
    (PL : StrictSimplePolygon (leftLength i j))
    (PR : StrictSimplePolygon (rightLength i j))
    (ρL : RayDirection PL) (ρR : RayDirection PR)
    (hPL : PL.q = subpolygonLeftTuple P i j)
    (hPR : PR.q = subpolygonRightTuple P i j) :
    {x : Pt | ClosedRegion P ρ x} =
      {x : Pt | ClosedRegion PL ρL x} ∪ {x : Pt | ClosedRegion PR ρR x} :=
  G.diagonal_split_region_union i j hdiag PL PR ρL ρR hPL hPR

lemma diagonal_split_region_union {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A4CuttingFacts P ρ) {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j)
    (PL : StrictSimplePolygon (leftLength i j))
    (PR : StrictSimplePolygon (rightLength i j))
    (ρL : RayDirection PL) (ρR : RayDirection PR)
    (hPL : PL.q = subpolygonLeftTuple P i j)
    (hPR : PR.q = subpolygonRightTuple P i j) :
    {x : Pt | ClosedRegion P ρ x} =
      {x : Pt | ClosedRegion PL ρL x} ∪ {x : Pt | ClosedRegion PR ρR x} :=
  diagonal_split_region_union_of_facts G hdiag PL PR ρL ρR hPL hPR

lemma diagonal_split_region_intersection_of_facts {n : ℕ}
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : A4CuttingFacts P ρ) {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j)
    (PL : StrictSimplePolygon (leftLength i j))
    (PR : StrictSimplePolygon (rightLength i j))
    (ρL : RayDirection PL) (ρR : RayDirection PR)
    (hPL : PL.q = subpolygonLeftTuple P i j)
    (hPR : PR.q = subpolygonRightTuple P i j) :
    {x : Pt | ClosedRegion PL ρL x} ∩ {x : Pt | ClosedRegion PR ρR x} =
      seg (P.q i) (P.q j) :=
  G.diagonal_split_region_intersection i j hdiag PL PR ρL ρR hPL hPR

lemma diagonal_split_region_intersection {n : ℕ}
    {P : StrictSimplePolygon n} {ρ : RayDirection P}
    (G : A4CuttingFacts P ρ) {i j : Fin n}
    (hdiag : IsDiagonal P ρ i j)
    (PL : StrictSimplePolygon (leftLength i j))
    (PR : StrictSimplePolygon (rightLength i j))
    (ρL : RayDirection PL) (ρR : RayDirection PR)
    (hPL : PL.q = subpolygonLeftTuple P i j)
    (hPR : PR.q = subpolygonRightTuple P i j) :
    {x : Pt | ClosedRegion PL ρL x} ∩ {x : Pt | ClosedRegion PR ρR x} =
      seg (P.q i) (P.q j) :=
  diagonal_split_region_intersection_of_facts G hdiag PL PR ρL ρR hPL hPR

lemma ear_delete_region_union_of_facts {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A4CuttingFacts P ρ) {i : Fin n}
    (hdiag : IsDiagonal P ρ (cyclicPrev i) (cyclicNext i))
    (PD : StrictSimplePolygon (n - 1)) (ρD : RayDirection PD)
    (hPD : PD.q = deleteVertexTuple P i) :
    {x : Pt | ClosedRegion P ρ x} =
      adjacentTriangle P i ∪ {x : Pt | ClosedRegion PD ρD x} :=
  G.ear_delete_region_union i hdiag PD ρD hPD

lemma ear_delete_region_union {n : ℕ} {P : StrictSimplePolygon n}
    {ρ : RayDirection P} (G : A4CuttingFacts P ρ) {i : Fin n}
    (hdiag : IsDiagonal P ρ (cyclicPrev i) (cyclicNext i))
    (PD : StrictSimplePolygon (n - 1)) (ρD : RayDirection PD)
    (hPD : PD.q = deleteVertexTuple P i) :
    {x : Pt | ClosedRegion P ρ x} =
      adjacentTriangle P i ∪ {x : Pt | ClosedRegion PD ρD x} :=
  ear_delete_region_union_of_facts G hdiag PD ρD hPD

end

end ProofsInTheBook.PolygonDiagonal
