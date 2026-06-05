I’ll give a single substrate choice and make the scope explicit: strict simple polygons as the main theorem, with a later collinear-cleanup bridge if you want the fully general textbook wording.

Global recommendation

Build one strict planar-polygon substrate for Chapter A, and let Chapter B use only its lower-level segment/orientation/convexity primitives. Do not make Cauchy rigidity depend on polygon regions, triangulations, or visibility.

For Chapter A, the least painful honest choice is:

represent a polygon by a cyclic vertex tuple with explicit segment-intersection simplicity;

define its closed region by a ray-crossing parity predicate, not by triangulations and not by Jordan;

prove triangulation by ear/diagonal cutting;

expose the final triangulation as finite triangle data for the already-proved combinatorial 3-coloring half.

For Chapter B, use a separate WeakConvexArm/ConvexPolygonalArm structure over vertex tuples and side lengths. It should not mention polygon regions.

0. Basic substrate

Let

lean
abbrev Pt := EuclideanSpace ℝ (Fin 2)

Use these primitive geometric definitions:

lean
def seg (a b : Pt) : Set Pt := segment ℝ a b
def closedTri (a b c : Pt) : Set Pt := convexHull ℝ ({a,b,c} : Set Pt)
def relIntTri (a b c : Pt) : Set Pt := relativeInterior (closedTri a b c)

Add a determinant/orientation layer:

lean
def det2 (u v : Pt) : ℝ
def orient (a b c : Pt) : ℝ := det2 (b - a) (c - a)
def Collinear3 (a b c : Pt) : Prop := orient a b c = 0

You want these before either chapter.

1. Polygon representation

Use a strict simple polygon first.

lean
structure StrictSimplePolygon (n : ℕ) where
  hthree : 3 ≤ n
  q : Fin n → Pt
  injective_q : Function.Injective q

  -- no degenerate consecutive angle
  noncollinear_consecutive :
    ∀ i : Fin n, orient (q (i - 1)) (q i) (q (i + 1)) ≠ 0

  -- edges meet exactly as polygon edges should
  edge_intersection :
    ∀ i j : Fin n,
      EdgeIntersectionCondition q i j

Here EdgeIntersectionCondition q i j should expand to:

if i = j, same edge;

if j = i + 1, then
seg (q i) (q (i+1)) ∩ seg (q j) (q (j+1)) = {q j};

if i = j + 1, then intersection is {q i};

if {i,j} are the first/last cyclic pair, intersection is the corresponding shared endpoint;

otherwise the two closed segments are disjoint.

This explicitly rules out self-crossing, overlapping adjacent edges, repeated vertices, and vertices lying in nonincident edges.

Collinear vertices

Exclude consecutive collinear triples in the main theorem.

This is the right first-pass formalization. It keeps ears nondegenerate, avoids degenerate “triangles” in triangulations, and makes the Fisk visibility step clean.

To recover the fully general textbook headline later, add a preprocessing theorem:

lean
theorem weakSimplePolygon_reduce_collinear :
  WeakSimplePolygon n →
  ∃ m ≤ n, StrictSimplePolygon m ∧ SameClosedRegionAfterRemovingCollinearVertices

Then the guard bound survives because

lean
floor (m / 3) ≤ floor (n / 3).

So the minimal honest first endpoint is:

lean
theorem artGallery_strictSimplePolygon :
  StrictSimplePolygon n → ∃ guards, guards.card ≤ n / 3 ∧ GuardsCoverPolygon guards

with the weak-collinear version as a later corollary.

2. Region without Jordan

Do not define the polygon region as the union of triangles from a triangulation. That makes the Chapter A triangulation theorem circular.

Use a ray-crossing parity region. Package the ray direction as data.

lean
structure RayDirection (P : StrictSimplePolygon n) where
  r : Pt
  r_ne_zero : r ≠ 0
  no_edge_parallel :
    ∀ i : Fin n, det2 r (P.q (i+1) - P.q i) ≠ 0

Define:

lean
def OnBoundary (P : StrictSimplePolygon n) (x : Pt) : Prop :=
  ∃ i : Fin n, x ∈ seg (P.q i) (P.q (i+1))

For ray crossing, use a half-open/oriented convention to avoid double-counting vertices.

lean
def EdgeCrossesRay (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (i : Fin n) : Prop :=
  x ∉ seg (P.q i) (P.q (i+1)) ∧
  RayProperlyCrossesHalfOpenEdge ρ.r x (P.q i) (P.q (i+1))

Then:

lean
def CrossingNumber (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) : ℕ :=
  Finset.card {i : Fin n | EdgeCrossesRay P ρ x i}

def ClosedRegion (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) : Prop :=
  OnBoundary P x ∨ Odd (CrossingNumber P ρ x)

This avoids the Jordan curve theorem completely. You only prove finite segment/ray-crossing facts.

Do not try to prove early that this definition is independent of ρ. It is true, but unnecessary for the chapter. Fix one ρ per polygon.

3. Diagonals and convex vertices

Define a geometric diagonal by region containment and boundary intersection.

lean
def IsDiagonal (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (i j : Fin n) : Prop :=
  i ≠ j ∧
  ¬ CyclicAdjacent i j ∧
  seg (P.q i) (P.q j) ⊆ {x | ClosedRegion P ρ x} ∧
  seg (P.q i) (P.q j) ∩ {x | OnBoundary P x}
    = {P.q i, P.q j}

Define convexity at a vertex using the polygon region, not just the sign of a determinant, because the orientation of the polygon may be clockwise or counterclockwise.

lean
def IsConvexVertex (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n) : Prop :=
  closedTri (P.q (i-1)) (P.q i) (P.q (i+1))
    ⊆ {x | ClosedRegion P ρ x}

You may additionally store the nondegenerate angle fact:

lean
0 < angle (P.q (i-1)) (P.q i) (P.q (i+1)) ∧
angle (P.q (i-1)) (P.q i) (P.q (i+1)) < Real.pi

but the region-containment formulation is the one useful for ear cutting.

4. Convex vertex and diagonal existence

The book proof should be formalized as two lemmas.

First:

lean
lemma exists_convex_vertex
  (P : StrictSimplePolygon n) (ρ : RayDirection P) :
  ∃ i : Fin n, IsConvexVertex P ρ i

Second, the slide argument:

lean
lemma convex_vertex_gives_diagonal_or_ear
  (P : StrictSimplePolygon n) (ρ : RayDirection P)
  (i : Fin n)
  (hconv : IsConvexVertex P ρ i) :
  IsDiagonal P ρ (i-1) (i+1) ∨
  ∃ z : Fin n,
    z ≠ i ∧ z ≠ i-1 ∧ z ≠ i+1 ∧
    P.q z ∈ closedTri (P.q (i-1)) (P.q i) (P.q (i+1)) ∧
    IsDiagonal P ρ i z

This is the Lean version of:

let A = q i,

B = q (i-1),

C = q (i+1);

if BC is clean, then BC is a diagonal;

otherwise choose a last enclosed vertex Z under the slide of BC toward A;

prove AZ is a diagonal.

The “last enclosed vertex” should be formalized by a finite maximum of a height functional.

Let

lean
def heightTowardA (A B C Z : Pt) : ℝ

be the barycentric coordinate of Z in the direction from line BC toward A.

Then state:

lean
lemma slide_last_vertex_exists
  (S : Finset (Fin n))
  (hS : S.Nonempty) :
  ∃ z ∈ S, ∀ w ∈ S,
    heightTowardA A B C (P.q w) ≤ heightTowardA A B C (P.q z)

Tie handling should be isolated in:

lean
lemma slide_last_vertex_visible_from_A
  (hmax : ∀ w ∈ S, heightTowardA A B C (P.q w) ≤ heightTowardA A B C (P.q z)) :
  seg A (P.q z) ⊆ {x | ClosedRegion P ρ x} ∧
  seg A (P.q z) ∩ {x | OnBoundary P x} = {A, P.q z}

This is where almost all ray-crossing and segment-intersection pain lives. Keep it as one geometric lemma.

5. Triangulation representation

Use both forms, but with different roles.

The user-facing/output triangulation should be finite data:

lean
structure GeomTriangulation
    (P : StrictSimplePolygon n) (ρ : RayDirection P) where
  tris : Finset (TriIdx n)

  tri_nondegenerate :
    ∀ T ∈ tris, ¬ Collinear3 (P.q T.1) (P.q T.2) (P.q T.3)

  tri_subset_region :
    ∀ T ∈ tris,
      closedTri (P.q T.1) (P.q T.2) (P.q T.3)
        ⊆ {x | ClosedRegion P ρ x}

  cover_region :
    {x | ClosedRegion P ρ x}
      ⊆ ⋃ T ∈ tris, closedTri (P.q T.1) (P.q T.2) (P.q T.3)

  interior_disjoint :
    ∀ T₁ ∈ tris, ∀ T₂ ∈ tris,
      T₁ ≠ T₂ →
      Disjoint
        (relIntTri (P.q T₁.1) (P.q T₁.2) (P.q T₁.3))
        (relIntTri (P.q T₂.1) (P.q T₂.2) (P.q T₂.3))

  edge_compatibility :
    EveryTriangleEdgeIsBoundaryEdgeOrDiagonal P ρ tris

But the existence proof should use an auxiliary inductive/cutting object:

lean
inductive EarTriangulation :
    (P : StrictSimplePolygon n) → RayDirection P → Type
| triangle :
    n = 3 →
    EarTriangulation P ρ
| cutEar :
    IsDiagonal P ρ (i-1) (i+1) →
    EarTriangulation (P.deleteVertex i) ρ' →
    EarTriangulation P ρ
| splitDiagonal :
    IsDiagonal P ρ i j →
    EarTriangulation (P.subpolygonLeft i j) ρ₁ →
    EarTriangulation (P.subpolygonRight i j) ρ₂ →
    EarTriangulation P ρ

Then prove:

lean
def EarTriangulation.toGeom :
  EarTriangulation P ρ → GeomTriangulation P ρ

This gives the best of both worlds:

existence induction follows the book;

coloring/visibility consumes finite triangle data.

6. Polygon cutting lemmas

For every diagonal, you need two smaller strict simple polygons.

lean
lemma diagonal_split_left_strict
  (hdiag : IsDiagonal P ρ i j) :
  StrictSimplePolygon (leftLength i j)
lean
lemma diagonal_split_right_strict
  (hdiag : IsDiagonal P ρ i j) :
  StrictSimplePolygon (rightLength i j)
lean
lemma diagonal_split_region
  (hdiag : IsDiagonal P ρ i j) :
  {x | ClosedRegion P ρ x}
    =
  {x | ClosedRegion (P.subpolygonLeft i j) ρ₁ x}
    ∪
  {x | ClosedRegion (P.subpolygonRight i j) ρ₂ x}
lean
lemma diagonal_split_region_intersection
  (hdiag : IsDiagonal P ρ i j) :
  {x | ClosedRegion (P.subpolygonLeft i j) ρ₁ x}
    ∩
  {x | ClosedRegion (P.subpolygonRight i j) ρ₂ x}
    =
  seg (P.q i) (P.q j)

For an ear deletion:

lean
lemma ear_delete_strict
  (hdiag : IsDiagonal P ρ (i-1) (i+1)) :
  StrictSimplePolygon (n-1)
lean
lemma ear_delete_region
  (hdiag : IsDiagonal P ρ (i-1) (i+1)) :
  {x | ClosedRegion P ρ x}
    =
  closedTri (P.q (i-1)) (P.q i) (P.q (i+1))
    ∪
  {x | ClosedRegion (P.deleteVertex i) ρ' x}

These region equalities are the substitute for Jordan. They are proved directly from ray-crossing parity and the diagonal intersection conditions.

7. Triangulation existence

Main theorem:

lean
theorem strictSimplePolygon_triangulable
  (P : StrictSimplePolygon n) (ρ : RayDirection P) :
  Nonempty (EarTriangulation P ρ)

Proof by induction on n.

Base n = 3:

lean
lemma triangle_polygon_triangulates
  (P : StrictSimplePolygon 3) :
  EarTriangulation P ρ

Step:

lean
lemma triangulation_step
  (P : StrictSimplePolygon n) (ρ : RayDirection P)
  (hn : 4 ≤ n) :
  ∃ P₁ P₂,
    SmallerPolygon P₁ P ∧
    SmallerPolygon P₂ P ∧
    RegionSplit P P₁ P₂

But in practice the step comes from:

lean
lemma exists_diagonal
  (P : StrictSimplePolygon n) (ρ : RayDirection P)
  (hn : 4 ≤ n) :
  ∃ i j : Fin n, IsDiagonal P ρ i j

derived from exists_convex_vertex and convex_vertex_gives_diagonal_or_ear.

Then split along that diagonal and recurse.

Finally:

lean
theorem strictSimplePolygon_geomTriangulation
  (P : StrictSimplePolygon n) (ρ : RayDirection P) :
  ∃ T : GeomTriangulation P ρ, T.tris.card = n - 2

The n - 2 count is useful for sanity and for matching the combinatorial triangulation theorem, but the guard theorem only needs finite coverage.

8. Visibility

Use the honest definition:

lean
def Sees
  (P : StrictSimplePolygon n) (ρ : RayDirection P)
  (v : Fin n) (x : Pt) : Prop :=
  seg (P.q v) x ⊆ {y | ClosedRegion P ρ y}

Then the key visibility lemma is short:

lean
lemma vertex_sees_point_in_incident_triangle
  (T : GeomTriangulation P ρ)
  (τ ∈ T.tris)
  (hv : v ∈ τ.vertices)
  (hx : x ∈ closedTri (P.q τ.1) (P.q τ.2) (P.q τ.3)) :
  Sees P ρ v x

Proof obligations:

closedTri is convex;

if v is a vertex of τ and x ∈ closedTri τ, then
seg (P.q v) x ⊆ closedTri τ;

T.tri_subset_region τ gives
closedTri τ ⊆ ClosedRegion P ρ.

That is all. No Jordan theorem, no polygon topology.

9. Art gallery bridge

Assume the combinatorial half is already proven:

lean
theorem abstractTriangulation_three_colorable :
  AbstractTriangulation n → ∃ c : Fin n → Fin 3, ProperTriangulationColoring c

Bridge the geometric triangulation to the abstract one:

lean
def GeomTriangulation.toAbstract
  (T : GeomTriangulation P ρ) :
  AbstractTriangulation n

Required lemmas:

lean
lemma geomTriangulation_edges_non_crossing
  (T : GeomTriangulation P ρ) :
  NoncrossingStraightLineEmbedding T.toAbstract
lean
lemma geomTriangulation_faces_are_triangles
  (T : GeomTriangulation P ρ) :
  EveryBoundedFaceTriangle T.toAbstract
lean
lemma geomTriangulation_abstract_vertices
  (T : GeomTriangulation P ρ) :
  T.toAbstract.vertexSet = Finset.univ

Then guard selection:

lean
lemma smallest_color_class_bound
  (c : Fin n → Fin 3) :
  ∃ k : Fin 3, (Finset.univ.filter fun i => c i = k).card ≤ n / 3

Coverage:

lean
lemma every_region_point_lies_in_some_triangle
  (T : GeomTriangulation P ρ)
  (hx : ClosedRegion P ρ x) :
  ∃ τ ∈ T.tris, x ∈ closedTri (P.q τ.1) (P.q τ.2) (P.q τ.3)

Coloring gives an incident guard:

lean
lemma triangle_has_vertex_of_color
  (hproper : ProperTriangulationColoring c)
  (τ ∈ T.tris)
  (k : Fin 3) :
  ∃ v ∈ τ.vertices, c v = k

Then:

lean
theorem artGallery_strict
  (P : StrictSimplePolygon n) (ρ : RayDirection P) :
  ∃ G : Finset (Fin n),
    G.card ≤ n / 3 ∧
    ∀ x : Pt, ClosedRegion P ρ x →
      ∃ g ∈ G, Sees P ρ g x

This is the clean formal endpoint for Fisk.

10. Chapter B: keep arm lemma separate from region machinery

Yes: the Cauchy arm lemma should avoid the polygon-region substrate entirely.

Use a weak convex polygonal arm.

lean
structure WeakConvexArm (n : ℕ) where
  hthree : 3 ≤ n
  q : Fin n → Pt
  injective_q : Function.Injective q

  side_nonzero :
    ∀ i : Fin (n-1), q i.castSucc ≠ q i.succ

  -- all vertices lie in the same closed half-plane of every directed edge,
  -- including the closing edge qₙ q₁
  convex_support :
    ∀ i : Fin n, ∀ k : Fin n,
      0 ≤ orient (q i) (q (i+1)) (q k)

  -- optional strictness for equality theorem
  strict_turns :
    ∀ i : InteriorIndex n,
      0 < angle (q (i-1)) (q i) (q (i+1)) ∧
      angle (q (i-1)) (q i) (q (i+1)) < Real.pi

For the induction and the stuck case, use the weak version internally. For the equality statement, assume strict convexity at the start and prove equality forces all angles equal.

Opening angle:

lean
def openingAngle (A : WeakConvexArm n) (i : InteriorIndex n) : ℝ :=
  angle (A.q (i-1)) (A.q i) (A.q (i+1))

Side lengths:

lean
def sideLength (A : WeakConvexArm n) (i : Fin (n-1)) : ℝ :=
  dist (A.q i.castSucc) (A.q i.succ)

Arm lemma statement:

lean
theorem cauchy_arm
  (A A' : WeakConvexArm n)
  (hsides :
    ∀ i : Fin (n-1), sideLength A i = sideLength A' i)
  (hangles :
    ∀ i : InteriorIndex n,
      openingAngle A i ≤ openingAngle A' i) :
  dist (A.q 0) (A.q (last n))
    ≤ dist (A'.q 0) (A'.q (last n))

Equality version:

lean
theorem cauchy_arm_eq_iff
  (A A' : StrictConvexArm n)
  (hsides : same side lengths)
  (hangles : all openingAngle A i ≤ openingAngle A' i) :
  dist endpoints A = dist endpoints A'
    ↔ ∀ i, openingAngle A i = openingAngle A' i
11. Schoenberg-Zaremba induction

The induction should be on n.

Base case

For n = 3:

lean
lemma cauchy_arm_three
  (a b c a' b' c' : Pt)
  (hab : dist a b = dist a' b')
  (hbc : dist b c = dist b' c')
  (hangle :
    angle a b c ≤ angle a' b' c') :
  dist a c ≤ dist a' c'

Proof: law of cosines plus monotonicity of cos on [0, π].

Needed lemma:

lean
lemma law_cos_endpoint_monotone
  {x x' y θ θ' : ℝ}
  (hx : 0 ≤ x) (hy : 0 ≤ y)
  (hθ : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
  (hθ' : 0 ≤ θ') (hθ'π : θ' ≤ Real.pi)
  (hle : θ ≤ θ') :
  x^2 + y^2 - 2*x*y*Real.cos θ
    ≤
  x^2 + y^2 - 2*x*y*Real.cos θ'

Since cos is decreasing on [0,π].

12. Opening the first angle

Let A = q₁ q₂ ... qₙ.

Define rotation of the tail about q₂.

lean
def openAtSecond
  (A : WeakConvexArm n)
  (θ : ℝ) :
  Fin n → Pt

with:

q₁ fixed;

q₂ fixed;

every qᵢ for i ≥ 3 rotated rigidly about q₂;

the new angle at q₂ is θ.

Package the valid angles:

lean
def AdmissibleOpenAngles
  (A A' : WeakConvexArm n) : Set ℝ :=
  {θ |
    openingAngle A 2 ≤ θ ∧
    θ ≤ openingAngle A' 2 ∧
    WeakConvexArm.ofPoints (openAtSecond A θ)}

The exact invariant maintained is:

the opened tuple remains a weak convex polygonal arm, i.e. all directed edge support inequalities
0 ≤ orient qᵢ qᵢ₊₁ qₖ continue to hold, including the closing edge.

This is the right invariant because it is a finite conjunction of closed determinant inequalities. Therefore the admissible set is closed.

Required lemmas:

lean
lemma admissible_angles_nonempty :
  openingAngle A 2 ∈ AdmissibleOpenAngles A A'
lean
lemma admissible_angles_closed :
  IsClosed (AdmissibleOpenAngles A A')
lean
lemma admissible_angles_bounded :
  AdmissibleOpenAngles A A' ⊆
    Set.Icc (openingAngle A 2) (openingAngle A' 2)
lean
lemma admissible_sup_mem :
  let θ₀ := sSup (AdmissibleOpenAngles A A')
  θ₀ ∈ AdmissibleOpenAngles A A'
13. The “reach target or get stuck” lemma

This is the core Schoenberg-Zaremba geometry lemma.

lean
lemma open_second_reaches_or_stuck
  (A A' : WeakConvexArm n)
  (hsides : same side lengths)
  (hangles : openingAngle A 2 ≤ openingAngle A' 2) :
  let θ₀ := sSup (AdmissibleOpenAngles A A')
  θ₀ = openingAngle A' 2 ∨
  Collinear3
    ((openAtSecond A θ₀) 1)
    ((openAtSecond A θ₀) 0)
    ((openAtSecond A θ₀) (last n))

In book notation, the second case is exactly:

q₂, q₁, qₙ* are collinear.

You should strengthen it to include betweenness:

lean
lemma stuck_betweenness
  (hstuck : Collinear3 q₂ q₁ qₙ*) :
  q₁ ∈ seg q₂ qₙ*

Then:

lean
lemma stuck_endpoint_distance
  (hstuck : q₁ ∈ seg q₂ qₙ*) :
  dist q₁ qₙ* = dist q₂ qₙ* - dist q₂ q₁

This is the exact place where weak convexity is needed. The endpoint gets stuck when the closing support inequality degenerates.

14. Endpoint distance monotonicity during opening

While the tail rotates rigidly about q₂, the distance dist q₂ qₙ is fixed. Therefore dist q₁ qₙ(θ) is governed by the triangle q₁ q₂ qₙ(θ).

lean
lemma open_second_preserves_tail_endpoint_distance
  (θ : ℝ) :
  dist ((openAtSecond A θ) 1) ((openAtSecond A θ) (last n))
    =
  dist (A.q 1) (A.q (last n))
lean
lemma open_second_endpoint_distance_monotone
  {θ η : ℝ}
  (hθ : θ ∈ AdmissibleOpenAngles A A')
  (hη : η ∈ AdmissibleOpenAngles A A')
  (hle : θ ≤ η) :
  dist ((openAtSecond A θ) 0) ((openAtSecond A θ) (last n))
    ≤
  dist ((openAtSecond A η) 0) ((openAtSecond A η) (last n))

Proof: law of cosines applied to triangle

q₁, q₂, qₙ(θ)

and monotonicity of the angle at q₂.

15. If target is reached: shorten the arm

If opening reaches α₂', compare the shortened arms

(q₁, q₃, q₄, ..., qₙ)
(q₁', q₃', q₄', ..., qₙ')

The first side length in the shortened arm is the diagonal q₁q₃. Since the two first triangles have equal adjacent side lengths and equal included angle, the diagonals agree.

lean
lemma shortened_first_side_equal
  (hα₂ : openingAngle A₂ 2 = openingAngle A' 2)
  (hsides : same side lengths) :
  dist q₁ q₃ = dist q₁' q₃'

The new angle at q₃ is the old angle at q₃ minus a triangle-dependent correction. That correction is the same on both sides because triangle q₁q₂q₃ is congruent to triangle q₁'q₂'q₃'.

lean
lemma shortened_angles_le
  (hα₂ : openingAngle A₂ 2 = openingAngle A' 2)
  (hangles : ∀ i, openingAngle A₂ i ≤ openingAngle A' i) :
  ∀ i : InteriorIndex (n-1),
    openingAngle (A₂.shortenSecond) i
      ≤
    openingAngle (A'.shortenSecond) i

Convexity is preserved:

lean
lemma shortenSecond_weakConvex
  (A : WeakConvexArm n) :
  WeakConvexArm (n-1)

Then apply induction.

16. If stuck: drop the first vertex

If opening gets stuck at q₂, q₁, qₙ* collinear, use induction on the tail arms:

(q₂, q₃, ..., qₙ)
(q₂', q₃', ..., qₙ')

Required lemmas:

lean
lemma tail_weakConvex
  (A : WeakConvexArm n) :
  WeakConvexArm (n-1)
lean
lemma tail_side_lengths_equal
  (hsides : same side lengths for A A') :
  same side lengths for A.tail A'.tail
lean
lemma tail_angles_le
  (hangles : ∀ i, openingAngle A i ≤ openingAngle A' i) :
  ∀ i, openingAngle A.tail i ≤ openingAngle A'.tail i

By induction:

lean
dist q₂ qₙ* ≤ dist q₂' qₙ'

Then use the stuck equality and triangle inequality:

lean
dist q₁ qₙ*
  = dist q₂ qₙ* - dist q₂ q₁
  ≤ dist q₂' qₙ' - dist q₂' q₁'
  ≤ dist q₁' qₙ'

The last inequality is just triangle inequality rearranged:

lean
dist q₂' qₙ' ≤ dist q₂' q₁' + dist q₁' qₙ'.

So:

lean
lemma stuck_case_endpoint_le
  (hstuck : q₁ ∈ seg q₂ qₙ*)
  (hind :
    dist q₂ qₙ* ≤ dist q₂' qₙ') :
  dist q₁ qₙ* ≤ dist q₁' qₙ'
17. Dependency-ordered lemma list
Layer A0: Euclidean primitives
lean
lemma det2_antisymm

det2 u v = - det2 v u.

lean
lemma orient_eq_zero_iff_collinear

orient a b c = 0 iff a,b,c are collinear.

lean
lemma segment_convex_subset_triangle

If x ∈ closedTri a b c, then seg a x ⊆ closedTri a b c.

lean
lemma closedTri_convex

closedTri a b c is convex.

lean
lemma segment_intersection_basic

Finite algebraic criteria for intersections of two closed segments in ℝ².

Layer A1: strict simple polygons
lean
def StrictSimplePolygon

Cyclic tuple of distinct vertices with explicit edge-intersection simplicity and no consecutive collinearity.

lean
def OnBoundary

A point lies on one polygon edge.

lean
def RayDirection

A nonzero ray direction not parallel to any polygon edge.

lean
lemma rayDirection_exists

Every strict simple polygon has a ray direction.

lean
def ClosedRegion

Boundary or odd ray-crossing parity.

lean
lemma closedRegion_boundary

Every boundary point lies in ClosedRegion.

lean
lemma closedRegion_edge_segment

Each polygon edge is contained in ClosedRegion.

Layer A2: diagonals
lean
def IsDiagonal

A nonadjacent vertex pair whose segment lies in the closed region and meets the boundary only at its endpoints.

lean
lemma diagonal_segment_subset_region

A diagonal segment is contained in the polygon region.

lean
lemma diagonal_no_boundary_crossing

A diagonal intersects the boundary only at its endpoints.

lean
lemma diagonal_splits_boundary_indices

A diagonal splits the cyclic vertex list into two smaller cyclic lists.

Layer A3: convex vertex and slide lemma
lean
def IsConvexVertex

A vertex whose adjacent triangle lies in the closed region.

lean
lemma exists_convex_vertex

Every strict simple polygon has a convex vertex.

lean
lemma convex_vertex_empty_triangle_gives_ear

If A is convex and no other polygon vertex lies inside triangle BAC, then BC is a diagonal.

lean
lemma slide_last_vertex_exists

If some polygon vertex lies inside triangle BAC, there is a vertex Z maximal under the slide-height functional.

lean
lemma slide_last_vertex_gives_diagonal

The segment AZ is a diagonal.

lean
lemma exists_diagonal

Every strict simple polygon with at least four vertices has a diagonal.

Layer A4: cutting
lean
def subpolygonLeft
def subpolygonRight
def deleteVertex

Polygon operations along a diagonal or ear.

lean
lemma diagonal_split_left_strict

The left subpolygon along a diagonal is strict simple.

lean
lemma diagonal_split_right_strict

The right subpolygon along a diagonal is strict simple.

lean
lemma diagonal_split_region_union

The original closed region is the union of the two subpolygon regions.

lean
lemma diagonal_split_region_intersection

The two subpolygon regions meet exactly on the diagonal segment.

lean
lemma ear_delete_strict

Deleting an ear produces a strict simple polygon.

lean
lemma ear_delete_region_union

The original region is the union of the ear triangle and the smaller polygon region.

Layer A5: triangulation
lean
inductive EarTriangulation

Recursive triangulation by triangle base, ear deletion, and diagonal split.

lean
structure GeomTriangulation

Finite set of nondegenerate vertex triangles covering the closed region with disjoint interiors.

lean
def EarTriangulation.toGeom

Compile recursive triangulation data to finite triangle data.

lean
theorem strictSimplePolygon_triangulable

Every strict simple polygon has an EarTriangulation.

lean
theorem strictSimplePolygon_geomTriangulation

Every strict simple polygon has a GeomTriangulation with n - 2 triangles.

Layer A6: visibility and Fisk
lean
def Sees

A vertex sees a point if the connecting segment is contained in the closed polygon region.

lean
lemma vertex_sees_point_in_incident_triangle

If a point lies in a triangulation triangle and v is one of that triangle’s vertices, then v sees the point.

lean
def GeomTriangulation.toAbstract

Build the abstract triangulation graph from geometric triangle data.

lean
lemma geomTriangulation_toAbstract_valid

The abstract object satisfies the already-proved combinatorial triangulation hypotheses.

lean
lemma every_region_point_in_triangle

Every point of the closed polygon region lies in some geometric triangle.

lean
lemma triangle_has_guard_color

In a proper 3-coloring of a triangulation, every triangle has one vertex of each color.

lean
lemma smallest_color_class_bound

Some color class has size at most n / 3.

lean
theorem artGallery_strict

Every strict simple polygon with n vertices has at most ⌊n/3⌋ vertex guards covering its closed region.

lean
theorem artGallery_weak

Optional later corollary: remove collinear vertices, apply the strict theorem, and transfer the guard set back.

Layer B0: convex arms
lean
structure WeakConvexArm

A vertex tuple q₁,...,qₙ forming a weakly convex polygonal arm, expressed by finite support-halfplane inequalities.

lean
structure StrictConvexArm

A weak convex arm with all relevant opening angles strictly between 0 and π.

lean
def openingAngle

The angle at an interior arm vertex.

lean
def sideLength

The length of each consecutive side.

lean
lemma weakConvex_openingAngle_mem_Icc

Every opening angle of a weak convex arm lies in [0,π].

Layer B1: law of cosines base
lean
lemma law_cos_endpoint_distance

For a triangle, the opposite side squared equals
x^2 + y^2 - 2xy cos θ.

lean
lemma law_cos_endpoint_monotone

With adjacent side lengths fixed, the opposite side is monotone increasing in the included angle on [0,π].

lean
lemma cauchy_arm_three

The arm lemma for three vertices.

Layer B2: opening operation
lean
def openAtSecond

Rotate the tail q₃,...,qₙ rigidly around q₂ so that the angle at q₂ becomes θ.

lean
lemma openAtSecond_preserves_side_lengths

All consecutive side lengths are preserved.

lean
lemma openAtSecond_preserves_tail_angles

All opening angles at vertices q₃,...,qₙ₋₁ are preserved.

lean
lemma openAtSecond_sets_second_angle

The opening angle at q₂ becomes θ.

lean
def AdmissibleOpenAngles

Angles between the original and target second angle for which the opened arm remains weakly convex.

lean
lemma admissible_angles_nonempty

The original second angle is admissible.

lean
lemma admissible_angles_closed

The admissible set is closed because weak convexity is a finite conjunction of closed determinant inequalities.

lean
lemma admissible_sup_mem

The supremum admissible angle is admissible.

lean
lemma open_second_endpoint_distance_monotone

Endpoint distance is nondecreasing while opening the second angle through admissible positions.

Layer B3: reach or stuck
lean
lemma open_second_reaches_or_stuck

The supremum admissible angle either equals the target angle or gives collinearity
q₂, q₁, qₙ*.

lean
lemma stuck_betweenness

In the stuck case, q₁ ∈ seg q₂ qₙ*.

lean
lemma stuck_endpoint_distance

If q₁ ∈ seg q₂ qₙ*, then
dist q₁ qₙ* = dist q₂ qₙ* - dist q₂ q₁.

Layer B4: induction reductions
lean
def tailArm

The arm q₂,...,qₙ.

lean
lemma tailArm_weakConvex

The tail of a weak convex arm is weak convex.

lean
lemma tailArm_sides_angles_inherited

Side lengths and angle inequalities are inherited by tail arms.

lean
def shortenSecond

The shortened arm q₁,q₃,q₄,...,qₙ.

lean
lemma shortenSecond_weakConvex

The shortened arm is weak convex.

lean
lemma shortened_first_side_equal

If the second angles are equal and the first two side lengths agree, then the new first diagonal side lengths agree.

lean
lemma shortened_angles_le

The opening angle inequalities transfer to the shortened arms.

Layer B5: Cauchy arm theorem
lean
theorem cauchy_arm_weak

For weak convex arms with equal side lengths and coordinatewise larger opening angles, endpoint distance is larger.

lean
theorem cauchy_arm_strict_eq_iff

For strict convex arms, equality of endpoint distances holds iff all corresponding opening angles are equal.

Final endpoint split

Use this chapter organization:

lean
theorem strictSimplePolygon_triangulation

for the geometric triangulation theorem.

lean
theorem artGallery_strict

for Fisk’s art-gallery theorem on strict simple polygons.

lean
theorem artGallery_weak

optional bridge for collinear vertices.

lean
theorem cauchy_arm_weak
theorem cauchy_arm_strict_eq_iff

for the planar Cauchy arm lemma.

This keeps the planar-polygon substrate shared, avoids Jordan entirely, and prevents the Cauchy chapter from depending on the art-gallery region/triangulation machinery.