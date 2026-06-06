I’ll treat the counterexample as decisive: the fixed half-open ray predicate defines the wrong region. The repair should replace the crossing convention while preserving the Cramer/affine infrastructure.

The cheapest faithful repair is route 3, but not the symmetric 1/2 + 1/2 rule. Use the classical scanline convention generalized to an arbitrary ray direction:

Count an edge when the ray line intersects the edge’s normal-coordinate span with one side strict and the other weak, and the intersection lies forward on the ray.

Equivalently, replace the old edge-parameter half-open rule

lean
0 ≤ u ∧ u < 1

by a side-coordinate half-open rule

lean
side a ≤ 0 ∧ 0 < side b
  ∨
side b ≤ 0 ∧ 0 < side a

where

lean
side x v := det ρ (v - x)

is the signed side of vertex v relative to the ray line x + ℝρ.

This is the convention designed so that all vertex events are parity-neutral. It fixes the square counterexample without direction quantifiers, without per-use generic rays, and without fractional crossing counts.

1. Ruling on the candidate repairs
1.1 Pointwise-generic region

Mathematically sound, but not the cheapest.

The proposed segment proof contains a false subclaim:

lean
for each segment, all but finitely many ray directions are event-free
along the whole segment

For a fixed polygon vertex v and a nontrivial moving segment S, the set of directions parallel to

lean
v - x,  x ∈ S

is usually an interval of directions, not a finite set. So there is no cofinite set of directions that avoids every vertex-sweep event along the whole segment.

You can still make a pointwise-generic definition work, but then the local-constancy proof becomes a two-parameter perturbation argument. It is much more expensive than changing the crossing convention.

1.2 Per-use generic ray

This does not work robustly.

For a fixed segment S and vertex v, a fixed direction ρ hits v somewhere along the sweep exactly when ρ lies in the pencil of directions from S to v. That pencil is generally a continuum.

Trying to choose ρ so that every vertex-sweep event is of the already-proven neutral type is also not robust. The same-side/opposite-side classification depends on the local geometry at the vertex and on ρ; for a finite list of candidate segments the bad arcs can easily cover all usable directions.

So route 2 is not a safe foundation.

1.3 Symmetric 1/2 endpoint convention

Do not use the naive symmetric rule

lean
interior intersection = 1
endpoint intersection = 1/2

for mod-2 region membership. At a tangent/local-extremum vertex, two incident endpoint hits contribute

lean
1/2 + 1/2 = 1

even though the correct parity contribution should be 0. That rule is natural for some oriented/winding-number treatments, but it is the wrong cheapest repair for mod-2 crossing parity.

Use the classical strict/weak span convention instead.

1.4 Recommended route

Replace the crossing predicate.

Keep:

lean
ClosedRegion x := OnBoundary x ∨ Odd (CrossingNumber ρ x)

but redefine CrossingNumber using the normal-coordinate half-open span rule.

This repairs the defect while preserving most of the existing Cramer and affine-sweep infrastructure.

2. New crossing predicate

Let the polygon vertices be

lean
V : Fin n → Point

with edge

lean
edge i := V i → V (i+1)

where indices are cyclic.

Let

lean
ρ : Vec

be a ray direction satisfying:

lean
ρ ≠ 0
∀ i, det ρ (V (i+1) - V i) ≠ 0

That is, ρ is not parallel to any polygon edge.

For a point x, define the signed side coordinate of a vertex:

lean
def side (ρ : Vec) (x v : Point) : ℚ :=
  det ρ (v - x)

The ray line is:

lean
x + t • ρ

A vertex is on the ray line iff:

lean
side ρ x v = 0.

For edge i, define:

lean
def side₀ (x) := side ρ x (V i)
def side₁ (x) := side ρ x (V (i+1))

The classical half-open span predicate is:

lean
def SpanCrossesSide (ρ : Vec) (x : Point) (i : Fin n) : Prop :=
  (side ρ x (V i) ≤ 0 ∧ 0 < side ρ x (V (i+1))) ∨
  (side ρ x (V (i+1)) ≤ 0 ∧ 0 < side ρ x (V i))

Equivalently, the two endpoints are on different sides of the ray line, with the nonpositive side included and the positive side excluded.

Now define the ray parameter t.

Use the existing Cramer machinery. For edge

lean
A := V i
B := V (i+1)
E := B - A

solve

lean
x + t • ρ = A + u • E.

Since det ρ E ≠ 0, t and u are uniquely defined.

Write:

lean
def rayT (ρ : Vec) (x : Point) (i : Fin n) : ℚ :=
  -- existing Cramer expression

Then define:

lean
def ClassicalRayCrossesEdge
    (P : StrictSimplePolygon)
    (ρ : RayDirection P)
    (x : Point)
    (i : Fin n) : Prop :=
  SpanCrossesSide ρ x i ∧ 0 ≤ rayT ρ x i

and:

lean
def ClassicalCrossingNumber
    (P : StrictSimplePolygon)
    (ρ : RayDirection P)
    (x : Point) : Nat :=
  Finset.card
    (Finset.univ.filter fun i =>
      ClassicalRayCrossesEdge P ρ x i)

Finally:

lean
def ClosedRegion
    (P : StrictSimplePolygon)
    (ρ : RayDirection P)
    (x : Point) : Prop :=
  OnBoundary P x ∨ Odd (ClassicalCrossingNumber P ρ x)

This is still a fixed-ray definition. No generic quantifier is needed.

3. What changes relative to the old half-open rule

The old rule was half-open in the edge parameter:

lean
0 ≤ u ∧ u < 1.

That chooses one of the two incident edges at a vertex by polygon orientation. The square counterexample shows that this choice is not compatible with fixed-ray parity under point motion.

The new rule is half-open in the side coordinate:

lean
side endpoint₀ ≤ 0 < side endpoint₁
∨
side endpoint₁ ≤ 0 < side endpoint₀.

This is the classical scanline rule. It chooses endpoint inclusion by whether the endpoint is on the lower/nonpositive side of the ray line, not by the edge’s local parameterization.

That is exactly what neutralizes vertex events.

4. Core algebraic truth table

Define:

lean
def Span (a b : ℚ) : Prop :=
  (a ≤ 0 ∧ 0 < b) ∨ (b ≤ 0 ∧ 0 < a)

The crucial lemma is:

lean
lemma span_xor_through_vertex
    {a b s : ℚ}
    (ha : a ≠ 0)
    (hb : b ≠ 0) :
  Xor (Span a s) (Span s b) ↔ Span a b

Or in parity-sum form:

lean
lemma span_mod_two_through_vertex
    {a b s : ℚ}
    (ha : a ≠ 0)
    (hb : b ≠ 0) :
  ((if Span a s then 1 else 0)
   +
   (if Span s b then 1 else 0)) % 2
  =
  (if Span a b then 1 else 0)

This is the whole vertex-event repair.

Interpretation:

At a vertex v, let the adjacent non-vertex endpoint side values be

lean
a := side ρ x w
b := side ρ x z
s := side ρ x v

for incident edges

lean
w -- v
v -- z.

Then the parity contribution of the two incident edges is independent of s, even as s changes sign through zero.

Cases:

a,b same sign:
  total contribution is always 0 mod 2.

a,b opposite signs:
  total contribution is always 1 mod 2.

This works at the event itself too, because s = 0 is handled by the weak/strict rule.

This replaces all old same-side/opposite-side vertex lemmas.

5. Forward-ray condition at vertex events

The span truth table handles the infinite ray line. We also need the forward half-ray condition.

For a vertex v on the ray line through x, define:

lean
vertexT ρ x v : ℚ

by:

lean
v = x + vertexT ρ x v • ρ

whenever side ρ x v = 0.

At a boundary-free sweep point, if the ray line hits a polygon vertex, then:

lean
vertexT ρ x v ≠ 0

because vertexT = 0 would mean x = v, hence x lies on the polygon boundary.

So locally around the event:

lean
vertexT > 0

or

lean
vertexT < 0

is constant.

If vertexT < 0, the two incident edge intersections are behind the ray origin near the event, so both are uncounted. Contribution is constantly 0.

If vertexT > 0, the two incident edge intersections are forward near the event, so their parity contribution is governed by the span lemma above.

Formal lemma:

lean
lemma incident_pair_parity_constant_at_vertex
    {w v z : Point}
    {x₀ : Point}
    (hprev : det ρ (v - w) ≠ 0)
    (hnext : det ρ (z - v) ≠ 0)
    (hline : side ρ x₀ v = 0)
    (hw : side ρ x₀ w ≠ 0)
    (hz : side ρ x₀ z ≠ 0)
    (hnotBoundary : x₀ ≠ v) :
  ∃ ε > 0,
    ∀ x,
      ‖x - x₀‖ < ε →
      PairContributionMod2 ρ x (edge w v) (edge v z)
        =
      PairContributionMod2 ρ x₀ (edge w v) (edge v z)

For your affine segment sweep, use the one-dimensional version:

lean
lemma incident_pair_parity_constant_at_vertex_sweep
    (γ : ℚ → Point)
    (hγ_affine : Affine γ)
    (τ₀ : ℚ)
    (hline : side ρ (γ τ₀) v = 0)
    (hnotBoundary : γ τ₀ ≠ v)
    (hw : side ρ (γ τ₀) w ≠ 0)
    (hz : side ρ (γ τ₀) z ≠ 0) :
  ∃ δ > 0,
    ∀ τ,
      |τ - τ₀| < δ →
      PairContributionMod2 ρ (γ τ) (edge w v) (edge v z)
        =
      PairContributionMod2 ρ (γ τ₀) (edge w v) (edge v z)

The proof uses:

side ρ (γ τ) w and side ρ (γ τ) z remain nonzero with constant sign near τ₀;

vertexT ρ (γ τ) v remains nonzero with constant sign because boundary-free excludes γ τ = v;

the span truth table.

6. Local constancy away from vertex events

Most of your existing affine-sweep proof survives.

For an edge i, the crossing predicate now depends on signs of affine functions:

lean
τ ↦ side ρ (γ τ) (V i)
τ ↦ side ρ (γ τ) (V (i+1))
τ ↦ rayT ρ (γ τ) i

Away from zeros of these functions, the truth value of

lean
ClassicalRayCrossesEdge P ρ (γ τ) i

is constant.

The only zero of rayT that matters together with span crossing corresponds to

lean
γ τ ∈ edge i

that is, boundary contact. Along a boundary-free segment this cannot occur.

So the away-from-events lemma becomes:

lean
lemma classical_crossing_const_on_event_free_interval
    (γ : ℚ → Point)
    (hγ_affine : Affine γ)
    (I : Set ℚ)
    (hI_connected : Interval I)
    (hNoVertexLine :
      ∀ τ ∈ I, ∀ v ∈ P.vertices,
        side ρ (γ τ) v ≠ 0)
    (hNoBoundary :
      ∀ τ ∈ I, ¬ OnBoundary P (γ τ)) :
  ∀ τ₁ τ₂ ∈ I,
    ClassicalCrossingNumber P ρ (γ τ₁)
      =
    ClassicalCrossingNumber P ρ (γ τ₂)

This is the same shape as your existing local-constancy-away-from-vertex-events theorem.

7. Handling persistent vertex-on-ray cases

There is one subtlety.

For a moving segment

lean
γ τ = a + τ • d

the function

lean
τ ↦ side ρ (γ τ) v

is affine. It can be identically zero if the entire moving segment lies on a line parallel to ρ through vertex v.

Then v is on the ray line for every τ.

This is not a problem, but it means the “finite event set” proof must classify affine functions into:

lean
identically zero

or

lean
has at most one zero.

For an identically-zero vertex line, the incident-pair contribution is still constant on a boundary-free interval because:

the adjacent endpoint sides are nonzero by ρ not parallel to incident edges;

the forward parameter to v cannot change sign without γ τ = v, which is boundary;

the span truth table at s = 0 applies for every τ.

Formal lemma:

lean
lemma incident_pair_parity_constant_persistent_vertex
    (γ : ℚ → Point)
    (hγ_affine : Affine γ)
    (v : Point)
    (hline_all : ∀ τ ∈ I, side ρ (γ τ) v = 0)
    (hNoBoundary : ∀ τ ∈ I, γ τ ≠ v)
    (hw : ∀ τ ∈ I, side ρ (γ τ) w ≠ 0)
    (hz : ∀ τ ∈ I, side ρ (γ τ) z ≠ 0) :
  ∀ τ₁ τ₂ ∈ I,
    PairContributionMod2 ρ (γ τ₁) (edge w v) (edge v z)
      =
    PairContributionMod2 ρ (γ τ₂) (edge w v) (edge v z)

This is the only new case your previous sweep machinery may not already cover.

8. Simultaneous vertex events

A ray line can pass through multiple polygon vertices at the same sweep parameter, especially if ρ is parallel to a vertex-vertex chord. That is allowed.

At a fixed τ₀, collect all vertices with:

lean
side ρ (γ τ₀) v = 0.

No polygon edge can have both endpoints in this set, because that would imply the edge is parallel to ρ, contradicting RayDirection.

Formal lemma:

lean
lemma no_edge_has_both_endpoints_on_rayLine
    (hρ : RayDirection P ρ)
    {i : Fin n}
    (h₀ : side ρ x (V i) = 0)
    (h₁ : side ρ x (V (i+1)) = 0) :
  False := by
  -- subtract:
  -- det ρ (V(i+1)-x) - det ρ (V i - x)
  -- = det ρ (V(i+1)-V i)
  -- contradiction with nonparallel edge

Therefore the incident-edge pairs around simultaneous vertex events are disjoint. Sum the pairwise parity-neutral lemmas.

lean
lemma all_vertex_events_neutral_at_time
    (γ : ℚ → Point)
    (τ₀ : ℚ)
    (hNoBoundary : ¬ OnBoundary P (γ τ₀)) :
  ∃ δ > 0,
    ∀ τ,
      |τ - τ₀| < δ →
      ClassicalCrossingNumber P ρ (γ τ) % 2
        =
      ClassicalCrossingNumber P ρ (γ τ₀) % 2

This is the direct replacement for the old vertex-event split into backward/same-side/opposite-side cases.

9. Main local-constancy theorem

Now prove:

lean
theorem classical_parity_const_on_boundary_free_segment
    (P : StrictSimplePolygon)
    (ρ : RayDirection P)
    (a b : Point)
    (hBoundaryFree :
      ∀ τ, 0 ≤ τ → τ ≤ 1 →
        ¬ OnBoundary P ((1 - τ) • a + τ • b)) :
  ∀ τ₁ τ₂,
    0 ≤ τ₁ → τ₁ ≤ 1 →
    0 ≤ τ₂ → τ₂ ≤ 1 →
    ClassicalCrossingNumber P ρ ((1 - τ₁) • a + τ₁ • b) % 2
      =
    ClassicalCrossingNumber P ρ ((1 - τ₂) • a + τ₂ • b) % 2

Proof outline:

Let

lean
γ τ := (1 - τ) • a + τ • b

For every vertex v, the function

lean
τ ↦ side ρ (γ τ) v

is affine.

Split vertices into:

persistent vertices: side function identically zero;

isolated-event vertices: at most one zero.

The isolated-event parameters form a finite set.

On each open interval between event parameters, every edge-crossing predicate is constant by the event-free lemma.

At each event parameter, the total parity is unchanged by all_vertex_events_neutral_at_time.

Persistent vertices contribute constantly by the persistent-vertex lemma.

Chain the equalities across the finite partition.

This yields segment-wise local constancy of the corrected parity region.

10. Boundary crossing theorem

The corrected region is:

lean
ClosedRegion x :=
  OnBoundary P x ∨ Odd (ClassicalCrossingNumber P ρ x)

Then from the parity-constancy theorem:

lean
theorem closedRegion_const_on_boundary_free_segment
    (hBoundaryFree :
      ∀ τ, 0 ≤ τ → τ ≤ 1 →
        ¬ OnBoundary P ((1 - τ) • a + τ • b)) :
  ClosedRegion P ρ a ↔ ClosedRegion P ρ b := by
  have hparity :=
    classical_parity_const_on_boundary_free_segment
      P ρ a b hBoundaryFree 0 1
      (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)

  simp [ClosedRegion]
  have hA : ¬ OnBoundary P a := by
    simpa using hBoundaryFree 0 (by norm_num) (by norm_num)
  have hB : ¬ OnBoundary P b := by
    simpa using hBoundaryFree 1 (by norm_num) (by norm_num)
  simp [hA, hB]
  exact odd_iff_odd_of_mod_two_eq hparity

This is the theorem your A3/A4 proofs wanted from the old fixed-ray parity region.

11. Migration plan
11.1 Survives verbatim

These layers should survive essentially unchanged:

lean
StrictSimplePolygon
RayDirection ρ not parallel to any edge
det / Cramer algebra
affine sweep infrastructure
boundary predicate
segment boundary-free definitions
finite vertex/edge indexing API

The Cramer solver itself survives because the line-edge intersection equations are unchanged.

11.2 Needs small edits

The old crossing predicate:

lean
0 ≤ u ∧ u < 1 ∧ 0 ≤ t

becomes:

lean
SpanCrossesSide ρ x i ∧ 0 ≤ rayT ρ x i

So Cramer characterization should be split into two lemmas:

lean
lemma cramer_ray_line_intersection :
  x + rayT ρ x i • ρ
    =
  V i + edgeU ρ x i • (V (i+1) - V i)

and:

lean
lemma spanCrossesSide_iff_edgeU_in_closed_segment_with_classical_endpoint :
  SpanCrossesSide ρ x i
    ↔
  -- the line intersects the edge segment, with the classical
  -- lower-included/upper-excluded endpoint convention

You no longer want to normalize everything to:

lean
0 ≤ u ∧ u < 1.

That was the source of the defect.

11.3 Reprove

Discard and replace the old vertex-event lemmas:

lean
backward neutral
same-side forward neutral
opposite-side forward case

with the single span truth-table lemma:

lean
span_mod_two_through_vertex

and its geometric consequence:

lean
incident_pair_parity_constant_at_vertex_sweep

This removes the same-side/opposite-side distinction entirely.

11.4 Reprove final local constancy

Reprove:

lean
parity_const_on_boundary_free_segment
closedRegion_const_on_boundary_free_segment

using the corrected vertex-event theorem.

The proof shape is the same as before; the event lemma is stronger and cleaner.

12. Dependency-ordered lemma chain

Implement in this order.

Layer 1: side-coordinate crossing
lean
side :
  Vec → Point → Point → ℚ

Span :
  ℚ → ℚ → Prop

SpanCrossesSide :
  RayDirection P → Point → Fin n → Prop

rayT :
  RayDirection P → Point → Fin n → ℚ

ClassicalRayCrossesEdge :
  P → ρ → Point → Fin n → Prop

ClassicalCrossingNumber :
  P → ρ → Point → Nat

ClosedRegion :
  P → ρ → Point → Prop

Definitions:

lean
Span a b :=
  (a ≤ 0 ∧ 0 < b) ∨ (b ≤ 0 ∧ 0 < a)

SpanCrossesSide ρ x i :=
  Span (side ρ x (V i)) (side ρ x (V (i+1)))
Layer 2: Cramer compatibility
lean
rayT_cramer :
  x + rayT ρ x i • ρ
    =
  V i + edgeU ρ x i • (V (i+1) - V i)

spanCrossesSide_iff_classical_segment_hit :
  SpanCrossesSide ρ x i ↔
    ClassicalHalfOpenSegmentHitInSideCoordinate ρ x i

classicalRayCrosses_iff_exists_intersection :
  ClassicalRayCrossesEdge P ρ x i ↔
    ∃ t u,
      0 ≤ t ∧
      ClassicalSideSpanU ρ x i u ∧
      x + t • ρ = V i + u • edgeVec i

The old Cramer algebra is reused here.

Layer 3: algebraic vertex truth table
lean
span_xor_through_vertex :
  a ≠ 0 →
  b ≠ 0 →
  Xor (Span a s) (Span s b) ↔ Span a b

or:

lean
span_mod_two_through_vertex :
  a ≠ 0 →
  b ≠ 0 →
  ((if Span a s then 1 else 0)
   +
   (if Span s b then 1 else 0)) % 2
  =
  (if Span a b then 1 else 0)

Also useful:

lean
span_false_same_nonpos :
  a < 0 → b < 0 → ¬ Span a b

span_false_same_pos :
  0 < a → 0 < b → ¬ Span a b

span_true_neg_pos :
  a < 0 → 0 < b → Span a b

span_true_pos_neg :
  0 < a → b < 0 → Span a b
Layer 4: nonparallel edge facts
lean
no_adjacent_vertices_both_on_rayLine :
  RayDirection P ρ →
  side ρ x (V i) = 0 →
  side ρ x (V (i+1)) = 0 →
  False

incident_other_endpoint_not_on_rayLine :
  RayDirection P ρ →
  side ρ x (V i) = 0 →
  side ρ x (V (i-1)) ≠ 0 ∧
  side ρ x (V (i+1)) ≠ 0

These come from:

lean
side ρ x b - side ρ x a = det ρ (b - a)

and ρ not parallel to edges.

Layer 5: event-free edge constancy
lean
classical_crossing_edge_const_on_sign_cell :
  signs of side endpoints and rayT are constant on I →
  ClassicalRayCrossesEdge P ρ (γ τ) i is constant on I

Then:

lean
classical_crossing_number_const_on_event_free_interval :
  no vertex side zero on I →
  boundary-free on I →
  ClassicalCrossingNumber parity is constant on I
Layer 6: vertex-event neutrality

For an isolated vertex event:

lean
incident_pair_parity_constant_at_vertex_sweep :
  side ρ (γ τ₀) v = 0 →
  γ τ₀ ≠ v →
  adjacent endpoints not on ray line →
  ∃ δ > 0,
    ∀ τ, |τ - τ₀| < δ →
      PairContributionMod2 at τ =
      PairContributionMod2 at τ₀

For persistent vertex-on-ray:

lean
incident_pair_parity_constant_persistent_vertex :
  (∀ τ ∈ I, side ρ (γ τ) v = 0) →
  (∀ τ ∈ I, γ τ ≠ v) →
  PairContributionMod2 constant on I

For simultaneous events:

lean
all_vertex_events_neutral_at_time :
  boundary-free at τ₀ →
  ∃ δ > 0,
    ∀ τ, |τ - τ₀| < δ →
      ClassicalCrossingNumber P ρ (γ τ) % 2
        =
      ClassicalCrossingNumber P ρ (γ τ₀) % 2
Layer 7: finite sweep over a boundary-free segment
lean
affine_side_function :
  τ ↦ side ρ (γ τ) v is affine

affine_zero_set_singleton_or_all :
  affine f →
  (∀ τ, f τ = 0) ∨ ∃ τ₀, ∀ τ, f τ = 0 ↔ τ = τ₀

finite_vertex_event_set :
  finite {τ ∈ [0,1] | ∃ v, side ρ (γ τ) v = 0}

classical_parity_const_on_boundary_free_segment :
  boundary-free γ on [0,1] →
  parity ClassicalCrossingNumber constant on [0,1]

If your current sweep already has the finite partition machinery, only the vertex-event theorem changes.

Layer 8: closed-region constancy
lean
closedRegion_const_on_boundary_free_segment :
  boundary-free segment a--b →
  ClosedRegion P ρ a ↔ ClosedRegion P ρ b

This is the main repaired theorem.

13. Why this fixes the square counterexample

In the square example, the moving point travels along

lean
x = -1

and the ray direction is

lean
ρ = (1, 3/10).

At the bad parameter, the ray line hits vertex (0,4).

Under the old edge-parameter half-open rule, the two incident edges contributed a parity-changing pattern:

2 / 1 / 0

Under the side-coordinate span rule, the two incident edges satisfy the algebraic identity:

lean
Span a s XOR Span s b = Span a b

so their combined parity contribution is constant across the event. Since the moving segment stays outside the square boundary, the total parity remains constantly even.

Thus the phantom boundary disappears.

14. Final recommendation

Adopt the classical side-span crossing convention:

lean
Span (side ρ x (V i)) (side ρ x (V (i+1)))
∧
0 ≤ rayT ρ x i

and discard the old edge-parameter half-open crossing predicate.

This is the cheapest faithful repair because:

it keeps a fixed global ray direction;

it avoids generic/cofinite direction quantifiers;

it avoids rational half-counts;

it preserves the existing Cramer and affine sweep infrastructure;

it replaces the fragile vertex classification by one algebraic truth-table lemma;

it makes local constancy along boundary-free segments true again.