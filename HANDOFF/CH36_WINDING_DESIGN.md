The clean route is: make the signed crossing contribution itself use the standard half-open endpoint convention, then prove a stronger “local constancy on boundary-complement” by reducing every vertex event to a two-edge cancellation. Then the half-plane exterior argument needs only a concrete escape ray, not Jordan.

The clean design is:

Define signed crossings with a half-open endpoint convention.

Prove local constancy by grouping all degeneracies into maximal ray-vertex blocks, not by individual edges.

For ExteriorWindingZero, avoid Jordan entirely: use the separating half-plane to build a straight escape path that never touches the subpolygon boundary, then use local constancy along that path.

The important correction is: at a vertex event the two signed contributions do not always cancel. They cancel at a tangent/grazing vertex; at a transverse vertex the contribution is transferred from one incident edge to the other with the same sign. The cluster sum is what is constant.

A. Signed local constancy through vertex/grazing events

Use coordinates relative to the upward ray from x.

lean
def X (x v : ℝ²) : ℝ := v.x - x.x
def Y (x v : ℝ²) : ℝ := v.y - x.y

For a nonvertical edge a → b, the vertical line through x hits the edge at parameter

lean
τ x a b := - X x a / (X x b - X x a)

and forward height

lean
hitY x a b :=
  Y x a + τ x a b * (Y x b - Y x a)

Define the signed edge contribution with a half-open horizontal straddle:

lean
def edgeWind (x a b : ℝ²) : ℤ :=
  if h : X x a = X x b then
    0
  else if X x a < 0 ∧ 0 ≤ X x b ∧ 0 < hitY x a b then
    1
  else if X x b < 0 ∧ 0 ≤ X x a ∧ 0 < hitY x a b then
    -1
  else
    0

Then:

lean
def windCross (Q : Polygon m) (x : ℝ²) : ℤ :=
  ∑ e : Fin m, edgeWind x (Q.q e) (Q.q (e+1))

The half-open convention is the key. It includes a crossing when the edge arrives at the ray line, but not when it leaves it. You can reverse the convention, but then all endpoint lemmas must be reversed consistently.

A1. Singleton vertex event

Let

lean
u = Q.q (r-1)
v = Q.q r
w = Q.q (r+1)

Assume at basepoint x₀:

lean
X x₀ v = 0
0 < Y x₀ v
X x₀ u ≠ 0
X x₀ w ≠ 0

Define the abstract signed straddle:

lean
def crossSign (α β : ℝ) : ℤ :=
  if α < 0 ∧ 0 < β then 1
  else if β < 0 ∧ 0 < α then -1
  else 0

Then the local vertex-pair lemma is:

lean
lemma vertex_pair_signed_sum
    (hXv : X x₀ v = 0)
    (hYv : 0 < Y x₀ v)
    (hXu : X x₀ u ≠ 0)
    (hXw : X x₀ w ≠ 0) :
    edgeWind x₀ u v + edgeWind x₀ v w
      =
    crossSign (X x₀ u) (X x₀ w)

The four cases are exactly:

u left,  w left  :  (+1) + (-1) = 0
u right, w right :    0  +   0  = 0
u left,  w right :  (+1) +   0  = +1
u right, w left  :    0  + (-1) = -1

So the signed contribution does not always cancel. It cancels only in the tangent cases. In the transverse cases the crossing contribution is passed from one incident edge to the other.

If the vertex is below the basepoint:

lean
X x₀ v = 0
Y x₀ v < 0

then choose a small neighborhood where the corresponding hit heights remain negative, and prove:

lean
lemma vertex_pair_below_zero :
  ∀ᶠ x in 𝓝 x₀,
    edgeWind x u v + edgeWind x v w = 0

The case Y x₀ v = 0 is impossible under x₀ ∉ boundary Q, because then x₀ = v.

A2. Vertical/grazing edge event = maximal ray block

Do not handle vertical edges one by one. Handle a whole maximal block of consecutive vertices lying on the ray line.

Suppose

lean
Q.q r, Q.q (r+1), ..., Q.q s

are consecutive vertices satisfying

lean
X x₀ (Q.q t) = 0
0 < Y x₀ (Q.q t)

for r ≤ t ≤ s, and the predecessor and successor are off the ray line:

lean
u := Q.q (r-1)
v := Q.q (s+1)

X x₀ u ≠ 0
X x₀ v ≠ 0

Internal edges of the block have X = 0 at both endpoints, hence contribute 0 by definition of edgeWind.

The block lemma is:

lean
lemma ray_block_signed_sum
    (hblockX : ∀ t ∈ Icc r s, X x₀ (Q.q t) = 0)
    (hblockY : ∀ t ∈ Icc r s, 0 < Y x₀ (Q.q t))
    (hleft  : X x₀ (Q.q (r-1)) ≠ 0)
    (hright : X x₀ (Q.q (s+1)) ≠ 0) :
    (∑ e in blockEdges r s,
        edgeWind x₀ (Q.q e) (Q.q (e+1)))
      =
    crossSign
      (X x₀ (Q.q (r-1)))
      (X x₀ (Q.q (s+1)))

where

lean
blockEdges r s = {r-1, r, r+1, ..., s}

i.e. the entry edge, all internal vertical/grazing edges, and the exit edge.

The proof is just:

entry edge contributes:
  +1 if predecessor is left,
   0 if predecessor is right.

internal block edges contribute:
   0.

exit edge contributes:
  -1 if successor is left,
   0 if successor is right.

So again the four cases are:

pred left,  succ left  : +1 - 1 = 0
pred right, succ right :  0 + 0 = 0
pred left,  succ right : +1 + 0 = +1
pred right, succ left  :  0 - 1 = -1

This also covers the case where the upward ray overlaps a vertical boundary segment above x₀.

If a maximal ray block is below x₀, i.e.

lean
∀ t ∈ Icc r s, Y x₀ (Q.q t) < 0

then the entire block contributes locally 0.

A vertical block cannot straddle Y = 0, because then x₀ would lie on one of the vertical boundary edges, contradicting x₀ ∉ boundary Q.

A3. Full nongeneric local constancy theorem

Package the previous lemmas into:

lean
theorem windCross_eventually_eq_basepoint
    (hx : x₀ ∉ boundary Q) :
    ∀ᶠ x in 𝓝 x₀,
      windCross Q x = windCross Q x₀

Proof skeleton:

lean
1. Since Q has finitely many edges and x₀ ∉ boundary Q,
   choose ε > 0 so that B(x₀, ε) avoids boundary Q.

2. Classify vertices of Q into:
   - off-ray vertices: X x₀ v ≠ 0;
   - ray-above vertices: X x₀ v = 0 ∧ 0 < Y x₀ v;
   - ray-below vertices: X x₀ v = 0 ∧ Y x₀ v < 0.

   The case X = 0 ∧ Y = 0 is impossible.

3. Break the cyclic list at an off-ray vertex.
   This avoids wraparound headaches. There is at least one off-ray vertex unless the polygon is degenerate/collinear, impossible for a simple polygon with area.

4. Decompose the resulting linear edge list into:
   - stable single edges whose endpoints are off the ray line;
   - maximal ray-above blocks;
   - maximal ray-below blocks.

5. For stable edges:
   all inequalities in `edgeWind` are strict at x₀, so the contribution is locally constant.

6. For ray-above blocks:
   use `ray_block_signed_sum`.
   The block contribution is locally equal to
   `crossSign predecessor successor`.

7. For ray-below blocks:
   the block contribution is locally `0`.

8. Sum over the finite block decomposition.

The final theorem you want available later is not the generic one but:

lean
theorem windCross_locally_constant_off_boundary
    (hx : x ∉ boundary Q) :
    ∀ᶠ y in 𝓝 x,
      windCross Q y = windCross Q x

This subsumes your current generic-stratum theorem.

B. Half-plane exterior implies winding zero

For this part, avoid Jordan completely.

Let the subpolygon be Q, and let the separating chord be the oriented segment a → b. Define the signed side function:

lean
def side (z : ℝ²) : ℝ :=
  det2 (b - a) (z - a)

Assume the subpolygon lies in the closed “inside” half-plane:

lean
hQside : ∀ z, z ∈ boundary Q → side z ≤ 0

and the point is strictly on the far side:

lean
hxside : 0 < side x

You want:

lean
theorem ExteriorWindingZero_halfplane
    (hQside : ∀ z, z ∈ boundary Q → side z ≤ 0)
    (hxside : 0 < side x) :
    windCross Q x = 0
B1. Choose a concrete escape direction

Pick a vector v satisfying:

lean
sideDir : 0 < det2 (b - a) v
vx_ne   : v.x ≠ 0

Mechanically:

lean
ν := rotate90 (b - a)

or -ν, choosing the sign so that

lean
0 < det2 (b - a) ν

If ν.x ≠ 0, use v = ν.

If ν.x = 0, perturb slightly:

lean
v := ν + ε • e₁

with ε ≠ 0 small enough that

lean
0 < det2 (b - a) v

This gives:

lean
lemma exists_escape_vec :
  ∃ v : ℝ²,
    0 < det2 (b - a) v ∧ v.x ≠ 0
B2. Define the escape path
lean
γ t := x + t • v

For t ≥ 0:

lean
side (γ t)
  = side x + t * det2 (b - a) v
  > 0

So:

lean
lemma escape_path_avoids_boundary
    (ht : 0 ≤ t) :
    γ t ∉ boundary Q := by
  intro hmem
  have h1 : side (γ t) ≤ 0 := hQside (γ t) hmem
  have h2 : 0 < side (γ t) := by
    unfold γ side
    nlinarith [hxside, sideDir, ht]
  linarith

This is the whole separation argument. No Jordan theorem appears.

B3. Pick a far endpoint with zero winding

Because v.x ≠ 0, choose T so that the vertical line through γ T is completely outside the polygon’s x-range.

Let

lean
minX_Q := Finset.inf' vertices ...
maxX_Q := Finset.sup' vertices ...

If 0 < v.x, choose

lean
T > (maxX_Q + 1 - x.x) / v.x

so that

lean
(maxX_Q < (γ T).x)

If v.x < 0, choose

lean
T > (x.x - (minX_Q - 1)) / (-v.x)

so that

lean
((γ T).x < minX_Q)

Then every edge has both endpoints strictly on the same horizontal side of the vertical line through γ T, hence every edge contribution is zero:

lean
lemma windCross_zero_of_x_outside_range
    (hleft : (γ T).x < minX_Q ∨ maxX_Q < (γ T).x) :
    windCross Q (γ T) = 0

Proof:

lean
intro edge e = a → b
have sameSide :
  (X (γ T) a < 0 ∧ X (γ T) b < 0)
  ∨
  (0 < X (γ T) a ∧ 0 < X (γ T) b)

so neither straddle condition in edgeWind can hold.

Thus:

lean
have hfar : windCross Q (γ T) = 0 :=
  windCross_zero_of_x_outside_range ...

This is more concrete than using a generic “far point exists” lemma, although your existing far-point lemma can replace this step if it has the right shape.

B4. Transport winding along the escape path

Use the nongeneric local constancy theorem from A.

First prove a path version once and reuse it:

lean
theorem windCross_constant_on_path
    (hγ : ContinuousOn γ (Set.Icc 0 T))
    (havoid : ∀ t ∈ Set.Icc 0 T, γ t ∉ boundary Q) :
    windCross Q (γ 0) = windCross Q (γ T)

Proof skeleton:

lean
1. For every t ∈ [0,T], apply
     windCross_locally_constant_off_boundary (havoid t)
   to get a neighborhood Ut of t in which
     windCross Q (γ s) = windCross Q (γ t).

2. Hence the function
     f t := windCross Q (γ t)
   is locally constant on [0,T].

3. Since [0,T] is preconnected/connected and ℤ is discrete,
   a locally constant map [0,T] → ℤ is constant.

4. Therefore f 0 = f T.

In Lean, if the general locally-constant-on-connected-space lemma is annoying, prove this specialized lemma for Set.Icc 0 T once. The codomain is ℤ, so fibers are clopen in the subtype interval.

Then:

lean
have hconst : windCross Q x = windCross Q (γ T) :=
  windCross_constant_on_path
    continuous_escape_path
    (by
      intro t ht
      exact escape_path_avoids_boundary (show 0 ≤ t from ht.1))

exact hconst.trans hfar

So:

lean
theorem ExteriorWindingZero_halfplane
    (hQside : ∀ z, z ∈ boundary Q → side z ≤ 0)
    (hxside : 0 < side x) :
    windCross Q x = 0 := by
  obtain ⟨v, hvside, hvx⟩ := exists_escape_vec ...
  let γ := fun t => x + t • v
  choose T hTpos hToutside using choose_large_T_outside_xrange x v hvx Q
  have hconst : windCross Q x = windCross Q (γ T) :=
    windCross_constant_on_path
      (by continuity)
      (by
        intro t ht
        exact escape_path_avoids_boundary hQside hxside hvside ht.1)
  have hfar : windCross Q (γ T) = 0 :=
    windCross_zero_of_x_outside_range Q (γ T) hToutside
  exact hconst.trans hfar
Final assembly

You already have:

lean
ExteriorWindingZero → OffDiagDisjoint

So instantiate ExteriorWindingZero with the half-plane theorem:

lean
theorem ExteriorWindingZero_for_chord_side
    (Q : SubPolygon)
    (a b : ℝ²)
    (hQside : ∀ z, z ∈ boundary Q → det2 (b-a) (z-a) ≤ 0) :
    ∀ x,
      0 < det2 (b-a) (x-a) →
      windCross Q x = 0 :=
by
  intro x hx
  exact ExteriorWindingZero_halfplane hQside hx

Then your disjointness theorem becomes:

lean
theorem region_L_inter_region_R_subset_diag :
    region L ∩ region R ⊆ diagSegment i j := by
  intro x hx
  by_contra hnotdiag

  -- Existing reduction:
  -- both-inside/off-parent gives
  --   windCross_L x = - windCross_R x ≠ 0
  -- but the half-plane exterior winding-zero theorem gives
  --   one of windCross_L x or windCross_R x is 0
  -- depending on which far side of the diagonal x lies on.

  exact OffDiagDisjoint_of_ExteriorWindingZero
    ExteriorWindingZero_for_chord_side
    hx
    hnotdiag

The two key lemmas to add are therefore:

lean
theorem windCross_locally_constant_off_boundary
    (hx : x ∉ boundary Q) :
    ∀ᶠ y in 𝓝 x,
      windCross Q y = windCross Q x

proved by the signed ray-block cancellation/transfer lemma, and

lean
theorem ExteriorWindingZero_halfplane
    (hQside : ∀ z, z ∈ boundary Q → side z ≤ 0)
    (hxside : 0 < side x) :
    windCross Q x = 0

proved by the straight escape path.

The signed vertex rule to remember is:

same side at vertex  → signed cancellation
opposite sides       → signed transfer, same total sign
vertical ray block   → reduce to predecessor/successor crossSign

That is the nongeneric replacement for the usual unsigned vertex-pairing argument.