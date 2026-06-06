I’ll keep this as a Lean-oriented design memo: an extrinsic spherical kernel in ℝ³, reusing projection-angle machinery and isolating the hard spherical arm monotonicity theorem.

The minimal honest spherical kernel should be extrinsic: unit vectors in ℝ³, spherical distance by arccos ⟪u,v⟫, and spherical angles by projecting neighbors to the tangent plane. That representation is enough for both pieces you need:

lean
vertex links of convex polyhedra
  → convex spherical polygons in S²

spherical arm lemma
  → monotonicity for convex spherical arms with fixed side lengths

The one genuinely hard lemma is the Schoenberg–Zaremba spherical arm lemma. Everything else can be built as local linear-algebra and projection lemmas, reusing your TetDihedral.projOut machinery.

1. Basic representation

Use no intrinsic manifold.

lean
abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev S2 : Type := {x : E3 // ‖x‖ = 1}

Coercion:

lean
instance : Coe S2 E3 := ⟨Subtype.val⟩

Inner product:

lean
def sInner (p q : S2) : ℝ :=
  ⟪(p : E3), (q : E3)⟫

Spherical distance:

lean
def sDist (p q : S2) : ℝ :=
  Real.arccos (sInner p q)

For unit vectors:

lean
lemma sInner_mem_Icc (p q : S2) :
  sInner p q ∈ Set.Icc (-1 : ℝ) 1

Then:

lean
lemma sDist_nonneg (p q : S2) :
  0 ≤ sDist p q

lemma sDist_le_pi (p q : S2) :
  sDist p q ≤ Real.pi

lemma Real.cos_sDist (p q : S2) :
  Real.cos (sDist p q) = sInner p q

Non-antipodal side condition:

lean
def ShortArc (p q : S2) : Prop :=
  p ≠ q ∧ (p : E3) ≠ - (q : E3)

Then:

lean
lemma sDist_pos_of_ne
    {p q : S2}
    (h : p ≠ q) :
  0 < sDist p q

lemma sDist_lt_pi_of_not_antipodal
    {p q : S2}
    (h : (p : E3) ≠ - (q : E3)) :
  sDist p q < Real.pi
2. Tangent projection and spherical angle

Reuse the projOut pattern from TetDihedral.lean.

For a unit vector v, the tangent projection of u to the plane orthogonal to v is:

lean
def projOut (v u : E3) : E3 :=
  u - ⟪u, v⟫ • v

For p q : S2:

lean
def tangentTo (p q : S2) : E3 :=
  projOut (p : E3) (q : E3)

Here tangentTo p q is the tangent vector at p pointing toward q along the shorter great circle.

Spherical angle at v between neighbors u,w:

lean
def sphAngle (u v w : S2) : ℝ :=
  InnerProductGeometry.angle (tangentTo v u) (tangentTo v w)

You need:

lean
lemma tangentTo_orthogonal (p q : S2) :
  ⟪tangentTo p q, (p : E3)⟫ = 0

and the nonzero criterion:

lean
lemma tangentTo_ne_zero_iff
    (p q : S2) :
  tangentTo p q ≠ 0 ↔ p ≠ q ∧ (p : E3) ≠ - (q : E3)

This is the key well-definedness lemma for spherical angles.

The proof is standard:

lean
projOut p q = 0
↔ q = ⟪q,p⟫ • p

and since both vectors have norm 1, the scalar is 1 or -1.

3. Convex spherical polygons

Do not start with a topological definition. Use oriented triple products.

Define oriented volume:

lean
def det3 (a b c : E3) : ℝ :=
  Matrix.det ![a, b, c]

or whichever determinant API is easiest in your repository.

For unit vectors:

lean
def sOrient (a b c : S2) : ℝ :=
  det3 (a : E3) (b : E3) (c : E3)

A closed spherical polygon is a cyclic tuple:

lean
P : Fin n → S2

with n ≥ 3.

The minimal convexity predicate should be:

lean
structure StrictConvexSphPolygon
    {n : Nat}
    (P : Fin n → S2) : Prop where
  three_le : 3 ≤ n

  edge_short :
    ∀ i, ShortArc (P i) (P (i+1))

  edge_support :
    ∀ i j,
      0 ≤ sOrient (P i) (P (i+1)) (P j)

  strict_nonincident :
    ∀ i j,
      j ≠ i →
      j ≠ i+1 →
      0 < sOrient (P i) (P (i+1)) (P j)

  open_hemisphere :
    ∃ h : E3, ‖h‖ = 1 ∧ ∀ i, 0 < ⟪h, (P i : E3)⟫

The edge_support field says every oriented great-circle edge supports the polygon. This is exactly the vector-language support condition you mentioned.

For arms, use a closed polygon made by adding the endpoint chord.

lean
def ArmToClosed
    {n : Nat}
    (A : Fin (n+1) → S2) :
    Fin (n+1) → S2 :=
  A

The closing edge is from A n back to A 0.

Then:

lean
structure StrictConvexSphArm
    {n : Nat}
    (A : Fin (n+1) → S2) : Prop where
  two_le : 2 ≤ n
  closed_convex :
    StrictConvexSphPolygon A

This definition is strong but very convenient. It is exactly what the Cauchy vertex links provide.

4. Spherical triangle kernel

The spherical arm lemma should be built on the spherical cosine rule.

For a b c : S2, with angle at b:

lean
sphAngle a b c

and side lengths:

lean
AB := sDist a b
BC := sDist b c
AC := sDist a c

prove:

lean
theorem spherical_cosine_rule
    {a b c : S2}
    (hab : ShortArc a b)
    (hbc : ShortArc b c) :
  Real.cos (sDist a c)
    =
  Real.cos (sDist a b) * Real.cos (sDist b c)
    +
  Real.sin (sDist a b) * Real.sin (sDist b c)
      * Real.cos (sphAngle a b c)
Proof

Let:

lean
ea := tangentTo b a
ec := tangentTo b c

Then:

lean
(a : E3)
  =
Real.cos (sDist a b) • (b : E3)
  + Real.sin (sDist a b) • (ea / ‖ea‖)

and similarly for c.

More Lean-friendly: prove the inner-product identity directly.

First:

lean
lemma norm_tangentTo
    {p q : S2}
    (h : ShortArc p q) :
  ‖tangentTo p q‖ = Real.sin (sDist p q)

Then:

lean
lemma decompose_unit_along_tangent
    {p q : S2}
    (h : ShortArc p q) :
  (q : E3)
    =
  Real.cos (sDist p q) • (p : E3)
    +
  tangentTo p q

because:

lean
tangentTo p q = q - ⟪q,p⟫ • p

and:

lean
⟪q,p⟫ = Real.cos (sDist p q).

Then take the inner product of the decompositions of a and c relative to b.

The tangent cross terms vanish because both tangent vectors are orthogonal to b.

Finally:

lean
⟪tangentTo b a, tangentTo b c⟫
  =
‖tangentTo b a‖ * ‖tangentTo b c‖
  * Real.cos (sphAngle a b c)

by the definition of InnerProductGeometry.angle.

5. Base monotonicity: spherical hinge lemma

For A,B ∈ (0,π) and included angles γ₁ ≤ γ₂, define the opposite sides by the spherical cosine rule.

The theorem:

lean
theorem spherical_hinge_mono
    {a b γ₁ γ₂ c₁ c₂ : ℝ}
    (ha0 : 0 < a) (hapi : a < Real.pi)
    (hb0 : 0 < b) (hbpi : b < Real.pi)
    (hg₁0 : 0 ≤ γ₁) (hg₁pi : γ₁ ≤ Real.pi)
    (hg₂0 : 0 ≤ γ₂) (hg₂pi : γ₂ ≤ Real.pi)
    (hγ : γ₁ ≤ γ₂)
    (hc₁ :
      Real.cos c₁ =
        Real.cos a * Real.cos b
          + Real.sin a * Real.sin b * Real.cos γ₁)
    (hc₂ :
      Real.cos c₂ =
        Real.cos a * Real.cos b
          + Real.sin a * Real.sin b * Real.cos γ₂)
    (hc₁range : 0 ≤ c₁ ∧ c₁ ≤ Real.pi)
    (hc₂range : 0 ≤ c₂ ∧ c₂ ≤ Real.pi) :
  c₁ ≤ c₂

Proof:

lean
0 < Real.sin a
0 < Real.sin b

because a,b ∈ (0,π).

Since cos is antitone on [0,π]:

lean
γ₁ ≤ γ₂ → Real.cos γ₂ ≤ Real.cos γ₁

Therefore:

lean
Real.cos c₂ ≤ Real.cos c₁

and again by antitonicity of cos on [0,π]:

lean
c₁ ≤ c₂.

Strict version:

lean
theorem spherical_hinge_strict
    ...
    (hγ : γ₁ < γ₂) :
  c₁ < c₂

provided the same nondegeneracy hypotheses.

This is the n = 3 base of the spherical arm lemma.

6. Can the planar profile trick be reused?

Not directly.

The planar proof uses:

lean
‖∑ lᵢ dir(θᵢ)‖²
  =
∑ lᵢ² + 2∑_{i<j} lᵢ lⱼ cos(θⱼ - θᵢ)

That works because endpoint displacement is a linear sum in a fixed vector space.

On the sphere, the endpoint of an arm is produced by a product of rotations, not a vector sum. There is no comparably useful global double-sum formula for endpoint chord length.

You can still compare endpoint chord length:

lean
‖p - q‖² = 2 - 2 ⟪p,q⟫

and this is monotone in sDist p q, but there is no flat direction-angle profile formula for ⟪p,q⟫.

So the honest route is Schoenberg–Zaremba induction.

7. Spherical arm lemma statement

Use open arms with n edges and n+1 vertices.

lean
def sideLen
    {n : Nat}
    (A : Fin (n+1) → S2)
    (i : Fin n) : ℝ :=
  sDist (A i.castSucc) (A i.succ)

def jointAngle
    {n : Nat}
    (A : Fin (n+1) → S2)
    (i : Fin (n-1)) : ℝ :=
  sphAngle
    (A i.castSucc)
    (A i.succ.castSucc)
    (A i.succ.succ)

The main theorem:

lean
theorem spherical_arm_mono
    {n : Nat}
    (hn : 2 ≤ n)
    (A B : Fin (n+1) → S2)
    (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B)
    (hSide : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hAngle : ∀ i : Fin (n-1), jointAngle A i ≤ jointAngle B i) :
  sDist (A 0) (A (Fin.last n))
    ≤
  sDist (B 0) (B (Fin.last n))

Strict version:

lean
theorem spherical_arm_mono_strict
    {n : Nat}
    (hn : 2 ≤ n)
    (A B : Fin (n+1) → S2)
    (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B)
    (hSide : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hAngle : ∀ i : Fin (n-1), jointAngle A i ≤ jointAngle B i)
    (hStrict : ∃ i : Fin (n-1), jointAngle A i < jointAngle B i) :
  sDist (A 0) (A (Fin.last n))
    <
  sDist (B 0) (B (Fin.last n))

The strict theorem is what Cauchy needs.

8. Schoenberg–Zaremba proof skeleton

This is the single hardest lemma of the chapter.

The clean formal route is to factor the proof into four subtheorems.

8.1 Rotation about a sphere point

Define an orientation-preserving linear isometry of E3 fixing an axis.

You can implement it by Rodrigues’ formula.

For a unit vector a : S2:

lean
def rotAbout (a : S2) (δ : ℝ) : E3 ≃ₗᵢ[ℝ] E3

satisfying:

lean
lemma rotAbout_apply_axis
    (a : S2) (δ : ℝ) :
  rotAbout a δ (a : E3) = a

lemma rotAbout_norm
    (a : S2) (δ : ℝ) (x : E3) :
  ‖rotAbout a δ x‖ = ‖x‖

lemma rotAbout_inner
    (a : S2) (δ : ℝ) (x y : E3) :
  ⟪rotAbout a δ x, rotAbout a δ y⟫ = ⟪x,y⟫

and for tangent vectors:

lean
lemma rotAbout_tangent_angle_add
    {a : S2}
    {u w : E3}
    (hu : ⟪u, (a : E3)⟫ = 0)
    (hw : ⟪w, (a : E3)⟫ = 0)
    (hu0 : u ≠ 0)
    (hw0 : w ≠ 0)
    (hδ : 0 ≤ δ)
    (hrange : InnerProductGeometry.angle u w + δ ≤ Real.pi) :
  InnerProductGeometry.angle u (rotAbout a δ w)
    =
  InnerProductGeometry.angle u w + δ

This is the one place where an oriented tangent-plane angle is useful. If your current angle API is unoriented, introduce an oriented tangent angle only inside this rotation module.

8.2 Hinge move

A hinge move at joint k fixes the prefix and rotates the suffix about axis A k.

lean
def HingeMove
    {n : Nat}
    (A B : Fin (n+1) → S2)
    (k : Fin (n+1))
    (δ : ℝ) : Prop :=
  (∀ i, i.val ≤ k.val → B i = A i) ∧
  (∀ i, k.val ≤ i.val →
      (B i : E3) = rotAbout (A k) δ (A i : E3))

The hinge preserves all side lengths:

lean
lemma hinge_preserves_side_lengths
    (h : HingeMove A B k δ) :
  ∀ i, sideLen A i = sideLen B i

It preserves every joint angle except possibly at k:

lean
lemma hinge_preserves_other_angles
    (h : HingeMove A B k δ)
    (i : Fin (n-1))
    (hi : i.succ.castSucc ≠ k) :
  jointAngle A i = jointAngle B i

It increases the hinge angle:

lean
lemma hinge_increases_joint
    (h : HingeMove A B k δ)
    (hδ : 0 ≤ δ)
    (hrange : jointAngle A k' + δ ≤ Real.pi) :
  jointAngle B k' = jointAngle A k' + δ

where k' is the corresponding internal-joint index.

Endpoint monotonicity:

lean
theorem hinge_endpoint_mono
    {n : Nat}
    (A B : Fin (n+1) → S2)
    (k : Fin (n+1))
    (δ : ℝ)
    (h : HingeMove A B k δ)
    (hδ : 0 ≤ δ)
    (hConvA : StrictConvexSphArm A)
    (hConvB : StrictConvexSphArm B) :
  sDist (A 0) (A (Fin.last n))
    ≤
  sDist (B 0) (B (Fin.last n))

Proof:

Consider the spherical triangle:

lean
A 0, A k, A n

and its hinged version:

lean
B 0 = A 0,
B k = A k,
B n = rotAbout (A k) δ (A n).

The two sides adjacent to A k are fixed:

lean
sDist (A 0) (A k) = sDist (B 0) (B k)
sDist (A k) (A n) = sDist (B k) (B n)

The included angle at A k increases by δ within [0,π], by convexity. Apply spherical_hinge_mono.

Strict version follows from spherical_hinge_strict.

8.3 Convexity under small hinge openings

You need a local persistence lemma.

lean
lemma convex_hinge_open_small
    {n : Nat}
    (A : Fin (n+1) → S2)
    (hA : StrictConvexSphArm A)
    (k : Fin (n+1))
    (hk_internal : 0 < k.val ∧ k.val < n)
    (hnotStraight : jointAngle A k' < Real.pi) :
  ∃ ε > 0,
    ∀ δ, 0 ≤ δ → δ < ε →
      StrictConvexSphArm (hingeOpened A k δ)

Proof:

All convexity inequalities are finite strict inequalities of continuous functions:

lean
δ ↦ sOrient (Pδ i) (Pδ (i+1)) (Pδ j)

For nonincident triples, they are positive at δ = 0, hence remain positive for small δ.

Weak support inequalities remain nonnegative by choosing the opening direction compatible with the convex side. This is where the orientation convention for rotAbout matters.

8.4 Schoenberg continuation lemma

This is the hard theorem to isolate.

lean
theorem spherical_SZ_opening_chain
    {n : Nat}
    (hn : 2 ≤ n)
    (A B : Fin (n+1) → S2)
    (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B)
    (hSide : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hAngle : ∀ i : Fin (n-1), jointAngle A i ≤ jointAngle B i) :
  ∃ N : Nat,
  ∃ chain : Fin (N+1) → (Fin (n+1) → S2),
    chain 0 = A ∧
    chain (Fin.last N) = B ∧
    (∀ r : Fin N,
      ∃ k δ,
        0 ≤ δ ∧
        HingeMove (chain r.castSucc) (chain r.succ) k δ ∧
        StrictConvexSphArm (chain r.castSucc) ∧
        StrictConvexSphArm (chain r.succ))

This is the formal Schoenberg–Zaremba induction.

Proof structure

Induct on n.

Base n = 2

There is one internal angle. This is the spherical hinge lemma.

Inductive step

If all angles are equal, the convex arms are congruent by successive triangle reconstruction, so the endpoint distances are equal.

Otherwise choose an internal joint k with deficit:

lean
jointAngle A k < jointAngle B k.

Open A at k.

There are two possibilities.

Case 1: Target reached

You can open until:

lean
jointAngle A' k = jointAngle B k

while preserving convexity. Then reduce the number of strict deficits and continue.

The measure is lexicographic:

lean
(n, number_of_unmatched_angles)
Case 2: Stuck before target

Convexity fails first when a previously strict support determinant becomes zero:

lean
sOrient (P i) (P (i+1)) (P j) = 0

Geometrically, some nonadjacent vertex lies on a supporting great circle. Equivalently, three relevant unit vectors are coplanar with the origin:

lean
det3 u v w = 0.

This gives a diagonal cut of the convex spherical arm into two smaller convex spherical arms.

Formal lemma:

lean
lemma convex_stuck_gives_cut
    (P : Fin (n+1) → S2)
    (hP : WeakConvexSphArm P)
    (hZero :
      sOrient (P i) (P (i+1)) (P j) = 0)
    (hnonincident : j ≠ i ∧ j ≠ i+1) :
  ∃ left right,
    SmallerConvexArm left ∧
    SmallerConvexArm right ∧
    -- the original endpoint distance comparison reduces
    -- to endpoint distance comparisons on left and right
    CutReduction P left right

Then apply the induction hypothesis to the two smaller arms and glue the inequalities using the spherical hinge lemma.

This is the exact spherical version of the planar “stuck case.”

8.5 Derive the arm lemma from the opening chain

Once spherical_SZ_opening_chain is proven, monotonicity is straightforward.

lean
theorem spherical_arm_mono
    ... :
  sDist (A 0) (A (Fin.last n))
    ≤
  sDist (B 0) (B (Fin.last n)) := by
  obtain ⟨N, chain, h0, hN, hsteps⟩ :=
    spherical_SZ_opening_chain hn A B hA hB hSide hAngle

  -- Each step is a nonnegative hinge opening.
  have hmono :
    ∀ r : Fin N,
      sDist (chain r.castSucc 0) (chain r.castSucc (Fin.last n))
        ≤
      sDist (chain r.succ 0) (chain r.succ (Fin.last n)) := by
    intro r
    obtain ⟨k, δ, hδ, hhinge, hc1, hc2⟩ := hsteps r
    exact hinge_endpoint_mono _ _ k δ hhinge hδ hc1 hc2

  -- Chain inequalities.
  exact monotone_chain hmono h0 hN

Strictness:

lean
theorem spherical_arm_mono_strict
    ... :
  sDist (A 0) (A (Fin.last n))
    <
  sDist (B 0) (B (Fin.last n))

At least one hinge step has δ > 0, and strict hinge monotonicity gives one strict inequality in the chain.

9. Vertex-link correspondence

For Cauchy, you do not need a full intrinsic spherical polygon API. You need a local theorem for each vertex of a convex polyhedron.

Use a polyhedron interface that gives the cyclic star at each vertex.

lean
structure VertexStar (P : Type*) where
  Vtx : Type
  point : Vtx → E3

  deg : Vtx → Nat
  deg_three : ∀ v, 3 ≤ deg v

  nbr : ∀ v, Fin (deg v) → Vtx

  -- face between nbr i and nbr (i+1) at v
  faceAt : ∀ v, Fin (deg v) → Face

  cyclic_incidence_cert : Prop
  convex_star_cert : Prop

For a vertex v, define edge directions:

lean
def edgeDir
    (P : Polyhedron)
    (v : P.Vtx)
    (i : Fin (P.deg v)) : S2 :=
  unitVector (P.point (P.nbr v i) - P.point v)

where unitVector requires:

lean
P.point (P.nbr v i) ≠ P.point v.

The link polygon is:

lean
def vertexLink
    (P : Polyhedron)
    (v : P.Vtx) :
    Fin (P.deg v) → S2 :=
  edgeDir P v
9.1 Link side length equals face angle

The side of the spherical link between consecutive edge directions is:

lean
sDist (edgeDir P v i) (edgeDir P v (i+1)).

The face angle at v in the face between those two edges is:

lean
EuclideanGeometry.angle
  (P.point (P.nbr v i))
  (P.point v)
  (P.point (P.nbr v (i+1)))

The theorem:

lean
theorem vertexLink_side_eq_faceAngle
    (P : ConvexPolyhedron)
    (v : P.Vtx)
    (i : Fin (P.deg v)) :
  sDist (vertexLink P v i) (vertexLink P v (i+1))
    =
  faceAngle P v i

Proof:

Both sides are arccos of the inner product of normalized edge vectors.

lean
cos(sDist eᵢ eⱼ) = ⟪eᵢ,eⱼ⟫
cos(faceAngle)  = ⟪eᵢ,eⱼ⟫

Both angles lie in [0,π]; use injectivity of cos on [0,π].

This should be short using Mathlib’s angle API.

9.2 Link spherical angle equals dihedral angle

At link vertex edgeDir P v i, the spherical angle is:

lean
sphAngle
  (edgeDir P v (i-1))
  (edgeDir P v i)
  (edgeDir P v (i+1)).

By definition:

lean
angle
  (projOut (edgeDir i) (edgeDir (i-1)))
  (projOut (edgeDir i) (edgeDir (i+1))).

The interior dihedral angle along the edge from v to nbr i should be defined using exactly the same projected cross-section rays.

lean
def interiorDihedral
    (P : ConvexPolyhedron)
    (v : P.Vtx)
    (i : Fin (P.deg v)) : ℝ :=
  InnerProductGeometry.angle
    (projOut (edgeDir P v i) (edgeDir P v (i-1)))
    (projOut (edgeDir P v i) (edgeDir P v (i+1)))

Then the theorem is definitionally or nearly definitionally true:

lean
theorem vertexLink_angle_eq_dihedral
    (P : ConvexPolyhedron)
    (v : P.Vtx)
    (i : Fin (P.deg v)) :
  sphAngle
    (vertexLink P v (i-1))
    (vertexLink P v i)
    (vertexLink P v (i+1))
    =
  interiorDihedral P v i := by
  rfl

If your existing dihedral uses face normals instead, prove equivalence once:

lean
theorem projOut_dihedral_eq_normal_dihedral :
  angle between projected cross-section rays
    =
  π - angle between outward face normals

or the corresponding convention. For Cauchy signs, choose the projected-ray convention if possible. It matches the link angle directly.

This is the main shortcut from TetDihedral.lean.

9.3 Vertex link is convex spherical polygon

The theorem:

lean
theorem vertexLink_strictConvex
    (P : ConvexPolyhedron)
    (v : P.Vtx) :
  StrictConvexSphPolygon (vertexLink P v)

Proof route:

Since v is a convex polyhedron vertex, there is a supporting linear functional ℓ with:

lean
ℓ (P.point v) > ℓ (P.point w)

for all other vertices w.

Therefore all edge directions from v lie in one open hemisphere:

lean
∃ h, ∀ i, 0 < ⟪h, edgeDir P v i⟫.

The tangent cone at v is convex.

Intersection of a convex cone with the unit sphere is geodesically convex: if a,b are unit vectors in the cone and sDist a b < π, then the shorter great-circle interpolation

lean
γ(t) =
  normalize
    (Real.sin ((1-t)*c) • a + Real.sin (t*c) • b)

is in the cone because it is a positive linear combination of a and b.

The cyclic order of incident edges gives the boundary of this spherical convex set.

Each oriented edge great circle supports all other link vertices, giving the determinant inequalities:

lean
0 ≤ sOrient (link i) (link (i+1)) (link j).

This proof can reuse whatever cyclic-sector infrastructure exists in SectorSum.

If full convex-polyhedron support is not yet formalized, introduce a local certificate:

lean
structure VertexLinkCert
    (P : Polyhedron)
    (v : P.Vtx) where
  link : Fin (deg v) → S2
  link_eq_edgeDir :
    link = vertexLink P v

  strictConvex :
    StrictConvexSphPolygon link

  side_eq_faceAngle :
    ∀ i, sDist (link i) (link (i+1)) = faceAngle P v i

  angle_eq_dihedral :
    ∀ i,
      sphAngle (link (i-1)) (link i) (link (i+1))
        =
      interiorDihedral P v i

Then Cauchy can consume VertexLinkCert immediately, and the global convexity proof can be filled later.

10. Cauchy bridge theorem

Suppose P and Q are convex polyhedra with the same combinatorics and congruent corresponding faces.

At a vertex v, their vertex links have:

lean
same side lengths

because corresponding face angles are equal.

The link angles are the dihedral angles.

So:

lean
theorem vertex_link_sides_equal_of_face_congruent
    (P Q : ConvexPolyhedron)
    (hFaces : CorrespondingFacesCongruent P Q)
    (v : P.Vtx) :
  ∀ i,
    sideLen (vertexLink P v) i
      =
    sideLen (vertexLink Q (corrV v)) i

and:

lean
theorem vertex_link_angles_eq_dihedrals
    (P : ConvexPolyhedron)
    (v : P.Vtx) :
  ∀ i,
    jointAngle (vertexLink P v) i
      =
    interiorDihedral P v i
11. Per-vertex Cauchy contradiction

This is the theorem the combinatorial sign-change core needs.

Let the cyclic sequence around a vertex be the signs of:

lean
interiorDihedral Q e - interiorDihedral P e.

The local spherical theorem:

lean
theorem no_vertex_all_dihedral_diffs_same_sign
    (P Q : ConvexPolyhedron)
    (hComb : SameCombinatorics P Q)
    (hFaces : CorrespondingFacesCongruent P Q)
    (v : P.Vtx)
    (hNondeg : 3 ≤ degree v) :
  ¬
    ((∀ i, interiorDihedral P v i ≤ interiorDihedral Q v i)
      ∧
     (∃ i, interiorDihedral P v i < interiorDihedral Q v i))
  ∧
  ¬
    ((∀ i, interiorDihedral Q v i ≤ interiorDihedral P v i)
      ∧
     (∃ i, interiorDihedral Q v i < interiorDihedral P v i))

Proof for the first half:

Choose an index r with strict inequality.

Choose a side of the closed link not incident to r. In a spherical polygon with at least three vertices, this is always possible. For a triangle, remove the side opposite r.

Removing that side turns the closed link into an open arm. The removed side is the endpoint distance of the arm.

Corresponding side lengths of the arms are equal by face congruence.

Internal joint angles of the Q arm are all ≥ those of the P arm, and one is strict.

By spherical_arm_mono_strict:

lean
endpointDist P_arm < endpointDist Q_arm.

But the endpoint distance is exactly the removed side length, and removed side lengths are equal by face congruence.

Contradiction.

The second half is symmetric.

This gives the standard Cauchy local rule:

lean
at every vertex, the nonzero cyclic sign sequence cannot have
zero sign changes.

Depending on your combinatorial core, you probably need the stronger normalized statement:

lean
theorem vertex_sign_sequence_has_at_least_four_changes
    ...
    (hSomeNonzeroIncident : ∃ incident edge, sign ≠ 0) :
  4 ≤ SignChangesAroundVertex ...

This follows from the spherical arm lemma plus the usual deletion of zero signs: if the nonzero signs had fewer than four changes, then after choosing a maximal block one obtains a vertex arm with all inequalities in one direction and one strict, contradicting the theorem above.

Your proven combinatorial core likely already has the exact sign-sequence format, so expose the spherical layer as the local axiom it expects.

12. Final assembly shape

The already-proven combinatorial core should consume something like:

lean
structure CauchyLocalData where
  sign : Edge → Sign
  sign_zero_iff_equal_dihedral :
    sign e = 0 ↔ dihedralP e = dihedralQ e

  vertex_rule :
    ∀ v,
      localSignCondition (cyclicIncidentSigns v)

The spherical layer provides:

lean
theorem cauchy_vertex_rule_from_spherical_links
    (P Q : ConvexPolyhedron)
    (hComb : SameCombinatorics P Q)
    (hFaces : CorrespondingFacesCongruent P Q)
    (hLinksP : ∀ v, VertexLinkCert P v)
    (hLinksQ : ∀ v, VertexLinkCert Q (corrV v)) :
  ∀ v,
    localSignCondition
      (cyclicIncidentDihedralSigns P Q v)

Then the core gives:

lean
theorem all_dihedral_signs_zero
    ... :
  ∀ e, interiorDihedral P e = interiorDihedral Q e

Finally, if not already proven:

lean
theorem congruent_faces_and_equal_dihedrals_imply_rigid
    (P Q : ConvexPolyhedron)
    (hComb : SameCombinatorics P Q)
    (hFaces : CorrespondingFacesCongruent P Q)
    (hDih : ∀ e, interiorDihedral P e = interiorDihedral Q e)
    (hFaceGraphConnected : ConnectedFaceAdjacency P) :
  ∃ T : EuclideanIsometry E3 E3,
    ∀ v, T (P.point v) = Q.point (corrV v)

Proof: fix one face by a Euclidean isometry; propagate across adjacent faces. Equal dihedral angles determine the next face uniquely on the convex side of the shared edge.

13. Dependency-ordered lemma list
Layer A: extrinsic sphere basics
lean
E3
S2
sInner
sDist
ShortArc

sInner_mem_Icc
Real.cos_sDist
sDist_nonneg
sDist_le_pi
sDist_pos_of_ne
sDist_lt_pi_of_not_antipodal
Layer B: tangent projections
lean
projOut
tangentTo
sphAngle

tangentTo_orthogonal
tangentTo_ne_zero_iff
norm_tangentTo
decompose_unit_along_tangent

Reuse TetDihedral.projOut here.

Layer C: spherical triangle
lean
spherical_cosine_rule
spherical_hinge_mono
spherical_hinge_strict
Layer D: convex spherical polygons
lean
det3
sOrient
StrictConvexSphPolygon
StrictConvexSphArm

edge_support lemmas
open_hemisphere lemmas
great_circle_interpolation_in_cone
Layer E: rotations and hinges
lean
rotAbout
rotAbout_apply_axis
rotAbout_inner
rotAbout_norm
rotAbout_tangent_angle_add

HingeMove
hinge_preserves_side_lengths
hinge_preserves_other_angles
hinge_increases_joint
hinge_endpoint_mono
hinge_endpoint_strict
convex_hinge_open_small
Layer F: Schoenberg–Zaremba
lean
convex_stuck_gives_cut
spherical_SZ_opening_chain

spherical_arm_mono
spherical_arm_mono_strict

This is the hardest layer.

Layer G: vertex links
lean
edgeDir
vertexLink

vertexLink_side_eq_faceAngle
vertexLink_angle_eq_dihedral
vertexLink_strictConvex

VertexLinkCert
Layer H: Cauchy local bridge
lean
vertex_link_sides_equal_of_face_congruent
vertex_link_angles_eq_dihedrals

no_vertex_all_dihedral_diffs_same_sign
vertex_sign_sequence_has_at_least_four_changes
cauchy_vertex_rule_from_spherical_links
Layer I: global Cauchy assembly
lean
all_dihedral_signs_zero
congruent_faces_and_equal_dihedrals_imply_rigid
cauchy_rigidity
14. Single hardest lemma and practical shortcut

The single hardest lemma is:

lean
spherical_arm_mono_strict

or more precisely its internal continuation theorem:

lean
spherical_SZ_opening_chain

Everything else is local vector algebra or finite combinatorics.

The recommended shortcut is:

Implement all extrinsic sphere/link machinery first.

State spherical_arm_mono_strict as the one major theorem with its dependencies isolated.

Prove the Cauchy bridge against that theorem.

Then fill spherical_arm_mono_strict using the Schoenberg–Zaremba hinge induction.

The most reusable existing code is:

lean
TetDihedral.projOut

for the tangent-plane angle/dihedral identity, and any SectorSum/cyclic-order infrastructure for the vertex-link convexity and cyclic sign sequences.

This design keeps the spherical layer minimal, honest, and aligned with what the Cauchy proof actually needs.