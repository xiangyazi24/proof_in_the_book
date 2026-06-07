I’ll separate the answer into three independent lemmas. The main correction is that R-C should not be proved by adding a new “side-monotone SZ” theorem; there is a much smaller one-edge spherical hinge transport that fits your existing cut proof.

R-C as stated is false. Do not add a general side-monotone SZ lemma.

Even in the 2-edge Euclidean/small-spherical limit, with sides a, b and joint angle θ,

d² = a² + b² - 2ab cos θ.

For small θ and b < a cos θ, increasing b decreases the endpoint distance. So side-length monotonicity is not available.

The correct final package should be:

R-cong : OK, prove by moving-frame uniqueness.
R-C    : replace by your already-proved any-support cut transport;
         do not prove side-monotone body transport.
R-O    : prove with a monitored finite constraint family and trichotomy.
R-cong: SSS/angle congruence

Use a moving oriented frame, not scalar distance recursion.

For each edge define the oriented edge-normal:

lean
edgeNormal A e :=
  normalize ((A e) × (A (e+1)))

Short edges guarantee the cross product is nonzero.

The recurrence is:

lean
A (e+1) =
  Rot (edgeNormal A e) (sideLen A e) (A e)

and at an interior vertex:

lean
edgeNormal A r =
  Rot (A r) (signedTurn A r) (edgeNormal A (r-1))

where signedTurn A r is determined from jointAngle A r plus the convex orientation. For strictly/weakly convex arms in one hemisphere, the sign is fixed.

The clean theorem is:

lean
theorem congruent_endpoint_eq
    (hA : WeakConvex A)
    (hB : WeakConvex B)
    (hs : ∀ e, sideLen A e = sideLen B e)
    (hj : ∀ r, jointAngle A r = jointAngle B r) :
    sDist (A 0) (A N) = sDist (B 0) (B N)

Proof skeleton:

Choose a spherical isometry Φ₁ sending the first oriented edge frame of A to that of B:

lean
Φ₁ (A 0) = B 0
Φ₁ (A 1) = B 1
Φ₁ (edgeNormal A 0) = edgeNormal B 0

Induct on r proving:

lean
Φ₁ (A r) = B r
Φ₁ (edgeNormal A r) = edgeNormal B r

Step r → r+1:

From the induction hypothesis and side equality,

lean
Φ₁ (A (r+1))
= Φ₁ (Rot (edgeNormal A r) (sideLen A r) (A r))
= Rot (edgeNormal B r) (sideLen B r) (B r)
= B (r+1).

For the next edge normal, use joint equality:

lean
edgeNormal A (r+1)
=
Rot (A (r+1)) (signedTurn A (r+1)) (edgeNormal A r)

and

lean
signedTurn A (r+1) = signedTurn B (r+1)

because the unsigned joint angles agree and convex orientation fixes the sign.

At r = N, get:

lean
Φ₁ (A N) = B N

so

lean
sDist (A 0) (A N)
= sDist (Φ₁ (A 0)) (Φ₁ (A N))
= sDist (B 0) (B N).

The key helper lemma is:

lean
lemma edgeNormal_next_eq_rot
    (hconv : WeakConvex A) :
    edgeNormal A r =
      Rot (A r) (signedTurn A r) (edgeNormal A (r-1))

Then R-cong is routine frame induction.

R-C: do not prove side-monotone transport

The statement

lean
sideLen bodyA e ≤ sideLen bodyB e
∧ jointAngle bodyA r ≤ jointAngle bodyB r
→ endpt bodyA ≤ endpt bodyB

is not true in general.

So the correct CUT closure should remain your special theorem:

lean
theorem anySupportCut
    (hA : WeakConvex A)
    (hB : StrictConvex B)
    (hsides : SameSides A B)
    (hjoints : JointLe A B)
    (hzero :
      ∃ i j, NonIncidentEdgeVertex i j ∧ support A i j = 0)
    (IH : ∀ {m}, m < N → Main m) :
    endpt A ≤ endpt B

Inside it, the body should not be closed by a general side-monotone lemma. It should be closed by the already-specialized cut transport:

lean
theorem splice_transport_of_diag_le
    (hdiag : sDist (A i) (A j) ≤ sDist (B i) (B j))
    ... :
    endpt A ≤ endpt B

If your current CUT branch now demands R-C, refactor so the diagonal inequality is consumed directly by splice_transport_of_diag_le, not by a general arm lemma.

The safe rule is:

equal-side recursion is allowed;
one-shorter-side recursion is not.
R-O: strict persistence at the admissible supremum

Define a single finite monitored family.

Let

lean
Aδ := openTail A k δ

Define support constraints:

lean
supportConstraint δ c :=
  det3 (Aδ c.i) (Aδ (c.i+1)) (Aδ c.j)

for all nonincident pairs c.

Define the hemisphere constraint using the fixed original hemisphere vector h₀:

lean
hemiConstraint δ r :=
  ⟪h₀, Aδ r⟫

Do not let the hemisphere vector vary with δ. Use the original one from StrictConvex A.

Define the joint slack:

lean
jointSlack δ :=
  jointAngle B k - jointAngle Aδ k

Now define:

lean
Monitored δ :=
  (∀ c, 0 < supportConstraint δ c) ∧
  (∀ r, 0 < hemiConstraint δ r) ∧
  0 ≤ jointSlack δ

and

lean
Adm δ := 0 ≤ δ ∧ Monitored δ

Let

lean
δ* := sSup {δ | Adm δ}
A* := Aδ*

At the supremum, closure gives weak inequalities:

lean
∀ c, 0 ≤ supportConstraint δ* c
∀ r, 0 ≤ hemiConstraint δ* r
0 ≤ jointSlack δ*

Now prove the endpoint trichotomy as:

lean
theorem opening_boundary_trichotomy :
    jointSlack δ* = 0
  ∨ (∃ c, supportConstraint δ* c = 0)
  ∨ (∃ r, hemiConstraint δ* r = 0)

Proof: if all three are not zero, then by closure they are all positive:

lean
0 ≤ f δ* ∧ f δ* ≠ 0 → 0 < f δ*

Continuity plus finite minimum gives an ε > 0 such that all monitored constraints remain valid on [δ*, δ*+ε], contradicting the definition of δ* as a supremum.

Then define:

lean
Reach :=
  jointSlack δ* = 0

Stuck :=
  (∃ c, supportConstraint δ* c = 0)
  ∨ (∃ r, hemiConstraint δ* r = 0)

The theorem you need is:

lean
theorem strict_persistence_at_reach
    (hreach : Reach)
    (hnotStuck : ¬ Stuck) :
    StrictConvex A* := by

Proof:

lean
-- supports
intro c
have hnonneg : 0 ≤ supportConstraint δ* c := support_closed_at_sup ...
have hne : supportConstraint δ* c ≠ 0 := by
  intro hz
  exact hnotStuck (Or.inl ⟨c, hz⟩)
exact lt_of_le_of_ne' hnonneg hne

-- hemisphere
use h₀
intro r
have hnonneg : 0 ≤ hemiConstraint δ* r := hemi_closed_at_sup ...
have hne : hemiConstraint δ* r ≠ 0 := by
  intro hz
  exact hnotStuck (Or.inr ⟨r, hz⟩)
exact lt_of_le_of_ne' hnonneg hne

So the REACH branch should carry not merely:

lean
jointSlack δ* = 0

but the mutually exclusive branch data:

lean
Reach ∧ ¬ Stuck

or use a trichotomy returning:

lean
| reach : jointSlack δ* = 0 → ¬ Stuck → ...
| stuck : Stuck → ...

That is the formal fix.

Minimal final statements

Use these three as your final targets:

lean
theorem congruent_endpoint_eq
    (hA : WeakConvex A)
    (hB : WeakConvex B)
    (hs : ∀ e, sideLen A e = sideLen B e)
    (hj : ∀ r, jointAngle A r = jointAngle B r) :
    endpt A = endpt B
lean
-- Replace R-C with this; do not prove side-monotone.
theorem splice_transport_of_diag_le
    (hdiag : sDist (A i) (A j) ≤ sDist (B i) (B j))
    ... :
    endpt A ≤ endpt B
lean
theorem strict_persistence_at_reach
    (hreach : jointSlack δ* = 0)
    (hnotStuck :
      ¬ ((∃ c, supportConstraint δ* c = 0)
        ∨ (∃ r, hemiConstraint δ* r = 0))) :
    StrictConvex (openTail A k δ*)

The main important change is: delete R-C as a general theorem. It is not true.