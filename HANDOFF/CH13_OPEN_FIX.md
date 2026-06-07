There is a subtle index/geometry point here: if openTail rotates all vertices > k by the same Rodrigues rotation fixing A k, then the triple at k+1 is actually jointly rotated, because A k = R(A k). So the corrected branch is either: fix the preservation lemma, or, if your current implementation rotates only the suffix after k+1, change the operation.

The correct fix is simpler than options (a)–(d): the standard tail rotation disturbs only joint k. The apparent disturbance of k+1 is a proof/definition mismatch, not a geometric obstruction.

For the operation

lean
Aδ r =
  if r ≤ k then A r else Rot (A k) δ (A r)

the joint at k+1 is preserved because the whole triple

lean
(A k, A (k+1), A (k+2))

is sent to

lean
(Rot (A k) δ (A k),
 Rot (A k) δ (A (k+1)),
 Rot (A k) δ (A (k+2)))

and

lean
Rot (A k) δ (A k) = A k.

So although A k is syntactically fixed in openTail, it is also the rotated image of itself. Your preservation lemma probably failed because the r = k+1 case was not rewritten through this fixed-axis identity.

Correct OPEN operation

Keep the operation exactly as:

lean
def openTail (A : Arm n) (k : Interior n) (δ : ℝ) : Arm n :=
  fun r =>
    if h : (r : ℕ) ≤ k then
      A r
    else
      Rot (A k) δ (A r)

where Rot (A k) δ is the spherical isometry induced by Rodrigues rotation about the unit axis A k.

The required fixed-axis lemma is:

lean
lemma rot_axis_fixed :
    Rot (A k) δ (A k) = A k

and the joint invariance lemma must be stated as:

lean
lemma jointAngle_openTail_eq_of_ne
    {r : Interior n}
    (hr : r ≠ k) :
    jointAngle (openTail A k δ) r = jointAngle A r

The proof split is:

lean
r < k      -- all three vertices fixed
r = k      -- excluded
k < r      -- all three vertices are rotated by Rot(A k) δ

For the delicate case r = k+1, prove it as part of k < r:

lean
openTail A k δ k       = A k
                       = Rot (A k) δ (A k)

openTail A k δ (k+1)   = Rot (A k) δ (A (k+1))

openTail A k δ (k+2)   = Rot (A k) δ (A (k+2))

Then apply joint-angle invariance under the same spherical isometry.

The exact lemma you need

Do not try to prove preservation by “both neighbors moved” reasoning. Prove a general three-point lemma.

lean
lemma jointAngle_eq_of_rot
    (R : SO3)
    (u v w : S²) :
    sphAngle (R u) (R v) (R w) = sphAngle u v w

Then specialize with:

lean
R = Rot (A k) δ
u = A (r-1)
v = A r
w = A (r+1)

For r = k+1, the local goal becomes:

lean
jointAngle (openTail A k δ) (k+1)
  =
sphAngle
  (A k)
  (Rot (A k) δ (A (k+1)))
  (Rot (A k) δ (A (k+2)))

Rewrite the first argument:

lean
rw [← rot_axis_fixed A k δ]

so the goal is:

lean
sphAngle
  (Rot (A k) δ (A k))
  (Rot (A k) δ (A (k+1)))
  (Rot (A k) δ (A (k+2)))
=
sphAngle
  (A k)
  (A (k+1))
  (A (k+2))

which is exactly jointAngle_eq_of_rot.

This is the missing Lean move.

Side preservation

Similarly, all sides are preserved:

lean
lemma sideLen_openTail_eq
    (e : EdgeIndex n) :
    sideLen (openTail A k δ) e = sideLen A e

Case split:

lean
e < k      -- both endpoints fixed
e = k      -- A k fixed = Rot(A k)δ(A k), A(k+1) rotated
k < e      -- both endpoints rotated

The e = k case is the same fixed-axis rewrite:

lean
sDist (A k) (Rot (A k) δ (A (k+1)))
=
sDist (Rot (A k) δ (A k)) (Rot (A k) δ (A (k+1)))
=
sDist (A k) (A (k+1)).
Correct REACH branch

Let

lean
A* := openTail A k δ*

In the REACH case:

lean
hreach : jointAngle A* k = jointAngle B k

You still get:

lean
deficitSet A* B = (deficitSet A B).erase k

because:

lean
jointAngle A* k = jointAngle B k

and for every r ≠ k,

lean
jointAngle A* r = jointAngle A r.

So the deficit count strictly decreases:

lean
lemma deficitCount_openTail_reach_lt
    (hk : jointAngle A k < jointAngle B k)
    (hreach : jointAngle A* k = jointAngle B k)
    (hpres :
      ∀ r ≠ k, jointAngle A* r = jointAngle A r) :
    deficitCount A* B < deficitCount A B

The proof is literally:

lean
deficitSet A* B = (deficitSet A B).erase k

with:

lean
k ∈ deficitSet A B
k ∉ deficitSet A* B
∀ r ≠ k, r ∈ deficitSet A* B ↔ r ∈ deficitSet A B

Then recurse at the same n with smaller deficit count.

lean
have hrec : endpt A* ≤ endpt B :=
  IH_same_n_smaller_deficit
    A* B
    hAstarWeakOrStrict
    hBstrict
    hsides_star
    hjoints_star
    hdef_lt

exact le_trans endpoint_open_mono hrec
Correct STUCK branch

The STUCK branch is unchanged.

You have:

lean
hmono : endpt A ≤ endpt A*
hsides_star : SameSides A* B
hjoints_star : JointLe A* B
hzero : ∃ i j, NonIncidentEdgeVertex i j ∧ support A* i j = 0

where hjoints_star follows from:

lean
r = k      : admissibility gives jointAngle A* k ≤ jointAngle B k
r ≠ k      : jointAngle A* r = jointAngle A r ≤ jointAngle B r

Then:

lean
have hcut : endpt A* ≤ endpt B :=
  anySupportCut
    hAstarWeak
    hBstrict
    hsides_star
    hjoints_star
    hzero
    IH_smaller_n

exact le_trans hmono hcut

No new measure is needed.

What likely went wrong in the mechanization

Your statement

lean
openTail_preserves_joint holds only for joints with index ≠ k, k+1

is true for a weaker syntactic lemma of the form:

lean
the three vertices are literally all fixed
∨ the three vertices are literally all rotated

because at k+1 the predecessor is syntactically fixed.

But geometrically the predecessor is also rotated, since the rotation fixes the axis:

lean
A k = Rot (A k) δ (A k).

So replace the syntactic preservation lemma with a normalized triple lemma:

lean
lemma openTail_joint_triple_eq_rot_or_fixed
    {r : Interior n} (hr : r ≠ k) :
    ∃ R : SphericalIsom,
      openTail A k δ (r-1) = R (A (r-1)) ∧
      openTail A k δ r     = R (A r) ∧
      openTail A k δ (r+1) = R (A (r+1))

where:

lean
if r < k then R = id
if k < r then R = Rot (A k) δ

The k < r case includes r = k+1; the first equality uses rot_axis_fixed.

Then:

lean
lemma jointAngle_openTail_eq_of_ne
    {r : Interior n} (hr : r ≠ k) :
    jointAngle (openTail A k δ) r = jointAngle A r := by
  obtain ⟨R, hprev, hcur, hnext⟩ :=
    openTail_joint_triple_eq_rot_or_fixed A k δ hr
  unfold jointAngle
  rw [hprev, hcur, hnext]
  exact jointAngle_eq_of_isometry R ...
Final corrected OPEN branch
lean
-- choose deficient k
rcases exists_deficit with ⟨k, hkdef⟩

let δ* := openingSup A B k
let A* := openTail A k δ*

have hmono : endpt A ≤ endpt A* :=
  endpoint_open_to_sup_mono A B k δ*

have hsides_star : SameSides A* B := by
  intro e
  calc
    sideLen A* e = sideLen A e := sideLen_openTail_eq A k δ* e
    _ = sideLen B e := hsides e

have hpres_joint :
    ∀ r, r ≠ k → jointAngle A* r = jointAngle A r := by
  intro r hr
  exact jointAngle_openTail_eq_of_ne A k δ* hr

have hjoints_star : JointLe A* B := by
  intro r
  by_cases hr : r = k
  · subst hr
    exact opened_joint_le_at_sup A B k δ*
  · calc
      jointAngle A* r = jointAngle A r := hpres_joint r hr
      _ ≤ jointAngle B r := hjoints r

rcases opening_trichotomy A B k δ* with hreach | hstuck

· -- REACH
  have hdef_lt :
      deficitCount A* B < deficitCount A B :=
    deficitCount_openTail_reach_lt
      hkdef
      hreach
      hpres_joint

  have hrec : endpt A* ≤ endpt B :=
    IH_same_n_smaller_deficit
      A* B
      hAstarWeakOrStrict
      hBstrict
      hsides_star
      hjoints_star
      hdef_lt

  exact le_trans hmono hrec

· -- STUCK
  have hcut : endpt A* ≤ endpt B :=
    anySupportCut
      hAstarWeak
      hBstrict
      hsides_star
      hjoints_star
      hstuck
      IH_smaller_n

  exact le_trans hmono hcut

So the corrected answer is:

Use the original lex-(n, deficitCount) measure.
Use the original tail rotation.
Do not open last-only.
Do not use cyclic shifts.
Do not switch to total angle deficit.
Fix the preservation lemma at r = k+1 by rewriting A k as Rot(A k)δ(A k).

The OPEN branch then works exactly as originally intended: REACH erases one deficit, STUCK cuts to smaller n.