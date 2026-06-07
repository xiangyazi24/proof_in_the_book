The right way to assemble this is not to make the stuck support endpoint-incident. Treat “support vanished somewhere” as a terminal reduction rule before doing any more opening. The induction theorem must be slightly stronger than the final theorem: the left arm is allowed to be closed/weakly convex, so that the δ* stuck arm is still an admissible input. The high-level statement is the usual spherical Cauchy arm lemma: increasing the intervening angles of a convex spherical arm cannot decrease the omitted endpoint side. 
MathOverflow

Below is the mechanizable skeleton.

1. Inductive invariant

Do not recurse only on strictly convex left arms. Use:

lean
Main(n) :
  ∀ A B : Arm n,
    WeakConvex A →          -- supports ≥ 0, sides short, hemisphere
    StrictConvex B →        -- supports > 0
    SameSides A B →
    JointLe A B →
    sDist (A 0) (A n) ≤ sDist (B 0) (B n)

The final theorem is Main(n) applied with StrictConvex A, since:

lean
StrictConvex A → WeakConvex A

The recursion measure is:

lean
measure(A,B) :=
  (n, deficitCount A B)

deficitSet A B :=
  { k : Interior n | jointAngle A k < jointAngle B k }

deficitCount A B := (deficitSet A B).card

ordered lexicographically.

The key point is that STUCK reduces n through the cut lemma, while REACH keeps n but strictly reduces deficitCount.

2. First case: weak support already vanished

At the top of every recursive call, split first on:

lean
∃ i j, NonIncidentEdgeVertex i j ∧ support A i j = 0

If this holds, do not open anything. Invoke your already-proved anySupportCut theorem.

The theorem should have this shape:

lean
theorem anySupportCut
    {n : ℕ} {A B : Arm n}
    (hA : WeakConvex A)
    (hB : StrictConvex B)
    (hsides : SameSides A B)
    (hjoints : JointLe A B)
    (hzero :
      ∃ i j, NonIncidentEdgeVertex i j ∧ support A i j = 0)
    (IH :
      ∀ {m : ℕ}, m < n → Main m) :
    endpt A ≤ endpt B

This is where the arbitrary interior stuck support belongs. The main opening induction should not try to special-case endpoint supports.

3. Interior STUCK cut: exact normalization and subarms

Suppose the vanished support is:

lean
support A i j = det3 (A i) (A (i+1)) (A j) = 0

with j ≠ i, j ≠ i+1.

There are two order cases. Normalize by reversing both arms if necessary:

lean
i + 1 < j

The reverse case j < i is literally the same after applying:

lean
reverseArm A
reverseArm B

and using:

lean
endpt_reverse      : endpt (reverseArm A) = endpt A
sameSides_reverse  : SameSides A B → SameSides (reverseArm A) (reverseArm B)
jointLe_reverse    : JointLe A B → JointLe (reverseArm A) (reverseArm B)
weakConvex_reverse : WeakConvex A → WeakConvex (reverseArm A)
strict_reverse     : StrictConvex B → StrictConvex (reverseArm B)

Now with i+1 < j, the relevant pieces are:

lean
earA  := intervalArm A (i+1) j
earB  := intervalArm B (i+1) j

capA  := intervalArm A i j
capB  := intervalArm B i j

bodyA := spliceArm A i j
-- vertices: A 0, ..., A i, A j, A (j+1), ..., A n

bodyB := spliceArm B i j
-- vertices: B 0, ..., B i, B j, B (j+1), ..., B n

But the important warning is:

bodyA and bodyB are not matched-SAS arms, because the new diagonal side satisfies only
sDist (A i) (A j) ≤ sDist (B i) (B j), not equality.

So the correct cut proof is not:

lean
apply IH to bodyA bodyB using SameSides

That is the naive step that fails.

The cut lemma instead uses the ear/cap comparison plus the spherical triangle inequality to transport the diagonal inequality.

For the normalized case i+1 < j, weak convexity plus support-zero gives the spherical betweenness orientation:

lean
sBetween (A (i+1)) (A i) (A j)

or equivalently:

lean
sDist (A (i+1)) (A j)
  =
sideLen A i + sDist (A i) (A j)

This is the “folded-flat” orientation: A i lies between A (i+1) and A j. This is the orientation that makes the flat local configuration minimal, not maximal.

Then the recursive comparison on the ear gives:

lean
hEar :
  sDist (A (i+1)) (A j)
    ≤
  sDist (B (i+1)) (B j)

because earA and earB are proper subarms with the original side and joint inequalities.

Using betweenness and equal side sideLen A i = sideLen B i:

lean
sDist (A i) (A j)
  =
sDist (A (i+1)) (A j) - sideLen A i

while the reverse triangle inequality in the spherical triangle
B i, B (i+1), B j gives:

lean
sDist (B (i+1)) (B j) - sideLen B i
  ≤
sDist (B i) (B j)

Therefore:

lean
diag_le :
  sDist (A i) (A j) ≤ sDist (B i) (B j)

This is the exact place where the asymmetry is resolved: A is flat, B is not; the reverse triangle inequality says the bent B-diagonal is at least the folded-flat A-diagonal.

After that, your anySupportCut theorem glues this diagonal inequality back into the endpoint comparison. If you expose the internals, it is best to package the body step as a separate lemma, not as ordinary matched recursion:

lean
theorem splice_transport_of_diag_le
    (hA : WeakConvex A)
    (hB : StrictConvex B)
    (hsides : SameSides A B)
    (hjoints : JointLe A B)
    (hzero : support A i j = 0)
    (hij : i+1 < j)
    (hdiag : sDist (A i) (A j) ≤ sDist (B i) (B j))
    (IHproper : ∀ {m}, m < n → Main m) :
    endpt A ≤ endpt B

Then:

lean
anySupportCut =
  normalize order by reversal
  prove hEar by IH on intervalArm A (i+1) j
  prove diag_le by betweenness + reverse triangle inequality
  exact splice_transport_of_diag_le ... diag_le ...

So the two actual geometric pieces are:

lean
earA  = A[i+1 .. j]
bodyA = A[0 .. i] ++ A[j .. n]

but only the ear is a plain equal-side recursive comparison. The body/glue is the special cut-transport theorem. That is why the interior stuck case is harmless.

4. If no support vanished, A is strict

After the initial cut check:

lean
¬ ∃ i j, NonIncidentEdgeVertex i j ∧ support A i j = 0

from WeakConvex A you prove:

lean
hAstrict : StrictConvex A

because every support is ≥ 0, and none is = 0, hence every support is > 0.

Now split on deficits.

If there is no deficient joint:

lean
¬ ∃ k, jointAngle A k < jointAngle B k

then with JointLe A B:

lean
∀ k, jointAngle A k = jointAngle B k

and your congruence theorem gives:

lean
endpt A = endpt B

so the result follows.

5. REACH/STUCK opening step

Choose a deficient joint:

lean
k : Interior n
hk : jointAngle A k < jointAngle B k

Define the opened arm:

lean
openTail A k δ

by fixing vertices ≤ k and rotating the tail vertices k+1, ..., n around the axis A k:

lean
(openTail A k δ) r =
  if r ≤ k then A r else Rodrigues (A k) δ (A r)

Your admissible set is:

lean
Admissible δ :=
  0 ≤ δ ∧
  jointAngle (openTail A k δ) k ≤ jointAngle B k ∧
  WeakConvex (openTail A k δ)

or strict convexity for δ < δ*, with closure at δ*.

Let:

lean
δ* := sSup { δ | Admissible δ }
A* := openTail A k δ*

You already have:

lean
endpoint_open_mono :
  endpt A ≤ endpt A*

and the trichotomy:

lean
REACH : jointAngle A* k = jointAngle B k

or

lean
STUCK : ∃ i j, NonIncidentEdgeVertex i j ∧ support A* i j = 0
6. REACH branch: why the deficit count decreases

This branch is clean because opening the tail preserves every side and every joint except the opened one.

You need the following lemma stated exactly:

lean
theorem openTail_preserves_sides
    (r : EdgeIndex n) :
    sideLen (openTail A k δ) r = sideLen A r

Proof split:

lean
r < k      -- both endpoints fixed
r = k      -- A k fixed, A(k+1) rotated by isometry fixing A k
k < r      -- both endpoints rotated by the same spherical isometry

For joints:

lean
theorem openTail_preserves_joint_ne
    {r : Interior n} (hr : r ≠ k) :
    jointAngle (openTail A k δ) r = jointAngle A r

Proof split:

lean
r < k      -- all three vertices fixed
r = k      -- excluded
k < r      -- all three vertices are images under the same rotation

For r = k, by construction in the REACH case:

lean
jointAngle A* k = jointAngle B k

Therefore:

lean
deficitSet A* B = (deficitSet A B).erase k

because:

lean
k ∈ deficitSet A B
k ∉ deficitSet A* B
∀ r ≠ k, r ∈ deficitSet A* B ↔ r ∈ deficitSet A B

Hence:

lean
deficitCount A* B < deficitCount A B

The recursive call is at the same n but smaller second measure:

lean
have hrec : endpt A* ≤ endpt B :=
  IH_same_n_smaller_deficit A* B hAstarStrict hB hsidesAstar hjointsAstar hdef_lt

exact le_trans endpoint_open_mono hrec

This answers your obstruction (b): yes, the deficit count strictly decreases. Opening joint k does not disturb the other joint comparisons.

7. STUCK branch: no measure problem

In the STUCK branch you have:

lean
hAstarWeak : WeakConvex A*
hzero :
  ∃ i j, NonIncidentEdgeVertex i j ∧ support A* i j = 0

Also:

lean
SameSides A* B

because opening preserves all side lengths, and:

lean
JointLe A* B

because the opened joint is still admissible, and all other joints are preserved.

Then simply invoke the cut rule:

lean
have hcut : endpt A* ≤ endpt B :=
  anySupportCut
    hAstarWeak
    hB
    hsidesAstar
    hjointsAstar
    hzero
    (fun {m} hm => IH_smaller_n hm)

exact le_trans endpoint_open_mono hcut

The recursion hidden inside anySupportCut is only on proper subarms, so the first coordinate n decreases. It does not matter where the vanished support is. Interior stuck supports are exactly what anySupportCut is for.

8. Full Lean-style skeleton
lean
theorem spherical_SZ_aux :
    ∀ n, Main n := by
  intro n
  -- better implemented by WellFounded.fix on (n, deficitCount)
  refine wellFounded_lex.fix ?_ n
where
  step :
    ∀ n,
      (∀ m, m <lex n → Main m) →
      Main n
  | n, IH, A, B, hAweak, hBstrict, hsides, hjoints => by

      -- 1. Cut before opening.
      by_cases hzero :
        ∃ i j, NonIncidentEdgeVertex i j ∧ support A i j = 0
      · exact
          anySupportCut
            hAweak hBstrict hsides hjoints hzero
            (by
              intro m hm
              exact IH (m, arbitraryDeficit) (lex_left hm))

      -- 2. Now A is strict.
      have hAstrict : StrictConvex A :=
        strict_of_weak_no_zero hAweak hzero

      -- 3. If no deficient joint, use congruence.
      by_cases hdef : ∃ k, jointAngle A k < jointAngle B k
      · rcases hdef with ⟨k, hk⟩

        let δstar := openingSup A B k
        let Astar := openTail A k δstar

        have hmono : endpt A ≤ endpt Astar :=
          endpoint_open_to_sup_mono A B k δstar

        have hsides_star : SameSides Astar B := by
          intro e
          calc
            sideLen Astar e = sideLen A e := openTail_preserves_sides A k δstar e
            _ = sideLen B e := hsides e

        have hjoints_star : JointLe Astar B := by
          intro r
          by_cases hr : r = k
          · subst hr
            exact opened_joint_le_at_sup A B k δstar
          · calc
              jointAngle Astar r = jointAngle A r :=
                openTail_preserves_joint_ne A k δstar hr
              _ ≤ jointAngle B r := hjoints r

        rcases opening_trichotomy A B k δstar with hreach | hstuck

        · -- REACH
          have hAstarStrict : StrictConvex Astar :=
            strict_persistence_at_reach A B k δstar hreach

          have hdef_lt :
              deficitCount Astar B < deficitCount A B := by
            -- prove deficitSet Astar B = (deficitSet A B).erase k
            exact deficit_count_decreases_reach
              hk hreach (openTail_preserves_joint_ne A k δstar)

          have hrec : endpt Astar ≤ endpt B :=
            IH (n, deficitCount Astar B)
              (lex_right hdef_lt)
              Astar B
              (StrictConvex.toWeak hAstarStrict)
              hBstrict
              hsides_star
              hjoints_star

          exact le_trans hmono hrec

        · -- STUCK
          rcases hstuck with ⟨i, j, hnoninc, hzero_star⟩

          have hAstarWeak : WeakConvex Astar :=
            weak_closed_at_sup A B k δstar

          have hcut : endpt Astar ≤ endpt B :=
            anySupportCut
              hAstarWeak
              hBstrict
              hsides_star
              hjoints_star
              ⟨i, j, hnoninc, hzero_star⟩
              (by
                intro m hm
                exact IH (m, arbitraryDeficit) (lex_left hm))

          exact le_trans hmono hcut

      · -- no deficient joint
        have hall :
            ∀ k, jointAngle A k = jointAngle B k := by
          intro k
          exact le_antisymm (hjoints k) (not_lt.mp (by
            intro hlt
            exact hdef ⟨k, hlt⟩))

        exact le_of_eq
          (congruent_endpoint_eq hAstrict hBstrict hsides hall)

In real Lean, do not literally use arbitraryDeficit; define the well-founded call on the actual pair:

lean
(A',B') ↦ (m, deficitCount A' B')

and prove either:

lean
m < n

or:

lean
m = n ∧ deficitCount A' B' < deficitCount A B
9. The essential answer to your two obstructions

For (a): an interior stuck triple is not converted into an endpoint stuck triple of the original arm. Normalize it to i+1 < j, cut off the ear

lean
A[i+1 .. j]

and use the flat support to prove the diagonal inequality

lean
sDist (A i) (A j) ≤ sDist (B i) (B j)

by:

lean
ear recursion + spherical reverse triangle inequality.

Then let your anySupportCut theorem glue this diagonal inequality back to the endpoint comparison. Do not attempt a matched-SAS recursion on the spliced body; the new diagonal is only weakly shorter on A.

For (b): in the REACH branch, the measure decreases because openTail preserves every side and every joint except k. Thus

lean
deficitSet A* B = (deficitSet A B).erase k

and the second component of the lexicographic measure strictly decreases.

The induction order is therefore:

lean
support-zero cut  →  no support zero means strict  →  no deficit congruent  →  open one deficient joint  →  REACH or STUCK

That ordering is the whole trick.