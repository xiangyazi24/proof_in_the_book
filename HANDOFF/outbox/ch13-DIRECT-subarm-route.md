I’ll treat this as a truth-risk review: first-contact need not mean unique contact, so I’ll compare FFCT110’s exact bridge against what WBS can non-circularly supply.

I found FFCT110’s global AtMostOneZero is stronger than the bridge’s real need: only the collision and final-ray double-zero patterns matter. The remaining issue is whether WBS supplies a non-generic “no bad active set” fact.

The right call is: do not commit openedWBS to AtMostOneZero. That hypothesis is too strong and is not structurally guaranteed by a support-stuck supremum. The clean direction is to prove ProperCrossPieceNoCollisionAtSup directly by lower-dimensional spherical-arm monotonicity on each proper subarm, not through the planar turning/no-repeat route.
Here is the precise resolution.

1. Can WBS bind two supports simultaneously?
Yes. Nothing in the WBS supremum mechanism prevents simultaneous first contact.
The monitored family is finite and contains one support constraint for every nonincident edge–vertex pair:
leandef NonIncident (n : ℕ) : Type :=  {c : Fin (n + 1) × Fin (n + 1) // c.2 ≠ c.1 ∧ c.2 ≠ c.1 + 1}
and
leansupportConstraint A K c θ=sOrient (openTail A K θ c.i)        (openTail A K θ (c.i + 1))        (openTail A K θ c.j)
SphericalMonitoredSup
At a support-stuck supremum, the current extraction gives only existence of a vanished nonincident support, not uniqueness. SphericalOpeningGlue
A symmetric tie is completely possible. The construction is:


Choose a strictly convex spherical arm $A$ with a reflection symmetry preserving the opening axis $A_K$.


Choose two nonincident edge–vertex pairs $c_1,c_2$ exchanged by that reflection.


Choose $B$ symmetrically, with the opened joint target sufficiently large that support contact happens before reach.


Along the symmetric opening, the two monitored support functions are identical:




$$\operatorname{supportConstraint}_{c_1}(\delta)
=
\operatorname{supportConstraint}_{c_2}(\delta)$$


for every $\delta$.
If that common function is the first support function to reach zero, then both supports bind at the same supremum angle. This is not a degeneracy excluded by strict convexity, equal side lengths, or JointLe; it is just a tie among finitely many continuous constraints.
So:
leanAtMostOneZero
is not a valid spherical fact for openedWBS unless one adds a genericity/tie-breaking hypothesis. It should not be used as an operational hypothesis for the actual WBS object.

2. The weaker planar hypothesis is correct but still not the best spherical route
Your observation is right: the planar suffix proof does not need global AtMostOneZero. It only uses that the following two specific bad double-zero patterns cannot occur.
Let


$$Z(i,j) :\Longleftrightarrow
\det(Q_i,Q_{i+1},Q_j)=0$$


for a nonincident edge–vertex pair.
Pattern A: collision double zero
If $Q_k=Q_n$, then two zeros occur:


$$Z(k,n)$$


because the support vertex $Q_n$ equals the edge endpoint $Q_k$, and


$$Z(n-1,k)$$


because the support vertex $Q_k$ equals the final endpoint $Q_n$.
So the planar suffix proof only needs:


$$\forall k,\quad
\neg \bigl(Z(k,n)\wedge Z(n-1,k)\bigr).$$


Lean shape:
leandef NoCollisionZeroPair (Q : Fin (n + 1) → E3) : Prop :=  ∀ k : ℕ, 1 ≤ k → k ≤ n - 2 →    ¬ (      det3 (Q ⟨k, by omega⟩)           (Q ⟨k + 1, by omega⟩)           (Q ⟨n, by omega⟩) = 0 ∧      det3 (Q ⟨n - 1, by omega⟩)           (Q ⟨n, by omega⟩)           (Q ⟨k, by omega⟩) = 0)
Pattern B: bad final-ray double zero
The bad suffix angle


$$b_k=(\theta_{n-1}-\theta_k)-a_k=\pi$$


means


$$Q_k=Q_n+\lambda(Q_n-Q_{n-1})
\quad\text{for some }\lambda>0.$$


That forces:


$$Z(n-1,k)$$


and


$$Z(n,n-1),$$


i.e. final-edge tangency at $Q_k$, and closing-edge tangency at $Q_{n-1}$.
So the planar suffix proof only needs to forbid:


$$Z(n-1,k)\wedge Z(n,n-1)\wedge
Q_k\in Q_n+\mathbb{R}_{>0}(Q_n-Q_{n-1}).$$


Lean shape:
leandef NoBadFinalRayPair (Q : Fin (n + 1) → E3) : Prop :=  ∀ k : ℕ, 1 ≤ k → k ≤ n - 2 →    ¬ (      det3 (Q ⟨n - 1, by omega⟩)           (Q ⟨n, by omega⟩)           (Q ⟨k, by omega⟩) = 0 ∧      det3 (Q ⟨n, by omega⟩)           (Q ⟨0, by omega⟩)           (Q ⟨n - 1, by omega⟩) = 0 ∧      ∃ λ : ℝ, 0 < λ ∧        Q ⟨k, by omega⟩ =          Q ⟨n, by omega⟩ +          λ • (Q ⟨n, by omega⟩ - Q ⟨n - 1, by omega⟩))
This planar weakening is mathematically right. Harmless simultaneous tangencies elsewhere are allowed.
But the spherical question is: does openedWBS prove these two forbidden-pattern hypotheses non-circularly?
For NoCollisionZeroPair, not from the support-stuck mechanism alone. The forbidden collision pattern is exactly an endpoint cross-piece collision $Q_k=Q_n$, which is a subcase of ProperCrossPieceNoCollisionAtSup, the goal. The support-stuck mechanism being “first contact” does not rule it out: a moving tail vertex can first contact the fixed convex hull at an existing fixed vertex, producing two simultaneous zero supports.
For NoBadFinalRayPair, first-contact also does not rule it out. It is a simultaneous pair of proper tangencies, and simultaneous first contact is possible by symmetry.
Therefore, the weakened planar hypothesis is better than AtMostOneZero, but it is still not a clean spherical supply unless you prove those forbidden patterns by some independent geometric argument.

3. Why “first contact” does not by itself rule out the collision pair
A collision


$$Q_k=Q_n$$


creates two support zeros:


$$\det(Q_k,Q_{k+1},Q_n)=0,$$




$$\det(Q_{n-1},Q_n,Q_k)=0.$$


Both are nonincident in the index sense when $1\le k\le n-2$. The monitored family sees both as support constraints.
If the WBS supremum is the first time any monitored support reaches zero, then a collision can be the first contact: the two support constraints simply bind simultaneously. This is not excluded by weak support, strict consecutive turns, open hemisphere, or the finite supremum definition.
The assertion “the stuck contact is a tangency, not a collision” is useful only if it is proved for every zero support at the supremum, not just for the chosen support witness. If there are two or more zeros, one chosen zero may be a proper tangency while another zero is collision-induced. The planar bridge needs to know that the collision-induced pair cannot exist.
So the honest non-circular options are:


prove directly that every zero support at the WBS supremum is geometrically proper, meaning the support vertex is distinct from both edge endpoints; or


prove ProperCrossPieceNoCollisionAtSup directly by another route.


Option 1 is essentially a no-collision theorem for zero-contact pairs. It may still be possible, but it should not be advertised as a consequence of “first support contact” alone.

4. The clean route: prove ProperCrossPieceNoCollisionAtSup directly by subarm induction
This is the direction I would commit to.
For a proper cross-piece pair


$$r\le K<s,\qquad r+2\le s,$$


consider the subarm


$$A^{r,s}(t)=A_{r+t},
\qquad
t=0,\dots,s-r.$$


The opening axis $K$ becomes the interior axis


$$K' = K-r$$


of this smaller arm.
The openedWBS restricted to this subarm is exactly the opened subarm:


$$(\operatorname{openedWBS} A B k)_{r+t}
=
\operatorname{openTail}(A^{r,s},K',-\delta^*)(t),$$


where $\delta^*$ is the WBS supremum angle.
The number of edges of this subarm is


$$m=s-r.$$


Because the pair is proper and the full closure $r=0,s=n$ is handled separately, we have


$$2\le m<n.$$


So the lower-dimensional spherical arm theorem applies to this subarm.
Direct proof skeleton
Assume, for contradiction,


$$\operatorname{openedWBS}(r)=\operatorname{openedWBS}(s).$$


Then the endpoint distance of the opened subarm is zero:


$$\operatorname{endpt}\bigl(\operatorname{openTail}(A^{r,s},K',-\delta^*)\bigr)=0.$$


But the original subarm $A^{r,s}$ is strictly convex, hence has no nonadjacent repeats. The repo already proves:
leanstrictConvex_noNonadjacentRepeat :  StrictConvexSphArm A → NoNonadjacentRepeat A
ZinanFFCT68
Since $r+2\le s$, the original endpoints $A_r,A_s$ are nonadjacent, so


$$A_r\ne A_s,$$


and therefore


$$0<\operatorname{sDist}(A_r,A_s).$$


By the lower-dimensional spherical arm monotonicity theorem applied to the subarm,


$$\operatorname{sDist}(A_r,A_s)
\le
\operatorname{sDist}(\operatorname{openedWBS}(r),
                     \operatorname{openedWBS}(s)).$$


The right side is zero under the collision assumption, contradiction.
Thus


$$\operatorname{openedWBS}(r)\ne \operatorname{openedWBS}(s).$$


This proves ProperCrossPieceNoCollisionAtSup without planar turning, without suffix nondegeneracy, without AtMostOneZero, and without needing uniqueness of the stuck support.

5. Why this route is non-circular
The final theorem you want is a same-level no-collision statement for an $n$-edge arm.
The direct subarm proof uses only the spherical arm theorem for strictly smaller arms:


$$m=s-r<n.$$


That is legitimate in the main Schoenberg–Zaremba induction.
The current repo already has infrastructure pointing in this direction: same-piece no-repeat is proved directly from strictness and rotation injectivity; only cross-piece no-collision is isolated as the remaining payload. ZinanFFCT68
The proper cross-piece pair is exactly the situation where the subarm is smaller than the full arm. The full closure $r=0,s=n$ is the only case where $m=n$; you said that case is handled separately by endpt = 0, so it should be excluded from this subarm induction proof.

6. Lean-level theorem to prove instead
Define the direct endpoint-subarm supply:
leandef ProperCrossPieceNoCollisionByIH : Prop :=  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),    StrictConvexSphArm A →    StrictConvexSphArm B →    SameSides A B →    JointLe A B →    ∀ k : Fin (n - 1),      jointAngle A k < jointAngle B k →      SupportStuckWBS A B k →      (∀ m : ℕ, m < n → MainPlus m) →      ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),        r + 2 ≤ s →        r ≤ (openingAxis k).val →        (openingAxis k).val < s →        ¬ (r = 0 ∧ s = n) →        openedWBS A B k ⟨r, hr⟩ ≠ openedWBS A B k ⟨s, hs⟩
The proof obligations are:
Lemma 1: subarm strictness
leanlemma strictConvex_subarm    (hA : StrictConvexSphArm A)    (hr : r < n + 1) (hs : s < n + 1)    (hrs : r + 2 ≤ s) :    StrictConvexSphArm (fun t : Fin (s - r + 1) =>      A ⟨r + t.val, by omega⟩)
This is routine restriction of strict supports, short edges, positive joints, and open hemisphere.
Lemma 2: openedWBS restriction equals subarm opening
leanlemma openedWBS_restrict_eq_openTail_subarm    :    openedWBS A B k ⟨r + t.val, by omega⟩      =    openTail A_sub K' (-(monitoredSupWBS A B k)) t
where


$$A_{\text{sub}}(t)=A_{r+t},
\qquad
K'=K-r.$$


This follows from the definition of openTail: vertices with global index ≤ K are fixed, vertices with global index > K are rotated by the same rotation about A K.
Lemma 3: side lengths are preserved
For the comparison between A_sub and the opened subarm:
lean∀ i : Fin m,  sideLen A_sub i = sideLen Opened_sub i
This is because:


fixed-fixed edges are unchanged,


rotated-rotated edges are preserved by rotation,


the crossing edge with endpoint at the axis is preserved because rotation fixes the axis and preserves distance.


The repo already uses the fact that the rotation fixes the axis:
leanrotS2_axis_fixed
SphericalSZFinal
and rotation is an isometry, as used for joint-angle invariance. SphericalSZFinal
Lemma 4: joint inequalities for the opened subarm
lean∀ i : Fin (m - 1),  jointAngle A_sub i ≤ jointAngle Opened_sub i
All joints except the opened one are preserved. The repo already has the preservation lemma:
leanjointAngle_openTail_eq_of_ne
for every joint other than the opened joint. SphericalSZFinal
The opened joint is widened by construction of WBS. The sign-corrected opening direction is already identified in the repo: opening by -δ is the genuine widening direction. SphericalOpeningGlue
Lemma 5: approximate strictness or weak-target extension
The opened arm at the supremum may be only weak, not strict. If the lower-dimensional theorem requires the target arm to be strict, use one of these two approaches:
Approach A: limit from below. For $\delta<\delta^*$ inside the admissible interval, the opened subarm is strict. Apply the lower-dimensional theorem to those strict opened subarms and pass to the limit by continuity of sDist.
Approach B: prove a weak-target corollary. The monotonicity conclusion is closed under limits, so package once:
leantheorem spherical_arm_mono_weakTarget_of_limit    :    -- strict source, weak convex target obtained as a limit of strict targets    sDist source₀ source_last ≤ sDist target₀ target_last
Approach A is more direct if the monitored-supremum API gives a sequence or interval of strict admissible angles below $\delta^*$. Approach B is cleaner if the repo already has weak convexity at the stuck boundary.
Either way, this is a standard closure argument and does not use no-collision.
Lemma 6: original subarm endpoints are distinct
Because $A$ is strict:
leanhave hnr : NoNonadjacentRepeat A :=  strictConvex_noNonadjacentRepeat hA
ZinanFFCT68
Then $r+2\le s$ gives


$$A_r\ne A_s.$$


Therefore


$$0<sDist(A_r,A_s).$$


The collision assumption gives


$$sDist(opened_r,opened_s)=0.$$


The lower-dimensional monotonicity gives a contradiction.

7. What to do with FFCT110
Keep FFCT110 as a valid planar theorem, but do not make it the main supply route for openedWBS unless you add a real, non-circular spherical proof of the forbidden double-zero patterns.
The safe dependency graph is:
Proper subarm IH    ↓ProperCrossPieceNoCollisionAtSup    ↓openedWBS no-repeat supply    ↓downstream endpoint/cut machinery
Not:
AtMostOneZero / forbidden double-zero    ↓suffix nondegeneracy    ↓turning < 2π    ↓no-repeat    ↓ProperCrossPieceNoCollisionAtSup
The latter route keeps trying to prove no-collision by smuggling in a no-collision-equivalent condition.

Final recommendation
Commit to direct subarm induction for ProperCrossPieceNoCollisionAtSup.
Do not try to prove global AtMostOneZero for openedWBS. It is false under symmetric simultaneous contacts.
Do not rely on “first contact” to forbid the collision double-zero pattern. First contact can be a simultaneous multi-contact.
The non-circular proof of proper cross-piece no-collision is:


$$\text{collision at }(r,s)
\Longrightarrow
\text{opened proper subarm endpoint distance }=0,$$


but lower-dimensional Schoenberg–Zaremba monotonicity gives


$$0<
sDist(A_r,A_s)
\le
sDist(opened_r,opened_s),$$


contradiction.
That route is faithful to the WBS geometry, allows multiple harmless tangencies, and avoids all planar turning degeneracies.
