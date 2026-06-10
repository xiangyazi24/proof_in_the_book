I’ll pin the indexing first: in the repo openTail A K δ takes the axis vertex K, while the deficient joint index k : Fin (n-1) uses K = openingAxis k = k+1. That distinction changes which adjacent joint is actually endangered.

1. Brick A: first fix the indexing

In the repo, openTail A K δ takes an axis vertex K : Fin (n+1), while a deficient joint k : Fin (n-1) is opened with K = openingAxis k = ⟨k.val+1,_⟩. The existing preservation lemma says a joint r is preserved if r.val + 2 ≤ K.val or K.val < r.val; the comment says the non-covered joints are r = K-1 and r = K. 

SphericalSZInduction

For a deficient joint index k, this means:

r = k is the target opened joint.

r = k+1 is the other non-covered joint.

r = k-1 is already preserved, because (k-1)+2 = k+1 = K.

So the dangerous “previous joint k-1” is a notation mismatch. The true extra joint is the upper adjacent joint k+1, and geometrically it is preserved because the triple (A K, A(K+1), A(K+2)) is the rotation of the original triple; rotS2 fixes A K and rotates the other two vertices.

2. Brick A1: preserve the upper adjacent joint
lean
theorem openTail_preserves_joint_axis
    {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (δ : ℝ)
    {r : Fin (n - 1)}
    (hr : r.val = K.val)
    (hK2 : K.val + 2 < n + 1) :
    jointAngle (openTail A K δ) r = jointAngle A r

Proof sketch: rewrite jointAngle; the three vertices are A K, A(K+1), A(K+2). Rewrite openTail A K δ K = A K, then rewrite it as rotS2 (A K) δ (A K) using the axis-fixing lemma, and rewrite the other two vertices by openTail_rot; conclude by sphAngle_rotS2. This complements openTail_preserves_joint_offaxis, which did not cover r.val = K.val.

Classification: routine/needs-care.

3. Brick A2: target joint monotonicity / formula
lean
theorem openedInteriorJointAngle_eq_add
    {n : ℕ} {A : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hδcap : jointAngle A k + δ ≤ Real.pi)
    (horient : OpeningDirectionPositive A k) :
    openedInteriorJointAngle A k δ = jointAngle A k + δ

Proof sketch: use the tangent-plane action of rotS2 recorded in SphericalRotation: rotS2 rotates the tangent direction by δ, and openedInteriorJointAngle is exactly the angle between the fixed incoming tangent and the rotated outgoing tangent. The hδcap hypothesis prevents wraparound through π, so arccos returns the intended branch. If the sign of the current rotS2 convention is opposite, define OpeningDirectionPositive A k to choose δ ↦ -δ; do not bury the sign in tactics.

Classification: genuinely-hard, because this is the branch-control theorem.

4. Brick A3: positivity at δ*
lean
theorem openTail_positiveJoints_at_sup
    {n : ℕ} {A : Fin (n + 1) → S2} {k : Fin (n - 1)} {δ : ℝ}
    (hApos : PositiveJoints A)
    (hδ : 0 ≤ δ)
    (hreachBound :
      openedInteriorJointAngle A k δ ≤ Real.pi)
    (hdir : OpeningDirectionPositive A k) :
    PositiveJoints (openTail A (openingAxis k) δ)

Proof sketch: split on a joint index r. If r is off-axis, use openTail_preserves_joint_offaxis; if r = k+1, use openTail_preserves_joint_axis; if r = k, use openedInteriorJointAngle_eq_add and hApos k. Thus no new “joint hits 0” event is needed once the true indexing is fixed.

Classification: needs-care after A1/A2.

5. Brick A4: admissibility predicate should not include all PositiveJoints

Do not make “joint hits 0” a new δ*-binding event unless A2 fails. The correct repaired admissibility is:

lean
def InteriorAdmissiblePlus
    {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (T Tcap δ : ℝ) : Prop :=
  δ ∈ Set.Icc 0 Tcap ∧
  (∀ o, 0 ≤ interiorCombined A k T o δ)

Then prove PositiveJoints (openTail ...) as a theorem from admissibility plus A1/A2, not as a monitored constraint. The current repo’s interior_reachOrStuck_at_sup already works over interiorCombined, yielding CAP/REACH/STUCK. 

SphericalSZClose

Classification: routine refactor.

6. Brick A5: modified reach/stuck dispatch
lean
theorem interior_reachOrStuck_plus_dispatch
    {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hA : WeakConvexSphArm A) (hApos : PositiveJoints A)
    (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (hdir : OpeningDirectionPositive A k)
    :
    ReachPlus A B k ∨ StuckPlus A B k

Sketch: run existing interior_reachOrStuck_at_sup; in the REACH case, construct openTail data and prove PositiveJoints using A3. In the STUCK case, keep the support-zero witness and separately convert it to StuckPlus with Gram signs / nonincident filtering. CAP is eliminated by taking Tcap equal to the target opening amount, or by proving CAP implies REACH.

Classification: genuinely-hard wrapper.

7. Brick B: is “first binding is last-corner-adjacent” true?

I would not rely on it. The current generic engine monitors all triples Fin(n+1)^3; interior_reachOrStuck_at_sup returns arbitrary ∃ ijl, interiorSupport ... ijl δ = 0, with no shape theorem. 

SphericalSZClose

So the robust design is: arbitrary support-zero → normalize to a StuckAtKData if it is nonincident and has the Gram signs; incident/trivial zero is ignored; if the normalized stuck is adjacent last-corner, P5 kills it; if it is far, route through FoldedFlatCutTransportPlus.

8. Brick B1: classify support-zero witnesses
lean
theorem support_zero_dispatch_to_stuck_or_trivial
    {n : ℕ} {A B : Fin (n + 1) → S2} {K : Fin (n + 1)}
    (hA : WeakConvexSphArm A) (hApos : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hside : SameSides A B) (hangle : JointLe A B)
    {ijl : Fin (n + 1) × Fin (n + 1) × Fin (n + 1)}
    (hzero : interiorSupport A K ijl δ = 0) :
    TrivialSupport ijl ∨
      ∃ i j : ℕ, StuckAtKData A B i j

Sketch: expand the triple; discard repeated/incident triples. For nonincident triples, orient the pair so i+1 < j; weak convexity gives support nonnegativity and ShortArc; the missing hard part is deriving the two Gram signs required by StuckAtKData. This is the exact place where old substrate carried Gram signs as hypotheses.

Classification: genuinely-hard.

9. Brick B2: adjacent stuck contradicts PositiveJoints
lean
theorem adjacent_stuck_hcol_forces_joint_zero
    {n : ℕ} {A : Fin (n + 1) → S2} {i : ℕ}
    (hi2 : i + 2 < n + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3),
          (A ⟨i + 2, by omega⟩ : E3)} : Set E3)) :
    jointAngle A (⟨i, by omega⟩ : Fin (n - 1)) = 0

Sketch: hcol gives distance additivity sDist A(i+1) A(i+2) = sDist A(i+1) A(i) + sDist A(i) A(i+2) via foldedFlat_dist_eq. At apex A(i+1), the two tangent directions toward A i and A(i+2) coincide, so sphAngle = 0. Use the same sphAngle_self_zero style as ZinanFFCT17.

Classification: needs-care.

10. Brick B3: no adjacent stuck under PositiveJoints
lean
theorem no_adjacent_stuck_of_positiveJoints
    {n : ℕ} {A B : Fin (n + 1) → S2} {i : ℕ}
    (hpos : PositiveJoints A)
    (hsk : StuckAtKData A B i (i + 2)) :
    False

Sketch: get hcol := stuckAtK_betweenness hsk.hij1 hsk.hj hsk. Apply B2 and contradict hpos ⟨i,_⟩. This handles the last-corner-adjacent event (n-1,n+1) in the opened arm.

Classification: routine after B2.

11. Brick B4: FoldedFlatCutTransportPlus proof strategy

FoldedFlatCutTransportPlus in FFCT18 already has the right shape: positive joints and explicit hcol. 

ZinanFFCT18

Do not prove it by the old spliced-body Main route. That route is structurally dead. Prove it by fold classification:

lean
theorem foldedFlatCutTransportPlus_holds :
    FoldedFlatCutTransportPlus

Sketch: normalize the cut so i+1 < j; if j = i+2, contradict PositiveJoints by B3. If j > i+2, use the sandwich/exclusion lemma to show the fold must be boundary: i = 0 ∧ (j = n ∨ j = n-1). The j=n case is exactly hdiag; the j=n-1 case is endpoint_le_of_tail_fold from FFCT18. 

ZinanFFCT18

Classification: master, but no IH is needed inside the endpoint transport once hdiag and hcol are supplied.

12. Brick B5: far-fold boundary exclusion
lean
theorem far_fold_boundary_classification
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hApos : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B)
    {i j : ℕ} (hij : i + 1 < j) (hj : j < n + 1)
    (hfar : i + 2 < j)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3)) :
    i = 0 ∧ (j = n ∨ j = n - 1)

Sketch: if i ≥ 1, use weak support of edge (i-1,i) at i+1 and j; betweenness makes the two coefficients have opposite signs, forcing the predecessor determinant to be zero. Then the joint at i is 0 or π; PositiveJoints rules out 0, and jointAngle_lt_pi from JointLe + strict B rules out π. Apply the symmetric tail argument for j ≤ n-2.

Classification: genuinely-hard.

13. Brick B6: near-tail endgame

Already banked pointwise in FFCT18:

lean
theorem endpoint_le_of_tail_fold
    {A0 An1 An B0 Bn1 Bn : S2}
    (hflatTail : sDist A0 An1 = sDist A0 An + sDist An An1)
    (hdiag : sDist A0 An1 ≤ sDist B0 Bn1)
    (hsideLast : sDist An An1 = sDist Bn Bn1) :
    sDist A0 An ≤ sDist B0 Bn

Use this for (i,j)=(0,n-1). The required hflatTail comes from hcol via foldedFlat_dist_eq, and the last side equality comes from SameSides. 

ZinanFFCT18

Classification: routine instantiation.

14. Final dispatch for arbitrary support binding
lean
theorem stuck_support_dispatch_plus
    (hcut : FoldedFlatCutTransportPlus)
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hApos : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hside : SameSides A B) (hangle : JointLe A B)
    (ih : ∀ m, m < n → MainPlus m)
    (hzero : interiorSupport A K ijl δ = 0) :
    endpt A ≤ endpt B

Sketch: classify hzero with B1. Trivial supports do not bind; adjacent stuck contradicts P5 via B3; far stuck derives hdiag using stuckAtK_diag_le_plus, derives hcol by stuckAtK_betweenness, and calls hcut. This is the main STUCK branch.

Classification: master wrapper.

15. Corrected full core
lean
def SZOpeningCorePlus : Prop :=
  ∀ n, 2 ≤ n →
    (∀ m, m < n → MainPlus m) →
    ∀ A B : Fin (n + 1) → S2,
      WeakConvexSphArm A → PositiveJoints A →
      StrictConvexSphArm B → SameSides A B → JointLe A B →
      (∀ A' B' : Fin (n + 1) → S2,
        WeakConvexSphArm A' → PositiveJoints A' →
        StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
        deficitCount A' B' < deficitCount A B →
        endpt A' ≤ endpt B') →
      endpt A ≤ endpt B

Sketch: in the no-deficit case, use congruence/equal-joints path. In the deficit case, open the chosen joint and run interior_reachOrStuck_plus_dispatch; REACH uses smaller-deficit IH, STUCK uses stuck_support_dispatch_plus. This replaces the false old SZOpeningStep.

Classification: final master assembly.
