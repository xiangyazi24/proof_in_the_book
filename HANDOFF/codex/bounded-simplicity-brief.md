# CODEX BRIEF (uisai2-local): bounded-joint simplicity -> UNCONDITIONAL Ch13 (FFCT89)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-88 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT89.lean. ON the build machine:
`export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT88 && lake env lean ProofsInTheBook/ZinanFFCT89.lean`.
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new. NO effort cap.

## The gap (HANDOFF/outbox/ch13-simplicity-report.md): the general weakConvex+positiveJoints=>NR
is FALSE (a degenerate weak arm with a joint = pi can self-intersect). The fix uses the pi UPPER
BOUND, which openedWBS HAS. Two-part close:

### Part 1 — the bounded-joint general simplicity theorem
```lean
theorem weakConvex_boundedJoints_noNonadjacentRepeat
    {n : ℕ} {P : Fin (n+1) -> S2}
    (hweak : WeakConvexSphArm P)
    (hpos : PositiveJoints P)
    (hlt  : ∀ i : Fin (n-1), jointAngle P i < Real.pi) :
    NoNonadjacentRepeat P
```
Proof = the pbook 4-step (HANDOFF/design-rounds/ch13-simplicity-route.md §3 + degenerate audit).
The digon base case is LANDED (FFCT88 weakConvex_positiveJoints_no_gap_two_repeat). Do the gap>2
case: face-propagation (FFCT22 OnFoldRay / far_fold_tail_collinear_step iterated; the two weak
supports opposite-multiples => det3=0 => next vertex coplanar, FFCT83/84/85 first-step coplanarity
forcing) => closed face-run on one great circle => some consecutive interior triple coplanar =>
sphAngle_eq_zero_or_pi_of_det3_zero (FFCT21) gives joint = 0 (kill by hpos) OR pi (kill by hlt) =>
contradiction. The hlt hypothesis is exactly what kills the pi branch. Use the closing edge (n,0)
for the s=n sub-case (WeakConvexSphPolygon wrap edge).

### Part 2 — openedWBS has bounded joints, then UNCONDITIONAL
```lean
theorem openedWBS_jointAngle_lt_pi
    {n : ℕ} (A B : Fin (n+1) -> S2) (k : Fin (n-1)) (hstuck : SupportStuckWBS A B k)
    (hB : StrictConvexSphArm B) (hangle : ...) :
    ∀ i, jointAngle (openedWBS A B k) i < Real.pi
```
Route: JointLe (openedWBS A B k) B (landed at the WBS sup — grep openedWBS JointLe / the FFCT46
WBS assembly) gives jointAngle (openedWBS) i <= jointAngle B i; strict B gives jointAngle B i < pi
(grep jointAngle_lt_pi / strictConvex joint upper bound — it must be landed, FFCT used it). Chain.
Then:
```lean
theorem weakPositiveSimplicity_holds_for_openedWBS : (the FFCT88 WeakPositiveSimplicity-shape
  specialized so that crossPieceCollisionEndpointAtSup_of_weakPositiveSimplicity fires) := ...
theorem crossPieceCollisionEndpointAtSup_unconditional : CrossPieceCollisionEndpointAtSup := ...
theorem spherical_arm_mono_ch13 : SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v11 crossPieceCollisionEndpointAtSup_unconditional
```
NOTE: FFCT88's WeakPositiveSimplicity is weakConvex+positiveJoints (no pi bound). If
crossPieceCollisionEndpointAtSup_of_weakPositiveSimplicity needs THAT exact shape, instead route
the collision directly: at the collision the opened arm IS weakConvex + positiveJoints +
(jointAngle < pi via Part 2), so weakConvex_boundedJoints_noNonadjacentRepeat applies directly =>
the collision (a nonadjacent repeat) is impossible => False. Build
crossPieceCollisionEndpointAtSup_unconditional from weakConvex_boundedJoints_noNonadjacentRepeat +
openedWBS_jointAngle_lt_pi + the landed openedWBS weakConvex/positiveJoints at the sup.

## Deliverable: ZinanFFCT89.lean (0 errors, clean-3) with weakConvex_boundedJoints_noNonadjacentRepeat
+ openedWBS_jointAngle_lt_pi + crossPieceCollisionEndpointAtSup_unconditional + spherical_arm_mono_ch13
(THE UNCONDITIONAL CHAPTER HEADLINE) if it closes, else the sharpest partial + report at
HANDOFF/outbox/ch13-unconditional-report.md. No git commit. Grind to terminal — this closes Ch13.
