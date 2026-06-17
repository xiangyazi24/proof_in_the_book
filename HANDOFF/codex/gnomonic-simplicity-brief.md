# CODEX BRIEF (uisai2-local): gnomonic convex-position simplicity (FFCT92)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-91 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT92.lean. ON the build machine:
`export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT91 && lake env lean ProofsInTheBook/ZinanFFCT92.lean`.
Rules: no sorry/admit/axiom/native_decide; clean-3. NO effort cap. PROVABLE classical geometry; grind.

## CRITICAL: do NOT route through FFCT91's FaceContiguityPropagation. Master's logic audit: in the
repeat hypothesis the run is a closed convex spherical polygon whose support function f(m) =
sOrient(P r)(P r+1)(P m) is UNIMODAL > 0 in the interior, so "run lies on the great circle" is FALSE
unless the repeat is impossible -- i.e. FaceContiguityPropagation is only vacuously true (= simplicity
itself), a circular subgoal. The correct route is GNOMONIC + planar convex position, which gives the
distinct-vertices contradiction directly WITHOUT the great-circle claim.

## GOAL (closes Ch13 unconditionally, composing FFCT88 digon + FFCT89 consecutive-kill + FFCT91's
non-circular wrappers / or a fresh wrapper):
```lean
theorem weakConvex_boundedJoints_noNonadjacentRepeat
    {n : ℕ} {P : Fin (n+1) -> S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hlt : ∀ i : Fin (n-1), jointAngle P i < Real.pi) :
    NoNonadjacentRepeat P
```
Then feed it into FFCT89/91's openedWBS instantiation => crossPieceCollisionEndpointAtSup_unconditional
=> spherical_arm_mono_ch13 : SphericalArmMonotone.

## THE GNOMONIC ROUTE:
1. Hemisphere normal h (from WeakConvexSphPolygon.open_hemisphere, <h, P m> > 0 all m). Define the
   gnomonic image Q m : Pt(R^2 or E3-in-tangent) = (P m) / <h, P m> (central projection to the plane
   <h, x> = 1). It is injective on the open hemisphere (P m = P m' <=> Q m = Q m'), so a repeat
   P r = P s gives Q r = Q s.
2. Great-circle / side preservation: sOrient (P i)(P j)(P k) = (positive scalar) * det2_planar of the
   Q-images (the gnomonic Jacobian is orientation-preserving with positive determinant on the open
   hemisphere). So WeakConvexSphArm's sOrient >= 0 becomes: every Q m is on the >=0 side of every
   edge-line (Q i, Q i+1) -- PLANAR WEAK CONVEXITY (convex position). And PositiveJoints + bounded
   joints (0 < joint < pi) become STRICT planar turns (the chain never goes straight or reverses).
   [Build these gnomonic facts; grep for any landed central-projection / det2 / planar orientation
   machinery -- the Ch36 2D toolkit (ZinanCh36*, det2, side), PlanarConvex, FFCT8/10 planar files.
   Estimate the from-scratch parts.]
3. THE PLANAR LEMMA (the real content): a finite planar point sequence Q_0..Q_n where every Q_m lies
   on one side of every consecutive edge-line (convex position) and the turns are strict has DISTINCT
   vertices: Q_a = Q_b with a < b is impossible. Proof: strict convex position => the vertices are in
   strictly convex position (each is an extreme point of the others' hull) and the chain visits them
   in strictly monotone angular order around the hull, so indices map injectively. Use Mathlib's
   Convex / convexHull / the planar orientation predicate (grep Sbtw, Wbtw, det2 sign monotonicity).
   ALTERNATIVELY the cleanest discrete form: the planar repeat Q a = Q b closes a sub-polygon
   Q_a..Q_b whose every vertex is on one side of edge (Q_a, Q_{a+1}) and which returns to Q_a; with
   strict turns this is a closed strictly-convex planar polygon, and a closed strictly-convex polygon
   with > 2 vertices cannot have a vertex coincide with the start unless it is the standard closure
   -- the nonadjacent repeat (b >= a+2) forces two boundary vertices to coincide, contradicting
   strict convexity (a strictly convex polygon has all vertices distinct extreme points).
4. Reduce to det3=0 consecutive triple where convenient: if the planar route is heavy, note that
   the gnomonic det2 = positive * det3, so a planar collinear triple <=> spherical det3 = 0 triple,
   feeding FFCT89's consecutive-flat kill. The digon (s=r+2) is FFCT88.

## START with s = r+3 (smallest non-digon): Q r, Q r+1, Q r+2, Q r+3 = Q r in convex position with
strict turns => closed convex triangle-ish with a repeat => the planar strict-convexity contradiction.
Generalize.

## Deliverable: ZinanFFCT92.lean (0 errors, clean-3) with weakConvex_boundedJoints_noNonadjacentRepeat
+ the UNCONDITIONAL spherical_arm_mono_ch13 if it closes, else the sharpest partial (gnomonic facts +
the planar convex-position lemma surface) + HANDOFF/outbox/ch13-gnomonic-report.md. No git commit.
Grind to terminal.
