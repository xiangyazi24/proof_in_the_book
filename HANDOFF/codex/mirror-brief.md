# CODEX BRIEF: discharge TailBoundaryReversalConvexity via the MIRROR transform

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-60 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT61.lean. Verify via scp + ssh uisai2 lake env lean (build FFCT60 olean
first). Rules: no sorry/admit/axiom/native_decide; clean-3; no vacuous conditionals.

## The problem (HANDOFF/outbox/ch13-tail-boundary-report.md)
FFCT60 needs WeakConvexSphArm (revArm P) / StrictConvexSphArm (revArm B), but index reversal flips
sOrient (orientation reversal), so the reversed arm satisfies the supports with the WRONG sign.
TailBoundaryReversalConvexity carries this as a named input.

## The master's discharge: compose with a linear REFLECTION
Let R : E3 -> E3 be the reflection negating ONE coordinate (e.g. R ![x,y,z] = ![x,y,-z], or
cleaner: R v = v - 2*<v,e>•e for a unit e — a linear isometry with det = -1). Define
mirrorArm P := fun m => (reflection of (revArm P m)) — i.e. compose pointwise R with revArm
(define RS2 : S2 -> S2 via norm preservation: ||R v|| = ||v||).
KEY FACTS to prove:
1. det3 (R x)(R y)(R z) = -det3 x y z (det R = -1; prove via the explicit coordinate form +
   ring — det3's coordinate expansion exists in the FFCT12-15 layer or SphericalCore).
2. <R x, R y> = <x, y> (isometry; coordinates + ring).
3. Therefore sOrient on mirrorArm = (-1)[from R] * (-1)[from reversal, FFCT52's
   sOrient_revArm_normalized] * sOrient on P = +sOrient — the supports transport with the RIGHT
   sign: WeakConvexSphArm P -> WeakConvexSphArm (mirrorArm P) (edge_short via 2; edge_support via
   1+FFCT52; open_hemisphere with h' := R h via 2; three_le trivial). Similarly Strict.
4. sDist/endpt invariant (via 2); sideLen, jointAngle (sphAngle uses inner products only — via 2),
   SameSides/JointLe/PositiveJoints/NoNonadjacentRepeat (injectivity of R) all transport.
5. The fold datum transports: spans map through the LINEAR R (Submodule.span NNReal maps under
   linear isometries; R is linear so R (a•u + b•v) = a•R u + b•R v).
6. Discharge: TailBoundaryReversalConvexity (or directly re-derive FFCT60's consumers with
   mirrorArm replacing revArm — read FFCT60's exact statements; the endpoint comparison transports
   back since endpt (mirrorArm P) = endpt P).
7. State the consequence: the tail-boundary kill now unconditional for j >= 2; with FFCT59's
   eliminations and the j in {0,1} boundary route, assemble the sharpest honest form of
   SupportStuckWBSImpossible (or its residual if the j in {0,1} transport still carries inputs —
   READ FFCT60's report for what the boundary route needs) and re-state the final headline chain.

## Deliverables
ZinanFFCT61.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-mirror-report.md with the final Ch13
surface. Do NOT git commit. Grind to terminal.
