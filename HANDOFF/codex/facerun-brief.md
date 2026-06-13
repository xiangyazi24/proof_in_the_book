# CODEX BRIEF (uisai2-local): face-run propagation -> UNCONDITIONAL Ch13 (FFCT90)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-89 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT90.lean. ON the build machine:
`export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT89 && lake env lean ProofsInTheBook/ZinanFFCT90.lean`.
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new. NO effort cap.

## THE ONE REMAINING THEOREM (closes Ch13 unconditionally):
```lean
theorem weakConvex_boundedJoints_noNonadjacentRepeat
    {n : ℕ} {P : Fin (n+1) -> S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hlt : ∀ i : Fin (n-1), jointAngle P i < Real.pi) :
    NoNonadjacentRepeat P
```
LANDED already: digon base case (FFCT88 weakConvex_positiveJoints_no_gap_two_repeat); the
consecutive-det3-zero kill (FFCT89 weakConvex_boundedJoints_no_consecutive_det3_zero — read its
exact statement: it should take a consecutive triple with det3=0 and derive False from pos+lt).
MISSING: the FACE-RUN PROPAGATION connecting an arbitrary repeat P r = P s (r+2 <= s) to a
consecutive vanishing det3 that FFCT89 then kills.

## THE PROOF (pbook design HANDOFF/design-rounds/ch13-simplicity-route.md §1-3 + the FFCT22
machinery — read both):
1. From P r = P s: det3 (P r)(P (r+1))(P (s+1)) = 0 [the two weak supports of edges (r,r+1) and
   (s,s+1) at the opposite vertices are opposite multiples; P r = P s substituted -- the
   FFCT83/84 opposite-multiple + first-step coplanarity-forcing mechanism, ALREADY landed shapes].
   Equivalently P (s+1) lies on the support great circle of edge (r,r+1).
2. FACE-RUN PROPAGATION (the work): set the plane Pi = span{P r, P (r+1)} (the support circle of
   edge (r,r+1)). Show by INDUCTION that every vertex P (r+1+t), t = 0,1,...,(s+1)-(r+1), lies in
   Pi. Inductive step: with P (r+1+t) in Pi and the edge (r+1+t, r+2+t) weak-supported, plus the
   closure anchor P r = P s in Pi, the FFCT22 far_fold_tail_collinear_step (determinant
   propagation: det3 over a common 2-plane with a strictly-positive coefficient) forces
   P (r+2+t) in Pi. Reuse FFCT22's OnFoldRay + far_fold_tail_collinear_step; the SIGN/cone
   coefficient is supplied by the weak supports being >= 0 and the boundedness. (This is the
   anchor-generic version of the propagation FFCT76-85 did for the wrap case; here the anchors
   are the FIXED edge (r,r+1), and the run is CLOSED -- P s = P r returns to the plane -- which
   is the termination certificate, simpler than the wrap case.)
3. The closed run: P r, P (r+1), ..., P s = P r all in the 2-plane Pi => any consecutive interior
   triple (e.g. P (r+1), P (r+2), P (r+3) if s >= r+3) is coplanar => det3 = 0 => FFCT89 kill.
   Handle the minimal s = r+2 (digon) by FFCT88. For s = r+3 the triple (r+1,r+2,r+3) ... ensure
   it's an INTERIOR joint (index in 1..n-1) -- the run is between r and s, interior indices
   available since the loop has >= 2 edges.
   Wrap sub-case s = n: use the closing edge (n,0) and the WeakConvexSphPolygon wrap support.

## Then INSTANTIATE (FFCT89 has the wrappers):
crossPieceCollisionEndpointAtSup_unconditional (via openedWBS weakConvex + positiveJoints +
openedWBS_jointAngle_lt_pi + this theorem) => spherical_arm_mono_ch13 : SphericalArmMonotone
(THE UNCONDITIONAL CHAPTER HEADLINE). Read FFCT89's
crossPieceCollisionEndpointAtSup_of_boundedWeakPositiveSimplicity +
openedWBS_noNonadjacentRepeat_of_boundedWeakPositiveSimplicity and feed the proven theorem into
the BoundedWeakPositiveSimplicity slot.

## Deliverable: ZinanFFCT90.lean (0 errors, clean-3) with weakConvex_boundedJoints_noNonadjacentRepeat
+ the unconditional spherical_arm_mono_ch13 if it closes, else the sharpest partial (the
propagation for gap=3, then general) + HANDOFF/outbox/ch13-facerun-report.md. No git commit.
Grind to terminal — this is the final geometric core of Chapter 13.
