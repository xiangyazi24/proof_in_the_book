# CODEX BRIEF (uisai2-local): the simplicity theorem (FFCT88) — UNCONDITIONAL Ch13

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-87 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT88.lean. ON the build machine:
`export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT87 && lake env lean ProofsInTheBook/ZinanFFCT88.lean`.
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new. NO effort cap.

## THE GOAL (the key that closes Ch13 unconditionally): prove the simplicity theorem
```lean
theorem weakConvex_positiveJoints_noNonadjacentRepeat
    {n : ℕ} {P : Fin (n+1) → S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P) :
    NoNonadjacentRepeat P
```
Then `CrossPieceCollisionEndpointAtSup` is VACUOUS:
```lean
theorem crossPieceCollisionEndpointAtSup_of_noRepeat : CrossPieceCollisionEndpointAtSup := by
  intro n A B hA hB hsame hjle k hlt hstuck r s hr hs hrs hrK hKs hcoll
  exact False.elim
    ((weakConvex_positiveJoints_noNonadjacentRepeat
        (openedWBS_weakConvex_at_sup ...) (openedWBS_positiveJoints_at_sup ...))
      r s hr hs hrs hcoll)
```
(find the EXACT landed names for openedWBS weak-convexity + positive-joints at the WBS sup —
they were used inside ZinanFFCT86/the WBS assembly FFCT46; grep openedWBS_weakConvex / 
openedWBS_positiveJoints / the FFCT46 supWBS lemmas). Then
`spherical_arm_mono_final_ch13_v11 crossPieceCollisionEndpointAtSup_of_noRepeat` is the
UNCONDITIONAL chapter headline: state `spherical_arm_mono_ch13 : SphericalArmMonotone`.

## THE PROOF (pbook design, full in HANDOFF/design-rounds/ch13-simplicity-route.md §3 + degenerate
audit §3-end — read it). 4 steps, all within the LANDED FFCT22 cone-propagation machinery:
1. `support_opposite_zero_of_repeat`: from P r = P s, the weak support of edge (r,r+1) at vertex
   s+1 and of edge (s,s+1) at vertex r+1 are OPPOSITE multiples of det3(P r)(P r+1)(P s+1) (the
   FFCT56/83 opposite-multiple mechanism, P r = P s substituted) => det3(P r)(P r+1)(P s+1) = 0.
2. `face_interval_of_support_zero`: the FACE-PROPAGATION lemma — a weakly convex spherical polygon
   with a nonincident vertex on an edge's support great circle has the WHOLE intervening boundary
   interval on that great circle. This is FFCT22's OnFoldRay / far_fold_tail_collinear_step
   iterated (the determinant-vanishing propagation); reuse/adapt FFCT22 + the FFCT84/85 first-step
   coplanarity-forcing (Y in-plane forced by the two weak supports being opposite multiples).
3. `positiveJoints_no_closed_face_run`: the interval returns to P r = P s => a CLOSED face-run on
   one great circle.
4. A closed run with short edges forces some joint = 0 or pi (FFCT21/22
   sphAngle_eq_zero_or_pi_of_det3_zero + three coplanar consecutive) => contradicts PositiveJoints.

## DEGENERATE AUDIT (pbook gave all — implement each):
- r = K: rotS2 (A K)(-δ*)(A s) = A K => A s = A K, contra strict_nonincident (K+2 ≤ s). [but note:
  the GENERAL theorem is about an arbitrary P, so handle r,s purely from P's structure; the
  openedWBS specifics only enter the instantiation]
- r=0,s=n: endpt = 0, sDist_nonneg (this is for the instantiation, not the general thm).
- s=n: use the CLOSING edge (n,0) in place of (s,s+1) [WeakConvexSphPolygon's wrap edge].
- r=0: use edge (0,1).
- r+2=s (digon): the loop P r,P r+1,P s=P r => joint at r+1 degenerate (the two edges (r,r+1),
  (r+1,s) with P s=P r make sphAngle at r+1 = the angle of an edge to its own reverse => 0 or pi)
  => PositiveJoints kill directly. This is the BASE case — do it first, it's the cleanest.

## STRUCTURE: build the general theorem; the digon (r+2=s) base case first (cleanest), then the
face-propagation induction for s > r+2. Land what compiles; if the full face-propagation resists,
the digon + small cases still shrink the residue — but aim for the full theorem (the machinery is
all landed in FFCT22).

## Deliverable: ZinanFFCT88.lean (0 errors, clean-3) with weakConvex_positiveJoints_noNonadjacentRepeat
+ crossPieceCollisionEndpointAtSup_of_noRepeat + spherical_arm_mono_ch13 (UNCONDITIONAL) if it
closes, else the sharpest partial + HANDOFF/outbox/ch13-simplicity-report.md. No git commit.
Grind to terminal — this is the last key.
