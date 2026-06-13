# CODEX BRIEF (uisai2-local): face-contiguity -> the simplicity theorem (FFCT91)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-90 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT91.lean. ON the build machine:
`export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT90 && lake env lean ProofsInTheBook/ZinanFFCT91.lean`.
Rules: no sorry/admit/axiom/native_decide; clean-3. NO effort cap. Treat the target as PROVABLE
hard geometry (it is a basic convexity fact); grind, do not classify it as irreducible.

## GOAL: BoundedFaceRunPropagation (FFCT90's exact residue): for a weakly-convex bounded-joint
arm P, a repeat P r = P s (r+3 <= s) yields some consecutive flat triple det3(P i)(P i+1)(P i+2)=0
with i interior. Combined with FFCT88 (digon) + FFCT89 (consecutive-flat kill) this gives
weakConvex_boundedJoints_noNonadjacentRepeat, hence the UNCONDITIONAL spherical_arm_mono_ch13.

## THE MATH (the face-contiguity lemma; pbook 4-step §2 in ch13-simplicity-route.md):
Let C = the support great circle of edge (r,r+1), i.e. f(m) := sOrient (P r)(P r+1)(P m). Weak
convexity gives f(m) >= 0 for all m. Landed seeds: f(r) = f(r+1) = 0 (the edge), f(s) = 0 (since
P s = P r lies on the edge), and FFCT90's f(s+1) = 0. The FACE-CONTIGUITY claim:
`f(m) = 0 for ALL m in [r+1, s]` (the whole run lies on C). Then any consecutive interior triple
in the run is coplanar (all on C) => det3 = 0 => FFCT89 kill.

## TWO ROUTES (try A first; it reuses Mathlib convexity):
### A. GNOMONIC reduction to planar convex position.
The arm is in an open hemisphere (open_hemisphere field). Gnomonic map g: open hemisphere -> tangent
plane R^2, g(x) = x / <x, h0> (central projection), sends great circles to lines and "x on the >=0
side of great circle C" to "g(x) on the >=0 side of line g(C)". So f(m) >= 0 becomes: the planar
points Q_m := g(P m) all lie on one side of the line through Q_r, Q_{r+1}; equivalently the planar
"signed area" sOrient maps to a positive multiple of the planar det2 (the gnomonic Jacobian is
positive). KEY: f(m) = lambda_m * det2 (Q_{r+1} - Q_r) (Q_m - Q_r) with lambda_m = (positive
gnomonic scale) -- so f(m) = 0 <=> Q_m on the line. The planar claim: a planar chain whose every
vertex is on the >=0 side of every edge-line (planar weak convexity) with a vertex Q_s = Q_r
(planar repeat) and Q_{s+1} on the line(Q_r,Q_{r+1}) has the whole sub-chain on that line. This is
the planar convex-position face fact -- prove it with Mathlib's Convex / det2 toolkit (grep det2,
the Ch36 2D files ZinanCh36*, PlanarConvex, the FFCT8/10 planar lemmas; the planar repeat + same-
side conditions force collinearity of the run). Land the gnomonic map's needed facts (great-circle
-> line, side preservation, the det3->det2 positive-multiple identity) -- these may need building;
estimate.
### B. DIRECT spherical support-function argument.
f(m) >= 0 on [r+1, s], f(r+1) = f(s) = 0. Show f convex/concave-structured from weak supports so
that the boundary zeros + the CLOSURE (P s = P r, the run is a closed loop returning to C) force
f == 0 on the run. Use: a closed convex spherical polygon meeting a supporting great circle at two
boundary points (P r and the edge) has its whole between-arc on the circle (convex ∩ supporting
hyperplane = connected face). The discrete version: if f(m0) > 0 for some interior m0, the run
leaves C and returns, but weak convexity (every vertex on the >=0 side of EVERY edge, in particular
edges incident to the leaving/returning vertices) + bounded joints forbid the re-entry -- formalize
the "convex polygon ∩ supporting circle is a connected face" as the FFCT8-style planar residue made
concrete here.

## START: do the s = r+3 case first (run = P r, P r+1, P r+2, P r+3 = ... no, s>=r+3 means the run
has >= 3 interior vertices; smallest gap=3 means s=r+3, run P r,P r+1,P r+2,P s=P r -- the triple
(P r+1,P r+2,P s=P r) ... actually with f(r+1)=f(r+2)?=0: prove f(r+2)=0 from the two adjacent
edge supports + closure, then the triple (P r,P r+1,P r+2) is on C => flat). Get gap=3, then induct.

## Deliverable: ZinanFFCT91.lean (0 errors, clean-3): the face-contiguity / BoundedFaceRunPropagation
+ the unconditional spherical_arm_mono_ch13 if it closes, else the sharpest partial (gap=3, then the
general induction surface) + HANDOFF/outbox/ch13-facecontig-report.md. No git commit. Grind to terminal.
