# CODEX BRIEF (uisai2-local): collision structure lemmas (FFCT87) — route-agnostic foundation

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-86 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT87.lean. ON the build machine: verify with
`export PATH=$HOME/.elan/bin:$PATH && lake build ProofsInTheBook.ZinanFFCT86 && lake env lean ProofsInTheBook/ZinanFFCT87.lean`.
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## Context: the chapter's LAST residue is CrossPieceCollisionEndpointAtSup (read its def in
ZinanFFCT86.lean): at the WBS widening sup, collision A' r = A' s (r <= K := openingAxis < s,
r+2 <= s, A' = openedWBS) must give endpt A' <= endpt B. The final endpoint inequality is a
DESIGN-PENDING geometry (a ChatGPT design round is in flight; the naive triangle-inequality route
has a direction trap, and the delete-the-loop route has a Bhat/SameSides obstruction). DO NOT
attempt the final endpt inequality. Instead land the ROUTE-AGNOSTIC structural foundation that
any correct route will consume. Report which structural facts close and which resist.

## Inventory first (read): openedWBS / openTail_fixed / openTail_rot (the fixed r<=K vs rotated
r>K split — used in ZinanFFCT86.openedWBS_noNonadjacentRepeat_of_localNoCross), rotS2 isometry
lemmas (sDist/sphAngle/inner preservation — grep rotS2 in SphericalRotation + the FFCT files),
det3 antisymmetry (det3 x y x = 0), the sub-arm / intervalArm congruence machinery (FFCT52/54).

## Bricks (land what compiles; report resisters):
A. `collision_identicalZeroSupports`: from `openedWBS A B k r = openedWBS A B k s` (the collision
   heq), the identically-zero supports — at least:
   - `sOrient (A' s) (A' (s+1)) (A' r) = 0`  [det3 _ _ (A' r), A' r = A' s, = det3 x y x = 0]
   - `sOrient (A' (r-1)) (A' r) (A' s) = 0`
   (handle s+1, r-1 boundary indices; n+1-wrap where needed). These are vanishing NONINCIDENT
   supports (r vs s nonadjacent). State them as clean lemmas with the index side-conditions.
B. `rigidTail_subarm_congruence`: the rotated piece [s..n] is rigidly congruent under
   R := rotS2 (A K) (-(monitoredSupWBS A B k)):  for s <= p,q <= n,
   `sDist (A' p) (A' q) = sDist (A p) (A q)` and `sphAngle (A' p)(A' q)(A' t) = sphAngle (A p)(A q)(A t)`
   (R isometry). And the fixed piece [0..r]:  for 0 <= p,q <= r <= K,
   `A' p = A p` (openTail_fixed) hence `sDist (A' p)(A' q) = sDist (A p)(A q)`. In particular
   `sDist (A' 0)(A' r) = sDist (A 0)(A r)` and `sDist (A' s)(A' n) = sDist (A s)(A n)`, and
   `endpt (openedWBS A B k) = sDist (A' 0)(A' n)`.
C. `deleteLoopArm`: define Ahat : Fin (n+1 - (s-r)) -> S2 by Ahat m = A' m for m <= r, A' (m + (s-r))
   for m > r (i.e. [0..r] ++ [s+1..n] with s glued into r since A' s = A' r). Prove
   `endpt Ahat = endpt (openedWBS A B k)` (same first/last vertices). ATTEMPT WeakConvexSphArm Ahat:
   old edges inherit; the GLUE edge (Ahat r, Ahat r+1) = (A' s, A' s+1) is short (it IS edge (s,s+1));
   the glue joint sphAngle (A' (r-1))(A' s)(A' s+1) and the glue edge_support are the genuine
   obstruction — land what's derivable, REPORT the exact residual (this informs the design round).
   Also note: whether a Bhat with SameSides Ahat Bhat exists is the design's open question — DO NOT
   construct Bhat; just report the Ahat side.

## Deliverable: ZinanFFCT87.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-collision-struct.md
(the structural facts + the precise glue-joint/glue-support residual + whether the loop is a digon
when s = r+2). No git commit. Grind to terminal on the STRUCTURAL bricks only.
