# CODEX BRIEF (uisai2-local): discharge CrossPieceNoCollisionAtSup (FFCT86) — Ch13's last input

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-85 committed; the chapter stands at
spherical_arm_mono_final_ch13_v10 (hcross)). CREATE ONLY ProofsInTheBook/ZinanFFCT86.lean.
You are ON the build machine: verify directly with
`export PATH=$HOME/.elan/bin:$PATH && lake env lean ProofsInTheBook/ZinanFFCT86.lean`
(build FFCT85 olean first: lake build ProofsInTheBook.ZinanFFCT85).
Rules: no sorry/admit/axiom/native_decide; clean-3 #print axioms; refutation-check anything new.

## The target: CrossPieceNoCollisionAtSup (exact statement in ZinanFFCT68/74 — read it + the
discussions in HANDOFF/outbox/ch13-lastthree-report.md and ch13-reconcile-report.md): at the WBS
support-stuck sup, no cross-piece vertex collision (a fixed-piece vertex A r (r <= K) equal to a
rotated-piece vertex openTail...(s) (s > K)).
## Routes (try in order):
1. THE FIRST-STEP WITNESS TRICK (the FFCT84/85 success template — read those files): a collision
   A' r = A' s creates IDENTICALLY-ZERO supports: det3 (A' r)(A' r+1)(A' s) = det3 x y x = 0 —
   a vanishing nonincident support at an ordinary edge with probe s. The consumer chain at the
   sup: this zero is itself a binding/witness — feed the landed no-tail consumer machinery
   (FFCT81/84's NormalizedStrictInteriorSupportZero path; check index bounds: r+1 <= K < s <= n;
   if s = n the apex/tail machinery (FFCT84) handles it). The collision case then yields the
   ENDPOINT PAYLOAD directly — meaning hcross's consumer (read how the v10 chain uses hcross:
   probably to derive NoNonadjacentRepeat of the opened arm for the hsa/distinctness fields)
   can be REPLACED: instead of excluding the collision, ROUTE the collision configuration to
   the endpoint conclusion. Check the exact consumption site: if hcross feeds a kill inside a
   dispatch whose other branches already conclude the endpoint, the collision branch concluding
   the endpoint TOO dissolves the input (restate the dispatch with the collision branch routed).
2. If route 1's consumer shapes resist: exclude the collision geometrically: at the sup the
   margins/supports structure + the rotation flow: a collision at delta* with no collision on
   [0, delta*) — the collision support (r, r+1; s) hits zero exactly at delta* = a binding; the
   trichotomy then runs at THIS binding: A' r = a A'(r+1) + b A' s with A' s = A' r:
   (1-b) A' r = a A'(r+1) => b = 1, a = 0 (units, independence) — the a=0,b=1 leg: FFCT74's
   static trichotomy killed a=0 via... read which kill; if it needed NR (circular here), use
   the first-step trick at the ADJACENT edge instead (the collision triple is coplanar-degenerate
   everywhere — pick the edge (s-1, s) with probe r: det3 (A'(s-1))(A' s)(A' r) =
   det3 (A'(s-1))(A' r)(A' r) = 0 ✓ another identically-zero support — the witness factory).
3. Whatever survives: name it strictly smaller with the exact goal.
## Then: `spherical_arm_mono_final_ch13_UNCONDITIONAL : SphericalArmMonotone` if hcross fully
dissolves (VERBATIM in the report), else the sharpest v11.
## Deliverable: ZinanFFCT86.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-hcross-report.md.
No git commit. Grind to terminal.
