# CODEX BRIEF: kill NonAxisTailBoundaryResidue (the LAST Ch13 stuck residue)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-59 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT60.lean. Verify via scp + ssh uisai2 lake env lean as before
(build ProofsInTheBook.ZinanFFCT59 olean first). Rules: no sorry/admit/axiom/native_decide;
clean-3 #print axioms; no vacuous conditionals (refutation-check anything new).

## Context
HANDOFF/outbox/ch13-nonaxis-report.md + ZinanFFCT59.lean: the only surviving support-stuck
configuration is the double-rotated pattern at the TAIL BOUNDARY i+1 = n: the binding triple
(A' (n-1), A' n, A' j) with j fixed (j <= K < n-1... check the exact pattern constraints in the
report), where the mid-fold kill fails because the apex A' n's successor edge is the WRAP edge
(n, 0) — wait, or because the joint at n is not an interior PositiveJoints index. READ the
report's precise reason.

## Attack routes (try in order; the first that closes wins)
1. THE WRAP-EDGE SUPPORT TRICK (FFCT42/47 precedent): the apex A' n's "successor" through the
   closed polygon is A' 0 via the wrap edge (n, 0) — the closed WeakConvexSphPolygon's
   edge_support covers it (∀ i j including i = n with i+1 = 0 in Fin (n+1)). The mid-fold kill's
   mechanism (two supports of the successor edge at the fold neighbors as opposite multiples of
   one det3) may run VERBATIM with R = A' 0: supports 0 <= det3 (A' n)(A' 0)(A' (n-1)) and
   0 <= det3 (A' n)(A' 0)(A' j) — check whether the FFCT56 midFold_interior_contradiction's
   algebra works with the wrap successor; the flat-joint conclusion lands at the WRAP "joint"
   (n-1, n, 0)?? — that triple's "joint" is not a PositiveJoints index either... BUT the collapse
   det3 (A'(n-1))(A' n)(A' 0) = 0 is a COPLANARITY of (n-1, n, 0) — combine with the binding
   coplanarity of (n-1, n, j): if the two planes coincide we get 4 coplanar points incl. three
   consecutive-through-wrap; if distinct, A' n lies on their intersection line through the origin
   => A' n = ±(unit on the line)... two planes through origin intersect in a line; A' n on both
   => A' n on the line; also A'(n-1) on both?? (n-1 is in both triples!) — both A'(n-1) and A' n
   on the intersection line => A'(n-1) = ±A' n => ShortArc edge kill!! So EITHER the planes
   coincide (4 coplanar: then det3 (A'(n-1))(A' n)(A' j) = 0 AND det3 (A'(n-1))(A' n)(A' 0) = 0
   with the edge (n-1, n) shared — every vertex in the plane? no: just 0 and j; then consider the
   support of edge (n-1, n) at... the binding IS sOrient (A'(n-1))(A' n)(A' j) = 0 — wait the
   binding triple per the report might be (i, i+1, j) = (n-1, n, j): the SUPPORT that vanishes is
   exactly det3 (A'(n-1))(A' n)(A' j). And the b<0 fold: A'(n-1) = a A' n + b A' j, rearranged
   mid-fold A' n = c A'(n-1) + d A' j (c,d>0). The kill needs the successor edge of the apex
   A' n: through the wrap, edge (n, 0): supports 0 <= sOrient (A' n)(A' 0)(A'(n-1)) and
   0 <= sOrient (A' n)(A' 0)(A' j). Substitute A' n = c A'(n-1) + d A' j into each:
   det3 (c P + d Q)(Z)(P) = d det3 Q Z P; det3 (c P + d Q)(Z)(Q) = c det3 P Z Q — opposite
   multiples of D = det3 P Q Z (P = A'(n-1), Q = A' j, Z = A' 0) => D = 0 => A' 0 in the binding
   plane too => then det3 (A'(n-1))(A' n)(A' 0) = (expand A' n) = d det3 (A'(n-1))(A' j)(A' 0)
   = ±d D = 0 => the triple (n-1, n, 0) coplanar => the wrap-adjacent triple flat => sphAngle at
   A' n between A'(n-1) and A' 0 is 0 or pi. Is THAT killable? It's the "closure joint" at the
   last vertex — not a PositiveJoints index. BUT: 0/pi at the closure joint means A'(n-1), A' n,
   A' 0 on a great circle — combined with ALL the wrap supports (edge (n,0) supports at every
   vertex >= 0) and the strict hemisphere... try the FFCT44 pencil: now we have the binding plane
   containing A'(n-1), A' n, A' j, A' 0 — FOUR vertices incl. THREE consecutive-through-wrap
   (n-1, n, 0). The interior joint at n-1 (between n-2 and n): is n-2 in the plane? Not yet...
   Push further: with A' 0 and A' j and the consecutive pair in one plane Pi, the supports of
   edge (n-1, n) at all vertices are >= 0 with EQUALITY at j and 0 — the polygon is tangent to
   Pi at the edge (n-1,n) with TWO vertices ON Pi on (possibly) both sides... if 0 and j are on
   the SAME side (both IN Pi, sOrient = 0) fine; all OTHER vertices strictly one side (weak >= 0).
   Then consider the edge (j-1, j) or (j, j+1) supports at n-1/n — more relations. This is the
   FFCT22 OnFoldRay/cone territory: vertices accumulating in a fold plane on a weak arm with
   PositiveJoints — the far_fold machinery (FFCT21/22/25) classified exactly this and FFCT25's
   far_fold_boundary_classification_final says the fold datum (A i in span>=0{A(i+1), A j}) forces
   i = 0 ∧ j ∈ {n-1, n}. HERE the rearranged mid-fold A' n = c A'(n-1) + d A' j is a fold at
   index n with generators predecessor + far — apply the REVERSED arm (FFCT52 revArm): on revArm,
   index n becomes 0, predecessor becomes successor: revA' 0 = c revA' 1 + d revA' (n-j) — EXACTLY
   the FFCT25 fold shape at i = 0!! And FFCT25's classification then constrains... i = 0 is
   ALREADY the conclusion (consistent — no contradiction from the classification itself), but the
   FFCT53 BOUNDARY TRANSPORT (foldedFlat_boundary_j_eq_n / the (0, n) and (0, n-1) closes) APPLIES
   to the reversed arm: the reversed fold at (0, n-j) — if n-j = n or n-1 i.e. j = 0 or 1 it's the
   closed boundary case giving endpt (revA') <= endpt (revB') = endpt A' <= endpt B DIRECTLY (the
   transport, not a kill!). For general j the reversed fold has 0 + 2 <= n-j < n: an INTERIOR far
   fold on the reversed arm => FFCT25's classification (applied to revArm, which needs revArm's
   WeakConvex + PositiveJoints + NoNonadjacentRepeat — FFCT52's transports!) FORCES n-j ∈
   {n-1, n} i.e. j ∈ {0, 1} — the general-j tail binding is IMPOSSIBLE, and j ∈ {0,1} goes
   through the FFCT53 boundary transport on the reversed pair!! Total: kill OR transport, both
   landed machinery + FFCT52 transports. THIS IS THE ROUTE — implement it.
2. If a step resists, decompose and grind each sub-lemma; document the exact failing goal.

## Deliverables
ZinanFFCT60.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-tail-boundary-report.md with the final
Ch13 stuck-surface verdict (should be EMPTY or the precisely-named leftover). Then state the
consequence chain: SupportStuckWBSImpossible (or its sharpest honest form) and the final
spherical_arm_mono headline status. Do NOT git commit. Grind to terminal.
