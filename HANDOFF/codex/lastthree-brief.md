# CODEX BRIEF: the LAST THREE Ch13 blockers (FFCT68)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-67 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT68.lean. Verify via scp + ssh uisai2 (build FFCT67 olean first).
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## Read HANDOFF/outbox/ch13-reconcile-report.md + ZinanFFCT67.lean first — the three blockers:
1. hspanSeed's revArm branch: at a binding normalized through orientationNormalized's REVERSED
   branch, the span seed derivation must run on the reversed/mirrored pair. FFCT61's mirrorArm
   suite (weakConvex_mirrorArm, the transports) + FFCT49/51's span extraction give it on the
   mirrored pair; the seed transports back through the mirror (linear isometry preserves spans
   and det3-vanishing up to the tracked sign). Wire the mirrored-branch seed supplier.
2. The endpoint cases' IH/diagonal interface: the cases (bpos_apos route through FFCT25 =>
   FFCT65 v2 boundary closes) need (i) the MainPlus IH at smaller n — the final recursion in
   FFCT67/66 must thread it into the case consumers' signatures (re-plumb the interface: state
   the cases WITH ihdim + supply at the recursion site); (ii) the diagonal inequality
   sDist(A' i)(A' j) <= sDist(B i)(B j) — its source: stuckAtK_diag-class lemmas (FFCT48's
   cut_step used stuckAtK_diag_le_plus from FFCT19 — read its hypotheses; it needs the StuckAtK
   Gram data or the ear-interval IH — at the bpos_apos case the NNReal datum IS available so
   StuckAtKData assembles (FFCT49's bridge + the trichotomy's b>0,a>0 leg) => the landed diag
   lemma fires). Re-plumb end-to-end.
3. Cross-piece collision (the no-repeat residual): implement the master's degeneration analysis:
   a cross-piece collision A' r = A' s at the WBS sup creates the zero support det3 (A' r)
   (A' r+1)(A' s) = 0; at the binding analysis this lands in the b-trichotomy's DEGENERATE legs:
   with A' j = A' i: A' i = a A'(i+1) + b A' i => (1-b) A' i = a A'(i+1) => if b != 1: A' i
   parallel A'(i+1) => edge-short kill; if b = 1: a = 0-vector relation => a = 0 (A'(i+1) != 0)
   => the b=1,a=0 'repeat' relation A' i = A' j — consistent, NOT killed locally — but then the
   SPAN SEED at this binding is degenerate ((A'(i+1), A' j) may still be independent — the seed
   exists with (a,b) = (0,1)) and the b-trichotomy's b>0,a=0 leg fires = the FFCT64
   span_azero_bpos_false_of_noRepeat kill — WHICH NEEDS no-repeat — CIRCULAR for this case!!
   Resolve: the a=0,b=1 binding means A' i = A' j literally (the collision); kill it WITHOUT
   no-repeat: the collision pair (i, j) with j nonincident: consider the SECOND support — the
   edge (j, j+1) at i: det3 (A' j)(A' j+1)(A' i) = det3 (A' j)(A' j+1)(A' j) = 0 — another zero
   support (fine, weak). The hemisphere/strict-arm structure: r <= K < s with A r = rot(A s
   original... the collision equation in the ORIGINAL arm: A r = rot_{-delta*}(A s) — i.e. the
   rotation maps A s onto A r — then for the SLIGHTLY SMALLER angle delta < delta*, no collision
   (sup is first binding... is the collision support the FIRST zero? If the collision-support
   member (r, r+1; s) was strictly positive on [0, delta*): its zero at delta* is a legitimate
   binding; the b-trichotomy runs at THE BINDING PAIR THE TRICHOTOMY PICKED which might be a
   DIFFERENT pair than the collision pair — the dispatch picks SOME vanishing support; if
   multiple vanish pick wisely: among the vanishing supports at the sup, choose one whose triple
   is NOT a collision (exists unless ALL vanishing supports are collision-type: then... the
   collision A' r = A' s forces MANY supports zero (every edge at r against s etc.) — analyze:
   can a collision happen at the sup with NO non-collision binding? The margins of OTHER
   constraints could be > 0. Then the only binding is the collision family. For THAT case: the
   geometric meaning — the opened arm self-touches. KILL via the strict original + injectivity
   of the rotation flow: the function delta -> sDist(A r, rot_{-delta}(A s)) is... at delta = 0
   it's sDist(A r, A s) > 0 (original strict distinctness — PROVE strict-arm nonadjacent
   distinctness first: repeat => det3 (A r)(A r+1)(A s) = det3 x y x = 0 contradicts
   strict_nonincident > 0 ✓✓ — LAND THIS as strict_arm_injective); it hits 0 at delta* — fine,
   continuous. No contradiction from that alone. BUT: at the collision, consider the support of
   edge (s-1, s) at r IN THE OPENED ARM: A'(s-1) and A' s both rotated, A' r fixed = A' s:
   det3 (A'(s-1))(A' s)(A' r) = det3 (A'(s-1))(A' s)(A' s) = 0 — zero. And the support of edge
   (r, r+1) at s: zero as shown. The PositiveJoints of A' at the collided vertex... A' is a map
   Fin -> S2 with two indices same VALUE: the joint at r (between r-1, r, r+1) is fine; no flat
   joint forced. Hmm — the collision genuinely needs a new mechanism OR stays as the named
   residual. HONEST OPTIONS: (a) name CrossPieceNoCollisionAtSup (sharper than NoNonadjacentRepeat,
   derive NoRepeatSupply from it + strict_arm_injective for same-piece pairs — the NET final
   input shrinks); (b) try the energy/first-binding argument: BEFORE delta*, the collision-
   support (r, r+1; s) is strictly positive — its VALUE is det3 (A r)(A r+1)(rot(A s)) — at the
   collision it's zero with the rotated point AT A r: the function's derivative at the collision
   relates to the approach velocity — the one-sided derivative <= 0 (from admissibility);
   compute: d/d(-delta) det3 (A r)(A r+1)(rot(A s)) at the collision point rot(A s) = A r:
   = det3 (A r)(A r+1)(k x A r) — the FFCT26 Binet form at the SPECIFIC point: = <(A r) x
   (A r+1), k x (A r)> = <A r, k><A r+1, A r> - <A r, A r><A r+1, k> = <A r,k><A r+1,A r> -
   <A r+1,k>. Sign-definite?? Not obviously. If indeterminate, go with (a).
   IMPLEMENT strict_arm_injective + the same-piece exclusion + the honest (a) naming (or the
   full kill if (b) lands).
## The deliverable
The sharpest final form: spherical_arm_mono_final_ch13_v2 mod (at most) CrossPieceNoCollisionAtSup.
+ HANDOFF/outbox/ch13-lastthree-report.md. No commit. Grind to terminal.
