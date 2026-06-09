# TASK Ch36-theta: port mono_theta onto the position vector -> RayCrossingAlternation seed

Repo: /Users/huangx/repos/proof_in_the_book (branch zinan-overnight). Create ONLY the new file
ProofsInTheBook/ZinanCh36Theta.lean. Do not edit anything else. No git commit.

GOAL (the chapter's single Jordan kernel, recommended route from HANDOFF/outbox/ch36-residue-map.md item 6):
prove `RayCrossingAlternation P rho x` (def at ProofsInTheBook/PolygonWindingBound.lean:211 — READ it
and its module header first) by porting the monotone branch-cut angle technique of
`ProofsInTheBook/ZinanFFCT9.lean` (`theta b p := arccos(ncos b p)`, `mono_theta`, `branch_squeeze_*`)
from edge-difference vectors onto the POSITION vector (boundary point − x), with crossings ordered by
`crossTau`. The alternation of `eSign` should fall out of the monotone squeeze; the ray-direction
genericity hypotheses already present in RayDirection kill the antipodal care-point.

Bricks in order (each a named lemma; bank each one that compiles even if later ones block):
1. `thetaPos` def: the branch-cut angle of (P t − x) against the ray direction, + its monotonicity
   lemma along a single edge crossing (adapt ZinanFFCT9.mono_theta / mono_ncos).
2. Alternation: consecutive crossings in crossTau order have opposite eSign.
3. Wiring: feed through the PROVEN bridges `windCross_mem_of_alternation` (PolygonWindingBound.lean:221)
   and `earDeletedExterior_of_seed` — the targets are the four equivalent kernel forms
   (EarCutData.earDeletedExterior @ PolygonEarDelete.lean:379 ≡ RayCrossingAlternation ≡
   EarDeletedWindingZero @ PolygonWindingPath.lean:177 ≡ LocalJumpSeed @ PolygonLocalJump.lean:172).
   Hitting ANY one of the four forms unconditionally closes the chapter's geometric side.

KNOWN DEAD ENDS (machine-refuted in repo, do not attempt): EarHalfPlaneContainment (reflex band);
InteriorOddSeed as stated (≡ allConvex, false at reflex); any route needing a known winding value.

VERIFY (your ONLY loop; Mac has no local lake):
scp -q ProofsInTheBook/ZinanCh36Theta.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ && ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && timeout 1800 lake env lean ProofsInTheBook/ZinanCh36Theta.lean 2>&1 | head -50'

STRICT: no sorry/axiom/admit/native_decide. End the file with #print axioms for every theorem you
claim (must be ⊆ {propext, Classical.choice, Quot.sound}). This is hard; grind it — the only
legitimate stops are: the mathematics is wrong (give the counterexample) or a genuinely missing
Mathlib API (name the exact missing lemma + the goal state). Keep every compiling sub-lemma; do not
fake. When done (or genuinely blocked) write HANDOFF/outbox/ch36-theta-reply.md: status, what is
proven (with #print axioms output), exact blockers.
