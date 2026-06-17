# CODEX BRIEF: discharge NonAxisMixedBindingResidue (Ch13, the gate of the REACH-only route)

Repo ~/repos/proof_in_the_book (branch zinan-overnight, all FFCT37-58 committed).
CREATE ONLY ProofsInTheBook/ZinanFFCT59.lean. NEVER touch any other file.
Verify loop: scp to uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ then
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanFFCT59.lean'
(build needed import oleans first via ssh uisai2 '... lake build ProofsInTheBook.ZinanFFCT56' etc.)
ABSOLUTE RULES: no sorry/admit/axiom/native_decide; #print axioms per main theorem must be
[propext, Classical.choice, Quot.sound]; every conditional hypothesis satisfiable (no vacuity —
this campaign killed four impostors; run the refutation check on anything you introduce).

## Context (read these first)
- HANDOFF/outbox/ch13-chirality-report.md + ProofsInTheBook/ZinanFFCT56.lean: the mid-fold kill
  is PATTERN-AGNOSTIC (midFold_bneg_false: any binding whose span coefficient b < 0 dies via the
  successor-edge support collapse). Axis-edge bindings: the derivative forces b <= 0 (FFCT55) and
  b = 0 dies, so b < 0 and the kill fires => axis-edge support-stuck eliminated. The SURVIVOR:
  NonAxisMixedBindingResidue (exact statement in ZinanFFCT56.lean) = for the NON-axis mixed
  binding patterns, supply the same b < 0 (or otherwise eliminate them).
- HANDOFF/outbox/ch13-beta-sign-report.md + ZinanFFCT55.lean: the slot-normalization ledger.
  Mixed patterns = which of the triple (c.i, c.i+1, c.j) is rotated (index > K) vs fixed.
  FFCT55 handled the pattern where the rotated vertex sits so the contraction pivots on the axis
  (i+1 = K). The non-axis patterns: the rotated subset is one of {i}, {j}, {i,i+1}, {i+1,j},
  {i,j}, {i,i+1 rotated and j fixed}, etc. — enumerate by position vs K (consecutive i,i+1 means
  they are on the same side of K or straddle: i+1 <= K => both fixed... the FIXED set is indices
  <= K, ROTATED is > K. So patterns: (a) i,i+1 <= K < j (j rotated only); (b) i <= K < i+1 <= j
  (i fixed, i+1 and j rotated) — note i+1 > K means i+1 = K+1 only when i = K (the axis edge —
  ALREADY DONE); i < K < i+1 impossible (consecutive); so (b) is i = K exactly = axis edge.
  Therefore the only genuine non-axis patterns are: (a) j rotated, i,i+1 fixed; (c) i,i+1 both
  rotated (> K), j fixed; (d) i,i+1 and j all... all-rotated/all-fixed are killed (FFCT55 R2
  constant-binding). So just TWO patterns: (a) and (c)!
- For pattern (a) (i,i+1 fixed, j rotated): the support function theta -> det3 (A i)(A i+1)(rot
  (-theta) (A j)) — single rotation in slot 3 directly, NO slot normalization needed. Its
  derivative: det3 (A i)(A i+1)(cross k (rot...)) — FFCT26's hasDerivAt + the one-sided argument
  gives the sign; expand via det3_cross_expansion and relate to the span coefficient b of
  A' i = a A'(i+1) + b A' j: this is the FFCT27/29 Gram <-> coefficient bridge BUT the pivot here
  is NOT the axis: the Binet expansion det3 x y (k x w) = <x,k><y,w> - <x,w><y,k> doesn't directly
  give the Gram-at-mid form. HOWEVER you do not need the Gram form: you need b's SIGN. Route:
  b = det3-ratio: from A' i = a A'(i+1) + b A' j, apply det3 (A' i)(A' i+1)(.)... no — apply the
  functional z -> det3 (A'(i+1)) z ... Use: det3 (A'(i+1)) (A' i) (w) = b det3 (A'(i+1)) (A' j) (w)
  for any w (the a-term dies). Pick w = an out-of-plane witness with known sign (the FFCT24-T2
  pattern; the produced hemisphere/another support supplies the witness). OR the cleaner route:
  at the binding the three are coplanar; the one-sided derivative tells you which side the rotated
  A' j moves to as theta decreases below delta*; admissibility (support >= 0 below) pins the sign
  geometrically. Work the ledger carefully (signs killed two designs; write each +- as an explicit
  lemma).
- For pattern (c) (i,i+1 rotated, j fixed): factor the common rotation out (FFCT29 R1
  det3_rot_rot_rot idiom): det3 (rot u)(rot v)(w) = det3 u v (rot^{-1} w) — single rotation in
  slot 3 with angle +theta — the MIRROR ledger of (a).
- If both patterns yield b < 0: NonAxisMixedBindingResidue is DISCHARGED, support-stuck is
  entirely impossible (state wbs_supportStuck_impossible), and via ZinanFFCT57's (a)-form
  (mainPlus_of_supportStuckImpossible — read its exact input shape) the REACH-only route closes:
  state the final theorem chain to spherical_arm_mono (the strict-arm chapter headline,
  UNCONDITIONAL except NoNonadjacentRepeat if FFCT57's (a) still carries it — read it).

## Deliverables
ZinanFFCT59.lean compiling 0-error clean-3 + HANDOFF/outbox/ch13-nonaxis-report.md with the
verdict per pattern and the final headline status. Do NOT git commit.
Work until terminal: each pattern either yields b < 0 (discharged), or a proven counterexample
(the binding pattern is realizable with b > 0 — then the cut route handles it, document), or a
precisely-stated irreducible sub-goal with the failing tactic chain shown. Grind.
