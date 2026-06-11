# CODEX BRIEF: minimize + discharge the Ch13ReachOnlyResidues bundle

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-61 + AUDIT_CAMPAIGN.md committed).
CREATE ONLY ProofsInTheBook/ZinanFFCT62.lean. Verify via scp + ssh uisai2 lake env lean (build
FFCT61's olean first). Rules: no sorry/admit/axiom/native_decide; clean-3 #print axioms; no
vacuous conditionals (this campaign killed 4 impostors via refutation checks — run them).

## Step 0 — BUNDLE MINIMIZATION (mechanical, do first)
Read ZinanFFCT59.lean's spherical_arm_mono_reachOnly_honest + szOpeningStepPlus_reachOnly_honest
and ZinanFFCT57.lean's (a)-form mainPlus_of_supportStuckImpossible. FFCT57's report claims the cut
machinery (hffct, hbridge/hwpc) is UNUSED in the (a)-path. VERIFY: does the reachOnly chain's
proof actually consume hwpc/hffct, or are they carried only as bundle fields? If unconsumed,
restate the headline with the MINIMAL bundle (only SupportStuckWBSImpossible) as
`spherical_arm_mono_reachOnly_v2` — this alone removes 2 of the 3 audit items from the surface.
CAREFUL: the induction recursion may pass WEAK arms after... in the reach-only path no cut happens
so arms STAY STRICT — verify the recursion's arm types line by line.

## Step 1 — the non-axis raw sign supply (the core of SupportStuckWBSImpossible)
Read HANDOFF/outbox/ch13-nonaxis-report.md + ZinanFFCT59.lean: codex59 eliminated patterns (a)
(j-rotated) and (c) (double-rotated, i+1<n) GIVEN the b<0 sign; the audit records "raw sign
supply into NonAxisMixedBindingResidue" as open. Supply it via the FFCT55 ledger machinery:
- Pattern (a) (i,i+1 fixed <= K < j rotated): support fn theta -> det3 (A i)(A (i+1))(rotS2 k
  (-theta) (A j)) — single rotation in slot 3 DIRECTLY. The one-sided argument at the WBS sup
  (admissibility on [0, delta*] from FFCT45 closure, zero at delta*) gives the derivative sign;
  FFCT26's hasDerivAt + det3_cross_expansion; then bridge the resulting inequality to the span
  coefficient b's sign: from A' i = a A'(i+1) + b A' j apply the functional w -> det3 (A' i)
  (A' (i+1)) w ... no — the coefficient readout: det3 (A'(i+1)) (A' i) w = b det3 (A'(i+1))
  (A' j) w for all w (a-term dies). Choose w := cross(A'(i+1), A' j)-direction or any w with
  det3 (A'(i+1))(A' j)(w) != 0 — get b = det3 (A'(i+1))(A' i)(w) / det3 (A'(i+1))(A' j)(w).
  The derivative inequality constrains exactly such a ratio at w = k-related vectors — work the
  ledger: at the binding the support is 0 and its one-sided derivative is <= 0 (approaching from
  admissible side); the derivative = det3 (A i)(A i+1)(cross k w_delta) where w_delta = the
  rotated A j position = A' j. So 0 >= det3 (A' i)(A' (i+1))(cross k (A' j)) [signs from the
  -theta chain rule — TRACK!]. Expand by Binet: = <(A' i) x (A' (i+1)), k x (A' j)> =
  <A' i, k><A'(i+1), A' j> - <A' i, A' j><A'(i+1), k>. Now substitute A' i = a A'(i+1) + b A' j
  and simplify (unit norms, G = <A'(i+1), A' j>): <A' i, k> = a<A'(i+1),k> + b<A' j,k>;
  <A' i, A' j> = aG + b. The expression becomes (after algebra) b * [<A' j,k><A'(i+1),A' j> ... ]
  — GRIND the algebra to isolate b times a sign-definite factor (the factor's sign from the
  geometry: k = the axis = A' K; the inner products <A'(i+1), k>, <A' j, k> etc. — what is
  sign-definite? Hmm the factor may NOT be sign-definite in general — if the algebra leaves a
  non-definite factor, that IS the obstruction; in that case document precisely and try pattern
  (c) (factored common rotation, mirror ledger) — maybe (c) is definite. Whichever patterns
  yield definite signs: combine with codex59's eliminations; whatever remains, name sharply.
## Step 2 — the tail j in {0,1} endpoint transport
FFCT60/61 routed j>=2 to death; j in {0,1} needs the boundary endpoint comparison on the MIRRORED
arm (FFCT61's mirrorArm suite is committed: weakConvex_mirrorArm etc.). The mirrored fold at
(0, n-j) with n-j in {n, n-1} = EXACTLY FFCT53's discharged boundary cases (foldedFlat_boundary_
j_eq_n and the (0,n-1) tail-fold close)! Apply FFCT53's theorems to the mirrored pair
(mirrorArm A', mirrorArm B) — need: the mirrored arms' hypotheses (FFCT61 transports), the
mirrored betweenness (FFCT61's span transport), the mirrored diagonal inequality, and the
endpoint transport back (endpt mirrorArm = endpt). Also the IH: FFCT53's boundary cases consume
MainPlus (n-1) — in the reachOnly induction the IH is available at smaller n — thread it.
CAREFUL with FFCT53's exact hypothesis list (hivl interval certs — FFCT54 discharged the A-side;
the B-side StrictDiagonalSupport... at the MIRRORED configuration the B-side interval is the
mirrored B's — the same named input or derivable? handle honestly).
## Step 3 — assemble
The sharpest honest form of SupportStuckWBSImpossible (or: supportStuckWBS_dispatch_final
covering ALL bindings: axis dead (FFCT56), non-axis (a)/(c) dead-or-named (step 1), tail j>=2
dead (FFCT61), tail j in {0,1} transported (step 2 — NOTE transport gives endpt <= endpt, NOT
False — so for those the STEP still concludes, just via transport not elimination: the step
theorem's shape must accommodate: ReachWBS or BaseStuck-handled or binding-eliminated or
boundary-transported — restate szOpeningStepPlus accordingly) + the minimized headline
`spherical_arm_mono_vNext` with the TRUE final surface. Report the surface precisely.

## Deliverables
ZinanFFCT62.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-bundle-report.md. No git commit.
Grind to terminal: each item = theorem / refutation / precisely-named irreducible with the
failing chain shown.
