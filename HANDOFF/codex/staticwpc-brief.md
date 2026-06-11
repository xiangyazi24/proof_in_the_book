# CODEX BRIEF: discharge WeakPositiveCutReady via the STATIC b-trichotomy (FFCT74)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-73 committed, build 8783 clean). CREATE
ONLY ProofsInTheBook/ZinanFFCT74.lean. Verify via scp + ssh uisai2 (build FFCT73 olean first).
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## The master's analysis (the merge-report blocker's resolution):
The recursion fundamentally passes through weak arms (the ear comparison's lower-dim call), so
hwpc (WeakPositiveCutReady) cannot be avoided — DISCHARGE IT INSTEAD. At a STATIC weak binding
(WeakConvexSphArm A + PositiveJoints A + StrictConvexSphArm B + SameSides + JointLe + the
vanishing nonincident support, NO sup/derivative context), run the b-trichotomy:
1. The span seed: vanishing support + (A(i+1), A j) independence (ShortArc + the arm's OWN
   strict open_hemisphere field — note WeakConvexSphPolygon's open_hemisphere is ALREADY strict
   ∀ i, 0 < ⟪h, P i⟫!) => A i = a A(i+1) + b A j real span (FFCT25 U2 / the FFCT49/51 extraction
   — these were sup-pinned? their MECHANISM is arm-level; mirror the short derivations).
   Orientation: handle j < i via FFCT52's normalization/the FFCT61 mirror (arm-level ✓); the
   wrap-base corner via the FFCT42-cyclic relabel (arm-level ✓ — the closed polygon's wrap
   support IS an edge support).
2. b < 0: midFold_coeffs_of_bneg (hemisphere ✓ the arm's own h) + midFold_interior_contradiction
   (weak supports + PositiveJoints + jointAngle_lt_pi from JointLe with strict B ✓ all arm-level)
   — the apex-interior case; apex-at-tail (i+1 = n): the FFCT60/61 mirror machinery — CHECK its
   WBS-pinning: the MECHANISM (mirror + classification) is arm-level; mirror what's needed.
   => the binding configuration is IMPOSSIBLE => the implication to CutReadyPlus holds by
   contradiction (SOUND, not vacuous-impostor: the contradiction derives from the binding
   hypotheses themselves).
3. b = 0: a = ±1 => consecutive equal (edge-short kill) or antipodal (hemisphere kill) =>
   impossible.
4. b > 0, a = 0: b = 1, A i = A j — a nonadjacent repeat: weak arms CAN repeat... the repeat
   makes the seed's independence... A i = A j with the vanishing support det3(A i)(A i+1)(A j)
   = det3 x y x = 0 consistent. KILL ROUTE: with A i = A j the polygon has a repeated vertex —
   then PositiveJoints/ShortArc at the j-side: the edges (j-1, j) and (j, j+1) attach at A j =
   A i... no immediate kill. HONEST handling: this leg needs NoNonadjacentRepeat A — and hwpc's
   statement does NOT carry it!! Options: (a) refine: state WeakPositiveCutReadyNR (the NR-
   threaded version), discharge THAT, and check the CONSUMER (SZOpeningStepPlus's weak-entry
   branch — does the recursion's weak arm HAVE no-repeat? The weak arms arising in the recursion
   are interval/spliced arms of STRICT originals + opened arms — strict originals have no-repeat
   (FFCT68's strictConvex_noNonadjacentRepeat); intervals of no-repeat arms inherit; opened arms
   = the CrossPiece story => the consumer-side supply exists modulo CrossPiece! Thread NR through
   the recursion as a carried invariant — the motive becomes MainPlusNR (weak+positive+NR entry);
   check FFCT18's MainPlus consumers tolerate the strengthening (the headline's strict arms
   supply NR free).
5. b > 0, a > 0: the NNReal datum => StuckAtKData (Gram signs free via
   gramSigns_iff_nonneg_coords; hsa from hemisphere+NR; hside from SameSides) + the ear
   certificates (FFCT73's intervalWrapData_of_positive_span + intervalWrapDataStrict_of_
   cyclicTriple + FFCT63's n∈{3,4}) => CutReadyPlus CONSTRUCTIVELY.
   a < 0 (b>0): the FFCT70 successor-collapse variant (arm-level) — impossible.
## Assemble: weakPositiveCutReadyNR_holds, then the SZOpeningStepPlus weak-entry branch closes,
then via FFCT72's recursion skeleton: mainPlusNR_all + the FINAL chapter headline
spherical_arm_mono_final_ch13_v8 mod the NET surface (expect: CrossPiece-class for the opened
arms' NR + the tail/wrap corners that genuinely survive — name exactly).
## Deliverable: ZinanFFCT74.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-staticwpc-report.md.
No commit. Grind to terminal.
