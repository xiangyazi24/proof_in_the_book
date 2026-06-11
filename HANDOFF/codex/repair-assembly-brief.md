# CODEX BRIEF: corrected FFCTPlus assembly + BTrichotomy wiring (FFCT65)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-64 committed, build 8774 clean). CREATE
ONLY ProofsInTheBook/ZinanFFCT65.lean. Verify via scp + ssh uisai2 lake env lean (build FFCT63/64
oleans first). Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check new Props
(6 impostors killed so far — including FFCT53's htfb, which is WHY this brief exists).

## Job 1 — the corrected FFCTPlus assembly (do NOT edit FFCT53)
HANDOFF/outbox/ch13-diag-tail-report.md (FFCT63): FFCT53's `htfb` binder is a FREE UNIVERSAL
TailFoldBoundary with no geometric hypotheses — proven FALSE numerically, so FFCT53's assembly
theorem `foldedFlatCutTransportPlusNR_holds` is dead weight (its hypothesis unsatisfiable).
FFCT63 supplied the satisfiable `BoundaryTailRay` + context-threading suppliers + the metric
reduction `tailFoldBoundary_of_rayMembership`. RE-DERIVE the assembly in FFCT65:
`foldedFlatCutTransportPlusNR_v2` with the (0,n−1) leg consuming BoundaryTailRay through FFCT63's
suppliers (reuse FFCT53's SOUND bricks: the adjacent kill, the (0,n) close, the classification
routing — import FFCT53 and call them; only the assembly + the (0,n−1) leg change). Also thread
FFCT63's StrictDiagonalSupport progress (n∈{3,4} discharged + arc-boundary lemmas) into the
interval-certs side (FFCT54's consumers) — the B-side hivl for n∈{3,4} is now FREE; for n≥5 carry
the named interior core.
## Job 2 — wire the BTrichotomy case consumers
Read HANDOFF/outbox/ch13-btrichotomy-report.md: the BTrichotomyDispatchSurface has 3 endpoint
case consumers + raw span supply + opened no-repeat. For each:
- raw span supply: the binding's vanishing sOrient + (A'(i+1), A' j) independence => the real
  span representation — FFCT25 U2 / FFCT51's machinery; independence from ShortArc + the FFCT46
  hemisphere (the FFCT49 bridge did exactly this — reuse/mirror).
- opened no-repeat: thread NoNonadjacentRepeat (openedWBS) — the accepted surface input; provide
  the named pass-through.
- the 3 endpoint case consumers: read their exact statements — they should be exactly the
  b>0 leg's FFCT25→corrected-assembly route (Job 1's v2!), the tail j∈{0,1} mirror transports
  (FFCT62's, mod their retained gaps — thread BoundaryTailRay there too if that's the gap), and
  the b<0 tail-apex leg (FFCT60/61's machinery). WIRE each to its landed supplier; whatever
  genuinely lacks a supplier, name sharply.
## Job 3 — the consolidated headline
`spherical_arm_mono_consolidated`: the sharpest current form with the FULL honest surface listed
in the docstring: expected = {NoNonadjacentRepeat-class, BoundaryTailRay/TailRayMembership core,
StrictDiagonalSupport n≥5 interior core} + whatever Job 2 surfaces. Report the exact list.

## Deliverables
ZinanFFCT65.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-repair-assembly-report.md. No commit.
Grind to terminal.
