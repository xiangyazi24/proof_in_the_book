# CODEX BRIEF: discharge the TWO FINAL Ch13 cores (FFCT66)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-65 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT66.lean. Verify via scp + ssh uisai2 lake env lean (build FFCT65 olean
first). Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## THE design: HANDOFF/design-rounds/ch13-two-cores.md — read ALL of it (17KB; the sections
beyond the executive summary contain the exact bricks, statements, estimates, and degenerate
audits for both cores). Follow it faithfully; where it cites landed names (cyclicTriplePos_
unconditional, PlanarConvexDiag, far_fold_tail_collinear_step, the FFCT24 witness machinery,
FFCT63's reductions and suppliers), VERIFY each against source before use.

## Core 1: StrictDiagonalSupport n>=5 interior — via the landed global convex-position machinery.
## Core 2: TailRayMembership — direct on the weak arm A via the A2 witness + weak supports +
PositiveJoints (the corrected route; the B-side chain was rejected for hypothesis mismatch).
## Then: feed both into FFCT65's spherical_arm_mono_consolidated and FFCT63's suppliers; state
the FINAL consolidated headline with the remaining surface (expected: NoNonadjacentRepeat-class
only, plus whatever the design honestly retains). Report the exact list.

## Deliverables
ZinanFFCT66.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-cores-report.md. No commit.
Grind to terminal — this is the last geometric content of Chapter 13.
