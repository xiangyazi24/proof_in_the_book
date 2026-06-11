# CODEX BRIEF: merge v5/v6 routes (FFCT73) — the sharpest true surface

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-72 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT73.lean. Verify via scp + ssh uisai2 (build FFCT72 olean first).
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## The situation (read HANDOFF/outbox/ch13-steplevel-report.md + ch13-surface70-report.md):
v5 (FFCT71): surface {hwrapSeed, hcross, hbpos_apos, hbpos_aneg_tail} — no hwpc/hffct.
v6 (FFCT72): surface {hwpc, hffct, hwrapSeed, hcross, hbpos_aneg_tail} — no hbpos_apos, but
re-carries hwpc (FLAGGED possibly-false in the q18b design round: the weak-entry Gram extraction
"may be false without a reachability/closure certificate" — ch13-cut-replacement.md §8) and
hffct.
## Job 0 — REFUTATION CHECK on hwpc (WeakPositiveCutReady): per the §3.3 discipline attempt the
refutation FIRST (a weak-positive arm with a vanishing support whose CutReadyPlus fails — the
Gram signs need not exist for arbitrary weak arms; the FFCT55/62 sign-indeterminacy witnesses
may adapt). If REFUTED: v6's surface is vacuous-conditional (impostor #7) — document loudly and
make v7 the repair. If not refuted after honest effort, still prefer eliminating it (Job 1).
## Job 1 — v7 = the v6 step-level structure WITH:
- the support-stuck branch entering through the STRICT-ONLY dispatch (FFCT62's
  strict_only/endpoint machinery — at the step level the arm A is STRICT (the induction starts
  strict and the REACH branch keeps strictness; the CUT branch's weak arm goes through the
  TRANSPORT not through a recursive weak MainPlus call — restructure so no weak-entry MainPlus
  is ever needed => hwpc GONE);
- hffct consumed via FFCT65's foldedFlatCutTransportPlusNR_v2 (the BoundaryTailRay-threaded,
  FFCT66-tail-supplied chain) instead of the bare Prop => hffct GONE (or reduced to v2's named
  context inputs — check what FFCT66 left; the cores were discharged so v2 should be
  essentially closed — VERIFY and wire);
- keep FFCT72's szOpeningStepPlus_v6 skeleton for the rest (the bpos_apos elimination).
Target: Ch13FinalSurface73 = {hwrapSeed, hcross, hbpos_aneg_tail} EXACTLY (the brief's original
v6 target), with `spherical_arm_mono_final_ch13_v7`.
## Deliverable: ZinanFFCT73.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-merge-report.md.
No commit. Grind to terminal.
