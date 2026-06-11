# CODEX BRIEF: the sign-carrying wrap propagation (FFCT80) — THE LAST LOCK

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-79 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT80.lean. Verify via scp + ssh uisai2 (export PATH=$HOME/.elan/bin:$PATH;
build FFCT79 olean first). Rules: no sorry/admit/axiom/native_decide; clean-3.

## THE design: HANDOFF/design-rounds/ch13-signcarry-final.md — read ALL of it (17.6KB; it was
written from the post-mortem of three failed runs and pins every brick: WrapPlaneState, the
landed boundaryPlane_step_sameSign instantiation at the wrap anchors, wrap_next_state_or_progress
(the sector re-extraction + the FOUR-branch trichotomy with the ANTI-CIRCULARITY routing table:
opposite-sign goes to FFCT56/70 kills or mirror transports — NEVER back to the v9 tail residue),
the zero-coefficient routing, the induction, the v10 assembly). Implement faithfully, brick by
brick, in the design's order. Verify every cited landed name against source.
## Target: wrapPlanePropagation (general) ⟹ the three v9 residues become theorems ⟹
`spherical_arm_mono_final_ch13_v10 : (the hcross binder) -> SphericalArmMonotone` — the
chapter's {hcross}-only final form. Report the statement verbatim.
## Deliverable: ZinanFFCT80.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-v10-final-report.md.
No commit. Grind to terminal.
