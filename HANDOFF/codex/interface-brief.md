# CODEX BRIEF: the interface reconciliation (FFCT77) — assemble v9

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-76 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT77.lean. Verify via scp + ssh uisai2 (build FFCT76 olean first).
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## The situation: HANDOFF/outbox/ch13-finalwave-report.md — FFCT76's propagation bricks
(boundaryPlane_step_sameSign + flat_interior_joint_absurd_public + normalized_zero_of_wrap_
probe_one) are landed clean-3, but the design's BoundaryZeroProgress endpoint branch carries a
type incompatible with the v8 residues (WeakVanishingWrapSeedResidue /
SupportStuckWBSWrapSeedResidue / BPosANegTailCornerResidue as consumed by FFCT74's
Ch13FinalSurface74).
## The job (INTERFACE SURGERY, the math is in):
1. Read the report's exact incompatibility. Define the v9-compatible residue forms (new Props
   whose endpoint branch matches BoundaryZeroProgress) + prove the BRIDGES: each v8 consumer
   site (in FFCT74's szOpeningStepPlusNR_v8 / mainPlusNR_all chain) accepts the v9 form via the
   FFCT76 bricks (the propagation induction assembled: iterate boundaryPlane_step_sameSign with
   the sign-branch routing per the q22b design table — the zero/opposite-sign branches route to
   the LANDED kills (FFCT56/70 collapses, repeat/antipodal kills, the mirror transports) and the
   endpoint branch to the endpoint payload — build the induction wrapper `wrapPlanePropagation`
   from the FFCT76 step pieces; termination: strong induction on the remaining un-planed
   vertices, at most n steps).
2. Discharge the three v8 residues via the assembled propagation (the wrap/weak-wrap seeds: the
   propagation either yields the normalized interior seed (route to the landed seed machinery)
   or kills; the aneg tail: the j=n apex propagation from the other end).
3. Assemble `spherical_arm_mono_final_ch13_v9 : CrossPieceNoCollisionAtSup -> SphericalArmMonotone`
   (or with the NR/strict-headline binders as the v8 form carries — match it exactly, hcross the
   ONLY residue field). The docstring: the complete honest statement of Chapter 13's formalized
   arm lemma.
## Deliverable: ZinanFFCT77.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-v9-report.md with the
v9 statement verbatim. No commit. Grind to terminal.
