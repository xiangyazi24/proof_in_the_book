# CODEX BRIEF: the two propagation induction wrappers (FFCT78) — the LAST assembly

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-77 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT78.lean. Verify via scp + ssh uisai2 (build FFCT77 olean first;
export PATH=$HOME/.elan/bin:$PATH on uisai2 shells).
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## Read: HANDOFF/outbox/ch13-v9-report.md (the exact missing wrapper statements) +
HANDOFF/design-rounds/ch13-wrap-propagation.md (the q22b induction design + sign-branch routing
table) + ZinanFFCT76.lean (the landed step pieces: boundaryPlane_step_sameSign,
flat_interior_joint_absurd_public, normalized_zero_of_wrap_probe_one).
## The job: build the TWO kernel-checked induction wrappers:
1. `wrapPlanePropagation`: from the wrap binding's boundary-zero, iterate the step — invariant:
   the plane contains the anchor pair + the swept prefix; each step: the same-sign branch
   advances (boundaryPlane_step_sameSign), the zero-coefficient branch hits the repeat/antipodal
   kills, the opposite-sign branch hits the FFCT56/70 collapses (per the design table); три
   consecutive interior in-plane => flat_interior_joint kill; termination: strong induction on
   the un-swept count (≤ n). Conclusion: the v9 residues' payload (the normalized interior seed
   OR the endpoint payload — match the v9 interface FFCT77 defined).
2. `apexNBoundaryZeroPropagation`: the j=n apex variant (the propagation from the other end —
   same skeleton, the mirror/wrap-successor entry per the FFCT75/76 probes).
Then: discharge the three v9 residues from CrossPieceNoCollisionAtSup alone is NOT the shape —
re-read: the residues' v9 forms should become THEOREMS given the wrappers (no hcross needed for
them); assemble `spherical_arm_mono_final_ch13_v10 : (the hcross binder) -> SphericalArmMonotone`
— THE {hcross}-only chapter form. Docstring: the complete final statement.
## Deliverable: ZinanFFCT78.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-v10-report.md with
the v10 statement verbatim. No commit. Grind to terminal — THIS IS THE LAST PIECE.
