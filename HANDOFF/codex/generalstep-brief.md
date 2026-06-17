# CODEX BRIEF: the general-probe decreasing step (FFCT79) — close wrapPlanePropagation

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-78 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT79.lean. Verify via scp + ssh uisai2 (export PATH=$HOME/.elan/bin:$PATH;
build FFCT78 olean first). Rules: no sorry/admit/axiom/native_decide; clean-3.

## Read: HANDOFF/outbox/ch13-v10-report.md (the exact missing general-probe statement) +
ZinanFFCT76/78.lean (boundaryPlane_step_sameSign at its position; wrapPlanePropagation_probe_one;
apexNBoundaryZeroPropagation — the apex side CLOSED, mirror its induction skeleton for the wrap
side) + the q22b design (HANDOFF/design-rounds/ch13-wrap-propagation.md).
## The job: generalize FFCT76's step to ARBITRARY probe position m (the algebra is positionally
uniform: the plane anchored at the wrap pair, the swept prefix 0..m in-plane, the supports of
edge (m, m+1) at the two anchors substitute the in-plane representation of A m => opposite
multiples => A (m+1) in-plane OR a sign-branch kill — the SAME ledger as FFCT76's brick with the
anchor-pair representation of A m threaded through the invariant (each in-plane vertex carries
its (c,d) coefficients; the step's multiplier signs come from the coefficients' signs — the
invariant must CARRY the sign data: strengthen to "in-plane with same-sign cone coefficients"
(the OnFoldRay pattern from FFCT22!! — the landed OnFoldRay/cone machinery IS this invariant;
reuse FFCT22's structure). Then the induction (mirror apexNBoundaryZeroPropagation's skeleton),
the kills per branch (landed), termination, => wrapPlanePropagation (general). Then the three
v9 residues become theorems => Ch13FinalSurface77 assembles from hcross alone =>
`spherical_arm_mono_final_ch13_v10 : (hcross binder) -> SphericalArmMonotone`.
## Deliverable: ZinanFFCT79.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-final-report.md with
the v10 statement verbatim. No commit. Grind to terminal.
