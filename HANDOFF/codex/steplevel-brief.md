# CODEX BRIEF: the step-level assembly rewrite (FFCT72) — eliminate hbpos_apos structurally

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-71 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT72.lean. Verify via scp + ssh uisai2 (build FFCT71 olean first).
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## The job (HANDOFF/outbox/ch13-surface70-report.md "hbpos_apos" section):
FFCT71 landed `BPosAPosDiagonalSupply` + `bpos_apos_endpoint_of_diagonalSupply_at_level`, but the
final recursion enters through FFCT62's strict-only dispatch which hides ihdim at the binding.
REWRITE the assembly at the SZOpeningStepPlus level: state `mainPlus_at_level_v6 (n) (ih : ∀ m < n,
MainPlus m) : MainPlus n`-shaped step where the support-stuck branch's bpos_apos case consumes
ihdim DIRECTLY (the FFCT68 adapter + FFCT71's supply assembled in-context: at the binding, a,b>0
gives the Gram signs via gramSigns_iff_nonneg_coords => StuckAtKData assembles (FFCT49 bridge
fields: hsupp from the binding, hsa from hemisphere+distinctness as FFCT49 did, hside from
SameSides) => the FFCT19-class diag lemma (stuckAtK_diag_le_plus — its hypotheses incl. the
interval/ear data: FFCT54/63's discharged certs + the n∈{3,4} freebies; thread the named interior
core where needed) => the FFCT65-v2 transport closes the branch with ih). Then the strong
induction `mainPlus_all_v6` (mirror the banked recursion skeleton) and the headline
`spherical_arm_mono_final_ch13_v6 : Ch13FinalSurface72 -> SphericalArmMonotone` where
Ch13FinalSurface72 = {hwrapSeed, hcross, hbpos_aneg_tail} (+ the diag interior core if it
genuinely re-enters via stuckAtK_diag) — hbpos_apos GONE from the surface.
## Also attempt (secondary): hbpos_aneg_tail's j=n endpoint — generalize the WBS-pinned mirror
tail machinery: the bare corner's statement vs NonAxisTailBoundaryResidue — write the bridge if
the shapes align after the mirror; else leave named.
## Deliverable: ZinanFFCT72.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-steplevel-report.md
with the v6 surface. No commit. Grind to terminal.
