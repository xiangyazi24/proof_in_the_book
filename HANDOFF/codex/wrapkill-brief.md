# CODEX BRIEF: kill the two wrap residues by the SAME first-step trick (FFCT85)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-84 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT85.lean. Verify via scp + ssh uisai2 (export PATH=$HOME/.elan/bin:$PATH;
build FFCT84 olean first). Rules: no sorry/admit/axiom/native_decide; clean-3.

## The success template: ZinanFFCT84's normalizedStrictInteriorSupportZero_of_tail_firstStep —
the cone-holder + ONE brick-B step at an adjacent ordinary edge forces the next vertex in-plane
=> a coplanar triple with an ordinary edge = the normalized interior witness => the no-tail
consumer. NO sweep, NO cone invariant.
## Apply to the wrap residues (read their EXACT statements in FFCT69/70/74 and the v10-done
report): the wrap binding sOrient (A n)(A 0)(A j) = 0 (raw weak or WBS-sup flavor). The
b-trichotomy on the wrap triple (legs killed/routed as landed; the surviving cone legs):
whichever vertex holds the OpenCone of the other two (e.g. A 0 = c A n + d A j or A n = ...):
apply brick B (FFCT83's edgeAnchor_prev_plane_of_next_openCone — anchors = the cone's base pair)
at the cone-holder's ADJACENT ORDINARY EDGE (A 0's edge (0,1); A n's edge (n-1, n)) with the
weak supports at the two anchors => the adjacent vertex (A 1 or A(n-1)) forced in-plane =>
coplanar triple (the adjacent ordinary edge + one anchor as probe) => the witness — CHECK the
nonincidence/index bounds per case (the anchor-as-probe must be nonincident to the chosen edge:
e.g. edge (0,1) with probe A n: n ≠ 0,1 ✓ for n ≥ 2; probe A j: j ≠ 0,1 cases — pick the anchor
that satisfies; enumerate). Cone legs that fail (opposite signs etc.): the landed kills (FFCT56/
83's adjacent contradiction, repeat/antipodal). Handle BOTH residue flavors (the raw weak one +
the WBS-sup one — same geometry, different wrappers; read their consumers).
## Then: ALL v9/v10 residues are theorems => assemble
`spherical_arm_mono_final_ch13_v10 (hcross : CrossPieceNoCollisionAtSup) : SphericalArmMonotone`
— VERBATIM in the report. THE CHAPTER CLOSES.
## Deliverable: ZinanFFCT85.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-FINAL.md. No commit.
Grind to terminal.
