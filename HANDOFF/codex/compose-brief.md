# CODEX BRIEF: the final composition (FFCT82)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-81 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT82.lean. Verify via scp + ssh uisai2 (export PATH=$HOME/.elan/bin:$PATH;
build FFCT81 olean first). Rules: no sorry/admit/axiom/native_decide; clean-3.

## The last gap (HANDOFF/outbox/ch13-v10-done-report.md): BoundaryZeroProgress's normalized
branch lacks j+1 < n+1; wrapPlanePropagation_probe_one returns the pair (0, n) which the no-tail
consumer rejects. THE COMPOSITION FIX:
1. The (0, n) output IS the apex shape: sOrient (A 0)(A 1)(A n) = 0 with the probe at n —
   apexNBoundaryZeroPropagation (FFCT78, landed) consumes EXACTLY this (its hypothesis
   sOrient (A i)(A i+1)(A n) = 0, i+1 < n) and returns NormalizedInteriorSupportZero (per the
   q23 §2 reading — VERIFY its exact output). Compose: probe-one wrap output -> apex theorem ->
   normalized interior zero (now WITH interiority) -> FFCT81's no-tail consumer. Mind i+1 < n
   side conditions (i = 0: 1 < n ⟸ 2 ≤ n ✓).
2. For the general-probe branches (FFCT80's WrapPlaneState chain): the propagation's normalized
   outputs — check each exit's pair shape; any apex-shaped exit routes through FFCT78 likewise;
   genuinely-interior exits carry/derive the bound (omega from the state's index constraints —
   strengthen the exit lemmas' statements where the bound is derivable from the invariant; the
   WrapPlaneState carries k < n+1 and the step conditions — thread).
3. Assemble: `spherical_arm_mono_final_ch13_v10 (hcross : CrossPieceNoCollisionAtSup) :
   SphericalArmMonotone`. Verbatim in the report. THE CHAPTER CLOSES HERE.
## Deliverable: ZinanFFCT82.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-CLOSED-report.md.
No commit. Grind to terminal.
