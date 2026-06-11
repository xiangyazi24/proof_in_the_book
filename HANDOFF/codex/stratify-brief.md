# CODEX BRIEF: the stratified consumer (FFCT81) — break the last circle

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-80 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT81.lean. Verify via scp + ssh uisai2 (export PATH=$HOME/.elan/bin:$PATH;
build FFCT80 olean first). Rules: no sorry/admit/axiom/native_decide; clean-3.

## The circle (HANDOFF/outbox/ch13-v10-final-report.md): tail residue -> wrap zero ->
WrapPlanePropagationGeneral -> BoundaryZeroProgress -> the GENERIC endpoint consumer ->
re-demands BPosANegTailCornerResidueV9. The math is all landed; the consumer is monolithic.
## The fix — STRATIFY:
1. Read BoundaryZeroProgress's exact disjuncts (FFCT76/77/80). Its interior-normalized-zero
   branch must feed an endpoint consumer that does NOT carry the tail corner: locate the v9
   chain's interior path (the normalized seed -> CutReady -> cut transport route through
   FFCT74/77's szOpeningStepPlusNR — the support-stuck dispatch's NON-tail branches) and state
   `endpoint_of_normalizedInteriorZero_noTail` — the consumer for ALREADY-normalized zeros,
   whose proof routes through the b-trichotomy WITHOUT the tail corner (the tail corner only
   arises for j=n apex bindings — a NORMALIZED interior zero has its triple interior, so the
   tail case is vacuous there: VERIFY by reading which branch demanded the tail residue — it
   should be the j=n case of the generic dispatch; the normalized zero's j is interior by
   construction => the demand vanishes definitionally or by an omega side condition).
2. Then discharge BPosANegTailCornerResidueV9: tail corner -> (FFCT80's non-circular wrap-zero
   production) -> WrapPlanePropagationGeneral -> BoundaryZeroProgress -> case: interior zero ->
   the NEW noTail consumer; endpoint payload -> direct. NO re-entry.
3. Then: the v9 residues all theorems; assemble
   `spherical_arm_mono_final_ch13_v10 (hcross : CrossPieceNoCollisionAtSup) : SphericalArmMonotone`
   — verbatim in the report.
## Deliverable: ZinanFFCT81.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-v10-done-report.md.
No commit. Grind to terminal.
