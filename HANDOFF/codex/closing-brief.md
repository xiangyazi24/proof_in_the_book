# CODEX BRIEF: THE CLOSING WAVE (FFCT83) — bpos_aneg_tail_forbidden + v10

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-82 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT83.lean. Verify via scp + ssh uisai2 (export PATH=$HOME/.elan/bin:$PATH;
build FFCT82 olean first). Rules: no sorry/admit/axiom/native_decide; clean-3.

## THE design: HANDOFF/design-rounds/ch13-tail-backward-sweep.md — the six bricks A-F verbatim
(the backward sweep from the tail; brick C is the one new semantic piece: the NR sign
re-extraction via ShortArc + OnFoldRay exclusion — reuse FFCT22's OnFoldRay; adapt the circle-
order argument at fixed edge anchors). Implement A->F in order, compile after each.
## Then: place `bpos_aneg_tail_forbidden` BEFORE the dispatch (the j=n witness never reaches the
no-tail consumer); the FFCT81/82 interlock dissolves; discharge the remaining v9 residues and
assemble `spherical_arm_mono_final_ch13_v10 (hcross : CrossPieceNoCollisionAtSup) :
SphericalArmMonotone` — verbatim in the report. THE CHAPTER CLOSES.
## Deliverable: ZinanFFCT83.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-CLOSED-final.md.
No commit. Grind to terminal.
