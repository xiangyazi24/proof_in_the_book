# CODEX BRIEF (uisai2-local): Ch35 fragment -> the FiveColorReducible certificate chain

Repo ~/repos/proof_in_the_book (zinan-overnight). CREATE ONLY ProofsInTheBook/ZinanCh35Cert.lean.
Verify locally: export PATH=$HOME/.elan/bin:$PATH && lake env lean ProofsInTheBook/ZinanCh35Cert.lean
(build needed oleans first). Rules: no sorry/admit/axiom/native_decide; clean-3.

## Context: AUDIT_CAMPAIGN.md's Ch35 row: the campaign closed chordSideResidue₁_final
(ZinanCh35FinalClose, mod the documented planar-input bundle), but the BOOK-level
Chapter35.chapter35 is the separate FiveColorReducible certificate theorem. THE JOB: wire the
campaign's closed chord-side subroutine INTO the book-level chain.
## Steps:
1. INVENTORY (read first, 30+ min): Chapter35's root file (grep `rg -n 'chapter35|FiveColorReducible' ProofsInTheBook/*.lean`),
   the JordanOracleConstruct / ThomassenInduction / ThomassenLists consumers (what does the
   induction need per recursion step: the ChordSideResidue for BOTH sides? the chordless branch?
   read the dichotomy), the campaign's outbox reports (ch35-*.md) for the landed surface.
2. The side-2 mirror: chordSideResidue₁_final is side-1; the side-2 analogue (the symmetric
   construction — check whether the landed machinery is side-symmetric or needs the mirror).
3. The CHORDLESS branch: the old design rounds (ch35-endgame-map.md if present, the
   FanIncidenceData/DeleteVertexMergedFaceSingleOrbit mentions in HANDOFF) — inventory what the
   chordless oracle needs and what's landed; wire or name sharply.
4. The certificate assembly: thread the residues into ThomassenLists/the induction; the planar
   input bundle stays named (the campaign's accepted surface). Target: the sharpest honest
   `fiveColor_of_planarInputs`-class theorem connecting to Chapter35.chapter35's hypothesis
   surface — report the exact remaining input list.
## Deliverable: ZinanCh35Cert.lean (0 errors, clean-3) + HANDOFF/outbox/ch35-cert-report.md.
No git commit. Grind to terminal.
