# CODEX BRIEF: full-repo playbook audit (the campaign close-out)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-60 + Ch35/Ch36 campaign modules committed).
CREATE ONLY: AUDIT_CAMPAIGN.md (repo root) and, if refutations are needed, ProofsInTheBook/ZinanAudit.lean.
Verify loop as usual (scp + ssh uisai2 lake env lean). Rules: no sorry/admit/axiom/native_decide in any
Lean you write; clean-3 prints.

## The audit (playbook §3.3, applied to the three campaign chapters)
For EACH of the three chapter endpoints:
- Ch36: ProofsInTheBook/ZinanCh36Assembly.lean :: artGallery_strict_mod_M (inputs: Esplit/rest/M)
- Ch35: ProofsInTheBook/ZinanCh35FinalClose.lean :: chordSideResidue₁_final (the planar-input surface
  documented in its report) + the upstream contiguousInterval/jordan chain
- Ch13: the FFCT57/58/59/60 endpoint chain (read HANDOFF/outbox/ch13-tail-boundary-report.md +
  ch13-endpoint-audit-report.md for the final headline name and its exact input list)
do:
1. AXIOM AUDIT: ssh uisai2, run lake env lean on a scratch file that #print axioms every headline +
   every named input Prop's guard theorems. Record outputs verbatim.
2. HYPOTHESIS REFUTATION PASS: for every NAMED input Prop on each headline's surface, attempt a
   refutation (constant/degenerate instances AT THE EXACT QUANTIFIER SCOPE). Each verdict:
   REFUTED (= impostor, must be reported loudly) / SATISFIABLE-GUARDED (cite the existing guard
   theorem) / SATISFIABLE-ARGUED (write the argument; add a guard lemma to ZinanAudit.lean if cheap).
3. EXFALSO SCAN: grep the discharge proofs of each headline chain for exfalso/absurd through a
   hypothesis; for each hit verify the killed branch is genuinely impossible (cite the kill theorem)
   rather than hypothesis-smuggled.
4. STATEMENT FAITHFULNESS: compare each headline against the book's chapter claim (Ch13 = Cauchy arm
   lemma endpoint monotonicity for convex spherical arms; Ch35 = five-color theorem; Ch36 = art
   gallery floor(n/3)). Verdict per chapter: FAITHFUL / CONDITIONAL-honest (+ the exact mod-list) /
   FRAGMENT. Check the chapter headline consumers (grep the Chapter13/35/36 root files if they exist)
   for what the book-level statement needs vs what the campaign delivers.
5. Write AUDIT_CAMPAIGN.md: per-chapter verdict table, the full input surfaces, the refutation log,
   the axiom outputs, and a one-paragraph executive summary. Honest tone, no inflation.
Do NOT git commit. Terminal: the audit file complete + any cheap guard lemmas compiling clean-3.
