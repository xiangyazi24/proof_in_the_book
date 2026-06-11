# CODEX BRIEF: hspanSeed + the hcases remnant (FFCT69)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-68 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT69.lean. Verify via scp + ssh uisai2 (build FFCT68 olean first).
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## Read first: HANDOFF/outbox/ch13-lastthree-report.md + ch13-reconcile-report.md +
ZinanFFCT67/68.lean — the EXACT current statements of hspanSeed
(SupportStuckWBSVanishingSpanSeedSupply) and the hcases remnant (which endpoint cases remain
after FFCT68 landed bpos_apos: presumably bpos_aneg and whatever the v2 surface lists), and the
REASONS the report gives for each blocker.
## Job 1 — hspanSeed (the revArm-branch seed):
The forward branch's seed = FFCT49/51's span extraction (vanishing support + independence).
The blocker was the REVERSED branch of orientationNormalized. Route: on the reversed branch the
binding lives on revArm A'; FFCT61's mirrorArm = reflection∘revArm carries FULL convexity
(weakConvex_mirrorArm) and FFCT52/61 transport the binding (sOrient sign tracked); run the
forward seed derivation on the MIRRORED pair; the span representation transports back through
the linear isometry (R linear: R(a•u+b•v) = a•Ru+b•Rv; reversal is an index map — the seed's
statement on A' at the original indices follows by rewriting). If the seed Prop's exact shape
resists transport, restate the dispatch to consume a SEED-ON-MIRROR disjunct (the consumer
chain after the seed is symmetric — verify and wire).
## Job 2 — the hcases remnant:
- bpos_aneg (a<0, b>0): the j-between rearrangement (A' j = c A' i + d A'(i+1), c,d>0) + the
  FFCT56-style successor-edge collapse at the relabeled apex (the FFCT64 brief's mechanism —
  check what FFCT64 actually landed for a<0 vs named; prove the variant: the apex is A' j with
  neighbors (j-1, j+1); its representation in terms of (A' i, A'(i+1)) is NOT the lemma's
  neighbor+far shape — prove the variant collapse: supports of edge (j, j+1) at i and i+1
  substitute to opposite multiples of one det3 => zero => plane accumulation => (j-1,j,j+1)
  coplanar => flat joint kill; the j=n / j+1 wrap corners via the FFCT60/61 mirror machinery).
- any other case the v2 surface lists: read + close or name sharply.
## Job 3 — the consolidated final:
spherical_arm_mono_final_ch13_v3 mod (ideally) ONLY CrossPieceNoCollisionAtSup. Report the
exact surface + what (if anything) still resists with the failing chains shown.
## Deliverables: ZinanFFCT69.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-spanseed-report.md.
No commit. Grind to terminal.
