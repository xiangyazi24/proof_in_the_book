# CODEX BRIEF: the wrap-base gap + endpoint-case remnant (FFCT70)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-69 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT70.lean. Verify via scp + ssh uisai2 (build FFCT69 olean first).
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new (6 impostors so far).

## Read first: HANDOFF/outbox/ch13-spanseed-report.md — the EXACT remaining items of
Ch13FinalSurface69 (the non-wrap/raw wrap-base gap from FFCT52's orientationNormalized + the
BTrichotomyEndpointCases remnant) with the recorded reasons.
## Job 1 — the wrap-base gap: FFCT52's orientationNormalized covers raw bindings with
a.val+1 < n+1 (non-wrap-base); the wrap-base case (the binding edge IS the wrap (n,0) or
the normalization hits the cyclic seam) was flagged. Ammunition: FFCT42's wrap-cyclic identity
(the wrap-edge support at K = the base diagonal via det3 cyclic permutation), the FFCT60/61
mirror machinery, FFCT68/69's adapters. Route: a wrap-base binding's triple relabels through the
cyclic det3 identities into a non-wrap form (the same trick FFCT42 used: sOrient (P n)(P 0)(P j)
= sOrient (P j)... work the cyclic ledger), then the landed normalization applies. If a genuine
seam corner survives, name it sharply.
## Job 2 — the endpoint-case remnant: read which cases remain (bpos_aneg variant collapse per
the FFCT64-brief mechanism — the relabeled-apex successor-edge collapse: supports of edge
(j, j+1) at i and i+1 substitute to opposite multiples => plane accumulation => (j-1,j,j+1)
coplanar => flat joint; the j=n/wrap corners via mirror). Implement the variant; close the cases.
## Job 3 — `spherical_arm_mono_final_ch13_v4`: mod ONLY CrossPieceNoCollisionAtSup (+anything
genuinely surviving 1-2, named). Update-ready docstring. Report the surface.
## Deliverables: ZinanFFCT70.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-wrapbase-report.md.
No commit. Grind to terminal.
