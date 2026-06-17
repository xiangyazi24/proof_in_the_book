# CODEX BRIEF: the three killable corners of Ch13FinalSurface74 (FFCT75)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-74 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT75.lean. Verify via scp + ssh uisai2 (build FFCT74 olean first).
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## Read: HANDOFF/outbox/ch13-staticwpc-report.md (+ ch13-surface70-report.md for the wrap
analysis history). The four v8 residues; hcross stays (proven sign-indeterminate, the accepted
input); kill the OTHER THREE:
1+2. The two wrap-seed residues (WeakVanishingWrapSeedResidue + SupportStuckWBSWrapSeedResidue):
the raw binding whose edge is the WRAP (n, 0). THE MIRROR END-SWAP: mirrorArm (= reflection ∘
index-reversal, FFCT61) maps index m to n−m: the wrap edge (n, 0) maps to (0, n)... as an EDGE of
the mirrored CLOSED polygon the wrap maps to the wrap (the closure edge is preserved as a SET but
its dart reverses). Hmm — the wrap stays wrap under mirror. ALTERNATIVE (the FFCT42 cyclic trick
GENERALIZED): the closed polygon's support family is CYCLICALLY symmetric — the wrap edge is only
special because the ARM structure picks index 0. Define the ROTATED arm (re-based at index r:
rotArm r P := fun m => P (r + m mod n+1))?? — the ARM is not cyclic (endpoints matter for endpt!)
— BUT the seed/CutReady machinery is about the LOCAL binding structure (StuckAtKData's fields are
index-local except hj : j <= N). Re-basing changes endpt — NOT directly usable for the headline...
THINK AGAIN: what does the wrap binding actually feed? The seed => CutReadyPlus => the cut
transport compares sDist diagonals + the IH on interval arms. A wrap-edge binding det3 (A n)(A 0)
(A j) = 0: the triple involves BOTH endpoints + an interior j. By cyclic det3 = det3 (A j)(A n)
(A 0): a coplanarity of (j, n, 0). The b-trichotomy on the REARRANGED representation: A n =
a A 0 + b A j or A 0 = a' A n + b' A j etc. — the fold-at-an-ENDPOINT configurations: i = n with
successor 0-through-wrap, or i = 0 with PREDECESSOR n. The far_fold machinery (FFCT21/25)
classified folds A i = a A(i+1) + b A j — at i = n the successor through the wrap IS A 0 (the
closed polygon's edge (n,0) is genuine; ShortArc holds by edge_short at the wrap ✓): the FFCT25
classification applied with the index convention... its proofs used Fin (n+1) cyclic arithmetic?
READ far_fold_boundary_classification_final's index hypotheses (i + 2 < j as NATURALS — the wrap
case has i = n, j interior: as naturals n + 2 < j is FALSE — out of scope). The REVERSED/mirrored
arm: mirror maps the wrap binding (n, 0, j) to (0, n, n−j) = a binding at edge (0, ...)... the
mirrored wrap edge: mirror sends m to n−m: the pair (n, 0) goes to (0, n) — i.e. the wrap again.
HONEST DEEP ROUTE: treat the wrap binding as the BASE-DIAGONAL configuration: det3 (A n)(A 0)
(A j) = 0 with the wrap edge short and supports — this is EXACTLY FFCT42's territory (the wrap
support at K = the base diagonal!): FFCT42/45 proved baseStuck => vanishing NONINCIDENT support
(the conversion FROM base TO ordinary support). A wrap binding IS a base-diagonal-zero event =>
by FFCT42's mechanism it yields an ordinary in-arm vanishing support (or Reach) => the seed runs
on THAT support instead!! Check FFCT42's exact statement (baseStuckWBS_forces_vanishingSupport /
the FFCT45 port) — if it converts ANY base-diagonal zero (not just the monitored BaseStuckWBS
event) — the arm-level version: base-diagonal zero + weak supports + ... => ∃ ordinary
nonincident vanishing support. If the landed form is family-pinned, prove the arm-level variant
(the mechanism was the det3 cyclic identity + ... read it). THEN both wrap-seed residues
discharge by rerouting to the ordinary-support seed (landed).
3. hbpos_aneg_tail (the j = n aneg endpoint): the apex A' j at j = n has no ordinary successor;
its successor-through-wrap is A' 0: run the FFCT70 successor-collapse with the WRAP successor
(supports of the wrap edge (n, 0) at i and i+1 — the closed polygon HAS them): substitute the
j-between representation into det3 (A' n)(A' 0)(A' i) and det3 (A' n)(A' 0)(A' i+1) => opposite
multiples => plane accumulation => (n−1, n, 0-through-wrap) coplanar => the closure joint flat —
NOT a PositiveJoints index... then iterate: the plane now contains i, i+1, n, 0 — use the
ORDINARY joint at n−1 or 1: continue the accumulation (the FFCT22 cone/pencil machinery) until an
INTERIOR consecutive triple lands in the plane => flat interior joint => kill. Implement with
the honest case analysis (small n separately).
## Then: spherical_arm_mono_final_ch13_v9 mod {hcross} ONLY (the target). Report exactly.
## Deliverable: ZinanFFCT75.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-corners-report.md.
No commit. Grind to terminal.
