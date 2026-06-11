# CODEX BRIEF: grind Ch13FinalSurface70 item by item (FFCT71)

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-70 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT71.lean. Verify via scp + ssh uisai2 (build FFCT70 olean first).
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## Read FIRST and FULLY: HANDOFF/outbox/ch13-wrapbase-report.md — the "What still resists"
sections give the EXACT blocking shape per item. Then the four items in priority order:

1. hbpos_apos (BPosAPosEndpointCase): FFCT68 landed the adapter WITH ihdim+hdiag; the v4 surface
   still carries the case because the adapter's own inputs aren't supplied AT THE HEADLINE SITE.
   Plumb: the final recursion (FFCT69/70's assembly through FFCT67/66) must provide ihdim (the
   strong-induction IH — restructure the headline as the induction step if needed: state
   mainPlus_at_level_v4 taking (∀ m < n, MainPlus m) and close the loop via the banked recursion
   (FFCT19's mainPlus_all pattern or FFCT58's rebuilt one — find which is live)); hdiag = the
   StuckAtKData diagonal — assembled at the bpos_apos binding from FFCT49's bridge + the
   trichotomy data (a,b>0 => the NNReal datum => StuckAtKData fields incl. hα/hβ from the
   coefficient equivalences (FFCT27/29) — they're FREE here because a,b>0 ARE the Gram signs via
   gramSigns_iff_nonneg_coords!!). Wire end-to-end.
2. hbpos_aneg_tail (the aneg tail corner): read its exact statement; the apex-at-tail aneg case —
   the FFCT60/61 mirror + the FFCT70 successor-collapse variant at the mirrored configuration.
3. hmirrorSeed's raw wrap corner: the wrap-edge SupportStuckWBS binding (base vertex n): the
   cyclic relabel — a wrap-edge support sOrient (A' n)(A' 0)(A' j) = 0 is, by det3 cyclic
   invariance, sOrient (A' j)... build the generic wrap-to-forward converter: the triple
   (n, 0, j) relabels as the forward triple (j', j'+1?...) NO — the binding EDGE must be an arm
   edge; the wrap (n,0) is the closure edge — the polygon's support family includes it; the
   StuckAtKData consumer needs a forward in-arm edge. Convert: the vanishing wrap support =
   (FFCT42's identity) the BASE diagonal support at... FFCT42 proved baseCapSupportW's zero IS
   the wrap support at K; conversely a wrap-edge binding at vertex j is det3 (A' n)(A' 0)(A' j)
   = 0 = (cyclic) det3 (A' j)(A' n)(A' 0): a coplanarity of (j, n, 0). Treat it as a FOLD at
   index... the b-trichotomy machinery applies to ANY coplanar triple with two distinguished
   short-arc-adjacent vertices — here (n, 0) are wrap-adjacent: run the trichotomy with the
   roles (i, i+1) := (n, 0-as-n+1) via the MIRROR/cyclic rotation of the arm (the arm has no
   cyclic symmetry, but the mirror swaps ends — the wrap edge maps to itself reversed; check
   whether mirrorArm sends the wrap binding to a forward binding near index 0 — the mirrored
   triple (0', n', j') with the edge (0,1)?? compute the index images precisely). If the
   honest conversion lands, the wrap corner dies; else SHRINK it (e.g. to a single named
   WrapEdgeBindingResidue with the precise statement).
4. hcross (CrossPieceNoCollisionAtSup): attempt the derivative-at-collision kill (the FFCT26
   machinery at the collision configuration: the one-sided derivative of the collision-support
   member at the sup — the lastthree-brief's computation det3 (A r)(A r+1)(k x A r) =
   <A r,k><A r+1,A r> - <A r+1,k>; CHECK sign-definiteness with the WBS context's available
   facts (hemisphere: <h,*> > 0; the axis k = A' K...; if indeterminate, KEEP hcross as the
   final named input — it is sharp and satisfiable; do not fake).
## Deliverable: the sharpest spherical_arm_mono_final_ch13_v5 + exact surface report at
HANDOFF/outbox/ch13-surface70-report.md. ZinanFFCT71.lean 0 errors clean-3. No commit. Grind.
