# CODEX BRIEF: the FINAL reconciliation (FFCT67) — close the consolidated66 surface

Repo ~/repos/proof_in_the_book (zinan-overnight; FFCT37-66 committed). CREATE ONLY
ProofsInTheBook/ZinanFFCT67.lean. Verify via scp + ssh uisai2 (build FFCT66 olean first).
Rules: no sorry/admit/axiom/native_decide; clean-3; refutation-check anything new.

## The four items of spherical_arm_mono_consolidated66 (read ZinanFFCT66.lean + its report):
1. hspanSeed (SupportStuckWBSVanishingSpanSeedSupply): the real span representation at the
   binding — FFCT49's bridge built exactly this (the vanishing support + independence => span;
   independence from ShortArc + the FFCT46/47 hemisphere). Wire it: read FFCT49/51's landed
   span-extraction lemmas and supply the field. If FFCT49's form is WB-pinned vs FFCT66's WBS
   shape, mirror the short derivation.
2. hback (BackwardFoldCase): FFCT54 PROVED the consumer-exclusion (backward_revArm_not_forward +
   the operative forward-only form; the consumer's StuckAtKData.hij1 excludes backward
   structurally). Check WHY consolidated66 still carries it: if its dispatch enters before the
   orientation normalization, REROUTE through FFCT52's orientationNormalized (raw binding =>
   normalized forward on P or revArm — and on revArm use FFCT61's MIRROR transports to get the
   convexity, then the forward machinery applies to the mirrored pair and endpt transports back).
   Close it; if a genuine corner survives (e.g. the wrap-base case FFCT52 flagged), name it
   sharply.
3. The two bpos endpoint consumers (BTrichotomyEndpointSurfaceV2):
   - bpos_apos: the (a>0, b>0) fold = the NNReal datum => FFCT25 classification => FFCT65's
     foldedFlatCutTransportPlusNR_v2 boundary closes (the (0,n) and the BoundaryTailRay-threaded
     (0,n-1) — FFCT66 supplies the tail proof in-context; wire end-to-end). The IH: the
     consolidated headline's induction provides MainPlus at smaller n — check FFCT66's recursion
     shape and thread.
   - bpos_aneg: the (a<0, b>0) configuration = FFCT64's plane-accumulation kill (the a<0 case
     analysis in the btrichotomy brief — read FFCT64's landed lemmas; if the kill was named-not-
     proven there, prove it now: the j-between rearrangement + the FFCT56-style successor-edge
     collapse at the relabeled apex — the mechanism is landed, the relabeling is the work).
4. hnorepeat: KEEP as the single named accepted input (NoNonadjacentRepeat of the opened arm) —
   provide the cleanest threading + its guard.
## The TRUE final theorem
`spherical_arm_mono_final_ch13` : mod ONLY the no-repeat supply (+ anything that genuinely
survives 1-3, named sharply). Update-ready docstring with the complete honest statement. Also
state the unconditional corollary under `NoRepeatSupply` and check whether the ORIGINAL strict
arm's no-repeat (strict arms have distinct vertices? grep for a strict-arm injectivity fact —
strict_nonincident might force pairwise distinctness: a repeat A r = A s makes some support
det3 = 0 vs STRICT > 0!! For the ORIGINAL B-arm yes; for the OPENED weak A' arm the supports are
weak — but wait: the no-repeat needed is on A' = openedWBS of the ORIGINAL STRICT A: a repeat
A' r = A' s with r,s both <= K or both > K maps back to A r' = A s' (openTail is injective on
each piece via rot) => a repeat in the STRICT original => strict support contradiction!! (check:
det3 (A r)(A r+1)(A s) with A s = A r is det3 x y x = 0, but strict_nonincident demands > 0 for
the NonIncident pair (r, s) when s != r, r+1 — CONTRADICTION => strict arms have NO nonadjacent
repeats!) The CROSS-piece case (r <= K < s, A r = rotated A s): NOT excluded by the original
strictness — the rotation can collide a fixed vertex with a rotated one at special angles...
BUT at the WBS sup, can it? A collision IS a nonadjacent repeat of A' — which creates the zero
support det3 (A' r)(A' r+1)(A' s) = 0 — at the SUP the supports are >= 0 weakly, so a collision
is CONSISTENT... however the collision is itself a binding-like event: would the monitored
family have stopped earlier? The supports member (r, r+1; s) hits 0 AT the collision angle —
the WBS sup is the FIRST binding, so at delta*_WBS either no collision happened on [0, delta*)
(margins strictly positive before) and AT the sup the collision IS the binding... so the
binding-with-collision case: the span seed at a collided binding: A' r = A' s = ... handle:
if the binding support's zero comes from a collision (A' j equals A' i or A' i+1 — but
NonIncident j != i, i+1 as INDICES; vertex-equality with distinct indices possible) — the
b-trichotomy at such a binding: A' i = a A'(i+1) + b A' j with A' j = A' i (say): then
(1-b) A' i = a A'(i+1) => collinear => ... it degenerates into the b=0/repeat analyses already
landed. THREAD this case analysis: cross-piece collision at the sup => one of the landed
degenerate kills fires OR it IS the no-repeat residual — pin precisely which. If the cross-piece
case is the ONLY survivor, the final input shrinks to CrossPieceNoCollisionAtSup — sharper than
full NoNonadjacentRepeat!)
## Deliverables
ZinanFFCT67.lean (0 errors, clean-3) + HANDOFF/outbox/ch13-reconcile-report.md. No commit.
Grind to terminal — this should be the LAST Ch13 file.
