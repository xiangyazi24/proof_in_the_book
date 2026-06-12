(q24 final design, pasted by Xiang 2026-06-11 — THE closing route for the last semantic case)

VERDICT: the a<0,b>0,j=n corner kills cleanly; NO hidden case behind it. The master's wrap-sweep
had a sign gap (plane membership insufficient — the state must carry OpenCone coefficients).
THE CLEAN ROUTE: BACKWARD sweep from the tail: A n -> A(n-1) -> ... -> A(i+2) along ordinary
edges (r >= i+3 keeps both anchors P=A i, Q=A(i+1) nonincident), landing
OpenCone (A i)(A i+1)(A (i+2)) => sOrient (A i)(A i+1)(A i+2) = 0 vs PositiveJoints at joint
i+1 (0 < sOrient ...) => False. Small-i cases unify automatically (table in the full text);
i = n-2 needs no sweep.

THE SIX BRICKS:
A. openCone_tail_of_aneg_bpos (rearrangement; 30-60 LoC, field_simp/ring_nf/linarith).
B. edgeAnchor_prev_plane_of_next_openCone (determinant zero step: OpenCone C + two weak supports
   of edge (Y,C) at P,Q => sOrient P Q Y = 0; the multiplier identities
   sOrient Y C P = -d * sOrient P Q Y, sOrient Y C Q = c * sOrient P Q Y; 50-90 LoC).
C. openCone_of_plane_short_not_on_edge — THE new semantic brick (120-220 LoC): Y in-plane +
   ShortArc Y C + C in OpenCone + NOT OnFoldRay Y C P + NOT OnFoldRay Y C Q => OpenCone P Q Y.
   Geometry: a short arc from the cone to outside it must pass through P or Q = exactly
   OnFoldRay; NR excludes it. Reuse FFCT22's OnFoldRay; the circle-order lemma at fixed edge
   anchors.
D. edgeAnchor_back_step (B+C composition; 20-40).
E. tailCone_backward_to_succsucc (descending induction with the invariant
   ∀ r, i+2 <= r <= n -> OpenCone P Q (A r); nonincidence by omega; 120-180).
F. aneg_bpos_tail_contra / bpos_aneg_tail_forbidden (50-80): placed BEFORE the dispatch — the
   j=n witness never reaches the no-tail consumer; the interlock dissolves; v10 assembles.

NOTE on landed names: the answer (working from public main) mapped to
SphericalStuckGeneral.StuckAtKData / foldedFlat_of_support / stuckAtK_diag_le — on OUR branch the
corresponding pieces are the FFCT22 OnFoldRay machinery + FFCT49/51's bridges; the NR
sign-extraction need is the SAME finding as FFCT22's audited honest scope note.
