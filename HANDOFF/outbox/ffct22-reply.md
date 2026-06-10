FFCT22 — Ch13 B5 tail half (OnFoldRay cone propagation). 2026-06-10, Opus worker.

STATUS: file `ProofsInTheBook/ZinanFFCT22.lean` builds clean-3 (propext, Classical.choice,
Quot.sound) for all 7 banked theorems; 0 sorry / 0 axiom / 0 admit / 0 native_decide.
Verified: `scp` + `lake build ProofsInTheBook.ZinanFFCT21` (clean) + `lake env lean ZinanFFCT22.lean`
(0 errors, all #print axioms clean-3).

WHAT IS BANKED (load-bearing, unconditional):
1. `OnFoldRay v w z` (structure): `det3 v w z = 0` ∧ `z ∈ span≥0 {v, w}` — exactly the design's cone
   datum. `OnFoldRay.coeffs` extracts the real nonnegative combination.
2. `far_fold_tail_collinear_step` — THE DETERMINANT-VANISHING HALF of the propagation, fully
   unconditional. Mechanism (symbolically verified in pure 3-D, NO planar lift): with the i=0 fold
   `A0 = a•A1 + b•Aj` (b>0) and the cone repr `At = c•A1 + d•Aj` (d>0),
       S1 = det3(A0, A1, At1) = -b · D ,   S2 = det3(At, At1, A1) = d · D ,   D = det3(A1, Aj, At1).
   The two weak supports (edge (A0,A1) at At1; edge (At,At1) at A1) give S1≥0, S2≥0 ⟹ D≤0 and D≥0 ⟹
   D = 0. This is the clean half and it closes.
3. `coplanar_triple_det3_zero` / `..._of_onFoldRay` — three vertices in a common 2-plane span{A1,Aj}
   have det3 = 0 (the bridge from a RANGE of cone memberships to the consecutive joint triple).
4. `far_fold_tail_not_interior` — a propagated consecutive collinearity det3(A(t-1),At,A(t+1))=0 at an
   interior position ⟹ jointAngle ∈ {0,π} (FFCT21's bridge) ⟹ PositiveJoints + jointAngle_lt_pi kill.
   Unconditional given the collinearity.
5. `far_fold_tail_refuted` — packages 3+4: the tail cone-propagation datum (three consecutive
   interior OnFoldRays) ⟹ False.
6. `far_fold_boundary_classification` — THE FULL B5, target signature
   `i = 0 ∧ (j = n ∨ j = n-1)`, combining FFCT21's i=0 half (unconditional) with the tail refutation.

THE PRECISE BLOCKING GAP (the audited master brick, NOT faked, NOT axiomatized):
The full induction needs to RE-EXTRACT the cone membership of A(t+1) — produce c',d'≥0 with d'>0 and
A(t+1)=c'•A1+d'•Aj — to continue. `far_fold_tail_collinear_step` gives only det3(A1,Aj,A(t+1))=0 (the
LINE), not the nonnegative-cone signs (the RAY). Direct computation shows WHY this is genuinely hard:
once A0, At, A(t+1) all lie in plane span{A1,Aj}, EVERY det3 among them vanishes, so NO support
involving only in-plane vertices can certify the sign of the A(t+1) coefficient. The sign requires an
OUT-OF-PLANE reference vertex vk with controlled orientation:
       det3(A1, A(t+1), vk) = q · det3(A1, Aj, vk)     (q = the Aj-coefficient of A(t+1))
       det3(A(t+1), Aj, vk) = p · det3(A1, Aj, vk)     (p = the A1-coefficient)
so the signs of p,q are read off from supports at an out-of-plane vk with KNOWN sign of
det3(A1,Aj,vk). Supplying such a witness with the correct, consistent sign needs the polygon's STRICT
convexity at the relevant tail edge — which the WEAK arm A does NOT provide pointwise (weak A may have
collapsed vertices). This is exactly the 250–450-line master brick the B5-B1 audit (lines 4–5) scoped
OUT. I mapped its full mechanism but did not close it; it is encapsulated honestly as the explicit
hypothesis `TailConePropagates A j hj` (a satisfiable Prop, guarded non-vacuous by `onFoldRay_self`),
so `far_fold_boundary_classification` is the HONEST CONDITIONAL form: unconditional in the i=0
direction (FFCT21), conditional on the named `TailConePropagates` witness in the j∈{n-1,n} direction.

NEXT BRICK (to make B5 fully unconditional): `far_fold_tail_cone_reextract` — from det3(A1,Aj,At1)=0,
the supports, and an out-of-plane witness with known orientation (built from STRICT B's
strict_nonincident at the tail edge transported to A via JointLe/SameSides), produce the nonnegative
coefficients of A(t+1) with d'>0; then `far_fold_tail_propagates` (the ℕ-induction up the tail
t=0…j+1 supplying `TailConePropagates`) discharges the hypothesis. This is the genuine master gap.
