# FFCT21 reply — Ch13 B5 bricks (far-fold boundary classification, `i = 0` half)

STATUS: COMPLETE (clean-3, no sorry/axiom/admit/native_decide). File: `ProofsInTheBook/ZinanFFCT21.lean` (385 lines). Only this file created; no other edits, no git.

VERIFICATION (uisai2, `lake env lean ProofsInTheBook/ZinanFFCT21.lean` after `lake build ProofsInTheBook.ZinanFFCT20`):
all 7 deliverable `#print axioms` report exactly `[propext, Classical.choice, Quot.sound]`. One harmless
linter warning (`hij` unused in `far_fold_no_predecessor` — kept as faithful far-fold interface context;
the predecessor kill is genuinely independent of the gap `j > i+2`).

## Delivered (per the ADVERSARIALLY-AUDITED design in ch13-B5-B1-audit.md)

1. `span_pair_coeffs_S2` — extract `a b : ℝ≥0` with `(a:ℝ)•v + (b:ℝ)•w = p` (FFCT19 mem_span_pair + NNReal.smul_def pattern).
2. `nnreal_smul_unit_eq_unit` — `p = a•v`, both unit, `a ≥ 0` ⟹ `a = 1 ∧ p = v` (norm both sides).
3. `coeff_b_pos_of_edge_short` — `b = 0` ⟹ `p = v`, contradicting `ShortArc p v` (def's first conjunct `p ≠ v`). ShortArc DID imply `p ≠ v` (no separate hypothesis needed).
4. `far_fold_no_predecessor` — the CORRECTED predecessor kill at `i ≥ 1`. Audited algebra implemented exactly:
   `det3 u p v = -b·det3 u v w`, `det3 u p w = a·det3 u v w` (via local left-multilinearity helpers
   `det3_add_mid`/`det3_smul_mid` — substrate only ships the right-argument versions); both weak supports
   `≥ 0` with `a,b > 0` ⟹ `det3 u v w = 0` AND `det3 u p v = 0` ⟹ adjacent triple at apex `A i` vanishes
   ⟹ `jointAngle A ⟨i-1⟩ ∈ {0,π}` ⟹ `PositiveJoints` kills 0, `jointAngle_lt_pi` (FFCT3) kills π. False.
5. **`far_fold_boundary_classification_of_nondeg`** — THE DELIVERABLE (audit fallback milestone): from
   `WeakConvexSphArm A`, `PositiveJoints A`, `StrictConvexSphArm B`, `JointLe A B`, `i + 2 < j < n+1`, and
   `hnd : ∃ a b : ℝ≥0, 0 < a ∧ 0 < b ∧ (a:ℝ)•A(i+1) + (b:ℝ)•A j = A i`, conclude `i = 0`. (Brick 4 at `i ≥ 1`.)
   ONLY the `i = 0` half — the tail half (`j ∈ {n-1,n}`) needs OnFoldRay propagation (master, NOT attempted).
6. `far_fold_i_eq_zero` — wrapper combining 1+3+5; derives `b > 0` from the short fold edge; `a > 0` stays a
   hypothesis (the no_repeat master brick supplying it is out of scope).

## New auxiliary geometric content (the bridge the audit named)

`sphAngle_eq_zero_or_pi_of_det3_zero` — the FORWARD bridge `det3 u v w = 0 ⟹ sphAngle u v w ∈ {0,π}`
(apex = middle vertex), the inverse of FFCT3 `det3_zero_of_sphAngle_pi` / FFCT18 `det3_zero_of_sphAngle_zero`.
Proved by: apex-transport `det3_apex_tangent_eq` (= `-det3 u v w`, one row swap) ⟹ apex area form vanishes
⟹ `collinear_of_det3_zero` (FFCT12) gives `tangentTo v w = c • tangentTo v u` ⟹ sign of `c` selects the
0/π branch via `InnerProductGeometry.angle_eq_zero_iff` / `angle_eq_pi_iff`.

## Faithfulness audit (playbook §3.3)
- Brick 5/6 hypotheses are all raw geometric data; no hard-half hidden in a certificate parameter. The
  `a,b > 0` nondegeneracy is the audit-mandated input, not a smuggled difficulty.
- Non-vacuity guards included (`det3_self_apex_zero`, `nnreal_smul_unit_eq_unit_nonvacuous`); the nondegenerate
  fold datum is the operative (non-vacuous) case the audit identified.
- Brick 4 genuinely consumes PositiveJoints + jointAngle_lt_pi + both supports + a,b>0 — the exact audited mechanism.

OUT OF SCOPE (not attempted, not axiomatized): the tail half (OnFoldRay cone propagation), and the no_repeat
master brick that would supply `a > 0`.
