# Ch13 T6/T7 — Signed-line tail CLOSURE (the unconditional B5)

**File:** `ProofsInTheBook/ZinanFFCT25.lean` (new module, imports `ZinanFFCT24`).
**Status:** compiles with 0 errors, 0 warnings, 0 sorries. Every `#print axioms` is clean-3
(`[propext, Classical.choice, Quot.sound]`). `lake build ProofsInTheBook.ZinanFFCT25` succeeds
(8484 jobs).

## What closed

The Chapter 13 far-fold boundary classification **tail half** is now UNCONDITIONAL. FFCT22 left it
conditional on the `TailConePropagates` hypothesis (the audited "cone re-extraction" master gap);
the signed-line propagation of FFCT24 plus the two named residue discharges below remove it entirely.

All six skeleton bricks landed:

* **U1 `not_antipodal_of_hemisphere`** — the open supporting hemisphere
  (`WeakConvexSphArm.closed_convex.open_hemisphere`, `0 < ⟪h, A i⟫`) excludes antipodal vertex pairs
  `(A r : E3) ≠ -(A s : E3)`. Exactly as designed (`inner_neg_right` + `linarith`).

* **U2 `lin_indep_span_of_det3_zero`** — two UNIT vectors `v, w` with `v ≠ w` and `v ≠ -w` are
  independent, and `det3 v w z = 0` gives `z = c•v + d•w` (real coefficients). Proved via the
  cross-product reciprocal basis: a helper `recip_basis_decomp` establishes
  `‖v×w‖² • z = ⟪z,v×w⟫•(v×w) + (z_v g_ww − z_w g_vw)•v + (z_w g_vv − z_v g_vw)•w`
  (pure `cross_cross` / `cross_antisymm` algebra, closed by `module`), then `⟪z, v×w⟫ = det3 v w z = 0`
  (cyclic + `inner_cross_eq_det3`) drops the normal component and `‖v×w‖² ≠ 0` (Lagrange + the two
  exclusions force `⟪v,w⟫ = ±1` ⟹ `v = ±w`, contradiction) divides out. This is the exact shape
  FFCT24's `hrepr_next` residue and `tail_line_step.repr` consume.

* **U3 `A1_ne_Aj` / `A1_not_antipodal_Aj` / `repr_of_collinear`** — in the far-fold context
  (`3 ≤ j`): `NoNonadjacentRepeat` gives `A 1 ≠ A j` (positions `1, j`, `1 + 2 ≤ j`), U1 gives
  `A 1 ≠ -A j`, and U2 packages the span representation `repr_of_collinear` from a collinearity.

* **U4 `tail_two_step_refutation`** (the T6 core, NO induction) — given the `i = 0` fold
  `A 0 = a•A 1 + b•A j` (`b > 0`) at an interior tail index (`3 ≤ j`, `j + 2 < n + 1`):
  1. `fold_A2_witness_negative` (FFCT24 T1) ⟹ `det3 (A 1)(A j)(A 2) < 0`.
  2. Step 1 (t = j): `tail_step_collinear` (seed `A j = 0•A 1 + 1•A j`) ⟹ `det3 (A 1)(A j)(A (j+1)) = 0`;
     `repr_of_collinear` ⟹ `A (j+1) = c1•A 1 + d1•A j`; T2 ⟹ `0 ≤ d1`; the `d1 = 0` absorption is
     killed by `tail_step_absorb_refuted` (no-repeat at `(1, j+1)` + hemisphere non-antipodal),
     so `0 < d1`.
  3. Step 2 (t = j+1): `far_fold_tail_collinear_step` (with `zt = A (j+1)`, `d1 > 0`) ⟹
     `det3 (A 1)(A j)(A (j+2)) = 0`; `repr_of_collinear` ⟹ `A (j+2)` on the line.
  4. `coplanar_triple_det3_zero` over base `(A 1, A j)` ⟹ `det3 (A j)(A (j+1))(A (j+2)) = 0`.
  5. `far_fold_tail_not_interior` at apex `A (j+1)` (`t = j+1`, `t−1 = j` defeq, `1 ≤ t`,
     `t+1 < n+1`) with the two `edge_short` arcs ⟹ `False`.

* **U5 `far_fold_boundary_classification_unconditional`** (the T7 headline) — from the raw NNReal
  span membership `A i ∈ span≥0 {A (i+1), A j}`, weak convexity, `PositiveJoints`, the non-flat
  bound, and `NoNonadjacentRepeat`: `i = 0 ∧ (j = n ∨ j = n − 1)`, **no `TailConePropagates`**.
  Route: FFCT23's `far_fold_boundary_i_eq_zero_of_span` gives `i = 0`; `far_fold_nondeg_datum_of_no_repeat`
  assembles `a, b > 0`; if `j + 2 < n + 1` (interior), U4 fires `False`; so `j ∈ {n−1, n}` by `omega`.

* **U6 non-vacuity guards** — `not_antipodal_self_nonvacuous` (`v ≠ -v` for units),
  `det3_axes_ne_zero`, `far_fold_final_conclusion_satisfiable`; `NoNonadjacentRepeat` satisfiability
  is cited from FFCT23 (`noNonadjacentRepeat_of_injective` / `_can_fail`), not duplicated.

## Deltas from the skeleton

1. **U2 span extraction was self-contained.** The skeleton flagged that the ℝ-version of
   `det3 = 0 ⟹ mem span` "may already exist." It did not (FFCT22 only ships the converse
   `coplanar_triple_det3_zero`). I built it from the cross-product machinery already in
   `SphericalRotation`/`ZinanFFCT9` (`cross_cross`, `cross_antisymm`, `inner_cross_eq_det3`,
   `norm_cross_sq`) via the reciprocal-basis helper `recip_basis_decomp`. No new substrate touched.

2. **`real_inner_comm` orientation.** Its signature is `real_inner_comm x y : ⟪y, x⟫ = ⟪x, y⟫`
   (first explicit arg appears *second* under the bracket). Minor; noted for future workers.

3. **`far_fold_boundary_i_eq_zero_of_span` argument order** is `hA hposA hnr hB hangle …`
   (`hnr` before `hB`), per FFCT23.

4. **Step 2 used `far_fold_tail_collinear_step` directly** (not the `tail_line_step` def) because at
   `t = j+1` I only need LINE membership of `A (j+2)`, not the strict-`d` upgrade — the design
   anticipated this ("d''≥0 suffices … only LINE membership").

No weakened or vacuous statements. No hypothesis still resists — every FFCT24/FFCT22 residue is
discharged.

## Exact headline statement for the downstream swap

`far_fold_boundary_classification_final` mirrors FFCT22's conditional
`far_fold_boundary_classification` **minus** the `htail : … → TailConePropagates` hypothesis, with
the same `hnd` nondegenerate-coefficient datum, **plus** `hnr : NoNonadjacentRepeat A` (already the
assumption of FFCT23's `i = 0` half, so no new external obligation):

```
theorem far_fold_boundary_classification_final {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hnd : ∃ a b : ℝ≥0, 0 < (a : ℝ) ∧ 0 < (b : ℝ) ∧
      (a : ℝ) • (A ⟨i + 1, by omega⟩ : E3) + (b : ℝ) • (A ⟨j, hj⟩ : E3) = (A ⟨i, by omega⟩ : E3)) :
    i = 0 ∧ (j = n ∨ j = n - 1)
```

The raw-span entry point (recommended for the consumer) is:

```
theorem far_fold_boundary_classification_unconditional {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hposA : PositiveJoints A)
    (hB : StrictConvexSphArm B) (hangle : JointLe A B) (hnr : NoNonadjacentRepeat A)
    {i j : ℕ} (hij : i + 2 < j) (hj : j < n + 1)
    (hcol : (A ⟨i, by omega⟩ : E3) ∈
      Submodule.span NNReal ({(A ⟨i + 1, by omega⟩ : E3), (A ⟨j, hj⟩ : E3)} : Set E3)) :
    i = 0 ∧ (j = n ∨ j = n - 1)
```

Downstream consumers of FFCT22's conditional classification: drop `htail`, supply `hnr`
(or use the raw-span form directly), one-line swap.
