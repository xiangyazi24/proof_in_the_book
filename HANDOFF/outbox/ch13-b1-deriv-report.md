# Ch13 B1 Gram-extraction — derivative-algebra layer (worker report)

**File:** `ProofsInTheBook/ZinanFFCT26.lean` (314 lines, 0 errors, clean-3).
**Verified on:** uisai2, `lake env lean ProofsInTheBook/ZinanFFCT26.lean` → no output (success);
olean built (`lake build ProofsInTheBook.ZinanFFCT26` ✔).
**Axioms (per main result, `#print axioms`):** all six → `[propext, Classical.choice, Quot.sound]`.
No `sorry`/`admit`/`axiom`/`native_decide`.

## Bricks delivered (all of WORKER/needs-care scope 1,2,3,4,8)

| Brick | Name | Status |
|---|---|---|
| 1 | `det3_cross_expansion` | landed — `det3 x y (k×w) = ⟪x,k⟫⟪y,w⟫ − ⟪x,w⟫⟪y,k⟫`, via `inner_cross_eq_det3` + `cross_cross` (Binet–Cauchy) |
| 4 | `det3_axis_cross_eq_neg_gram` (+ `_S2` form) | landed — `det3 x y (y×w) = −(⟪x,w⟫ − ⟪x,y⟫⟪w,y⟫)` for unit `y`; the literal `-hβ` |
| 2a | `hasDerivAt_rot` | **landed in the strong cross form** — `HasDerivAt (fun t => rot k t v) (cross k (rot k θ v)) θ`. The explicit-formula fallback was NOT needed; the collapse to `cross k (rot k θ v)` went through cleanly via `cross_cross` (`k×(k×v)=⟪k,v⟫•k−v` for unit `k`) + `cross_self` (`k×k=0`) + `module`. |
| 2b | `hasDerivAt_mixedSupport` (+ helper `hasDerivAt_det3_third`) | landed — composes 2a with the third-slot-linear `z ↦ det3 x y z`, differentiated coordinatewise (mirroring `continuous_mixedSupport`); matches the design's exact derivative value `det3 (A ij.1)(A ij.2)(openAxis × rot tail)` |
| 3 | `deriv_nonpos_of_left_nonneg_zero` | landed — self-contained difference-quotient/filter argument (`hasDerivWithinAt_iff_tendsto_slope` on `Set.Iio δ`, slope eventually `≤ 0` on `Ioo 0 δ`, `le_of_tendsto`). No fragile one-sided Mathlib extremum API used. |
| 8 | `shortArc_axis_opened_tail` (+ `rot_injective`, `rot_neg`, `shortArc_rotS2`) | landed against the real `openArm`/`openAxis` vocabulary — uses `openArm_fixed`/`openArm_last`, axis fixity `rot_axis`, and `rotS2`-preservation of `ShortArc` (both `≠` and `≠ −` conjuncts via injectivity of `rot`). |

Supporting lemmas also exported: `hasDerivAt_det3_third`, `rot_injective`, `rot_neg`,
`shortArc_rotS2`, `det3_axis_cross_eq_neg_gram_S2`.

## Non-vacuity guards
- Brick 3: `example (δ) (0<δ) : (-1:ℝ) ≤ 0` obtained by **actually applying**
  `deriv_nonpos_of_left_nonneg_zero` to `f := fun θ => δ − θ` (deriv `−1`, `≥0` on `[0,δ]`,
  `f δ = 0`) — confirms hypotheses are jointly satisfiable and the lemma fires.
- Brick 1: `det3 e0 e1 (e0 × e1) = 1` computed kernel-style (expansion + `inner_eq_coord` + `simp`),
  no `decide`/`native_decide`.

## Notes for the master assembly (bricks 5/6/7/9/10)
- Brick 5 (`hbeta_of_axis_edge_binding`) now has both inputs ready: derivative value from
  `hasDerivAt_mixedSupport`, its `-hβ` identity from `det3_axis_cross_eq_neg_gram`, and the sign from
  `deriv_nonpos_of_left_nonneg_zero`. The axis-edge case requires `A ij.2 = openAxis A` so that the
  third-slot cross axis `k = openAxis A` coincides with `y = A ij.2` (then brick 4 applies). The
  evaluation point is `θ = δ*` with `wθ = rot (openAxis A) δ* (A (Fin.last (n+1)))`.
- Brick 8 is stated for the original short edge `ShortArc (A ⟨n,_⟩) (A (Fin.last (n+1)))` as the
  hypothesis `hshort`; in the assembly this comes from `WeakConvexSphArm`/`closed_convex.edge_short`
  at the last edge index. `openArm_fixed`/`openArm_last` are the rewrite bridges.

## Key dependency facts mined (for reference)
- `rot k θ v = cos θ•v + sin θ•(k×v) + ((1−cos θ)⟪k,v⟫)•k` (`SphericalRotation.rot_apply`).
- Third-slot det3 linearity is **already landed**: `det3_add_right`, `det3_smul_right`
  (`ZinanFFCT10`). `det3 x y z = ⟪x, y×z⟫` (`inner_cross_eq_det3`).
- `ShortArc p q := p ≠ q ∧ (p:E3) ≠ −(q:E3)` (`SphericalKernel`). `rotS2` is an isometry
  (`sDist_rotS2`); `rot` injective via `norm_rot`.
