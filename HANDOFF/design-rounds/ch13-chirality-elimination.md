[intro]
I’ll pin the exact FFCT55 chirality result and the FFCT52 reverse-arm API first, then I’ll separate the algebraic coefficient flip from the actual cut transport.

[answer]
1. **Inventory / sign correction**

For the **axis-edge WBS binding**, FFCT55 explicitly records the sign flip:

```lean
g'(δ*) = +hβ_form
g ≥ 0 on [0,δ*], g δ* = 0
⇒ hβ_form ≤ 0
```

This is the opposite of the legacy `StuckAtKData` / `WBSBetaSign` direction. FFCT55 states this as `wbsAxisEdge_hbeta_le_zero`, and the header emphasizes that the `-θ` chain-rule minus and the axis-slot contraction minus multiply to `+1`. fileciteturn158file FFCT55 text I read documents this for the **axis-edge** single-rotation branch; it says the general non-axis mixed binding remains a separate residual. fileciteturn158file0L plug it into the same bricks below.

---

2. **Coefficient rearrangement is correct**

Given

```lean
(P i : E3) = a • (P (i+1) : E3) + b • (P j : E3)
```

with `b < 0` and a strict open hemisphere for all vertices, then `a > 0`.

Reason: if `a ≤ 0`, then taking inner product with the hemisphere normal `h` gives

```lean
⟪h, P i⟫ = a ⟪h, P(i+1)⟫ + b ⟪h, P j⟫ < 0,
```

contradicting `0 < ⟪h, P i⟫`.

Then rearrange:

```lean
(P (i+1) : E3)
  = (1 / a) • (P i : E3) + ((-b) / a) • (P j : E3)
```

and both coefficients are strictly positive. Thus the **between vertex is `P(i+1)`**, not `P i`.

---

3. **Brick C1: algebraic rearrangement**

```lean
theorem midFold_coeffs_of_bneg
    {n : ℕ} {P : Fin (n + 1) → S2} {i j : ℕ}
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (P r : E3)⟫ : ℝ))
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1)
    {a b : ℝ}
    (hp : (P ⟨i, hi⟩ : E3)
        = a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨j, hj⟩ : E3))
    (hb : b < 0) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
      (P ⟨i + 1, hi1⟩ : E3)
        = c • (P ⟨i, hi⟩ : E3) + d • (P ⟨j, hj⟩ : E3)
```

Sketch: prove `0 < a` by the hemisphere inner-product argument; set `c = 1/a`, `d = -b/a`; `field_simp`; `nlinarith`.

Classification: **worker**, 40–70 lines.

---

4. **Brick C2: `b = 0` degeneration**

```lean
theorem bcoef_ne_zero_of_short_edge
    {p mid q : S2} {a b : ℝ}
    (hpm : ShortArc p mid)
    (hp : (p : E3) = a • (mid : E3) + b • (q : E3))
    (hb0 : b = 0) :
    False
```

Sketch: with `b=0`, `p = a • mid`. Taking norms gives `a = 1 ∨ a = -1`; hence `p = mid` or `p = -mid`, both excluded by `ShortArc p mid`.

Classification: **worker**, 50–80 lines.

---

5. **Main geometric point: mid-fold is locally impossible**

Once `P(i+1)` is in the positive span of `{P i, P j}`, the successor edge `(P(i+1), P(i+2))` kills it.

Let

```lean
M = P(i+1),  P0 = P i,  Q = P j,  R = P(i+2),
M = c P0 + d Q,  c,d > 0.
```

Weak supports of edge `(M,R)` at `P0` and `Q` give

```lean
0 ≤ det3 M R P0 = d * det3 Q R P0
0 ≤ det3 M R Q  = c * det3 P0 R Q
```

and these are opposite multiples of `D = det3 P0 Q R`, so `D = 0`. Then

```lean
det3 P0 M R = d * D = 0,
```

so the adjacent joint at apex `M = P(i+1)` is `0` or `π`, contradicting `PositiveJoints` plus `jointAngle_lt_pi`.

---

6. **Brick C3: local mid-fold contradiction**

```lean
theorem midFold_interior_contradiction
    {n : ℕ} {P B : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P)
    (hpos : PositiveJoints P)
    (hB : StrictConvexSphArm B)
    (hangle : JointLe P B)
    {i j : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hi2 : i + 2 < n + 1)
    (hj : j < n + 1)
    (hpm : ShortArc (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩))
    (hmr : ShortArc (P ⟨i + 1, hi1⟩) (P ⟨i + 2, hi2⟩))
    (hmid : ∃ c d : ℝ, 0 < c ∧ 0 < d ∧
      (P ⟨i + 1, hi1⟩ : E3)
        = c • (P ⟨i, hi⟩ : E3) + d • (P ⟨j, hj⟩ : E3)) :
    False
```

Sketch: expand as in §5. Use `hP.closed_convex.edge_support ⟨i+1⟩ ⟨i⟩` and `... ⟨j⟩`. Then apply `sphAngle_eq_zero_or_pi_of_det3_zero` from FFCT21 to the adjacent triple `(P i, P(i+1), P(i+2))`; `hpos ⟨i⟩` kills `0`, and `jointAngle_lt_pi hB hangle ⟨i⟩` kills `π`. FFCT21’s flat-angle bridge is documented as the converse of the zero/π determinant facts. fileciteturn106file0-edge WBS support-stuck is impossible**

For the axis-edge branch, `i+1 = openingAxis k`. Since `k : Fin (n-1)`, the axis is interior, so `i+2 < n+1`. Therefore C3 applies.

```lean
theorem wbs_axisEdge_supportStuck_false
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B)
    {k : Fin (n - 1)}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hangle' : JointLe (openedWBS A B k) B)
    {i j : ℕ}
    (hi_axis : i + 1 = (openingAxis k).val)
    (hj : j < n + 1)
    (hspan : ∃ a b : ℝ,
      (openedWBS A B k ⟨i, by omega⟩ : E3)
        = a • (openedWBS A B k ⟨i + 1, by omega⟩ : E3)
          + b • (openedWBS A B k ⟨j, hj⟩ : E3) ∧ b < 0)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ)) :
    False
```

Sketch: use `midFold_coeffs_of_bneg`; edge shorts come from `hA'weak.closed_convex.edge_short`; call `midFold_interior_contradiction`.

Classification: **needs-care**, 80–140 lines.

---

8. **This is not a new `MidFoldCutTransport`**

The mid-fold chirality does **not** need a transport theorem in the interior case. It is incompatible with weak convexity + positive/nonflat joints before any endpoint comparison is needed.

So the correct replacement for the old `StuckAtKData` route is not:

```lean
MidFoldCutTransport : ... → endpt A ≤ endpt B
```

but rather:

```lean
MidFoldInteriorImpossible : ... → False
```

For WBS support-stuck, this means the axis-edge branch is eliminated, not transported.

---

9. **What about the reverse-arm classification idea?**

The rearranged datum is

```lean
A(i+1) ∈ span≥0 {A i, A j}
```

This is a **predecessor-shaped** fold. FFCT25’s classification expects a **successor-shaped** fold:

```lean
A m ∈ span≥0 {A(m+1), A far}.
```

Applying `revArm` sends `A(i+1)` to the reversed index `n-i-1`, whose successor is `A i`, but the far vertex `A j` becomes index `n-j`, which lies **behind** because `j > i+1`. So the reversed datum is still a backward-orientation case, not directly an FFCT25 forward case.

FFCT52’s reversal suite is useful for raw orientation normalization generally: it defines `revArm`, proves `sOrient_revArm_normalized`, and records `revArm_sideLen` / `revArm_jointAngle`. fileciteturn and stronger.

---

10. **Boundary cases**

The local contradiction requires `i+2 < n+1`, i.e. the middle vertex `i+1` is an interior joint apex.

If `i+1 = n`, the joint is at the endpoint and `PositiveJoints` does not apply. That is a genuine boundary case:

```lean
def MidFoldLastBoundaryCase : Prop :=
  ∀ n A B, ... →
    (opened vertex A n ∈ span≥0 {A(n-1), A j}) →
    endpt A ≤ endpt B
```

But for the WBS **axis-edge** branch, `i+1 = openingAxis k`, and `openingAxis k` is interior by construction; so `MidFoldLastBoundaryCase` is not reached there.

---

11. **General non-axis mixed bindings**

Do not overuse FFCT55. The fetched FFCT55 says the single-rotation derivative sign finding is axis-edge, and the non-axis mixed binding uses the full `det3_cross_expansion`, not the Gram `hβ` form. fileciteturn158file0:

```lean
theorem wbs_supportStuck_dispatch_chiral
    ... :
    AxisEdgeBinding ... ∨ NonAxisMixedBinding ...
```

Axis-edge: impossible by C7.  
Non-axis: either prove a separate sign theorem reducing it to mid-fold, or leave the existing non-axis sign residual.

Classification: **master**, 150–250 lines for dispatch, more if proving non-axis sign.

---

12. **Ordered bricks**

1. `bcoef_ne_zero_of_short_edge` — worker, 50–80 lines.  
2. `bcoef_neg_of_wbs_axisEdge_derivative` — needs-care, 80–130 lines; uses FFCT55 `wbsAxisEdge_hbeta_le_zero` and coefficient algebra.  
3. `midFold_coeffs_of_bneg` — worker, 40–70 lines.  
4. `midFold_interior_contradiction` — master/needs-care, 120–200 lines.  
5. `wbs_axisEdge_supportStuck_false` — needs-care, 80–140 lines.  
6. `wbs_supportStuck_dispatch_chiral` — master, 150–250 lines.  
7. Optional boundary: `MidFoldLastBoundaryCase` — master, 200–350 lines, but not needed for axis-edge WBS.  
8. Optional non-axis: `nonAxisMixedBinding_to_midFold_or_residue` — master, 300+ lines.

---

13. **Degenerate audit**

`δ* = 0`: already killed by FFCT55’s `wbsBinding_delta_zero_false`. fileciteturn158-fixed/all-rotated binding: killed by `wbsConstantBinding_false_allFixed` / `wbsConstantBinding_false_allRotated`. fileciteturn158file0L16-L20ShortArc` between `A i` and `A(i+1)`.

`a ≤ 0`: killed by the strict hemisphere of the opened arm once `b < 0`.

`j = i` or `j = i+1`: excluded by `NonIncident`.

`j = i+2`: included in `midFold_interior_contradiction`; the adjacent triple itself becomes flat.

`i+1 = n`: only remaining boundary version; not reachable when `i+1 = openingAxis k`.

---

14. **Final design shift**

Do not try to force WBS stuck events into `StuckAtKData`. The chirality is opposite. For the WBS widening family, the support-stuck path should be:

```text
support-stuck
→ slot/orientation normalization
→ if axis-edge: derivative gives b<0
→ rearrange to mid-fold
→ local weak-support contradiction
```

Only non-axis mixed bindings remain as a separate sign-normalization problem.
