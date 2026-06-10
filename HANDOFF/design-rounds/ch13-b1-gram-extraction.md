[intro]
I’ll pin the exact `mixedSupport`, open-axis, and admissible-supremum names before giving the brick DAG, because the derivative/sign statements depend on argument order.

[answer]
1. **Derivative expansion: exact algebra**

For

```lean
mixedSupport A ij θ =
  det3 (A ij.1 : E3) (A ij.2 : E3)
    (rot (openAxis A : E3) θ (A (Fin.last (n + 1)) : E3))
```

the derivative is

```lean
det3 x y (k × wθ)
```

where

```lean
x := (A ij.1 : E3)
y := (A ij.2 : E3)
k := (openAxis A : E3)
wθ := rot k θ (A (Fin.last (n+1)) : E3)
```

`mixedSupport` is defined exactly this way in `SphericalCore.lean`. fileciteturn110y × (k × w) = ⟪y,w⟫ • k - ⟪y,k⟫ • w`:

```lean
det3 x y (cross k w)
  = (⟪x,k⟫ : ℝ) * (⟪y,w⟫ : ℝ)
    - (⟪x,w⟫ : ℝ) * (⟪y,k⟫ : ℝ)
```

Lean brick:

```lean
theorem mixedSupport_deriv_expansion
    {x y k w : E3} :
    det3 x y (cross k w)
      = (⟪x, k⟫ : ℝ) * (⟪y, w⟫ : ℝ)
        - (⟪x, w⟫ : ℝ) * (⟪y, k⟫ : ℝ)
```

Proof: `rw [← inner_cross_eq_det3, cross_cross]`; simplify inner products; `ring`.

Classification: **worker**, 15–25 lines.

---

2. **Derivative = `-hβ` in the axis-incident edge case**

For the edge pair

```lean
x = A i
y = A (i+1)
k = A (i+1)
w = opened tail
```

the expansion becomes:

```lean
det3 x y (cross y w)
  = ⟪x,y⟫ * ⟪y,w⟫ - ⟪x,w⟫ * ⟪y,y⟫
  = ⟪x,y⟫ * ⟪w,y⟫ - ⟪x,w⟫
  = - (⟪x,w⟫ - ⟪x,y⟫ * ⟪w,y⟫)
```

That parenthesized term is exactly `StuckAtKData.hβ` for `p=x`, `mid=y`, `q=w`:

```lean
0 ≤ ⟪p,q⟫ - ⟪p,mid⟫ * ⟪q,mid⟫
```

So the audit’s `f'(δ*) = -hβ` is literally correct **only when the binding edge’s second vertex is the opening axis**.

Lean brick:

```lean
theorem mixedSupport_deriv_axis_edge_eq_neg_hbeta
    {x y w : S2} :
    det3 (x : E3) (y : E3) (cross (y : E3) (w : E3))
      =
    - ((⟪(x : E3), (w : E3)⟫ : ℝ)
       - (⟪(x : E3), (y : E3)⟫ : ℝ)
         * (⟪(w : E3), (y : E3)⟫ : ℝ))
```

Classification: **worker**, 15–20 lines.

---

3. **Derivative sign: avoid fragile one-sided Mathlib API**

Admissibility gives:

```lean
∀ θ ∈ Set.Icc 0 δ, 0 ≤ f θ
f δ = 0
```

Hence `δ` is a minimum on `[0,δ]`, so the left derivative satisfies `f' ≤ 0`.

I recommend proving a local custom lemma instead of depending on Mathlib’s one-sided extremum API:

```lean
theorem deriv_nonpos_of_left_nonneg_zero
    {f : ℝ → ℝ} {δ f' : ℝ}
    (hδ : 0 < δ)
    (hderiv : HasDerivAt f f' δ)
    (hleft : ∀ θ, θ ∈ Set.Icc 0 δ → 0 ≤ f θ)
    (hzero : f δ = 0) :
    f' ≤ 0
```

Proof sketch: for `ε > 0` small, `δ - ε ∈ [0,δ]`, so

```lean
0 ≤ f (δ - ε)
```

and

```lean
(f (δ - ε) - f δ) / (-ε) ≤ 0.
```

Let `ε → 0+` using `hderiv`. This is 60–100 lines but fully controlled.

Classification: **needs-care**, preferable to searching for `IsMinOn.hasDerivWithinAt_nonpos`.

---

4. **Derivative of `mixedSupport`**

Use the explicit Rodrigues derivative, not general Frechet calculus.

New brick:

```lean
theorem deriv_rot
    {k v : E3} (hk : ‖k‖ = 1) (θ : ℝ) :
    HasDerivAt (fun t : ℝ => rot k t v)
      (cross k (rot k θ v)) θ
```

Proof: unfold `rot`; differentiate `cos`, `sin`; use `cross_cross` and the identity

```lean
d/dθ rot k θ v = k × rot k θ v.
```

Then:

```lean
theorem hasDerivAt_mixedSupport
    {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (ij : Fin (n + 1 + 1) × Fin (n + 1 + 1)) (θ : ℝ) :
    HasDerivAt (mixedSupport A ij)
      (det3 (A ij.1 : E3) (A ij.2 : E3)
        (cross (openAxis A : E3)
          (rot (openAxis A : E3) θ (A (Fin.last (n + 1)) : E3)))) θ
```

Classification: **master/needs-care**, 120–180 lines.

---

5. **`hβ` extraction for an axis-incident edge**

```lean
theorem hbeta_of_axis_edge_binding
    {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    {i : ℕ} {δ : ℝ}
    (hi_axis : i + 1 = n)
    (hδpos : 0 < δ)
    (hadm : ∀ θ, θ ∈ Set.Icc 0 δ →
      0 ≤ mixedSupport A
        (⟨i, by omega⟩, ⟨i + 1, by omega⟩) θ)
    (hzero :
      mixedSupport A
        (⟨i, by omega⟩, ⟨i + 1, by omega⟩) δ = 0) :
    0 ≤
      (⟪(A ⟨i, by omega⟩ : E3),
          (rot (openAxis A : E3) δ
            (A (Fin.last (n + 1)) : E3))⟫ : ℝ)
      -
      (⟪(A ⟨i, by omega⟩ : E3), (A ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
      *
      (⟪(rot (openAxis A : E3) δ
            (A (Fin.last (n + 1)) : E3)),
          (A ⟨i + 1, by omega⟩ : E3)⟫ : ℝ)
```

Proof: derivative nonpositive by Section 3; derivative equals `-hβ` by Section 2; conclude `hβ ≥ 0`.

Classification: **master**, 80–130 lines after derivative bricks.

---

6. **Companion sign `hα`: not from the same derivative**

`hα` is

```lean
0 ≤ ⟪p,mid⟫ - ⟪p,q⟫ * ⟪mid,q⟫.
```

For `p=A i`, `mid=A(i+1)=axis`, `q=opened tail`, this is not the derivative of the same `mixedSupport`. The derivative gives only `hβ`.

Recommended companion mechanism:

```lean
theorem halpha_of_hbeta_and_positive_axis_joint
    {p mid q : S2}
    (hcol : det3 (p : E3) (mid : E3) (q : E3) = 0)
    (hsa : ShortArc mid q)
    (hpm : ShortArc mid p)
    (hbeta :
      0 ≤ (⟪(p:E3),(q:E3)⟫ : ℝ)
        - (⟪(p:E3),(mid:E3)⟫ : ℝ)
          * (⟪(q:E3),(mid:E3)⟫ : ℝ))
    (hjoint_pos : 0 < sphAngle p mid q) :
    0 ≤ (⟪(p:E3),(mid:E3)⟫ : ℝ)
      - (⟪(p:E3),(q:E3)⟫ : ℝ)
        * (⟪(mid:E3),(q:E3)⟫ : ℝ)
```

Sketch: by collinearity, write `p = a•mid + b•q`. `hbeta ≥ 0` gives `b ≥ 0`. If `a < 0`, then `p` lies beyond `q` on the same ray from `mid`, so `sphAngle p mid q = 0`, contradicting `hjoint_pos`; if `a=0`, then `p=q`, contradicting shortness. Thus `a ≥ 0`, hence `hα ≥ 0`.

Classification: **genuinely-hard algebra**, 180–260 lines.

---

7. **Normalization of the binding witness**

`mixedSupport` ranges over arbitrary fixed pairs:

```lean
ij : Fin (n+1+1) × Fin (n+1+1)
```

not only consecutive edges. fileciteturn110file0L119-L127_normalizes_to_axis_edge
    {n : ℕ} {A : Fin (n + 1 + 1) → S2} {δ : ℝ}
    (hAδweak : WeakConvexSphArm (openArm A δ))
    (hAδpos : PositiveJoints (openArm A δ))
    (hfirst :
      FirstBindingMixedSupport A δ ij)
    (hzero : mixedSupport A ij δ = 0) :
    ∃ i : ℕ,
      i + 1 = n ∧
      mixedSupport A (⟨i, by omega⟩, ⟨i + 1, by omega⟩) δ = 0
```

Sketch: this is the real normalization brick. If a non-edge diagonal pair binds first, use weak edge supports and positive joints to show some consecutive edge on the chain to the axis must also bind; otherwise the diagonal zero would force a flat/zero joint or a support-sign contradiction. This is where the “genuine edge-support triple” audit note lives.

Classification: **master**, 250–400 lines.

---

8. **ShortArc for the stuck pair**

`StuckAtKData` requires:

```lean
hsa : ShortArc (A (i+1)) (A j)
```

For axis-incident last-corner, this is the opened last side, preserved by rotation from the original short edge.

```lean
theorem shortArc_axis_opened_tail
    {n : ℕ} {A : Fin (n + 1 + 1) → S2} (θ : ℝ) :
    ShortArc (openArm A θ ⟨n, by omega⟩)
      (openArm A θ (Fin.last (n + 1)))
```

Hypothesis needed:

```lean
hA : WeakConvexSphArm A
```

Sketch: rewrite axis fixed and tail rotated; use `sDist_axis_openLast` / rotation nondegeneracy, or preserve `ShortArc` under `rotS2`. Original last edge is short from `hA.closed_convex.edge_short`. `openArm_sideLen` already preserves lengths. fileciteturn110file0 axis-edge `StuckAtKData`**

```lean
theorem StuckAtKData_of_axis_edge_binding
    {n : ℕ} {A B : Fin (n + 1 + 1) → S2} {δ : ℝ}
    (hA : WeakConvexSphArm A)
    (hAδpos : PositiveJoints (openArm A δ))
    (hB : StrictConvexSphArm B)
    (hside : SameSides (openArm A δ) B)
    (i : ℕ) (hi_axis : i + 1 = n)
    (hsupp :
      mixedSupport A (⟨i, by omega⟩, ⟨i + 1, by omega⟩) δ = 0)
    (hbeta : ...)
    (halpha : ...) :
    StuckAtKData (N := n + 1) (openArm A δ) B i (n + 1)
```

Sketch: `hij1` and `hj` are `omega`; `hsupp` is exactly the mixed support rewritten through `openArm_fixed` / `openArm_last`; `hsa` from Section 8; `hside` from `SameSides` at the edge `i+1`; `halpha/hbeta` from Sections 5–6.

Classification: **needs-care wrapper**, 80–120 lines.

---

10. **Hemi-margin branch**

`augmented_reachOrStuck_at_sup` has a third branch:

```lean
hemiMargin A h δ* = 0
```

This is not a `StuckAtKData` branch. It must be dispatched separately.

Recommended brick:

```lean
theorem hemiMargin_zero_impossible_of_PositiveJoints
    {n : ℕ} {A B : Fin (n + 1 + 1) → S2} {δ : ℝ} {h : E3}
    (hAδweak : WeakConvexSphArm (openArm A δ))
    (hAδpos : PositiveJoints (openArm A δ))
    (hhem : hemiMargin A h δ = 0) :
    False
```

Sketch: if the open hemisphere margin is zero, some vertex lies on the boundary of the old hemisphere. For the last-joint opening, only the rotated tail can hit the boundary; combine with open hemisphere of the weak arm at δ, or show this branch contradicts the strict `open_hemisphere` field required in `WeakConvexSphArm`. If the branch is produced before constructing `WeakConvexSphArm (openArm A δ)`, then this is exactly the missing hemisphere-persistence brick.

Classification: **master**, unless already handled in `augmented_reachOrStuck_at_sup`.

---

11. **Degenerate cases**

1. **`δ* = 0`.**  
   If `mixedSupport A edge 0 = 0`, strict initial arm should contradict strict convexity or `PositiveJoints` unless the edge is incident/repeated. Add:
   ```lean
   theorem no_initial_axis_edge_binding
     (hA : StrictConvexSphArm A) :
     mixedSupport A (⟨i,_⟩,⟨i+1,_⟩) 0 ≠ 0
   ```
   Classification: worker/needs-care.

2. **Opened tail equals `A i` or `A(i+1)`.**  
   Killed by `ShortArc` / side preservation. Use `shortArc_axis_opened_tail` and no-repeat/positive-joint for predecessor equality.

3. **Opened tail antipodal to axis or predecessor.**  
   Killed by open hemisphere or `ShortArc`. FFCT18 has `weakConvex_no_antipodal`. fileciteturn92file0L160-L171

4. **Binding pair not an edge.**  
   Handled only by Section 7 normalization; do not try to manufacture Gram signs directly from arbitrary pair derivative.

---

12. **Recommended B1 DAG**

1. `mixedSupport_deriv_expansion` — worker, 20 lines.  
2. `deriv_rot` + `hasDerivAt_mixedSupport` — master/needs-care, 150 lines.  
3. `deriv_nonpos_of_left_nonneg_zero` — needs-care, 80 lines.  
4. `mixedSupport_deriv_axis_edge_eq_neg_hbeta` — worker, 20 lines.  
5. `hbeta_of_axis_edge_binding` — master, 100 lines.  
6. `halpha_of_hbeta_and_positive_axis_joint` — master, 200 lines.  
7. `binding_pair_normalizes_to_axis_edge` — master, 300 lines.  
8. `shortArc_axis_opened_tail` — worker, 60 lines.  
9. `StuckAtKData_of_axis_edge_binding` — needs-care, 100 lines.  
10. `hemiMargin_zero_impossible_or_persist` — master, 150–250 lines.  

Total B1 realistic size: **700–1100 lines**, with the true risk concentrated in normalization and `hα`.
