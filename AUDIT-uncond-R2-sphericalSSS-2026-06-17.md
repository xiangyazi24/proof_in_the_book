Yes. The clean base-case proof is **spherical SSS**:

```lean
equal three cyclic side lengths
  ⇒ equal three spherical angles
  ⇒ ∀ i, linkDiff A B i = 0
  ⇒ nzSigns (linkDiff A B) = []
  ⇒ signChangesFull A B = 0
  ⇒ signChangesFull A B ≠ 2
```

Your repo already has the right kernel facts: `sDist` is `arccos` of the spherical inner product, `sphAngle` is the Mathlib angle between tangent projections, `ShortArc.sin_sDist_pos` gives the nonzero sine denominators, and `spherical_cosine_rule` is already proved in `SphericalKernel`. The full-link sign count is also already exactly `cyclicFlips (nzSigns (linkDiff A B))` in `Ch13ArmVertexFull`.

## 1. The math route is the right one

For unit vectors `u v w : S2`, with angle at `v`,

```lean
γ = sphAngle u v w
```

the spherical law of cosines gives:

```lean
Real.cos (sDist u w)
  =
Real.cos (sDist u v) * Real.cos (sDist v w)
  + Real.sin (sDist u v) * Real.sin (sDist v w) * Real.cos γ
```

So, if the two adjacent sides are short, hence their sines are positive,

```lean
Real.cos γ
  =
(Real.cos (sDist u w)
  - Real.cos (sDist u v) * Real.cos (sDist v w))
/
(Real.sin (sDist u v) * Real.sin (sDist v w)).
```

Thus `γ` is determined by the three side lengths. Since `sphAngle` lies in `[0, π]`, equality of `cos γ` gives equality of `γ`.

This is the cleanest route. It is also preferable to proving a general spherical congruence theorem, because your repo already has the law of cosines and the angle-range lemmas.

## 2. Key identity to add

Put this near `spherical_cosine_rule` in `SphericalKernel.lean`.

First, the side-distance version:

```lean
theorem cos_sphAngle_eq_of_short
    {u v w : S2}
    (huv : ShortArc u v)
    (hvw : ShortArc v w) :
    Real.cos (sphAngle u v w)
      =
    (Real.cos (sDist u w)
      - Real.cos (sDist u v) * Real.cos (sDist v w))
      /
    (Real.sin (sDist u v) * Real.sin (sDist v w)) := by
  have hcos := spherical_cosine_rule u v w
  have hsin_uv : 0 < Real.sin (sDist u v) := huv.sin_sDist_pos
  have hsin_vw : 0 < Real.sin (sDist v w) := hvw.sin_sDist_pos
  have hden_pos :
      0 < Real.sin (sDist u v) * Real.sin (sDist v w) :=
    mul_pos hsin_uv hsin_vw
  have hden_ne :
      Real.sin (sDist u v) * Real.sin (sDist v w) ≠ 0 :=
    ne_of_gt hden_pos

  -- From the cosine rule:
  --   cos uw = cos uv * cos vw + den * cos γ
  -- solve for `cos γ`.
  field_simp [hden_ne]
  nlinarith [hcos]
```

Then optionally add the pure inner-product version, which is exactly the identity you asked for:

```lean
theorem cos_sphAngle_eq_inner_of_short
    {u v w : S2}
    (huv : ShortArc u v)
    (hvw : ShortArc v w) :
    Real.cos (sphAngle u v w)
      =
    (sInner u w - sInner u v * sInner v w)
      /
    (Real.sin (sDist u v) * Real.sin (sDist v w)) := by
  rw [← cos_sDist u w, ← cos_sDist u v, ← cos_sDist v w]
  exact cos_sphAngle_eq_of_short huv hvw
```

This is equivalent to the tangent-projection identity

```lean
⟪tangentTo v u, tangentTo v w⟫
  = sInner u w - sInner u v * sInner v w
```

because

```lean
‖tangentTo v u‖ = sin (sDist u v)
‖tangentTo v w‖ = sin (sDist v w)
```

and `sphAngle u v w` is the angle between those two tangent vectors.

If you want that as a separate lemma:

```lean
theorem inner_tangentTo_tangentTo
    (u v w : S2) :
    (⟪tangentTo v u, tangentTo v w⟫ : ℝ)
      = sInner u w - sInner u v * sInner v w := by
  rw [tangentTo_eq, tangentTo_eq]
  simp only [
    inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right,
    S2.inner_self
  ]
  rw [sInner_comm w v]
  ring
```

That one is often useful because it avoids touching `spherical_cosine_rule` at all.

## 3. SSS lemma: angle determined by three sides

Add this next:

```lean
theorem angle_eq_of_cos_eq_on_Icc
    {α β : ℝ}
    (hα0 : 0 ≤ α) (hαπ : α ≤ Real.pi)
    (hβ0 : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (hcos : Real.cos α = Real.cos β) :
    α = β := by
  apply le_antisymm
  · by_contra hle
    have hlt : β < α := lt_of_not_ge hle
    have hcos_lt : Real.cos α < Real.cos β :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hβ0 hαπ hlt
    linarith
  · by_contra hle
    have hlt : α < β := lt_of_not_ge hle
    have hcos_lt : Real.cos β < Real.cos α :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hα0 hβπ hlt
    linarith
```

Then the actual spherical SSS angle lemma:

```lean
theorem sphAngle_eq_of_three_sDist_eq
    {u v w u' v' w' : S2}
    (huv  : ShortArc u v)
    (hvw  : ShortArc v w)
    (huv' : ShortArc u' v')
    (hvw' : ShortArc v' w')
    (h_uv : sDist u v = sDist u' v')
    (h_vw : sDist v w = sDist v' w')
    (h_uw : sDist u w = sDist u' w') :
    sphAngle u v w = sphAngle u' v' w' := by
  have hcosA := cos_sphAngle_eq_of_short huv hvw
  have hcosB := cos_sphAngle_eq_of_short huv' hvw'

  -- Rewrite B's formula to A's three side lengths.
  have hcosB' :
      Real.cos (sphAngle u' v' w')
        =
      (Real.cos (sDist u w)
        - Real.cos (sDist u v) * Real.cos (sDist v w))
        /
      (Real.sin (sDist u v) * Real.sin (sDist v w)) := by
    rw [hcosB]
    rw [← h_uv, ← h_vw, ← h_uw]

  have hcos :
      Real.cos (sphAngle u v w)
        =
      Real.cos (sphAngle u' v' w') := by
    rw [hcosA, hcosB']

  exact angle_eq_of_cos_eq_on_Icc
    (sphAngle_nonneg u v w)
    (sphAngle_le_pi u v w)
    (sphAngle_nonneg u' v' w')
    (sphAngle_le_pi u' v' w')
    hcos
```

This is the central lemma. Everything after this is bookkeeping.

## 4. Triangle-link angle equality

For the triangle case, avoid clever `Fin 3` algebra. Just do `fin_cases i`.

You need the cyclic edge-short facts from strict convexity:

```lean
theorem arm_edge_short {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A)
    (i : Fin (n + 1)) :
    ShortArc (A i) (A (i + 1)) :=
  hA.closed_convex.edge_short i
```

Then prove:

```lean
theorem linkAngle_eq_of_three_sides_triangle
    (A B : Fin 3 → S2)
    (hA : StrictConvexSphArm (n := 2) A)
    (hB : StrictConvexSphArm (n := 2) B)
    (hsides :
      ∀ i : Fin 3,
        sDist (A i) (A (i + 1))
          =
        sDist (B i) (B (i + 1))) :
    ∀ i : Fin 3,
      linkAngle A i = linkAngle B i := by
  intro i
  fin_cases i

  · -- i = 0, angle at vertex 0: sphAngle (A 2) (A 0) (A 1)
    unfold linkAngle
    simp
    refine sphAngle_eq_of_three_sDist_eq
      (u := A 2) (v := A 0) (w := A 1)
      (u' := B 2) (v' := B 0) (w' := B 1)
      ?huv ?hvw ?huv' ?hvw' ?h_uv ?h_vw ?h_uw
    · simpa using arm_edge_short (n := 2) hA (2 : Fin 3)
    · simpa using arm_edge_short (n := 2) hA (0 : Fin 3)
    · simpa using arm_edge_short (n := 2) hB (2 : Fin 3)
    · simpa using arm_edge_short (n := 2) hB (0 : Fin 3)
    · simpa using hsides (2 : Fin 3)
    · simpa using hsides (0 : Fin 3)
    · calc
        sDist (A 2) (A 1)
            = sDist (A 1) (A 2) := sDist_comm _ _
        _   = sDist (B 1) (B 2) := hsides (1 : Fin 3)
        _   = sDist (B 2) (B 1) := (sDist_comm _ _).symm

  · -- i = 1, angle at vertex 1: sphAngle (A 0) (A 1) (A 2)
    unfold linkAngle
    simp
    refine sphAngle_eq_of_three_sDist_eq
      (u := A 0) (v := A 1) (w := A 2)
      (u' := B 0) (v' := B 1) (w' := B 2)
      ?huv ?hvw ?huv' ?hvw' ?h_uv ?h_vw ?h_uw
    · simpa using arm_edge_short (n := 2) hA (0 : Fin 3)
    · simpa using arm_edge_short (n := 2) hA (1 : Fin 3)
    · simpa using arm_edge_short (n := 2) hB (0 : Fin 3)
    · simpa using arm_edge_short (n := 2) hB (1 : Fin 3)
    · simpa using hsides (0 : Fin 3)
    · simpa using hsides (1 : Fin 3)
    · calc
        sDist (A 0) (A 2)
            = sDist (A 2) (A 0) := sDist_comm _ _
        _   = sDist (B 2) (B 0) := hsides (2 : Fin 3)
        _   = sDist (B 0) (B 2) := (sDist_comm _ _).symm

  · -- i = 2, angle at vertex 2: sphAngle (A 1) (A 2) (A 0)
    unfold linkAngle
    simp
    refine sphAngle_eq_of_three_sDist_eq
      (u := A 1) (v := A 2) (w := A 0)
      (u' := B 1) (v' := B 2) (w' := B 0)
      ?huv ?hvw ?huv' ?hvw' ?h_uv ?h_vw ?h_uw
    · simpa using arm_edge_short (n := 2) hA (1 : Fin 3)
    · simpa using arm_edge_short (n := 2) hA (2 : Fin 3)
    · simpa using arm_edge_short (n := 2) hB (1 : Fin 3)
    · simpa using arm_edge_short (n := 2) hB (2 : Fin 3)
    · simpa using hsides (1 : Fin 3)
    · simpa using hsides (2 : Fin 3)
    · calc
        sDist (A 1) (A 0)
            = sDist (A 0) (A 1) := sDist_comm _ _
        _   = sDist (B 0) (B 1) := hsides (0 : Fin 3)
        _   = sDist (B 1) (B 0) := (sDist_comm _ _).symm
```

This is intentionally boring. For `Fin 3`, boring is best. It avoids general cyclic-index lemmas.

Depending on how much `simp` knows about your `Fin 3` numerals, the `unfold linkAngle; simp` lines may need local helper rewrites, but the structure above is the right one.

## 5. Prove `signChangesFull = 0`

Add a small helper for all-zero sign functions:

```lean
theorem nzSigns_eq_nil_of_all_zero
    {m : ℕ} (d : Fin m → ℝ)
    (hzero : ∀ i, d i = 0) :
    nzSigns d = [] := by
  unfold nzSigns
  simp [hzero]
```

Then:

```lean
theorem signChangesFull_eq_zero_triangle
    (A B : Fin 3 → S2)
    (hA : StrictConvexSphArm (n := 2) A)
    (hB : StrictConvexSphArm (n := 2) B)
    (hsides :
      ∀ i : Fin 3,
        sDist (A i) (A (i + 1))
          =
        sDist (B i) (B (i + 1))) :
    signChangesFull A B = 0 := by
  have hangle :
      ∀ i : Fin 3, linkAngle A i = linkAngle B i :=
    linkAngle_eq_of_three_sides_triangle A B hA hB hsides

  have hdiff :
      ∀ i : Fin 3, linkDiff A B i = 0 := by
    intro i
    unfold linkDiff
    rw [hangle i]
    ring

  unfold signChangesFull
  rw [nzSigns_eq_nil_of_all_zero (linkDiff A B) hdiff]
  rfl
```

Finally:

```lean
theorem signChangesFull_ne_two_triangle
    (A B : Fin 3 → S2)
    (hA : StrictConvexSphArm (n := 2) A)
    (hB : StrictConvexSphArm (n := 2) B)
    (hsides :
      ∀ i : Fin 3,
        sDist (A i) (A (i + 1))
          =
        sDist (B i) (B (i + 1))) :
    signChangesFull A B ≠ 2 := by
  have hzero :=
    signChangesFull_eq_zero_triangle A B hA hB hsides
  rw [hzero]
  norm_num
```

If Lean has trouble inferring the implicit `n` in `signChangesFull`, spell it explicitly:

```lean
(@signChangesFull 2 A B) ≠ 2
```

and similarly:

```lean
(@linkAngle 2 A i)
(@linkDiff 2 A B i)
```

## 6. Degenerate cases

The only possible denominator problem is

```lean
Real.sin (sDist u v) * Real.sin (sDist v w) = 0.
```

This would happen if one adjacent side has length `0` or `π`, i.e. equal or antipodal endpoints. Your `StrictConvexSphArm` rules this out because its closed convex polygon field gives every cyclic edge as a `ShortArc`, and `ShortArc.sin_sDist_pos` gives:

```lean
0 < Real.sin (sDist p q)
```

So the denominator is genuinely positive. No extra nondegeneracy hypothesis is needed.

## Recommendation

Add exactly three reusable lemmas:

```lean
cos_sphAngle_eq_of_short
sphAngle_eq_of_three_sDist_eq
nzSigns_eq_nil_of_all_zero
```

Then prove the `Fin 3` result by `fin_cases`.

This closes the triangular-link residual unconditionally: for three equal-sided strict spherical triangles, every link angle is equal, every `linkDiff` is zero, `nzSigns` is empty, and `signChangesFull = 0`, so `signChangesFull ≠ 2`.
