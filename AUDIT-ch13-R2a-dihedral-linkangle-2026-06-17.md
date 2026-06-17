The robust route is the **cross-product/cosine route**, not a 2D oriented-angle route. It reduces the whole identity to one scalar product identity plus one sign/orientation lemma.

The important warning: orthogonality of `n_f` to `a,b` and `n_g` to `b,c` is **not enough** to choose supplement versus equality. Replacing one normal by its negative changes `angle n_f n_g` to its supplement. You need an explicit same-side orientation hypothesis for the two normals.

## The algebraic core

Let

```lean
ta := tangentTo b a = a - ⟪a,b⟫ • b
tc := tangentTo b c = c - ⟪c,b⟫ • b

X := a ⨯₃ b
Y := b ⨯₃ c
```

assuming `‖a‖ = ‖b‖ = ‖c‖ = 1`.

Then the two key identities are:

```text
⟪ta, tc⟫ = ⟪a,c⟫ - ⟪a,b⟫ * ⟪b,c⟫
⟪X, Y⟫  = ⟪a,b⟫ * ⟪b,c⟫ - ⟪a,c⟫
```

so

```text
⟪ta, tc⟫ = - ⟪X, Y⟫.
```

The second identity is exactly Mathlib’s `cross_dot_cross` / Binet–Cauchy identity for `crossProduct`: `(u × v) · (w × x) = (u·w)(v·x) − (u·x)(v·w)`. Mathlib’s cross product file exposes `crossProduct`, notation `⨯₃`, perpendicularity lemmas, and `cross_dot_cross`. citeturn650645view0

You also get the norm equalities:

```text
‖ta‖ = ‖a ⨯₃ b‖
‖tc‖ = ‖b ⨯₃ c‖
```

because both squared norms are `1 - ⟪a,b⟫^2` and `1 - ⟪b,c⟫^2`.

Therefore

```text
cos (angle ta tc) = - cos (angle X Y).
```

Since Mathlib’s `InnerProductGeometry.angle` is an unoriented angle in `[0,π]`, and Mathlib has both `cos_angle` and the bounds `angle_nonneg`, `angle_le_pi`, you can conclude angle equality by injectivity of `Real.cos` on `[0,π]`. citeturn233081view1turn425631view0

A particularly clean final form is:

```text
angle ta tc = angle X (-Y)
            = π - angle X Y.
```

The second equality is Mathlib’s `InnerProductGeometry.angle_neg_right`. citeturn233081view1

So the geometric target becomes:

```lean
sphAngle a b c = Real.pi - InnerProductGeometry.angle (a ⨯₃ b) (b ⨯₃ c)
```

and then you identify the face normals with common-sign multiples of those cross products.

## Minimal orientation hypothesis

The cleanest theorem should not take only

```lean
⟪n_f, a⟫ = 0, ⟪n_f, b⟫ = 0,
⟪n_g, b⟫ = 0, ⟪n_g, c⟫ = 0.
```

That leaves the signs ambiguous.

Use one of these equivalent minimal hypotheses.

### Best Lean hypothesis

```lean
∃ λ μ : ℝ,
  0 < λ ∧ 0 < μ ∧
    ((n_f = λ • (a ⨯₃ b) ∧ n_g = μ • (b ⨯₃ c)) ∨
     (n_f = λ • (-(a ⨯₃ b)) ∧ n_g = μ • (-(b ⨯₃ c))))
```

This says the two outward normals are chosen with the **same cross-product orientation**. Then

```lean
angle n_f n_g = angle (a ⨯₃ b) (b ⨯₃ c)
```

by `angle_smul_left_of_pos`, `angle_smul_right_of_pos`, and, in the second branch, `angle_neg_neg`. These lemmas are in the unoriented angle API. citeturn233081view1

### If you want to derive it from support inequalities

Suppose you already know:

```lean
n_f = s • (a ⨯₃ b)
n_g = t • (b ⨯₃ c)
⟪n_f, c⟫ < 0
⟪n_g, a⟫ < 0
Δ := ⟪a, b ⨯₃ c⟫ ≠ 0
```

Then use cyclic triple-product identities to show:

```text
⟪a ⨯₃ b, c⟫ = Δ
⟪b ⨯₃ c, a⟫ = Δ.
```

So the inequalities give:

```text
s * Δ < 0
t * Δ < 0
```

hence `s` and `t` have the same sign. If `Δ > 0`, both are negative; if `Δ < 0`, both are positive. Thus the best Lean hypothesis above follows. Mathlib exposes cyclic triple-product facts such as `triple_product_permutation` and determinant/triple-product lemmas in the cross product file. citeturn650645view0

I would **not** derive `n_f ∥ a×b` from orthogonality inside the main theorem. Prove or assume that separately:

```lean
∃ s, n_f = s • (a ⨯₃ b)
∃ t, n_g = t • (b ⨯₃ c)
```

Deriving it from the orthogonal complement of a 2-plane is possible but much more API-heavy than the angle identity itself.

## Lean theorem shape

Use a theorem like this:

```lean
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

open InnerProductGeometry
open scoped Matrix RealInnerProductSpace

abbrev E3 := EuclideanSpace ℝ (Fin 3)

def tangentToVec (v u : E3) : E3 :=
  u - (inner ℝ u v) • v

theorem spherical_angle_eq_pi_sub_normal_angle
    {a b c n_f n_g : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hta : tangentToVec b a ≠ 0)
    (htc : tangentToVec b c ≠ 0)
    (hX : a ⨯₃ b ≠ 0)
    (hY : b ⨯₃ c ≠ 0)
    (horient :
      ∃ λ μ : ℝ,
        0 < λ ∧ 0 < μ ∧
          ((n_f = λ • (a ⨯₃ b) ∧ n_g = μ • (b ⨯₃ c)) ∨
           (n_f = λ • (-(a ⨯₃ b)) ∧ n_g = μ • (-(b ⨯₃ c))))) :
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
      = Real.pi - InnerProductGeometry.angle n_f n_g := by
  ...
```

If your `S2` points are subtypes, first prove wrapper simp lemmas:

```lean
@[simp] lemma norm_coe_S2 (u : S2) : ‖(u : E3)‖ = 1 := by
  exact u.property

@[simp] lemma inner_self_coe_S2 (u : S2) :
    inner ℝ (u : E3) (u : E3) = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_coe_S2]
  norm_num
```

Then the theorem applies to `(a : E3)`, `(b : E3)`, `(c : E3)`.

## Lemma stack

### 1. Tangent inner product

```lean
lemma inner_tangent_tangent_unit
    {a b c : E3} (hb : ‖b‖ = 1) :
    inner ℝ (tangentToVec b a) (tangentToVec b c)
      = inner ℝ a c - inner ℝ a b * inner ℝ b c := by
  classical
  unfold tangentToVec
  have hb_inner : inner ℝ b b = 1 := by
    rw [real_inner_self_eq_norm_sq, hb]
    norm_num
  -- expand and ring
  simp [inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, hb_inner, real_inner_comm]
  ring
```

Depending on your local simp set, you may need to replace `real_inner_smul_left/right` names by `inner_smul_left`, `inner_smul_right`. The inner-product basic file exposes `inner_sub_left`, `inner_sub_right`, and real scalar inner-product simp lemmas. citeturn650645view1

### 2. Cross-product inner product

```lean
lemma inner_cross_cross_unit
    {a b c : E3} (hb : ‖b‖ = 1) :
    inner ℝ (a ⨯₃ b) (b ⨯₃ c)
      = inner ℝ a b * inner ℝ b c - inner ℝ a c := by
  have hb_inner : inner ℝ b b = 1 := by
    rw [real_inner_self_eq_norm_sq, hb]
    norm_num
  -- `cross_dot_cross a b b c` says:
  -- (a×b)·(b×c) = (a·b)(b·c) - (a·c)(b·b)
  -- Bridge `⬝ᵥ` and `inner ℝ`; often this is `rfl` for `Fin 3 → ℝ`.
  simpa [hb_inner, real_inner_comm] using
    (cross_dot_cross (R := ℝ) a b b c)
```

If `EuclideanSpace ℝ (Fin 3)` is not definitionally `Fin 3 → ℝ` in your file, insert a local bridge lemma rather than fighting `simp` repeatedly:

```lean
lemma inner_eq_dot (x y : E3) : inner ℝ x y = x ⬝ᵥ y := by
  -- often `rfl` / `simp [PiLp.inner_apply]`
  rfl
```

Then rewrite `inner_eq_dot`.

### 3. The negative relation

```lean
lemma inner_tangent_eq_neg_inner_cross
    {a b c : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    inner ℝ (tangentToVec b a) (tangentToVec b c)
      = - inner ℝ (a ⨯₃ b) (b ⨯₃ c) := by
  rw [inner_tangent_tangent_unit hb, inner_cross_cross_unit hb]
  ring
```

### 4. Norm relation

Prove squared norms, then take nonnegative square roots.

```lean
lemma norm_tangent_eq_norm_cross_left
    {a b : E3} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖tangentToVec b a‖ = ‖a ⨯₃ b‖ := by
  have ht_sq :
      ‖tangentToVec b a‖ ^ 2 =
        1 - (inner ℝ a b) ^ 2 := by
    -- expand `inner (tangent) (tangent)` and use `real_inner_self_eq_norm_sq`
    ...
  have hX_sq :
      ‖a ⨯₃ b‖ ^ 2 =
        1 - (inner ℝ a b) ^ 2 := by
    -- use `cross_dot_cross a b a b`
    ...
  have hsq : ‖tangentToVec b a‖ ^ 2 = ‖a ⨯₃ b‖ ^ 2 := by
    rw [ht_sq, hX_sq]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq |>.elim id (fun hneg => by
    have h1 := norm_nonneg (tangentToVec b a)
    have h2 := norm_nonneg (a ⨯₃ b)
    linarith)
```

Analogously:

```lean
lemma norm_tangent_eq_norm_cross_right
    {b c : E3} (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) :
    ‖tangentToVec b c‖ = ‖b ⨯₃ c‖ := ...
```

### 5. Cosine equality

```lean
lemma cos_tangent_eq_neg_cos_cross
    {a b c : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hta : tangentToVec b a ≠ 0)
    (htc : tangentToVec b c ≠ 0)
    (hX : a ⨯₃ b ≠ 0)
    (hY : b ⨯₃ c ≠ 0) :
    Real.cos (InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c))
      =
    - Real.cos (InnerProductGeometry.angle (a ⨯₃ b) (b ⨯₃ c)) := by
  rw [InnerProductGeometry.cos_angle,
      InnerProductGeometry.cos_angle,
      inner_tangent_eq_neg_inner_cross ha hb hc,
      norm_tangent_eq_norm_cross_left ha hb,
      norm_tangent_eq_norm_cross_right hb hc]
  field_simp [norm_pos_iff.mpr hX, norm_pos_iff.mpr hY]
```

`cos_angle` is exactly Mathlib’s theorem for the cosine of the angle between two vectors. citeturn233081view1

### 6. Convert cosine equality to angle equality

```lean
lemma tangent_angle_eq_cross_neg
    {a b c : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hta : tangentToVec b a ≠ 0)
    (htc : tangentToVec b c ≠ 0)
    (hX : a ⨯₃ b ≠ 0)
    (hY : b ⨯₃ c ≠ 0) :
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
      =
    InnerProductGeometry.angle (a ⨯₃ b) (-(b ⨯₃ c)) := by
  apply Real.injOn_cos
  · exact ⟨InnerProductGeometry.angle_nonneg _ _,
           InnerProductGeometry.angle_le_pi _ _⟩
  · exact ⟨InnerProductGeometry.angle_nonneg _ _,
           InnerProductGeometry.angle_le_pi _ _⟩
  · rw [cos_tangent_eq_neg_cos_cross ha hb hc hta htc hX hY]
    -- show `cos(angle X (-Y)) = - cos(angle X Y)`
    rw [InnerProductGeometry.cos_angle, InnerProductGeometry.cos_angle]
    simp [inner_neg_right, norm_neg]
```

Then:

```lean
lemma tangent_angle_eq_pi_sub_cross_angle
    ... :
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
      =
    Real.pi - InnerProductGeometry.angle (a ⨯₃ b) (b ⨯₃ c) := by
  rw [tangent_angle_eq_cross_neg ha hb hc hta htc hX hY]
  exact InnerProductGeometry.angle_neg_right (a ⨯₃ b) (b ⨯₃ c)
```

`Real.injOn_cos` is available on `[0,π]`; Mathlib’s trigonometric docs list it as injectivity of `cos` on `Set.Icc 0 π`. citeturn425631view0

### 7. Normals to cross products

```lean
lemma angle_normals_eq_cross
    {a b c n_f n_g : E3}
    (horient :
      ∃ λ μ : ℝ,
        0 < λ ∧ 0 < μ ∧
          ((n_f = λ • (a ⨯₃ b) ∧ n_g = μ • (b ⨯₃ c)) ∨
           (n_f = λ • (-(a ⨯₃ b)) ∧ n_g = μ • (-(b ⨯₃ c))))) :
    InnerProductGeometry.angle n_f n_g
      =
    InnerProductGeometry.angle (a ⨯₃ b) (b ⨯₃ c) := by
  rcases horient with ⟨λ, μ, hλ, hμ, hcase⟩
  rcases hcase with ⟨hf, hg⟩ | ⟨hf, hg⟩
  · rw [hf, hg]
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hλ]
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ hμ]
  · rw [hf, hg]
    rw [InnerProductGeometry.angle_smul_left_of_pos _ _ hλ]
    rw [InnerProductGeometry.angle_smul_right_of_pos _ _ hμ]
    rw [InnerProductGeometry.angle_neg_neg]
```

Adjust argument order for `angle_smul_left_of_pos`/`angle_smul_right_of_pos` if your local Mathlib version expects implicit scalar arguments; the docs show both lemmas exist. citeturn233081view1

### 8. Final theorem

```lean
theorem sphAngle_eq_dihedral
    {a b c n_f n_g : E3}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)
    (hta : tangentToVec b a ≠ 0)
    (htc : tangentToVec b c ≠ 0)
    (hX : a ⨯₃ b ≠ 0)
    (hY : b ⨯₃ c ≠ 0)
    (horient :
      ∃ λ μ : ℝ,
        0 < λ ∧ 0 < μ ∧
          ((n_f = λ • (a ⨯₃ b) ∧ n_g = μ • (b ⨯₃ c)) ∨
           (n_f = λ • (-(a ⨯₃ b)) ∧ n_g = μ • (-(b ⨯₃ c))))) :
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
      =
    Real.pi - InnerProductGeometry.angle n_f n_g := by
  calc
    InnerProductGeometry.angle (tangentToVec b a) (tangentToVec b c)
        = Real.pi - InnerProductGeometry.angle (a ⨯₃ b) (b ⨯₃ c) :=
            tangent_angle_eq_pi_sub_cross_angle ha hb hc hta htc hX hY
    _ = Real.pi - InnerProductGeometry.angle n_f n_g := by
        rw [angle_normals_eq_cross horient]
```

For your repo definitions:

```lean
sphAngle a b c =
  InnerProductGeometry.angle (tangentTo b a) (tangentTo b c)
```

so the final bridge is just unfolding `sphAngle` and `tangentTo`.

## What to avoid

Avoid proving “`n_f` is a 90° rotation of `t_a` in `bᗮ`.” It is mathematically nice but Lean-expensive: it drags in orientation of a subspace, linear isometries on `bᗮ`, and sign choices. The cross-product proof does the same job with scalar algebra.

Also avoid deriving the normal direction from orthogonality inside the identity theorem. Make a separate lemma for face normals:

```lean
face_normal_parallel_cross :
  n_f ⟂ a → n_f ⟂ b → n_f ≠ 0 → a ⨯₃ b ≠ 0 →
  ∃ s, n_f = s • (a ⨯₃ b)
```

or, better, define your concrete face normal as the normalized signed cross product in the first place. Then the dihedral identity is just the theorem above.
