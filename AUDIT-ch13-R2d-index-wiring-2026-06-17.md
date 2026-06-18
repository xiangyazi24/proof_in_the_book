The application should be split into two independent bridges:

```lean
-- combinatorial/index bridge
linkAngle_at_Jd_rewrites_to_sphAngle_sigma :
  linkAngle star.vertexLink (J d)
    = sphAngle (edgeDir (M.σ d)) (edgeDir d) (edgeDir (M.σ.symm d))

-- geometric/orientation bridge
sphAngle_sigma_eq_dihedral :
  sphAngle (edgeDir (M.σ d)) (edgeDir d) (edgeDir (M.σ.symm d))
    = Real.pi - angle (dartNormal P (M.α d)) (dartNormal P d)
```

Then finish by `angle_comm`:

```lean
dihedralAngleAtDart P d
  = Real.pi - angle (dartNormal P d) (dartNormal P (M.α d))
  = Real.pi - angle (dartNormal P (M.α d)) (dartNormal P d)
  = linkAngle ...
```

The key combinatorial fact is: for edge dart `d` with `tail d = v`, the two faces meeting that edge are always

```lean
M.dartFace d
M.dartFace (M.α d)
```

not `dartFace (M.σ⁻¹ d)` directly. But `dartFace d` is also the face between `M.σ.symm d` and `d`, because

```lean
M.φ (M.α (M.σ.symm d)) = d
```

and `dartFace (M.α d)` is the face between `d` and `M.σ d`, because

```lean
M.φ (M.α d) = M.σ d.
```

## 1. The index map `J`

Let

```lean
v  := M.tail d
d⁺ := M.σ d
d⁻ := M.σ.symm d
```

In the raw σ-order around `v`, the local order is:

```text
..., d⁻, d, d⁺, ...
```

Your `vertexStarOfEuclidean` reverses this order using `Fin.rev`. Therefore, in the **link order**:

```text
..., d⁺, d, d⁻, ...
```

So the local link angle at the link vertex corresponding to `d` is

```lean
sphAngle (edgeDir d⁺) (edgeDir d) (edgeDir d⁻)
```

assuming your `linkAngle i` is `sphAngle (i-1) i (i+1)`.

Package the index map by theorem, not by exposing arithmetic:

```lean
def J (hd : M.tail d = v) : Fin star.n := ...

@[simp] theorem incidentDart_J
    (hd : M.tail d = v) :
    star.incidentDart (J hd) = d := ...

@[simp] theorem incidentDart_pred_J
    (hd : M.tail d = v) :
    star.incidentDart ((J hd) - 1) = M.σ d := ...

@[simp] theorem incidentDart_succ_J
    (hd : M.tail d = v) :
    star.incidentDart ((J hd) + 1) = M.σ.symm d := ...
```

The proof should be only the `Fin.rev` arithmetic plus σ-toList successor/predecessor lemmas. Avoid using `simp [vertexStarOfEuclidean]` downstream; prove these three lemmas once and mark only these as `[simp]`.

Then prove the link rewrite:

```lean
theorem linkAngle_J
    (hd : M.tail d = v) :
    linkAngle (vertexStarOfEuclidean P v).vertexLink (J hd)
      =
    sphAngle
      (edgeDir P (M.σ d))
      (edgeDir P d)
      (edgeDir P (M.σ.symm d)) := by
  unfold linkAngle
  simp [incidentDart_J, incidentDart_pred_J, incidentDart_succ_J]
```

The exact sign of `±1` depends on your cyclic predecessor/successor definitions, but the invariant you want is:

```lean
(J d - 1) ↦ M.σ d
(J d)     ↦ d
(J d + 1) ↦ M.σ.symm d
```

If your `Fin.rev` lemmas give the opposite, swap the two outside arguments; `sphAngle` is symmetric in the outside arguments because `angle` is symmetric, but the orientation lemma below must be stated consistently.

## 2. Which normals go with which link arcs?

With the reversed order:

```lean
a := edgeDir P (M.σ d)
b := edgeDir P d
c := edgeDir P (M.σ.symm d)
```

the face spanned by `a,b` is the face between `d` and `M.σ d`, hence:

```lean
f_plus := M.dartFace (M.α d)
n_f    := dartNormal P (M.α d)
```

because

```lean
M.φ (M.α d) = M.σ d.
```

The face spanned by `b,c` is the face between `M.σ.symm d` and `d`, hence:

```lean
f_minus := M.dartFace d
n_g     := dartNormal P d
```

because

```lean
M.φ (M.α (M.σ.symm d)) = d.
```

Add these as permanent local lemmas:

```lean
@[simp] lemma phi_alpha (d : D) :
    M.φ (M.α d) = M.σ d := by
  simp [CombMap.φ]

lemma face_between_next (d : D) :
    M.dartFace (M.σ d) = M.dartFace (M.α d) := by
  -- `M.σ d = M.φ (M.α d)`
  rw [← phi_alpha]

lemma face_between_prev (d : D) :
    M.dartFace (M.α (M.σ.symm d)) = M.dartFace d := by
  -- `M.φ (M.α (M.σ.symm d)) = d`
  apply Quotient.sound
  exact ⟨1, by simp [CombMap.φ]⟩
```

Then the geometric identity should be applied as:

```lean
pure_sph_dihedral
  (a := edgeDir P (M.σ d))
  (b := edgeDir P d)
  (c := edgeDir P (M.σ.symm d))
  (n_f := dartNormal P (M.α d))
  (n_g := dartNormal P d)
```

This returns:

```lean
sphAngle a b c = Real.pi - angle (dartNormal P (M.α d)) (dartNormal P d)
```

and the dihedral definition follows by `angle_comm`.

## 3. Plane/normal bridge: do it for all darts in a triangular face

Your `face_plane` field is probably stated for the chosen `faceVertex f i`. For this bridge you need a more usable lemma:

```lean
theorem face_plane_tail_of_dart
    {f : M.Face} {e : D}
    (he : M.dartFace e = f) :
    inner ℝ (P.outward_normal f)
      (P.pos (M.tail e) - P.face_point f) = 0 := ...
```

For a triangular face, every dart in the `φ`-orbit is one of the three `faceDart f`, `φ faceDart f`, `φ² faceDart f`. Use `hNT.inner_tri` / triangularity or your polyhedron’s face-triangle data to reduce to the three stored `faceVertex` entries.

Then derive edge-vector perpendicularity:

```lean
theorem normal_perp_edgeVec_of_same_face
    {f : M.Face} {e₁ e₂ : D}
    (h₁ : M.dartFace e₁ = f)
    (h₂ : M.dartFace e₂ = f) :
    inner ℝ (P.outward_normal f)
      ((P.pos (M.tail e₁)) - (P.pos (M.tail e₂))) = 0 := by
  have hA := face_plane_tail_of_dart P h₁
  have hB := face_plane_tail_of_dart P h₂
  -- subtract the two equations
  linear_combination hA - hB
```

For `f_plus = dartFace (α d)`, use the darts:

```lean
M.α d       -- tail = head d
M.σ d       -- tail = v
```

and also the relevant third dart if needed. For the edge directions at `v`, you want perpendicularity to:

```lean
edgeVec (M.σ d) = pos (head (M.σ d)) - pos v
edgeVec d       = pos (head d) - pos v
```

Those are differences of two vertices of `f_plus`, so the normal is perpendicular to both.

For `f_minus = dartFace d`, use:

```lean
d
M.α (M.σ.symm d)
```

to get perpendicularity to:

```lean
edgeVec d
edgeVec (M.σ.symm d)
```

## 4. Parallel-to-cross lemma

State the reusable lemma in vector form:

```lean
abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem perp_two_imp_parallel_cross
    {n u v : E3}
    (hnu : inner ℝ n u = 0)
    (hnv : inner ℝ n v = 0)
    (huv : u ⨯₃ v ≠ 0) :
    ∃ s : ℝ, n = s • (u ⨯₃ v) := by
  -- Recommended proof:
  -- Let S := span ℝ {u,v}.
  -- `huv` gives LinearIndependent ℝ ![u,v] via
  -- `crossProduct_ne_zero_iff_linearIndependent`.
  -- Hence finrank S = 2 and finrank Sᗮ = 1 in E3.
  -- `u×v` lies in Sᗮ and is nonzero.
  -- Since `n` is also in Sᗮ, one-dimensionality gives n ∈ span {u×v}.
```

Mathlib has the key cross-product facts: `crossProduct_ne_zero_iff_linearIndependent`, perpendicularity of cross products to their factors via `dot_self_cross` / `dot_cross_self`, and the scalar quadruple product `cross_dot_cross`. citeturn918553view0

If the subspace/finrank route is heavy, prove a coordinate lemma once for `Fin 3 → ℝ` and cast `EuclideanSpace ℝ (Fin 3)` to that representation. But keep it isolated; do not inline this in the dihedral bridge.

## 5. Sign extraction from support inequalities

This is the minimal sign lemma you want:

```lean
theorem normal_eq_pos_smul_neg_cross_of_support
    {n u v w : E3}
    (hnu : inner ℝ n u = 0)
    (hnv : inner ℝ n v = 0)
    (hcross : u ⨯₃ v ≠ 0)
    (hopp : inner ℝ n w < 0)
    (hdet : 0 < inner ℝ (u ⨯₃ v) w) :
    ∃ λ : ℝ, 0 < λ ∧ n = λ • (-(u ⨯₃ v)) := by
  obtain ⟨s, hs⟩ := perp_two_imp_parallel_cross hnu hnv hcross
  have hsneg : s < 0 := by
    have hdot : inner ℝ n w = s * inner ℝ (u ⨯₃ v) w := by
      rw [hs]
      simp [inner_smul_left]
    nlinarith [hopp, hdet, hdot]
  refine ⟨-s, by linarith, ?_⟩
  rw [hs]
  simp [neg_smul]
```

Support inequality must be **strict** for the opposite link vertex. A non-strict `≤ 0` only gives `s ≤ 0`, which is not enough to produce a positive multiple of either cross direction. So you need a lemma of this form from your convexity/support layer:

```lean
strict_support_opposite_vertex
  (f : M.Face) (w : M.Vertex)
  (hw_not_on_f : w not one of the three vertices of f) :
  inner ℝ (P.outward_normal f) (P.pos w - P.face_point f) < 0
```

or the already-mentioned support inequalities:

```lean
inner ℝ (dartNormal P (M.α d))
  (P.pos (M.head (M.σ.symm d)) - P.pos (M.tail d)) < 0

inner ℝ (dartNormal P d)
  (P.pos (M.head (M.σ d)) - P.pos (M.tail d)) < 0
```

If your support field is based at `face_point f`, convert it to base point `pos v` by subtracting the face-plane equation for `v`:

```lean
inner n (pos w - pos v)
  = inner n (pos w - face_point f)
    - inner n (pos v - face_point f)
  = inner n (pos w - face_point f)
```

## 6. The two normal-orientation lemmas for dart `d`

Let:

```lean
a := edgeDir P (M.σ d)
b := edgeDir P d
c := edgeDir P (M.σ.symm d)
```

Assume your star construction gives:

```lean
turn_support_at_Jd :
  0 < inner ℝ (a ⨯₃ b) c
```

Then by cyclicity of the scalar triple product, also:

```lean
0 < inner ℝ (b ⨯₃ c) a
```

Mathlib has `triple_product_permutation` and `triple_product_eq_det` for cyclic triple-product handling. citeturn918553view0

Now prove:

```lean
theorem normal_alpha_d_eq_neg_cross
    (hd : M.tail d = v)
    :
    ∃ λ : ℝ, 0 < λ ∧
      dartNormal P (M.α d)
        = λ • (-(edgeDir P (M.σ d) ⨯₃ edgeDir P d)) := by
  apply normal_eq_pos_smul_neg_cross_of_support
  · -- perpendicular to edgeDir(σ d)
    exact normal_perp_edgeDir_face_plus_left ...
  · -- perpendicular to edgeDir d
    exact normal_perp_edgeDir_face_plus_right ...
  · -- nondegenerate face
    exact cross_ne_zero_of_turn_positive ...
  · -- strict support: c is on the interior side of face dartFace(α d)
    exact support_face_plus_opposite_prev ...
  · -- positive determinant
    exact turn_support_at_Jd ...
```

and:

```lean
theorem normal_d_eq_neg_cross
    (hd : M.tail d = v)
    :
    ∃ μ : ℝ, 0 < μ ∧
      dartNormal P d
        = μ • (-(edgeDir P d ⨯₃ edgeDir P (M.σ.symm d))) := by
  apply normal_eq_pos_smul_neg_cross_of_support
  · -- perpendicular to edgeDir d
  · -- perpendicular to edgeDir(σ.symm d)
  · -- nondegenerate face
  · -- strict support: a is on the interior side of face dartFace d
  · -- cyclic determinant positivity
```

These two lemmas produce the **negative/negative branch** of your pure-vector `horient` hypothesis:

```lean
have horient :
  ∃ λ μ : ℝ,
    0 < λ ∧ 0 < μ ∧
      ((nf = λ • (a ⨯₃ b) ∧ ng = μ • (b ⨯₃ c)) ∨
       (nf = λ • (-(a ⨯₃ b)) ∧ ng = μ • (-(b ⨯₃ c)))) := by
  obtain ⟨λ, hλ, hnf⟩ := normal_alpha_d_eq_neg_cross ...
  obtain ⟨μ, hμ, hng⟩ := normal_d_eq_neg_cross ...
  exact ⟨λ, μ, hλ, hμ, Or.inr ⟨hnf, hng⟩⟩
```

Your pure-vector theorem can then use `angle_smul_left_of_pos`, `angle_smul_right_of_pos`, `angle_neg_neg`, and `angle_neg_right`; these are all in Mathlib’s unoriented angle API. citeturn475633view1turn475633view0

## 7. Final wiring theorem

The final theorem should look like this:

```lean
theorem dihedralAngleAtDart_eq_linkAngle
    {d : D} (hd : M.tail d = v)
    (hndeg : nondegenerate local star hypotheses)
    (hsupport_plus : strict support for dartFace (M.α d) opposite M.σ.symm d)
    (hsupport_minus : strict support for dartFace d opposite M.σ d) :
    dihedralAngleAtDart P d
      =
    linkAngle (vertexStarOfEuclidean P v).vertexLink (J hd) := by
  classical

  let a := edgeDir P (M.σ d)
  let b := edgeDir P d
  let c := edgeDir P (M.σ.symm d)
  let nf := dartNormal P (M.α d)
  let ng := dartNormal P d

  have hlink :
      linkAngle (vertexStarOfEuclidean P v).vertexLink (J hd)
        = sphAngle a b c := by
    exact linkAngle_J P hd

  have horient :
      ∃ λ μ : ℝ,
        0 < λ ∧ 0 < μ ∧
          ((nf = λ • (a ⨯₃ b) ∧ ng = μ • (b ⨯₃ c)) ∨
           (nf = λ • (-(a ⨯₃ b)) ∧ ng = μ • (-(b ⨯₃ c)))) := by
    exact horient_for_dart_reversed_order P d hd hsupport_plus hsupport_minus

  have hpure :
      sphAngle a b c = Real.pi - InnerProductGeometry.angle nf ng := by
    exact pure_sphAngle_eq_pi_sub_normal_angle
      (a := a) (b := b) (c := c) (n_f := nf) (n_g := ng)
      -- unit/nonzero/link nondegenerate hypotheses
      horient

  calc
    dihedralAngleAtDart P d
        = Real.pi - InnerProductGeometry.angle ng nf := by
            rfl
    _ = Real.pi - InnerProductGeometry.angle nf ng := by
            rw [InnerProductGeometry.angle_comm]
    _ = sphAngle a b c := by
            exact hpure.symm
    _ = linkAngle (vertexStarOfEuclidean P v).vertexLink (J hd) := by
            exact hlink.symm
```

The pure-vector part can use `cos_angle` and `cross_dot_cross` if you have not already hidden it behind `pure_sphAngle_eq_pi_sub_normal_angle`; Mathlib documents both `cos_angle` and the cross-product Binet–Cauchy identity `cross_dot_cross`. citeturn475633view2turn918553view0

## 8. Checklist of structural lemmas to add

Add these wrappers once; then the final theorem becomes short.

```lean
-- Index/star lemmas
incidentDart_J
incidentDart_pred_J
incidentDart_succ_J
vertexLink_J
vertexLink_pred_J
vertexLink_succ_J
linkAngle_J

-- Face-combinatorics lemmas
phi_alpha
face_between_next
face_between_prev

-- Plane lemmas
face_plane_tail_of_dart
normal_perp_edgeVec_of_same_face
normal_perp_edgeDir_of_same_face

-- Cross/sign lemmas
perp_two_imp_parallel_cross
normal_eq_pos_smul_neg_cross_of_support
normal_alpha_d_eq_neg_cross
normal_d_eq_neg_cross
horient_for_dart_reversed_order
```

The only genuinely geometric hypotheses still needed are the strict support/opposite-side facts and local nondegeneracy/positive determinant facts. The combinatorial part determines **which** faces and **which** link neighbors; the support/determinant part determines the normal signs.
