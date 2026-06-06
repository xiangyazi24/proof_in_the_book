# Chapter 13 — Full extrinsic-sphere + Cauchy-rigidity design (authoritative)

Pasted by Xiang 2026-06-06. The complete chapter roadmap: extrinsic S² kernel
(Layers A–C, already built in SphericalKernel/Rotation), convex spherical
polygons/arms (Layer D), rotations + hinges (Layer E, Rodrigues `rot`/`rotS2`
already in SphericalRotation), the **Schoenberg–Zaremba opening chain** (Layer F,
the single hardest lemma — currently isolated as `OpeningData` / `HingeConvexPosition`),
vertex links (Layer G), Cauchy local bridge (Layer H), global Cauchy assembly
(Layer I).

The key resolution of the earlier terminal-visibility obstruction is **§8.4 Case 2**:
when opening gets stuck before the target, a *non-terminal* support determinant
goes to zero (`sOrient (P i) (P (i+1)) (P j) = 0`), giving a **diagonal cut** of
the convex spherical arm into two smaller convex arms (`convex_stuck_gives_cut`),
then induct + glue with the spherical hinge lemma. This sidesteps needing
terminal-first identification entirely.

---

## 1. Basic representation

Use no intrinsic manifold.

```lean
abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev S2 : Type := {x : E3 // ‖x‖ = 1}
```

`sInner p q := ⟪p,q⟫`, `sDist p q := arccos (sInner p q)`, `ShortArc p q := p ≠ q ∧ p ≠ -q`.
Basics: `sInner_mem_Icc`, `Real.cos_sDist`, `sDist_nonneg`, `sDist_le_pi`,
`sDist_pos_of_ne`, `sDist_lt_pi_of_not_antipodal`.

## 2. Tangent projection and spherical angle

`projOut v u := u - ⟪u,v⟫•v` (reuse TetDihedral.projOut), `tangentTo p q := projOut p q`,
`sphAngle u v w := InnerProductGeometry.angle (tangentTo v u) (tangentTo v w)`.
Key: `tangentTo_orthogonal`, `tangentTo_ne_zero_iff` (well-definedness),
`norm_tangentTo` (= sin sDist), `decompose_unit_along_tangent`.

## 3. Convex spherical polygons (oriented triple products, NOT topology)

`det3 a b c := Matrix.det ![a,b,c]`, `sOrient a b c := det3 a b c`.

```lean
structure StrictConvexSphPolygon {n} (P : Fin n → S2) : Prop where
  three_le : 3 ≤ n
  edge_short : ∀ i, ShortArc (P i) (P (i+1))
  edge_support : ∀ i j, 0 ≤ sOrient (P i) (P (i+1)) (P j)
  strict_nonincident : ∀ i j, j ≠ i → j ≠ i+1 → 0 < sOrient (P i) (P (i+1)) (P j)
  open_hemisphere : ∃ h, ‖h‖ = 1 ∧ ∀ i, 0 < ⟪h, (P i : E3)⟫

structure StrictConvexSphArm {n} (A : Fin (n+1) → S2) : Prop where
  two_le : 2 ≤ n
  closed_convex : StrictConvexSphPolygon A
```

## 4. Spherical triangle kernel

`spherical_cosine_rule`: cos(AC) = cos AB cos BC + sin AB sin BC cos(angle at B).
Proof: decompose a,c along b's tangent frame; tangent cross terms vanish
(orthogonal to b); `⟪tangentTo b a, tangentTo b c⟫ = ‖·‖‖·‖cos(sphAngle)`.

## 5. Spherical hinge lemma (base monotonicity, n=3)

```lean
theorem spherical_hinge_mono (a b γ₁ γ₂ ∈ ranges) (hγ : γ₁ ≤ γ₂)
  (hc₁ hc₂ : cosine-rule definitions of c₁ c₂) : c₁ ≤ c₂
```

Proof: sin a, sin b > 0; cos antitone on [0,π] ⟹ cos γ₂ ≤ cos γ₁ ⟹ cos c₂ ≤ cos c₁
⟹ c₁ ≤ c₂. Strict version with hγ : γ₁ < γ₂.

## 6. Planar profile trick does NOT transfer

Endpoint on the sphere is a *product of rotations*, not a vector sum. No global
double-sum formula. Honest route = Schoenberg–Zaremba induction.

## 7. Arm lemma statement

```lean
sideLen A i := sDist (A i.castSucc) (A i.succ)
jointAngle A i := sphAngle (A i.castSucc) (A i.succ.castSucc) (A i.succ.succ)

theorem spherical_arm_mono (hn : 2 ≤ n) (A B : Fin (n+1) → S2)
  (hA hB : StrictConvexSphArm) (hSide : equal sides)
  (hAngle : ∀ i, jointAngle A i ≤ jointAngle B i) :
  sDist (A 0) (A (last n)) ≤ sDist (B 0) (B (last n))
-- strict: + (∃ i, jointAngle A i < jointAngle B i) ⟹ strict <
```

## 8. Schoenberg–Zaremba proof skeleton (the single hardest layer)

### 8.1 Rotation about a sphere point — Rodrigues
`rotAbout a δ : E3 ≃ₗᵢ E3` fixing axis a. **Already built**: SphericalRotation `rot`/`rotS2`,
`rot_axis`, `inner_rot_rot`, `norm_rot`, `rot_comp` (group law), `sDist_rotS2`,
`tangentTo_rotS2`. Plus the oriented `rotAbout_tangent_angle_add`:
angle u (rot a δ w) = angle u w + δ for 0≤δ, angle+δ ≤ π (oriented tangent angle,
introduced ONLY inside the rotation module).

### 8.2 Hinge move
```lean
def HingeMove A B k δ : Prop :=
  (∀ i, i.val ≤ k.val → B i = A i) ∧
  (∀ i, k.val ≤ i.val → (B i : E3) = rotAbout (A k) δ (A i))
```
`hinge_preserves_side_lengths`, `hinge_preserves_other_angles`,
`hinge_increases_joint` (jointAngle B k' = jointAngle A k' + δ),
`hinge_endpoint_mono` (via the triangle A0,Ak,An with included angle at Ak
increasing by δ ⟹ spherical_hinge_mono), and strict version.

### 8.3 Convexity under small hinge openings
```lean
lemma convex_hinge_open_small (hA : StrictConvexSphArm A) (k internal)
  (hnotStraight : jointAngle A k' < π) :
  ∃ ε > 0, ∀ δ ∈ [0,ε), StrictConvexSphArm (hingeOpened A k δ)
```
Proof: convexity inequalities are finite strict inequalities of continuous functions
of δ; positive at δ=0 ⟹ remain positive for small δ. Weak support inequalities stay
≥0 by choosing the opening direction compatible with the convex side (orientation
convention for rotAbout matters here).

### 8.4 Schoenberg continuation lemma (THE hard theorem)
```lean
theorem spherical_SZ_opening_chain (hn : 2 ≤ n) (A B) (hA hB) (hSide) (hAngle) :
  ∃ N (chain : Fin (N+1) → (Fin (n+1) → S2)),
    chain 0 = A ∧ chain (last N) = B ∧
    ∀ r, ∃ k δ, 0 ≤ δ ∧ HingeMove (chain r.castSucc) (chain r.succ) k δ ∧
      StrictConvexSphArm (chain r.castSucc) ∧ StrictConvexSphArm (chain r.succ)
```
Induct on n. **Base n=2**: one internal angle = spherical hinge lemma.
**Step**: if all angles equal ⟹ congruent by triangle reconstruction (distances equal).
Else pick internal joint k with deficit jointAngle A k < jointAngle B k; open A at k.
- **Case 1 (target reached)**: open until jointAngle A' k = jointAngle B k preserving
  convexity; reduce # unmatched angles; continue. Measure: lex (n, #unmatched).
- **Case 2 (stuck before target)**: convexity fails first when a previously strict
  support determinant hits zero: `sOrient (P i)(P(i+1))(P j) = 0`, i.e. `det3 u v w = 0`,
  some nonadjacent vertex on a supporting great circle. This gives a **diagonal cut**:
  ```lean
  lemma convex_stuck_gives_cut (hP : WeakConvexSphArm P)
    (hZero : sOrient (P i)(P(i+1))(P j) = 0) (hnonincident : j≠i ∧ j≠i+1) :
    ∃ left right, SmallerConvexArm left ∧ SmallerConvexArm right ∧ CutReduction P left right
  ```
  Apply IH to the two smaller arms, glue with the spherical hinge lemma. This is the
  exact spherical analogue of the planar "stuck case" — and it needs NO terminal-first
  identification (any stuck position, terminal or not, yields the cut).

### 8.5 Derive arm lemma from the opening chain
`spherical_arm_mono`: obtain chain; each step is nonnegative hinge opening
(`hinge_endpoint_mono`); chain the inequalities. Strict: ≥1 step has δ>0.

## 9. Vertex-link correspondence
`edgeDir P v i := unitVector (point(nbr v i) - point v)`, `vertexLink P v := edgeDir P v`.
- **9.1** `vertexLink_side_eq_faceAngle`: both = arccos⟪eᵢ,eⱼ⟫, cos inj on [0,π].
- **9.2** `vertexLink_angle_eq_dihedral`: sphAngle(link i-1, link i, link i+1) =
  interiorDihedral (projected-ray convention), nearly `rfl` with projOut.
- **9.3** `vertexLink_strictConvex`: supporting functional ℓ ⟹ all edge dirs in one
  open hemisphere; tangent cone convex; cone∩sphere geodesically convex; cyclic order
  ⟹ boundary ⟹ determinant inequalities. Reuse SectorSum cyclic infrastructure.
  Local certificate `VertexLinkCert` if global support not yet formalized.

## 10–13. Cauchy bridge + assembly
- `vertex_link_sides_equal_of_face_congruent`, `vertex_link_angles_eq_dihedrals`.
- `no_vertex_all_dihedral_diffs_same_sign`: pick strict joint r, remove a side not
  incident to r (always possible for ≥3 vertices), open arm, apply
  `spherical_arm_mono_strict` ⟹ endpoint(P_arm) < endpoint(Q_arm); but removed side
  lengths equal by face congruence ⟹ contradiction. Symmetric other half.
- `vertex_sign_sequence_has_at_least_four_changes` (delete zero signs).
- `cauchy_vertex_rule_from_spherical_links`, `all_dihedral_signs_zero`,
  `congruent_faces_and_equal_dihedrals_imply_rigid` (fix one face, propagate across
  adjacent faces; equal dihedrals determine next face uniquely on convex side),
  `cauchy_rigidity`.

## 14. Single hardest lemma + shortcut
Hardest = `spherical_arm_mono_strict` / its `spherical_SZ_opening_chain`. Recommended:
build all extrinsic machinery first, state the arm lemma with deps isolated, prove
Cauchy bridge against it, then fill the SZ hinge induction. Most reusable existing
code: TetDihedral.projOut (tangent angle/dihedral identity), SectorSum cyclic-order
infra (vertex-link convexity + cyclic sign sequences).

---

## Current Lean state (2026-06-06)

- Layers A–C, E (rotation): **built** (SphericalKernel, SphericalRotation, SphericalArm,
  SphericalCore, SphericalFinish, SphericalSZ, SphericalOpening, SphericalHinge).
- The arm lemma is **proven conditional on `OpeningData` = `HingeConvexPosition`**
  (SphericalFinish.schoenbergZaremba_of_openingData, SphericalHinge clean lemmas).
  `OpeningData` is exactly the single-step §8.4 opening obligation in geometric form
  (see SphericalFinish.lean:283). Discharging it = implementing §8.4 (the SZ opening
  chain / hinge induction + `convex_stuck_gives_cut`) ⟹ unconditional arm lemma.
- Layer G–I (vertex links + Cauchy bridge §9–§13): **frontier**, stated as
  `VertexLinkCorrespondence` (SphericalHinge.lean:352).
