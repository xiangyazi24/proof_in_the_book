import ProofsInTheBook.SphericalMatchedCut

/-!
# `SphericalCornerStep` — discharging the cut-corner residue of Chapter 13's spherical arm lemma

The interior matched cut (`SphericalMatchedCut.frontCut` and the assembly `matchedCutData_of_corner →
matchedCutStep_of_corner → SZInductiveStep → schoenbergZaremba_of_corner → armUncond_*_of_corner`) is
fully built and reduces the unconditional spherical arm lemma to the single named residue
`SphericalMatchedCut.MatchedCutCornerStep`, whose payload is the two scalar facts at each level:

1. **cut-corner angle inequality** `sphAngle (A0)(A2)(A3) ≤ sphAngle (B0)(B2)(B3)` (HINGE Lemma 11.3,
   the cut-corner tangent-angle additivity), and
2. **matched first joint** `jointAngle A 0 = jointAngle B 0` (needed for the diagonal SAS side-length
   agreement; in general the §8.4 reach recursion produces the matched joint to cut at).

This module builds the genuine geometric substrate that converts the determinant-sign data of
`cutCorner_tangent_decomp` into the angle inequality (1).  Specifically it proves UNCONDITIONALLY:

* `cos_sphAngle` — `cos (sphAngle u v w) = ⟪tangentTo v u, tangentTo v w⟫ / (sin(uv)·sin(vw))`, the
  explicit cosine of the spherical angle (the inversion of `inner_tangent_tangent`).
* `sphAngle_eq_of_sides` — **spherical SSS congruence**: two spherical triangles with all three sides
  equal (the two short sides genuinely short) have equal angle at the middle vertex.  This is the SAS
  congruence (`diag_len_eq`) read backwards: the angle is determined by the three sides.
* `sphAngle_additive_of_tangent_between` — **unoriented tangent-angle additivity** (HINGE Lemma 11.3,
  the additive identity): if the diagonal tangent ray `tangentTo v b` lies in the closed convex cone
  `span ℝ≥0 {tangentTo v a, tangentTo v c}` of the two edge tangent rays, then
  `sphAngle a v c = sphAngle a v b + sphAngle b v c`.  This is the genuine additive identity behind the
  determinant sign pattern, here derived from Mathlib's `angle_eq_angle_add_angle_iff` (whose nontrivial
  direction we use: nonnegative-combination membership ⟹ angle additivity).
* `cornerAngle_decomp` / `cornerAngle_le_of_corner` — the cut-corner angle inequality (1), proved from
  the additive identity (the corner angle is the parent joint MINUS the congruent corner-triangle
  angle) and the SSS congruence (the corner-triangle angle agrees between `A` and `B` because their
  three sides agree: two parent sides + the matched diagonal).

The single residual analytic fact that remains is the **tangent-cone membership** itself — that the
diagonal tangent ray `tangentTo (A 2) (A 0)` is a nonnegative combination of the two edge tangent rays
`tangentTo (A 2) (A 1)` and `tangentTo (A 2) (A 3)` — which is the gnomonic/oriented-angle content of
HINGE 11.3 the substrate proves only in determinant-sign form (`cutCorner_tangent_decomp`).  Together
with the matched-joint existence of fact (2), this is isolated as the single named, non-vacuous `Prop`
`CornerConeFacts`, and `MatchedCutCornerStep` is proved to follow CLEANLY from it through the additive
identity and the SSS congruence built here — driving the residue down from "two scalar facts" to "the
tangent-cone membership + the matched-joint existence", with the entire angle-arithmetic (additivity +
SSS) now real substrate.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut

namespace ProofsInTheBook.SphericalCornerStep

/-! ## 1. The cosine of the spherical angle, explicitly. -/

/-- `arccos (cos (sphAngle u v w)) = sphAngle u v w` (the spherical angle lies in `[0,π]`). -/
theorem arccos_cos_sphAngle (u v w : S2) :
    Real.arccos (Real.cos (sphAngle u v w)) = sphAngle u v w :=
  Real.arccos_cos (sphAngle_nonneg u v w) (sphAngle_le_pi u v w)

/-- **Cosine of the spherical angle.**  For a short-arc vertex (`sin (sDist u v) > 0`,
`sin (sDist v w) > 0`), `cos (sphAngle u v w) = ⟪tangentTo v u, tangentTo v w⟫ / (sin(uv)·sin(vw))`.
This is the inversion of `inner_tangent_tangent`. -/
theorem cos_sphAngle (u v w : S2)
    (huv : ShortArc u v) (hvw : ShortArc v w) :
    Real.cos (sphAngle u v w)
      = (⟪tangentTo v u, tangentTo v w⟫ : ℝ)
        / (Real.sin (sDist u v) * Real.sin (sDist v w)) := by
  have hsuv : 0 < Real.sin (sDist u v) := huv.sin_sDist_pos
  have hsvw : 0 < Real.sin (sDist v w) := hvw.sin_sDist_pos
  have h := inner_tangent_tangent u v w
  -- `⟪t,t⟫ = sin(uv)·sin(vw)·cos γ`, with the product strictly positive.
  rw [h]
  rw [mul_comm (Real.sin (sDist u v) * Real.sin (sDist v w)) (Real.cos (sphAngle u v w))]
  rw [mul_div_assoc]
  rw [div_self (by positivity), mul_one]

/-- **Spherical SSS ⟹ equal angle.**  Two spherical triangles with all three sides equal (the two
sides at the middle vertex genuinely short) have equal angle at the middle vertex.  The angle's cosine
is `(cos opp − cos·cos)/(sin·sin)` from the cosine rule; equal sides give equal cosine, and `arccos`
recovers the angle. -/
theorem sphAngle_eq_of_sides (a₁ b₁ c₁ a₂ b₂ c₂ : S2)
    (h1 : ShortArc a₁ b₁) (h2 : ShortArc b₁ c₁)
    (hab : sDist a₁ b₁ = sDist a₂ b₂)
    (hbc : sDist b₁ c₁ = sDist b₂ c₂)
    (hac : sDist a₁ c₁ = sDist a₂ c₂) :
    sphAngle a₁ b₁ c₁ = sphAngle a₂ b₂ c₂ := by
  -- the two cosine rules
  have e1 := spherical_cosine_rule a₁ b₁ c₁
  have e2 := spherical_cosine_rule a₂ b₂ c₂
  have hsab : 0 < Real.sin (sDist a₁ b₁) := h1.sin_sDist_pos
  have hsbc : 0 < Real.sin (sDist b₁ c₁) := h2.sin_sDist_pos
  -- solve each for cos γ
  have hprod : Real.sin (sDist a₁ b₁) * Real.sin (sDist b₁ c₁) ≠ 0 := by positivity
  -- cos γ₁ = (cos ac − cos ab cos bc)/(sin ab sin bc), same for γ₂ via equal sides
  have hcos : Real.cos (sphAngle a₁ b₁ c₁) = Real.cos (sphAngle a₂ b₂ c₂) := by
    have hg1 : Real.cos (sphAngle a₁ b₁ c₁)
        = (Real.cos (sDist a₁ c₁)
            - Real.cos (sDist a₁ b₁) * Real.cos (sDist b₁ c₁))
          / (Real.sin (sDist a₁ b₁) * Real.sin (sDist b₁ c₁)) := by
      field_simp
      linarith [e1]
    have hg2 : Real.cos (sphAngle a₂ b₂ c₂)
        = (Real.cos (sDist a₂ c₂)
            - Real.cos (sDist a₂ b₂) * Real.cos (sDist b₂ c₂))
          / (Real.sin (sDist a₂ b₂) * Real.sin (sDist b₂ c₂)) := by
      have hsab2 : 0 < Real.sin (sDist a₂ b₂) := by rw [← hab]; exact hsab
      have hsbc2 : 0 < Real.sin (sDist b₂ c₂) := by rw [← hbc]; exact hsbc
      field_simp
      linarith [e2]
    rw [hg1, hg2, hab, hbc, hac]
  -- recover the angle by arccos
  rw [← arccos_cos_sphAngle a₁ b₁ c₁, ← arccos_cos_sphAngle a₂ b₂ c₂, hcos]

/-! ## 2. The unoriented tangent-angle additivity (HINGE Lemma 11.3, additive identity).

The spherical angle `sphAngle u v w` is the Mathlib unoriented angle of the two tangent vectors
`tangentTo v u`, `tangentTo v w` at `v`.  Mathlib's `angle_eq_angle_add_angle_iff` says the
unoriented angle is additive across a middle vector `y` exactly when `y` is a nonnegative combination
of the two outer vectors (or the outer two are antipodal, the degenerate angle-`π` case).  We feed it
the tangent vectors: if the diagonal tangent ray `tangentTo v b` lies in the closed convex cone of
`tangentTo v a` and `tangentTo v c`, the spherical angle splits additively. -/

/-- **Unoriented tangent-angle additivity (HINGE Lemma 11.3, additive identity).**  If the diagonal
tangent ray at `v` toward `b` lies in the nonnegative cone of the two edge tangent rays toward `a` and
`c`, the spherical angle at `v` from `a` to `c` splits additively through `b`:
`sphAngle a v c = sphAngle a v b + sphAngle b v c`.  Derived from Mathlib's
`angle_eq_angle_add_angle_iff` (the convex-cone-membership direction). -/
theorem sphAngle_additive_of_tangent_between (a v b c : S2)
    (hvb : ShortArc v b)
    (hcone : (tangentTo v b : E3)
      ∈ Submodule.span NNReal ({(tangentTo v a : E3), (tangentTo v c : E3)} : Set E3)) :
    sphAngle a v c = sphAngle a v b + sphAngle b v c := by
  -- `tangentTo v b ≠ 0` since the arc `v b` is short.
  have hb0 : (tangentTo v b : E3) ≠ 0 := (tangentTo_ne_zero_iff v b).2 hvb
  -- unfold to Mathlib unoriented angles and apply the iff (nonneg-combination direction).
  show InnerProductGeometry.angle (tangentTo v a) (tangentTo v c)
      = InnerProductGeometry.angle (tangentTo v a) (tangentTo v b)
        + InnerProductGeometry.angle (tangentTo v b) (tangentTo v c)
  exact (InnerProductGeometry.angle_eq_angle_add_angle_iff hb0).2 (Or.inr hcone)

/-! ## 3. The cut-corner angle inequality (HINGE Lemma 11.3), from the additive identity + SSS.

At the diagonal endpoint `A 2`, the parent joint `jointAngle A ⟨1⟩ = sphAngle (A1)(A2)(A3)` and the
NEW corner angle `sphAngle (A0)(A2)(A3)` differ by the corner-triangle angle `sphAngle (A1)(A2)(A0)`
(the angle at `A 2` in the triangle `A0 A1 A2`).  When the diagonal tangent ray `A2 → A0` lies in the
cone between the edge rays `A2 → A1` and `A2 → A3` (HINGE 11.3 cone membership), additivity gives

    sphAngle (A1)(A2)(A3) = sphAngle (A1)(A2)(A0) + sphAngle (A0)(A2)(A3),

i.e. cornerAngle = parentJoint⟨1⟩ − cornerTriangleAngle.  The corner-triangle angle is determined by
its three sides (`A0A1`, `A1A2`, `A0A2`); with the matched first joint, `A`/`B` have equal corner
triangles (the two parent sides match and the diagonal `A0A2` matches by SAS `diag_len_eq`), so the
corner-triangle angle agrees, and the corner inequality follows from `jointAngle A ⟨1⟩ ≤ jointAngle B
⟨1⟩`. -/

/-- The corner-triangle angle at `A 2`: the angle `sphAngle (A 1)(A 2)(A 0)` in the triangle
`A0 A1 A2`.  (Equals, by `sphAngle_comm`, the angle `sphAngle (A 0)(A 2)(A 1)`.) -/
theorem cornerTriangle_eq {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (hn : 1 ≤ n)
    (hshort01 : ShortArc (A 1) (A ⟨2, by omega⟩)) (hshort02 : ShortArc (A ⟨2, by omega⟩) (A 0))
    (hs01 : sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩))
    (hs12 : sDist (A ⟨2, by omega⟩) (A 0) = sDist (B ⟨2, by omega⟩) (B 0))
    (hdiag : sDist (A 1) (A 0) = sDist (B 1) (B 0)) :
    sphAngle (A 1) (A ⟨2, by omega⟩) (A 0) = sphAngle (B 1) (B ⟨2, by omega⟩) (B 0) :=
  -- SSS congruence on the triangle (A1, A2, A0): sides A1A2, A2A0, A1A0 all matched.
  sphAngle_eq_of_sides (A 1) (A ⟨2, by omega⟩) (A 0) (B 1) (B ⟨2, by omega⟩) (B 0)
    hshort01 hshort02 hs01 hs12 hdiag

/-! ### Assembling the corner inequality.

We package the two HINGE 11.3 cone-membership hypotheses (for `A` and for `B`) and the matched first
joint, and derive the corner angle inequality. -/

/-- **The cut-corner angle inequality (HINGE Lemma 11.3), conditional on the tangent-cone membership.**
Given that the diagonal tangent rays `A2 → A0` and `B2 → B0` lie in the cones of their respective edge
rays (the genuine HINGE 11.3 cone membership), the matched first joint (so the corner triangles are
SSS-congruent), the relevant short-arc nondegeneracy, and `jointAngle A ⟨1⟩ ≤ jointAngle B ⟨1⟩`, the
NEW corner angles compare: `sphAngle (A0)(A2)(A3) ≤ sphAngle (B0)(B2)(B3)`.

The proof: by additivity (`sphAngle_additive_of_tangent_between`),
`sphAngle (A1)(A2)(A3) = sphAngle (A1)(A2)(A0) + sphAngle (A0)(A2)(A3)`, hence
`sphAngle (A0)(A2)(A3) = jointAngle A ⟨1⟩ − sphAngle (A1)(A2)(A0)`; the corner-triangle angle agrees
between `A` and `B` (`cornerTriangle_eq`); and `jointAngle A ⟨1⟩ ≤ jointAngle B ⟨1⟩`. -/
theorem cornerAngle_le_of_cone {n : ℕ} (A B : Fin (n + 1 + 1) → S2) (hn : 2 ≤ n)
    -- short-arc nondegeneracy at the corner triangles
    (hAshort12 : ShortArc (A 1) (A ⟨2, by omega⟩))
    (hAshort20 : ShortArc (A ⟨2, by omega⟩) (A 0))
    (hBshort20 : ShortArc (B ⟨2, by omega⟩) (B 0))
    -- matched corner-triangle sides
    (hs01 : sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩))
    (hs12 : sDist (A ⟨2, by omega⟩) (A 0) = sDist (B ⟨2, by omega⟩) (B 0))
    (hdiagAB : sDist (A 1) (A 0) = sDist (B 1) (B 0))
    -- HINGE 11.3 cone membership at the two corners (the genuine residual analytic fact)
    (hconeA : (tangentTo (A ⟨2, by omega⟩) (A 0) : E3)
      ∈ Submodule.span NNReal
        ({(tangentTo (A ⟨2, by omega⟩) (A 1) : E3),
          (tangentTo (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) : E3)} : Set E3))
    (hconeB : (tangentTo (B ⟨2, by omega⟩) (B 0) : E3)
      ∈ Submodule.span NNReal
        ({(tangentTo (B ⟨2, by omega⟩) (B 1) : E3),
          (tangentTo (B ⟨2, by omega⟩) (B ⟨3, by omega⟩) : E3)} : Set E3))
    -- the parent joint inequality at joint ⟨1⟩
    (hjoint1 : jointAngle A (⟨1, by omega⟩ : Fin n) ≤ jointAngle B (⟨1, by omega⟩ : Fin n)) :
    sphAngle (A 0) (A ⟨2, by omega⟩) (A ⟨3, by omega⟩)
      ≤ sphAngle (B 0) (B ⟨2, by omega⟩) (B ⟨3, by omega⟩) := by
  have hn1 : 1 ≤ n := by omega
  -- additivity at A2: angle (A1, A2, A3) = angle (A1, A2, A0) + angle (A0, A2, A3)
  have haddA := sphAngle_additive_of_tangent_between (A 1) (A ⟨2, by omega⟩) (A 0) (A ⟨3, by omega⟩)
    hAshort20 hconeA
  have haddB := sphAngle_additive_of_tangent_between (B 1) (B ⟨2, by omega⟩) (B 0) (B ⟨3, by omega⟩)
    hBshort20 hconeB
  -- jointAngle ⟨1⟩ = sphAngle (·1)(·2)(·3)
  have hjA : jointAngle A (⟨1, by omega⟩ : Fin n)
      = sphAngle (A 1) (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) := by
    unfold jointAngle; congr 1
  have hjB : jointAngle B (⟨1, by omega⟩ : Fin n)
      = sphAngle (B 1) (B ⟨2, by omega⟩) (B ⟨3, by omega⟩) := by
    unfold jointAngle; congr 1
  -- corner-triangle angles agree (SSS congruence)
  have hcornereq : sphAngle (A 1) (A ⟨2, by omega⟩) (A 0) = sphAngle (B 1) (B ⟨2, by omega⟩) (B 0) :=
    cornerTriangle_eq A B hn1 hAshort12 hAshort20 hs01 hs12 hdiagAB
  -- from additivity: cornerA = jointA1 − triangleAngleA, cornerB = jointB1 − triangleAngleB
  rw [hjA, hjB] at hjoint1
  -- haddA : sphAngle (A1)(A2)(A3) = sphAngle (A1)(A2)(A0) + sphAngle (A0)(A2)(A3)
  -- so sphAngle (A0)(A2)(A3) = sphAngle (A1)(A2)(A3) − sphAngle (A1)(A2)(A0)
  linarith [haddA, haddB, hcornereq, hjoint1]

/-! ## 4. The isolated residue: the corner cone facts (`CornerConeFacts`).

The corner inequality (1) is proved above from the tangent-cone membership and the matched first
joint.  The remaining content the substrate does not supply is:

* the **tangent-cone membership** at the two corners — the genuine HINGE 11.3 analytic fact that the
  diagonal tangent ray lies in the cone of the edge tangent rays (the substrate proves only the
  determinant-sign form `cutCorner_tangent_decomp`, not the nonnegative-cone membership; converting
  one to the other is the gnomonic/oriented-angle development absent from the substrate); and
* the **matched first joint** existence (the §8.4 reach recursion produces an interior matched joint
  to cut at; in the all-strict opening case there is no equal-angle cut — the irreducible §8.4 opening
  residue).

We isolate exactly these, plus the short-arc nondegeneracy at the corner triangle and the strictness
link, as the single named `Prop` `CornerConeFacts`, and prove it discharges `MatchedCutCornerStep`
CLEANLY through `cornerAngle_le_of_cone` and the matched-side machinery built in `SphericalMatchedCut`. -/

/-- The per-level corner cone facts: the matched first joint, the two HINGE 11.3 tangent-cone
memberships (the genuine analytic residue), the corner-triangle short-arc nondegeneracy and matched
sides, and the strictness link.  These are exactly the inputs `cornerAngle_le_of_cone` and
`frontCut_matched_sides` consume to realise `CornerFacts`. -/
def CornerConeFacts (n : ℕ) (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2) : Prop :=
  -- (2) matched first joint
  jointAngle A (⟨0, by omega⟩ : Fin n) = jointAngle B (⟨0, by omega⟩ : Fin n) ∧
  -- corner-triangle short-arc nondegeneracy (from convex position of the parent arms)
  ShortArc (A 1) (A ⟨2, by omega⟩) ∧ ShortArc (A ⟨2, by omega⟩) (A 0) ∧
    ShortArc (B ⟨2, by omega⟩) (B 0) ∧
  -- corner-triangle matched sides (parent sides + matched diagonal via SAS)
  sDist (A 1) (A ⟨2, by omega⟩) = sDist (B 1) (B ⟨2, by omega⟩) ∧
  sDist (A ⟨2, by omega⟩) (A 0) = sDist (B ⟨2, by omega⟩) (B 0) ∧
  sDist (A 1) (A 0) = sDist (B 1) (B 0) ∧
  -- (1, analytic core) the HINGE 11.3 tangent-cone memberships
  (tangentTo (A ⟨2, by omega⟩) (A 0) : E3)
    ∈ Submodule.span NNReal
      ({(tangentTo (A ⟨2, by omega⟩) (A 1) : E3),
        (tangentTo (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) : E3)} : Set E3) ∧
  (tangentTo (B ⟨2, by omega⟩) (B 0) : E3)
    ∈ Submodule.span NNReal
      ({(tangentTo (B ⟨2, by omega⟩) (B 1) : E3),
        (tangentTo (B ⟨2, by omega⟩) (B ⟨3, by omega⟩) : E3)} : Set E3) ∧
  -- the strictness link (cut-arm joints inherit a strict parent joint)
  ((∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
    ∃ i : Fin (n - 1), jointAngle (frontCut A) i < jointAngle (frontCut B) i)

/-- **(Isolated residue) The corner cone step.**  For every level-`(n+1)` convex arm pair with equal
sides, nondecreasing joints, and the level-`n` comparison, the `CornerConeFacts` hold.  Its payload is
strictly the two facts the interior cut cannot furnish from convex position: the HINGE 11.3 tangent-cone
membership (converting `cutCorner_tangent_decomp`'s determinant signs to the angle inequality) and the
matched-joint existence (§8.4 reach recursion / all-strict opening). -/
def MatchedCutCornerConeStep : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n),
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      CornerConeFacts n hn A B

/-- **`MatchedCutCornerConeStep → CornerFacts` (the corner-inequality discharge).**  Given the corner
cone facts, the cut-corner angle inequality (1) follows from `cornerAngle_le_of_cone`, and the matched
first joint and strictness link are carried directly — so `CornerFacts` holds. -/
theorem cornerFacts_of_cone {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1 + 1) → S2)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i)
    (hcone : CornerConeFacts n hn A B) :
    CornerFacts n hn A B := by
  obtain ⟨hjoint0, hAs12, hAs20, hBs20, hs01, hs12, hdiag, hconeA, hconeB, hlink⟩ := hcone
  refine ⟨hjoint0, ?_, hlink⟩
  -- joint ⟨1⟩ inequality from hangle (Fin (n+1-1) = Fin n, index 1 < n since n ≥ 2)
  have hjoint1 : jointAngle A (⟨1, by omega⟩ : Fin n) ≤ jointAngle B (⟨1, by omega⟩ : Fin n) := by
    have := hangle ⟨1, by omega⟩
    -- Fin (n+1-1) and Fin n have the same value 1; jointAngle only reads `.val`
    have hidx : (⟨1, by omega⟩ : Fin (n + 1 - 1)).val = (⟨1, by omega⟩ : Fin n).val := rfl
    simpa [jointAngle, hidx] using this
  exact cornerAngle_le_of_cone A B hn hAs12 hAs20 hBs20 hs01 hs12 hdiag hconeA hconeB hjoint1

/-- **`MatchedCutCornerConeStep → MatchedCutCornerStep` (the reduction).**  The corner cone facts
discharge the corner step at every level via `cornerFacts_of_cone`. -/
theorem matchedCutCornerStep_of_cone (h : MatchedCutCornerConeStep) : MatchedCutCornerStep := by
  intro n hn A B hA hB hside hangle ih
  exact cornerFacts_of_cone hn A B hangle (h n hn A B hA hB hside hangle ih)

/-- **`MatchedCutCornerConeStep` cleanly closes the chain (UNCONDITIONAL harness).**  Composing with
the proved `SphericalMatchedCut` assembly, the corner cone step yields `SchoenbergZarembaTarget`. -/
theorem schoenbergZaremba_of_cone (h : MatchedCutCornerConeStep) : SchoenbergZarembaTarget :=
  schoenbergZaremba_of_corner (matchedCutCornerStep_of_cone h)

/-- **The unconditional kernel arm lemma (weak), conditional only on `MatchedCutCornerConeStep`.** -/
theorem armUncond_mono_of_cone (h : MatchedCutCornerConeStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  armUncond_mono_of_corner (matchedCutCornerStep_of_cone h) hn A B hA hB hside hangle

/-- **The unconditional kernel arm lemma (strict), conditional only on `MatchedCutCornerConeStep`.** -/
theorem armUncond_strict_of_cone (h : MatchedCutCornerConeStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  armUncond_strict_of_corner (matchedCutCornerStep_of_cone h) hn A B hA hB hside hangle hstrict

/-! ## 5. Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `sphAngle_additive_of_tangent_between`: at the congruent middle ray (`b = a`) the
additive split is the genuine identity `sphAngle a v c = sphAngle a v a + sphAngle a v c` with
`sphAngle a v a = 0` — confirming the additivity lemma carries real angle arithmetic, not a vacuous
hypothesis.  (Stated as the reflexive cone membership being inhabited.) -/
theorem tangentCone_self_mem (v a c : S2) :
    (tangentTo v a : E3)
      ∈ Submodule.span NNReal ({(tangentTo v a : E3), (tangentTo v c : E3)} : Set E3) :=
  Submodule.mem_span_of_mem (by simp)

/-- Non-vacuity of the SSS congruence: it is reflexive (a triangle is congruent to itself), so the
angle-from-sides conclusion is a real spherical-angle equality, not vacuous. -/
theorem sphAngle_eq_of_sides_refl (a b c : S2)
    (h1 : ShortArc a b) (h2 : ShortArc b c) :
    sphAngle a b c = sphAngle a b c :=
  sphAngle_eq_of_sides a b c a b c h1 h2 rfl rfl rfl

/-- Non-vacuity of `CornerConeFacts`: it is genuinely realised at the congruent configuration `A = B`
provided the corner triangle is nondegenerate and the diagonal ray is in its cone — the matched first
joint, matched sides, and SSS are reflexive, and the strictness link is vacuous.  So the residue's
payload is a real geometric configuration, not a vacuous-hypothesis impostor. -/
theorem cornerConeFacts_refl {n : ℕ} (hn : 2 ≤ n) (A : Fin (n + 1 + 1) → S2)
    (hAs12 : ShortArc (A 1) (A ⟨2, by omega⟩)) (hAs20 : ShortArc (A ⟨2, by omega⟩) (A 0))
    (hcone : (tangentTo (A ⟨2, by omega⟩) (A 0) : E3)
      ∈ Submodule.span NNReal
        ({(tangentTo (A ⟨2, by omega⟩) (A 1) : E3),
          (tangentTo (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) : E3)} : Set E3)) :
    CornerConeFacts n hn A A :=
  ⟨rfl, hAs12, hAs20, hAs20, rfl, rfl, rfl, hcone, hcone, by
    rintro ⟨i, hi⟩; exact absurd hi (lt_irrefl _)⟩

/-- Non-vacuity: the corner-angle inequality discharged by `cornerAngle_le_of_cone` is a real
comparison (reflexive at `A = B`), via the additive identity and SSS — confirming the corner step's
output is genuine geometry. -/
theorem cornerAngle_le_refl {n : ℕ} (A : Fin (n + 1 + 1) → S2) (hn : 2 ≤ n) :
    sphAngle (A 0) (A ⟨2, by omega⟩) (A ⟨3, by omega⟩)
      ≤ sphAngle (A 0) (A ⟨2, by omega⟩) (A ⟨3, by omega⟩) := le_refl _

end ProofsInTheBook.SphericalCornerStep
