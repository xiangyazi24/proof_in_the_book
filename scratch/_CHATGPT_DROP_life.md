# Ch13 Route B finite convex-position lemma: four cyclic points give a positive Radon relation

This is the finite planar lemma needed for the four-point contradiction in the cyclic-flip route.  It is deliberately stated in `ℝ²` with an explicit determinant.  The landed vertex-link code should instantiate it by choosing the landed affine plane / oriented angular frame and transporting the repo's `det3` or `cyclicTriple` positivity to the planar orientation predicate `orient2` below.

The proof does **not** use turning number, Jordan curve, Umlaufsatz, or topology.  It is the affine Grassmann/Radon identity for four planar points:

```text
[BCD] A + [DAB] C = [CDA] B + [ABC] D,
```

where `[XYZ]` is the oriented doubled area `orient2 X Y Z`.  If the cyclic order is strictly convex, the four cyclic areas `[ABC]`, `[BCD]`, `[CDA]`, `[DAB]` are all strictly positive, so this identity is exactly a positive Radon relation between the two diagonals.  Applying a linear functional immediately rules out the alternating halfspace patterns.

```lean
import Mathlib

noncomputable section

open scoped BigOperators

namespace ProofsInTheBook.Ch13FiniteConvexPosition

/-- A concrete planar point.  This avoids any dependency on affine-space API;
all proofs are coordinate `ring` proofs. -/
abbrev P2 : Type := Fin 2 → ℝ

/-- The planar determinant / oriented area form. -/
def det2 (u v : P2) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- Oriented doubled area of the triangle `(a,b,c)`. -/
def orient2 (a b c : P2) : ℝ :=
  det2 (b - a) (c - a)

/-- A concrete dot product, used only for the halfspace corollary. -/
def dot2 (u v : P2) : ℝ :=
  u 0 * v 0 + u 1 * v 1

@[simp] theorem dot2_smul_add_smul (g x y : P2) (rx ry : ℝ) :
    dot2 g (rx • x + ry • y) = rx * dot2 g x + ry * dot2 g y := by
  simp [dot2]
  ring

/-- The affine Grassmann/Radon identity for four planar points.

Written with cyclic labels `a,b,c,d`, this says
`[BCD] A + [DAB] C = [CDA] B + [ABC] D`.  No convexity is used here; it is a
coordinate identity. -/
theorem radon_identity_orient2 (a b c d : P2) :
    orient2 b c d • a + orient2 d a b • c =
      orient2 c d a • b + orient2 a b c • d := by
  ext i
  fin_cases i <;>
    simp [orient2, det2]
    <;> ring

/-- The matching mass identity for the same four coefficients:
`[BCD] + [DAB] = [CDA] + [ABC]`.  This is what makes the Radon relation affine;
dividing by this positive common mass gives the normalized diagonal intersection. -/
theorem radon_mass_identity_orient2 (a b c d : P2) :
    orient2 b c d + orient2 d a b = orient2 c d a + orient2 a b c := by
  simp [orient2, det2]
  ring

/-- Strict cyclic convex position of four points, in the minimal form needed here:
each cyclic triple has positive oriented area. -/
def StrictCyclicFour (a b c d : P2) : Prop :=
  0 < orient2 a b c ∧
  0 < orient2 b c d ∧
  0 < orient2 c d a ∧
  0 < orient2 d a b

/-- Four points in strict cyclic convex order have a positive unnormalized Radon
relation between the two diagonals.

The coefficients are explicitly

```text
λa = [BCD],  λc = [DAB],  λb = [CDA],  λd = [ABC].
```

They are all strictly positive under the cyclic-triple hypotheses, and their
left/right sums are equal. -/
theorem positive_radon_relation_of_strictCyclicFour
    {a b c d : P2} (h : StrictCyclicFour a b c d) :
    ∃ λa λc λb λd : ℝ,
      0 < λa ∧ 0 < λc ∧ 0 < λb ∧ 0 < λd ∧
      λa + λc = λb + λd ∧
      λa • a + λc • c = λb • b + λd • d := by
  rcases h with ⟨hABC, hBCD, hCDA, hDAB⟩
  refine ⟨orient2 b c d, orient2 d a b, orient2 c d a, orient2 a b c,
    hBCD, hDAB, hCDA, hABC, ?_, ?_⟩
  · exact radon_mass_identity_orient2 a b c d
  · exact radon_identity_orient2 a b c d

/-- Same theorem with the four cyclic positivity hypotheses exposed separately.
This is the shape most convenient when the caller has landed `cyclicTriple` or
`det3` positivity facts. -/
theorem positive_radon_relation_of_cyclic_orient2_pos
    {a b c d : P2}
    (hABC : 0 < orient2 a b c)
    (hBCD : 0 < orient2 b c d)
    (hCDA : 0 < orient2 c d a)
    (hDAB : 0 < orient2 d a b) :
    ∃ λa λc λb λd : ℝ,
      0 < λa ∧ 0 < λc ∧ 0 < λb ∧ 0 < λd ∧
      λa + λc = λb + λd ∧
      λa • a + λc • c = λb • b + λd • d := by
  exact positive_radon_relation_of_strictCyclicFour
    ⟨hABC, hBCD, hCDA, hDAB⟩

/-- Alternating halfspace pattern I is impossible:
`a,c` are strictly negative while `b,d` are nonnegative. -/
theorem no_alternating_halfspace_neg_nonneg_of_cyclic_orient2_pos
    {a b c d g : P2}
    (hABC : 0 < orient2 a b c)
    (hBCD : 0 < orient2 b c d)
    (hCDA : 0 < orient2 c d a)
    (hDAB : 0 < orient2 d a b)
    (ha : dot2 g a < 0) (hb : 0 ≤ dot2 g b)
    (hc : dot2 g c < 0) (hd : 0 ≤ dot2 g d) :
    False := by
  obtain ⟨λa, λc, λb, λd, hλa, hλc, hλb, hλd, _hmass, hrel⟩ :=
    positive_radon_relation_of_cyclic_orient2_pos hABC hBCD hCDA hDAB
  have hdot := congrArg (dot2 g) hrel
  have hlineq :
      λa * dot2 g a + λc * dot2 g c =
        λb * dot2 g b + λd * dot2 g d := by
    simpa using hdot
  have hleft_neg : λa * dot2 g a + λc * dot2 g c < 0 := by
    exact add_neg (mul_neg_of_pos_of_neg hλa ha)
      (mul_neg_of_pos_of_neg hλc hc)
  have hright_nonneg : 0 ≤ λb * dot2 g b + λd * dot2 g d := by
    exact add_nonneg (mul_nonneg (le_of_lt hλb) hb)
      (mul_nonneg (le_of_lt hλd) hd)
  have hright_neg : λb * dot2 g b + λd * dot2 g d < 0 := by
    rwa [hlineq] at hleft_neg
  exact not_lt_of_ge hright_nonneg hright_neg

/-- Alternating halfspace pattern II is impossible:
`a,c` are nonnegative while `b,d` are strictly negative.  This is the swapped
version used when the Bool values are reversed. -/
theorem no_alternating_halfspace_nonneg_neg_of_cyclic_orient2_pos
    {a b c d g : P2}
    (hABC : 0 < orient2 a b c)
    (hBCD : 0 < orient2 b c d)
    (hCDA : 0 < orient2 c d a)
    (hDAB : 0 < orient2 d a b)
    (ha : 0 ≤ dot2 g a) (hb : dot2 g b < 0)
    (hc : 0 ≤ dot2 g c) (hd : dot2 g d < 0) :
    False := by
  obtain ⟨λa, λc, λb, λd, hλa, hλc, hλb, hλd, _hmass, hrel⟩ :=
    positive_radon_relation_of_cyclic_orient2_pos hABC hBCD hCDA hDAB
  have hdot := congrArg (dot2 g) hrel
  have hlineq :
      λa * dot2 g a + λc * dot2 g c =
        λb * dot2 g b + λd * dot2 g d := by
    simpa using hdot
  have hleft_nonneg : 0 ≤ λa * dot2 g a + λc * dot2 g c := by
    exact add_nonneg (mul_nonneg (le_of_lt hλa) ha)
      (mul_nonneg (le_of_lt hλc) hc)
  have hright_neg : λb * dot2 g b + λd * dot2 g d < 0 := by
    exact add_neg (mul_neg_of_pos_of_neg hλb hb)
      (mul_neg_of_pos_of_neg hλd hd)
  have hleft_neg : λa * dot2 g a + λc * dot2 g c < 0 := by
    rwa [← hlineq] at hright_neg
  exact not_lt_of_ge hleft_nonneg hleft_neg

end ProofsInTheBook.Ch13FiniteConvexPosition
```

## How the Route B caller instantiates this

In the landed link plane, choose the oriented 2D coordinate frame already used by `rayAngleKey` / `ProjectedAngleInjective`, and define

```lean
toP2 : E3 → P2
```

by the two coordinates in that frame.  The caller needs the standard orientation-transport lemma:

```lean
orient2 (toP2 qa) (toP2 qb) (toP2 qc) > 0
```

from the repo's landed `cyclicTriple` / `det3` positivity fact, for the four cyclic triples `(a,b,c)`, `(b,c,d)`, `(c,d,a)`, `(d,a,b)`.  In the current Route B naming, this is the same bridge family as the gnomonic/landed orientation facts: `sOrient_pos_iff_planar_pos`, `gnomonic_consecutive_turn_pos`, and the affine determinant identity used to pass between `det3 axis (edge_i) (edge_{i+1})` and point-triple orientation.

After that, apply one of the two corollaries above to the planar functional

```lean
g₂ := toP2 g
```

or, equivalently, prove `dot2 g₂ (toP2 q) = ⟪g, q⟫` for the landed points and rewrite.  The contradiction is then exactly the alternating halfspace contradiction needed by the cyclic-flips `> 2` four-point proof.
