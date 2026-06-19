# Ch13 Route B finite convex-position lemma: four cyclic points give a positive Radon relation

This file is the requested drop for the finite four-point convex-position residue feeding the cyclic-flips four-point proof.  The proof is deliberately **pure affine/determinant algebra**.  It uses no turning number, no Umlaufsatz, no Jordan curve theorem, and no topology.

The clean Lean route is to state the lemma in an oriented affine chart `P2 := Fin 2 → ℝ`.  The caller obtains the four hypotheses

```lean
0 < orient2 qa qb qc
0 < orient2 qb qc qd
0 < orient2 qc qd qa
0 < orient2 qd qa qb
```

from the landed `det3`/`cyclicTriple` positivity after choosing the link plane coordinates.  In the current repo vocabulary, the relevant upstream objects are:

* `ProofsInTheBook.SphericalCyclicTriple.CyclicTriplePos` for cyclic-triple positivity of spherical/link triples;
* `ProofsInTheBook.SphericalGnomonic.gproj` and the gnomonic sign-correspondence layer for transporting `sOrient`/`det3` signs to a planar chart;
* `ProofsInTheBook.PlanarConvexDiag.planarConvexDiagPos_holds` when the four facts are obtained from a strict planar convex-position polygon.

The algebraic engine is the four-point Grassmann/Radon identity

```text
[BCD] A + [DAB] C = [CDA] B + [ABC] D,
```

where `[XYZ]` means the oriented doubled area `orient2 X Y Z`.  In strict cyclic order all four coefficients `[ABC]`, `[BCD]`, `[CDA]`, `[DAB]` are positive.  The matching mass identity

```text
[BCD] + [DAB] = [CDA] + [ABC]
```

lets us divide by the common positive mass and get the normalized diagonal-intersection statement: the open segment `AC` meets the open segment `BD`.

```lean
import Mathlib

noncomputable section

namespace ProofsInTheBook.Ch13FiniteConvexPosition

/-- A concrete planar affine chart.  This avoids any dependency on affine-space API;
all determinant identities below are coordinate `ring` proofs. -/
abbrev P2 : Type := Fin 2 → ℝ

/-- The planar determinant / signed doubled area form on displacement vectors. -/
def det2 (u v : P2) : ℝ :=
  u 0 * v 1 - u 1 * v 0

/-- Oriented doubled area of the triangle `(a,b,c)`. -/
def orient2 (a b c : P2) : ℝ :=
  det2 (b - a) (c - a)

/-- A concrete dot product, used only for the halfspace corollary. -/
def dot2 (u v : P2) : ℝ :=
  u 0 * v 0 + u 1 * v 1

/-- The linear functional `x ↦ dot2 g x`.  The generic contradiction theorem below is
stated for an arbitrary linear map; this is the immediate specialization for halfspaces. -/
def dot2Lin (g : P2) : P2 →ₗ[ℝ] ℝ where
  toFun x := dot2 g x
  map_add' := by
    intro x y
    simp [dot2]
    ring
  map_smul' := by
    intro r x
    simp [dot2]
    ring

@[simp] theorem dot2Lin_apply (g x : P2) : dot2Lin g x = dot2 g x := rfl

/-- The affine Grassmann/Radon identity for four planar points.

Written with cyclic labels `a,b,c,d`, this says
`[BCD] A + [DAB] C = [CDA] B + [ABC] D`.
No convexity is used here; it is a coordinate identity. -/
theorem radon_identity_orient2 (a b c d : P2) :
    orient2 b c d • a + orient2 d a b • c =
      orient2 c d a • b + orient2 a b c • d := by
  ext i
  fin_cases i
  · simp [orient2, det2]
    ring
  · simp [orient2, det2]
    ring

/-- The matching mass identity for the same four coefficients:
`[BCD] + [DAB] = [CDA] + [ABC]`.

This is what makes the Radon relation affine; after division by this positive common
mass, both sides have total coefficient `1`. -/
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

/-- Four points in strict cyclic convex order have a positive **unnormalized** Radon
relation between the two diagonals.

The coefficients are explicitly

```text
λa = [BCD],  λc = [DAB],  λb = [CDA],  λd = [ABC].
```

They are all strictly positive under the cyclic-triple hypotheses, and their left/right
sums are equal. -/
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

/-- Same positive unnormalized Radon relation, with the four cyclic positivity facts
exposed separately.  This is the shape most convenient when the caller has landed
`cyclicTriple`/`det3` positivity facts. -/
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

/-- Four points in strict cyclic convex order have a positive **normalized** Radon
relation.  Equivalently, the diagonal segment `AC` meets the diagonal segment `BD`
at an interior point.

This is the exact normalized form:

```text
λa A + λc C = λb B + λd D,
λa + λc = 1,
λb + λd = 1,
λa, λc, λb, λd > 0.
``` -/
theorem crossing_diagonals_of_cyclic_orient2_pos
    {a b c d : P2}
    (hABC : 0 < orient2 a b c)
    (hBCD : 0 < orient2 b c d)
    (hCDA : 0 < orient2 c d a)
    (hDAB : 0 < orient2 d a b) :
    ∃ λa λc λb λd : ℝ,
      0 < λa ∧ 0 < λc ∧ 0 < λb ∧ 0 < λd ∧
      λa + λc = 1 ∧ λb + λd = 1 ∧
      λa • a + λc • c = λb • b + λd • d := by
  obtain ⟨λa, λc, λb, λd, hλa, hλc, hλb, hλd, hmass, hrel⟩ :=
    positive_radon_relation_of_cyclic_orient2_pos hABC hBCD hCDA hDAB
  let m : ℝ := λa + λc
  have hm_pos : 0 < m := by
    dsimp [m]
    exact add_pos hλa hλc
  have hm_ne : m ≠ 0 := ne_of_gt hm_pos
  refine ⟨λa / m, λc / m, λb / m, λd / m,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact div_pos hλa hm_pos
  · exact div_pos hλc hm_pos
  · exact div_pos hλb hm_pos
  · exact div_pos hλd hm_pos
  · dsimp [m]
    rw [← add_div]
    exact div_self hm_ne
  · rw [← add_div]
    have hright : λb + λd = m := by
      dsimp [m]
      exact hmass.symm
    rw [hright]
    exact div_self hm_ne
  · have hscaled := congrArg (fun x : P2 => (m⁻¹) • x) hrel
    simpa [div_eq_mul_inv, smul_add, smul_smul,
      mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Wrapper using the bundled strict-cyclic predicate. -/
theorem crossing_diagonals_of_strictCyclicFour
    {a b c d : P2} (h : StrictCyclicFour a b c d) :
    ∃ λa λc λb λd : ℝ,
      0 < λa ∧ 0 < λc ∧ 0 < λb ∧ 0 < λd ∧
      λa + λc = 1 ∧ λb + λd = 1 ∧
      λa • a + λc • c = λb • b + λd • d := by
  rcases h with ⟨hABC, hBCD, hCDA, hDAB⟩
  exact crossing_diagonals_of_cyclic_orient2_pos hABC hBCD hCDA hDAB

/-- Alternating halfspace pattern I is impossible for any linear functional:
`a,c` are strictly negative while `b,d` are nonnegative. -/
theorem no_alternating_linear_neg_nonneg_of_cyclic_orient2_pos
    {a b c d : P2} (ℓ : P2 →ₗ[ℝ] ℝ)
    (hABC : 0 < orient2 a b c)
    (hBCD : 0 < orient2 b c d)
    (hCDA : 0 < orient2 c d a)
    (hDAB : 0 < orient2 d a b)
    (ha : ℓ a < 0) (hb : 0 ≤ ℓ b)
    (hc : ℓ c < 0) (hd : 0 ≤ ℓ d) :
    False := by
  obtain ⟨λa, λc, λb, λd, hλa, hλc, hλb, hλd, _hmass, hrel⟩ :=
    positive_radon_relation_of_cyclic_orient2_pos hABC hBCD hCDA hDAB
  have hlineq :
      λa * ℓ a + λc * ℓ c =
        λb * ℓ b + λd * ℓ d := by
    have hlin := congrArg (fun x : P2 => ℓ x) hrel
    simpa using hlin
  have hleft_neg : λa * ℓ a + λc * ℓ c < 0 := by
    exact add_neg (mul_neg_of_pos_of_neg hλa ha)
      (mul_neg_of_pos_of_neg hλc hc)
  have hright_nonneg : 0 ≤ λb * ℓ b + λd * ℓ d := by
    exact add_nonneg (mul_nonneg (le_of_lt hλb) hb)
      (mul_nonneg (le_of_lt hλd) hd)
  have hright_neg : λb * ℓ b + λd * ℓ d < 0 := by
    rwa [hlineq] at hleft_neg
  exact not_lt_of_ge hright_nonneg hright_neg

/-- Alternating halfspace pattern II is impossible for any linear functional:
`a,c` are nonnegative while `b,d` are strictly negative.  This is the same argument
with the two color classes swapped. -/
theorem no_alternating_linear_nonneg_neg_of_cyclic_orient2_pos
    {a b c d : P2} (ℓ : P2 →ₗ[ℝ] ℝ)
    (hABC : 0 < orient2 a b c)
    (hBCD : 0 < orient2 b c d)
    (hCDA : 0 < orient2 c d a)
    (hDAB : 0 < orient2 d a b)
    (ha : 0 ≤ ℓ a) (hb : ℓ b < 0)
    (hc : 0 ≤ ℓ c) (hd : ℓ d < 0) :
    False := by
  obtain ⟨λa, λc, λb, λd, hλa, hλc, hλb, hλd, _hmass, hrel⟩ :=
    positive_radon_relation_of_cyclic_orient2_pos hABC hBCD hCDA hDAB
  have hlineq :
      λa * ℓ a + λc * ℓ c =
        λb * ℓ b + λd * ℓ d := by
    have hlin := congrArg (fun x : P2 => ℓ x) hrel
    simpa using hlin
  have hleft_nonneg : 0 ≤ λa * ℓ a + λc * ℓ c := by
    exact add_nonneg (mul_nonneg (le_of_lt hλa) ha)
      (mul_nonneg (le_of_lt hλc) hc)
  have hright_neg : λb * ℓ b + λd * ℓ d < 0 := by
    exact add_neg (mul_neg_of_pos_of_neg hλb hb)
      (mul_neg_of_pos_of_neg hλd hd)
  have hleft_neg : λa * ℓ a + λc * ℓ c < 0 := by
    rwa [← hlineq] at hright_neg
  exact not_lt_of_ge hleft_nonneg hleft_neg

/-- Dot-product specialization of alternating pattern I. -/
theorem no_alternating_halfspace_neg_nonneg_of_cyclic_orient2_pos
    {a b c d g : P2}
    (hABC : 0 < orient2 a b c)
    (hBCD : 0 < orient2 b c d)
    (hCDA : 0 < orient2 c d a)
    (hDAB : 0 < orient2 d a b)
    (ha : dot2 g a < 0) (hb : 0 ≤ dot2 g b)
    (hc : dot2 g c < 0) (hd : 0 ≤ dot2 g d) :
    False := by
  exact no_alternating_linear_neg_nonneg_of_cyclic_orient2_pos (dot2Lin g)
    hABC hBCD hCDA hDAB ha hb hc hd

/-- Dot-product specialization of alternating pattern II. -/
theorem no_alternating_halfspace_nonneg_neg_of_cyclic_orient2_pos
    {a b c d g : P2}
    (hABC : 0 < orient2 a b c)
    (hBCD : 0 < orient2 b c d)
    (hCDA : 0 < orient2 c d a)
    (hDAB : 0 < orient2 d a b)
    (ha : 0 ≤ dot2 g a) (hb : dot2 g b < 0)
    (hc : 0 ≤ dot2 g c) (hd : dot2 g d < 0) :
    False := by
  exact no_alternating_linear_nonneg_neg_of_cyclic_orient2_pos (dot2Lin g)
    hABC hBCD hCDA hDAB ha hb hc hd

end ProofsInTheBook.Ch13FiniteConvexPosition
```

## Caller hook for Route B / cyclic-flips≤2

In the landed link plane, instantiate the theorem with the affine coordinate chart already used by the gnomonic/landed development:

```lean
-- Schematic only: `toP2` is the chosen oriented coordinate frame in the landed plane.
def toP2 : E3 → ProofsInTheBook.Ch13FiniteConvexPosition.P2 := ...
```

For cyclically ordered vertices `a,b,c,d`, prove the four hypotheses by transporting the repo's positive orientation facts:

```lean
have hABC : 0 < orient2 (toP2 qa) (toP2 qb) (toP2 qc) := by
  -- from `CyclicTriplePos` / `sOrient` / `det3` positivity and the orientation-transport lemma
  ...
have hBCD : 0 < orient2 (toP2 qb) (toP2 qc) (toP2 qd) := by ...
have hCDA : 0 < orient2 (toP2 qc) (toP2 qd) (toP2 qa) := by ...
have hDAB : 0 < orient2 (toP2 qd) (toP2 qa) (toP2 qb) := by ...
```

Then the alternating sign contradiction is one line.  For an arbitrary landed linear functional, package it as a linear map on the chart:

```lean
let ℓ : ProofsInTheBook.Ch13FiniteConvexPosition.P2 →ₗ[ℝ] ℝ := ...
exact
  ProofsInTheBook.Ch13FiniteConvexPosition
    .no_alternating_linear_neg_nonneg_of_cyclic_orient2_pos
      ℓ hABC hBCD hCDA hDAB ha hb hc hd
```

where `ha hb hc hd` are the transported sign assumptions

```lean
ha : ℓ (toP2 qa) < 0
hb : 0 ≤ ℓ (toP2 qb)
hc : ℓ (toP2 qc) < 0
hd : 0 ≤ ℓ (toP2 qd)
```

If the chart is chosen so that `ℓ (toP2 q) = ⟪g, q⟫`, this is exactly the contradiction to the alternating halfspace pattern

```text
⟪g,qa⟫ < 0,  0 ≤ ⟪g,qb⟫,  ⟪g,qc⟫ < 0,  0 ≤ ⟪g,qd⟫.
```
