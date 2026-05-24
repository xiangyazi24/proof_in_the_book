import Mathlib

/-!
# Chapter 15: Every large point set has an obtuse angle

The book statement is the Danzer-Grünbaum theorem: any set of more than `2^d`
points in `ℝ^d` contains three points forming an obtuse angle.

Intended Lean theorem: for `points : Finset (EuclideanSpace ℝ (Fin d))`,
`2^d < points.card` should imply that three points of `points` make an obtuse
angle, expressed by a negative inner product.

Formalization status (playbook point 17): status ③. The reduction from the
no-obtuse-angle condition to the antipodal/supporting-strip condition is
formalized below. The remaining frontier is the Klee/Danzer-Grünbaum antipodal
cardinality bound: a finite antipodal point set in `ℝ^d` has cardinal at most
`2^d`, usually proved by the touching half-sized translates / volume argument.

This file intentionally does not contain the old sign-vector pigeonhole theorem:
there is no assumed `sign` map and no assumed injectivity.
-/

namespace ProofsInTheBook.Chapter15

open scoped RealInnerProductSpace

noncomputable section

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The inner-product form of the angle at `z` in the triangle `x,z,y`. -/
def AngleInner {d : ℕ} (x y z : Point d) : ℝ :=
  ⟪x - z, y - z⟫

/-- The angle `xzy` is obtuse exactly when this inner product is negative. -/
def ObtuseTriple {d : ℕ} (x y z : Point d) : Prop :=
  AngleInner x y z < 0

/-- No three distinct points of the finite set form an obtuse angle. -/
def NoObtuseAngles {d : ℕ} (points : Finset (Point d)) : Prop :=
  ∀ x ∈ points, ∀ y ∈ points, ∀ z ∈ points,
    x ≠ y → x ≠ z → y ≠ z → 0 ≤ AngleInner x y z

/--
For the ordered pair `a,b`, the point `x` lies in the closed strip bounded by
the two hyperplanes through `a` and `b` perpendicular to `b - a`.
-/
def InPerpendicularStrip {d : ℕ} (a b x : Point d) : Prop :=
  0 ≤ ⟪b - a, x - a⟫ ∧ 0 ≤ ⟪a - b, x - b⟫

/--
Every pair of points determines two parallel supporting hyperplanes with all
points in the strip between them: the antipodal-set condition used in the
Danzer-Grünbaum/Klee volume argument.
-/
def HasAntipodalStrips {d : ℕ} (points : Finset (Point d)) : Prop :=
  ∀ a ∈ points, ∀ b ∈ points, a ≠ b → ∀ x ∈ points, InPerpendicularStrip a b x

theorem noObtuseAngles_iff_not_exists_obtuse {d : ℕ} (points : Finset (Point d)) :
    NoObtuseAngles points ↔
      ¬ ∃ x ∈ points, ∃ y ∈ points, ∃ z ∈ points,
        x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ObtuseTriple x y z := by
  classical
  constructor
  · intro h hbad
    rcases hbad with ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, hlt⟩
    exact (not_lt_of_ge (h x hx y hy z hz hxy hxz hyz)) hlt
  · intro h x hx y hy z hz hxy hxz hyz
    by_contra hnonneg
    exact h ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz, lt_of_not_ge hnonneg⟩

/--
The direct geometric part of the chapter proof.

If every angle determined by three distinct points is non-obtuse, then for every
pair `a,b` all points lie in the closed strip between the two hyperplanes
through `a` and `b` perpendicular to `b - a`.
-/
theorem NoObtuseAngles.hasAntipodalStrips {d : ℕ} {points : Finset (Point d)}
    (hno : NoObtuseAngles points) : HasAntipodalStrips points := by
  intro a ha b hb hab x hx
  by_cases hxa : x = a
  · subst x
    rw [InPerpendicularStrip]
    constructor
    · simp
    · simp
  by_cases hxb : x = b
  · subst x
    rw [InPerpendicularStrip]
    constructor
    · simp
    · simp
  rw [InPerpendicularStrip]
  constructor
  · simpa [AngleInner] using hno b hb x hx a ha (Ne.symm hxb) (Ne.symm hab) hxa
  · simpa [AngleInner] using hno a ha x hx b hb (Ne.symm hxa) hab hxb

/--
The genuine Chapter 15 statement follows from the remaining antipodal cardinal
bound. This is not the old sign-vector pigeonhole theorem: the hypothesis is the
geometric supporting-strip condition obtained above from the angle assumption.
-/
theorem chapter15_from_antipodal_card_bound {d : ℕ}
    (antipodal_card_bound :
      ∀ points : Finset (Point d), HasAntipodalStrips points → points.card ≤ 2 ^ d)
    (points : Finset (Point d)) (hcard : 2 ^ d < points.card) :
    ∃ x ∈ points, ∃ y ∈ points, ∃ z ∈ points,
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ ObtuseTriple x y z := by
  classical
  by_contra hnone
  have hno : NoObtuseAngles points :=
    (noObtuseAngles_iff_not_exists_obtuse points).2 hnone
  exact (not_lt_of_ge (antipodal_card_bound points hno.hasAntipodalStrips)) hcard

end

end ProofsInTheBook.Chapter15
