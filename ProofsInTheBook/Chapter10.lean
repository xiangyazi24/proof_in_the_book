import Mathlib

/-!
# Chapter 10: Lines in the plane and decompositions of graphs

From "Proofs from THE BOOK":

**Sylvester-Gallai theorem**: Given a finite set of points in the plane,
not all collinear, there exists a line passing through exactly two of them.

The book's proof (by T. Gallai): Among all pairs (P, ℓ) where P is a point
not on line ℓ (spanned by other points), choose the pair minimizing
dist(P, ℓ). If ℓ contains ≥ 3 points, one can find a closer pair,
contradicting minimality.

The chapter also discusses graph decompositions and the related
theorem about bipartite graphs.
-/

namespace ProofsInTheBook.Chapter10

/-!
### Sylvester-Gallai theorem

The proof by Gallai's extremal argument is a beautiful application of
the well-ordering principle. The formalization requires:
1. A finite point set in ℝ² (or an affine plane)
2. The notion of a line through two points
3. The distance from a point to a line
4. The extremal argument

This geometric result is not yet in Mathlib.
-/

/-- The points of a finite configuration lying on a candidate line. -/
def pointsOnLine {Point Line : Type*} [DecidableEq Point] (points : Finset Point)
    (onLine : Point → Line → Prop) [DecidableRel onLine] (line : Line) : Finset Point :=
  points.filter fun p => onLine p line

/--
An ordinary line for a finite point configuration: exactly two configuration
points lie on the line.
-/
def OrdinaryLine {Point Line : Type*} [DecidableEq Point] (points : Finset Point)
    (onLine : Point → Line → Prop) [DecidableRel onLine] (line : Line) : Prop :=
  ∃ p q, p ∈ points ∧ q ∈ points ∧ p ≠ q ∧ onLine p line ∧ onLine q line ∧
    ∀ r ∈ points, onLine r line → r = p ∨ r = q

theorem ordinaryLine_of_two_points_on_line {Point Line : Type*} [DecidableEq Point]
    (points : Finset Point) (onLine : Point → Line → Prop) [DecidableRel onLine]
    (line : Line) (hcard : (pointsOnLine points onLine line).card = 2) :
    OrdinaryLine points onLine line := by
  obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hcard
  have hp : p ∈ points ∧ onLine p line := by
    have : p ∈ pointsOnLine points onLine line := by simp [hset]
    simpa [pointsOnLine] using this
  have hq : q ∈ points ∧ onLine q line := by
    have : q ∈ pointsOnLine points onLine line := by simp [hset]
    simpa [pointsOnLine] using this
  refine ⟨p, q, hp.1, hq.1, hpq, hp.2, hq.2, ?_⟩
  intro r hr hline
  have hrset : r ∈ pointsOnLine points onLine line := by simp [pointsOnLine, hr, hline]
  simpa [hset] using hrset

theorem chapter10 {Point Line : Type*} [DecidableEq Point]
    (points : Finset Point) (onLine : Point → Line → Prop) [DecidableRel onLine]
    (line : Line) (hcard : (pointsOnLine points onLine line).card = 2) :
    OrdinaryLine points onLine line :=
  ordinaryLine_of_two_points_on_line points onLine line hcard

end ProofsInTheBook.Chapter10
