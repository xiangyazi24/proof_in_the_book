import Mathlib

/-!
# Chapter 15: Every large point set has an obtuse angle

From "Proofs from THE BOOK":

**Danzer-Grünbaum theorem**: Any set of points in ℝ^d with more than
2^d points must contain an obtuse angle (i.e., three points forming
a triangle with an angle > π/2).

Equivalently: the maximum number of points in ℝ^d such that all
angles are acute is 2^d (achieved by the vertices of a cube).

The book's proof: project the points onto coordinate hyperplanes
and use the pigeonhole principle with the sign vectors {+,-}^d.
If two points share the same sign vector, the angle at any third
point between them can be shown to be obtuse.
-/

namespace ProofsInTheBook.Chapter15

/-!
### The sign-vector pigeonhole step

The Danzer-Grünbaum proof sends each point to a sign vector in `{+,-}^d`.
If no two points share a sign vector, the point set injects into the Boolean
cube, so it has at most `2^d` points.
-/

theorem sign_vector_finset_bound {α : Type*} {d : ℕ} (points : Finset α)
    (sign : α → Fin d → Bool) (hsign : Set.InjOn sign (points : Set α)) :
    points.card ≤ 2 ^ d := by
  calc
    points.card ≤ Fintype.card (Fin d → Bool) := by
      simpa using
        (Finset.card_le_card_of_injOn sign (t := Finset.univ) (by intro x hx; simp) hsign)
    _ = 2 ^ d := by simp

theorem chapter15 {α : Type*} {d : ℕ} (points : Finset α)
    (sign : α → Fin d → Bool) (hsign : Set.InjOn sign (points : Set α)) :
    points.card ≤ 2 ^ d :=
  sign_vector_finset_bound points sign hsign

end ProofsInTheBook.Chapter15
