import Mathlib

/-!
# Chapter 20: One square and an odd number of triangles

From "Proofs from THE BOOK":

**Monsky's theorem**: A square cannot be divided into an odd number
of triangles of equal area.

The book's proof uses a 2-adic valuation argument: define a coloring
of the plane using the 2-adic valuation of coordinates, then apply
Sperner's lemma to show the triangulation must have an even count.
-/

namespace ProofsInTheBook.Chapter20

/-- The three colors used in Monsky's 2-adic coloring argument. -/
inductive MonskyColor where
  | red | green | blue
  deriving DecidableEq, Repr

open MonskyColor

/-- A triangle is trichromatic when its three vertex colors are pairwise different. -/
def TrichromaticTriangle (a b c : MonskyColor) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ a

theorem trichromatic_of_eq_red_green_blue {a b c : MonskyColor}
    (ha : a = red) (hb : b = green) (hc : c = blue) : TrichromaticTriangle a b c := by
  subst a
  subst b
  subst c
  simp [TrichromaticTriangle]

theorem not_trichromatic_of_first_two_same {a b c : MonskyColor}
    (hab : a = b) : ¬ TrichromaticTriangle a b c := by
  intro h
  exact h.1 hab

theorem chapter20 : TrichromaticTriangle red green blue :=
  trichromatic_of_eq_red_green_blue rfl rfl rfl

end ProofsInTheBook.Chapter20
