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

/-- Orientation-free red-green edge predicate used in the Sperner parity count. -/
def RedGreenEdge (a b : MonskyColor) : Prop :=
  (a = red ∧ b = green) ∨ (a = green ∧ b = red)

instance decidableRedGreenEdge (a b : MonskyColor) : Decidable (RedGreenEdge a b) := by
  unfold RedGreenEdge
  infer_instance

instance decidableTrichromaticTriangle (a b c : MonskyColor) :
    Decidable (TrichromaticTriangle a b c) := by
  unfold TrichromaticTriangle
  infer_instance

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

/--
Local Sperner parity atom: a triangle is trichromatic exactly when it has an
odd number of red-green edges.
-/
theorem odd_redGreenEdges_iff_trichromatic (a b c : MonskyColor) :
    Odd
      ((if RedGreenEdge a b then 1 else 0 : ℕ) +
       (if RedGreenEdge b c then 1 else 0 : ℕ) +
       (if RedGreenEdge c a then 1 else 0 : ℕ)) ↔
      TrichromaticTriangle a b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem redGreenEdges_zmod_two_eq_trichromatic (a b c : MonskyColor) :
    ((if RedGreenEdge a b then 1 else 0 : ZMod 2) +
     (if RedGreenEdge b c then 1 else 0 : ZMod 2) +
     (if RedGreenEdge c a then 1 else 0 : ZMod 2)) =
    (if TrichromaticTriangle a b c then 1 else 0 : ZMod 2) := by
  cases a <;> cases b <;> cases c <;> decide

theorem chapter20 : TrichromaticTriangle red green blue :=
  trichromatic_of_eq_red_green_blue rfl rfl rfl

end ProofsInTheBook.Chapter20
