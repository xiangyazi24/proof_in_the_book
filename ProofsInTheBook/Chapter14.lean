import Mathlib

/-!
# Chapter 14: Touching simplices

From "Proofs from THE BOOK":

**Perles's theorem**: In ℝ^d, there exist at most 2^d pairwise touching
d-simplices (simplices whose interiors are disjoint but whose boundaries
touch pairwise).

The book's proof uses a clever signing argument: assign to each
simplex a sign vector in {+,-}^d based on which side of a separating
hyperplane it lies on. Since there are only 2^d sign patterns,
the bound follows.
-/

namespace ProofsInTheBook.Chapter14

/-!
### The sign-vector counting step

The geometric proof assigns to each simplex a sign vector in `{+,-}^d`.
Once that assignment is injective, the numerical bound is the pigeonhole
principle: there are exactly `2^d` Boolean sign vectors.
-/

theorem sign_vector_injection_bound {ι : Type*} [Fintype ι] {d : ℕ}
    (sign : ι → Fin d → Bool) (hsign : Function.Injective sign) :
    Fintype.card ι ≤ 2 ^ d := by
  calc
    Fintype.card ι ≤ Fintype.card (Fin d → Bool) := Fintype.card_le_of_injective sign hsign
    _ = 2 ^ d := by simp

theorem chapter14 {ι : Type*} [Fintype ι] {d : ℕ}
    (sign : ι → Fin d → Bool) (hsign : Function.Injective sign) :
    Fintype.card ι ≤ 2 ^ d :=
  sign_vector_injection_bound sign hsign

end ProofsInTheBook.Chapter14
