import Mathlib

/--
Chapter 4: Representing numbers as sums of two squares.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter04

theorem chapter04 : Infinite {p : ℕ // p.Prime} := by
  apply Set.infinite_coe_iff.mp
  exact Nat.infinite_setOf_prime

end ProofsInTheBook.Chapter04
