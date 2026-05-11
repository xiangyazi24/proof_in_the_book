import Mathlib

/--
Chapter 5: The law of quadratic reciprocity.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter05

theorem chapter05 : Infinite {p : ℕ // p.Prime} := by
  apply Set.infinite_coe_iff.mp
  exact Nat.infinite_setOf_prime

end ProofsInTheBook.Chapter05
