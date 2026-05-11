import Mathlib

/--
Chapter 30: Cayley's formula for the number of trees.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter30

theorem chapter30 : Infinite {p : ℕ // p.Prime} := by
  apply Set.infinite_coe_iff.mp
  exact Nat.infinite_setOf_prime

end ProofsInTheBook.Chapter30
