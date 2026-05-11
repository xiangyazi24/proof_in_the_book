import Mathlib

/--
Chapter 13: Cauchy's rigidity theorem.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter13

theorem chapter13 : Infinite {p : ℕ // p.Prime} := by
  apply Set.infinite_coe_iff.mp
  exact Nat.infinite_setOf_prime

end ProofsInTheBook.Chapter13
