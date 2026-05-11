import Mathlib

/--
Chapter 13: Cauchy's rigidity theorem.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter13

theorem chapter13 : Infinite {p : ℕ // p.Prime} := by
  exact Nat.infinite_setOf_prime.to_subtype

end ProofsInTheBook.Chapter13
