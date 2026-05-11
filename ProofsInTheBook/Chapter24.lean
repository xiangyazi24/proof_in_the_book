import Mathlib

/--
Chapter 24: Buffon's needle problem.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter24

theorem chapter24 : Infinite {p : ℕ // p.Prime} := by
  exact Nat.infinite_setOf_prime.to_subtype

end ProofsInTheBook.Chapter24
