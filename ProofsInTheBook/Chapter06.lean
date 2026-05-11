import Mathlib

/--
Chapter 6: Every finite division ring is a field.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter06

theorem chapter06 : Nat.Infinite {p : ℕ // p.Prime} := by
  simpa using Nat.infinite_setOf_prime.to_subtype

end ProofsInTheBook.Chapter06
