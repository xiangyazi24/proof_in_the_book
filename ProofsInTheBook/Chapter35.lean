import Mathlib

/--
Chapter 35: How to guard a museum.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter35

theorem chapter35 : Infinite {p : ℕ // p.Prime} := by
  exact Nat.infinite_setOf_prime.to_subtype

end ProofsInTheBook.Chapter35
