import Mathlib

/--
Chapter 15: Every large point set has an obtuse angle.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter15

theorem chapter15 : Infinite {p : ℕ // p.Prime} := by
  exact Nat.infinite_setOf_prime.to_subtype

end ProofsInTheBook.Chapter15
