import Mathlib

/--
Chapter 3: Binomial coefficients are (almost) never powers.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter03

theorem chapter03 : Nat.Infinite {p : ℕ // p.Prime} := by
  simpa using Nat.infinite_setOf_prime.to_subtype

end ProofsInTheBook.Chapter03
