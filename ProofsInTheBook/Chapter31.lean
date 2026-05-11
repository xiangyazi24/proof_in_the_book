import Mathlib

/--
Chapter 31: Identities versus bijections.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter31

theorem chapter31 : Nat.Infinite {p : ℕ // p.Prime} := by
  simpa using Nat.infinite_setOf_prime.to_subtype

end ProofsInTheBook.Chapter31
