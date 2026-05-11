import Mathlib

/--
Chapter 17: Sets, functions, and the continuum hypothesis.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter17

theorem chapter17 : Nat.Infinite {p : ℕ // p.Prime} := by
  simpa using Nat.infinite_setOf_prime.to_subtype

end ProofsInTheBook.Chapter17
