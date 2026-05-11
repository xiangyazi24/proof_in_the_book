import Mathlib

/--
Chapter 40: Probability makes counting (sometimes) easy.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter40

theorem chapter40 : Nat.Infinite {p : ℕ // p.Prime} := by
  simpa using Nat.infinite_setOf_prime.to_subtype

end ProofsInTheBook.Chapter40
