import Mathlib

/--
Chapter 23: Cotangent and the Herglotz trick.
This file is a mechanical scaffold. Replace the placeholder proof with formalized proofs.
-/

namespace ProofsInTheBook.Chapter23

theorem chapter23 : Infinite {p : ℕ // p.Prime} := by
  apply Set.infinite_coe_iff.mp
  exact Nat.infinite_setOf_prime

end ProofsInTheBook.Chapter23
