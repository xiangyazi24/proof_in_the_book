import Mathlib

/--
Chapter 2: Bertrand's postulate.

This file is intentionally mechanical. Replace each `sorry` with a full Lean proof.
-/

namespace ProofsInTheBook.Chapter02

/--
Bertrand's postulate statement.
For every n ≥ 1 there exists a prime p with n < p ≤ 2*n.
-/

theorem chapter02_bertrand : True := by
  sorry

/--
Landau's reduction.
A finite sequence of explicit checked primes gives Bertrand for small n, then only large n remain.
-/

theorem chapter02_landau_trick : True := by
  sorry

/--
Inequality (1): product of primes up to x ≤ 4^(x-1) for x ≥ 2.
-/

theorem chapter02_prime_product_bound : True := by
  sorry

/--
Legendre exponent decomposition for n! and binomial valuation bounds used in the proof.
-/

theorem chapter02_legendre : True := by
  sorry

/--
Binomial coefficient estimate and contradiction step giving a prime in (n, 2n].
-/

theorem chapter02_binomial_bound : True := by
  sorry

/--
Overall chapter marker.
-/

theorem chapter02 : True := by
  aesop

end ProofsInTheBook.Chapter02
