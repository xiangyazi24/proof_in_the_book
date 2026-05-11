import Mathlib

/--
Chapter 1: Six proofs of the infinity of primes.

This file is intentionally mechanical. Replace each `sorry` with a full Lean proof.
-/

namespace ProofsInTheBook.Chapter01

/--
Euclid's proof.
For any finite set of primes p1,...,pr, the number n = p1*...*pr+1 has a prime divisor
not among p1,...,pr.
-/

theorem chapter01_euclid : True := by
  sorry

/--
Second proof via Fermat numbers.
Show that Fermat numbers are pairwise coprime, implying infinitely many primes.
-/

theorem chapter01_fermat_coprime : True := by
  sorry

/--
Third proof via Mersenne numbers.
If p is the largest prime, any prime divisor q of 2^p - 1 satisfies q > p.
-/

theorem chapter01_mersenne : True := by
  sorry

/--
Fourth proof via integration.
Use bounds on product decompositions of `binom` to show primes up to x contribute enough.
-/

theorem chapter01_euler : True := by
  sorry

/--
Fifth proof (Furstenberg style) via topology and residue classes.
-/

theorem chapter01_furstenberg : True := by
  sorry

/--
Overall chapter marker.
-/

theorem chapter01 : True := by
  aesop

end ProofsInTheBook.Chapter01
