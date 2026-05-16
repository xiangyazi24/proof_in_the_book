import Mathlib

/-!
# Chapter 5: The law of quadratic reciprocity

From "Proofs from THE BOOK":

**Quadratic reciprocity**: For distinct odd primes p and q,
  (q/p) · (p/q) = (-1)^{(p-1)/2 · (q-1)/2}

The book presents Eisenstein's proof via counting lattice points:
the number of lattice points in {1,...,(p-1)/2} × {1,...,(q-1)/2}
below y = (q/p)x equals ∑_{j=1}^{(p-1)/2} ⌊jq/p⌋, which by
Gauss's lemma determines (q/p). Since gcd(p,q) = 1, no point lies
on the diagonal, and the two triangles tile the rectangle of size
(p-1)/2 · (q-1)/2, giving the sign.
-/

namespace ProofsInTheBook.Chapter05

/-!
### Quadratic reciprocity

We state the law using the Legendre symbol `legendreSym`.
-/

theorem chapter05_quadratic_reciprocity (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) :=
  legendreSym.quadratic_reciprocity hp hq hpq

theorem chapter05_qr_one_mod_four (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p % 4 = 1) (hq : q ≠ 2) :
    legendreSym q p = legendreSym p q :=
  legendreSym.quadratic_reciprocity_one_mod_four hp hq

theorem chapter05_qr_three_mod_four (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p % 4 = 3) (hq : q % 4 = 3) :
    legendreSym q p = -legendreSym p q :=
  legendreSym.quadratic_reciprocity_three_mod_four hp hq

theorem chapter05 (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) :=
  chapter05_quadratic_reciprocity p q hp hq hpq

end ProofsInTheBook.Chapter05
