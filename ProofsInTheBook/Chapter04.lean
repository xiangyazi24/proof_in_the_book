import Mathlib

/-!
# Chapter 4: Representing numbers as sums of two squares

From "Proofs from THE BOOK":

**Fermat's two-squares theorem**: An odd prime p is a sum of two squares
iff p ≡ 1 (mod 4).

The book gives Zagier's celebrated "one-sentence proof" via an involution
on S = {(x,y,z) ∈ ℕ₊³ : x² + 4yz = p}, plus the general characterization:
n is a sum of two squares iff every prime factor p ≡ 3 (mod 4) of n
occurs to an even power.
-/

namespace ProofsInTheBook.Chapter04

open Nat

/-!
### Necessity: p ≡ 3 (mod 4) implies p is NOT a sum of two squares

*Book proof.* Squares mod 4 are 0 or 1, so a² + b² mod 4 ∈ {0, 1, 2}.
Hence a² + b² ≢ 3 (mod 4).
-/

private lemma sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  rcases n.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left; ring_nf; omega
  · right; ring_nf; omega

theorem chapter04_necessity (a b : ℕ) : (a ^ 2 + b ^ 2) % 4 ≠ 3 := by
  have ha := sq_mod_four a
  have hb := sq_mod_four b
  omega

/-!
### Brahmagupta–Fibonacci identity

The set of sums of two squares is closed under multiplication:
  (a² + b²)(c² + d²) = (ac - bd)² + (ad + bc)².

This is a key tool: once we know primes ≡ 1 (mod 4) are sums of two squares,
we can represent any product of such primes.
-/

theorem chapter04_brahmagupta {a b x y u v : ℕ}
    (ha : a = x ^ 2 + y ^ 2) (hb : b = u ^ 2 + v ^ 2) :
    ∃ r s : ℕ, a * b = r ^ 2 + s ^ 2 :=
  Nat.sq_add_sq_mul ha hb

/-!
### Sufficiency: primes p ≡ 1 (mod 4) are sums of two squares

The book presents Zagier's proof: Consider the finite set
  S = {(x, y, z) ∈ ℕ₊³ : x² + 4yz = p}.
Define the involution
  f(x, y, z) = (x + 2z, z, y - x - z)  if x < y - z,
             = (2y - x, y, x - y + z)   if y - z < x < 2y,
             = (x - 2y, x - y + z, y)   if x > 2y.
This involution has exactly one fixed point (1, 1, (p-1)/4), so |S| is odd.
The involution g(x,y,z) = (x,z,y) also acts on S. Since |S| is odd,
g must have a fixed point (x,y,y), giving x² + 4y² = p.

The full formalization of this involution argument is left as sorry;
it requires careful case analysis on a finite set with a parity argument.
-/

/-- Finite ambient version of Zagier's triples `x^2 + 4yz = p`. -/
structure ZagierTriple (p : ℕ) where
  x : Fin (p + 1)
  y : Fin (p + 1)
  z : Fin (p + 1)
  x_pos : 0 < x.val
  y_pos : 0 < y.val
  z_pos : 0 < z.val
  equation : x.val ^ 2 + 4 * y.val * z.val = p

namespace ZagierTriple

/-- The simple involution `(x,y,z) ↦ (x,z,y)` on Zagier triples. -/
def swapYZ (p : ℕ) : ZagierTriple p ≃ ZagierTriple p where
  toFun t :=
    { x := t.x
      y := t.z
      z := t.y
      x_pos := t.x_pos
      y_pos := t.z_pos
      z_pos := t.y_pos
      equation := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using t.equation }
  invFun t :=
    { x := t.x
      y := t.z
      z := t.y
      x_pos := t.x_pos
      y_pos := t.z_pos
      z_pos := t.y_pos
      equation := by
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using t.equation }
  left_inv t := by
    cases t
    rfl
  right_inv t := by
    cases t
    rfl

theorem swapYZ_apply_x (p : ℕ) (t : ZagierTriple p) : ((swapYZ p) t).x = t.x := rfl

theorem swapYZ_apply_y (p : ℕ) (t : ZagierTriple p) : ((swapYZ p) t).y = t.z := rfl

theorem swapYZ_apply_z (p : ℕ) (t : ZagierTriple p) : ((swapYZ p) t).z = t.y := rfl

theorem swapYZ_fixed_iff (p : ℕ) (t : ZagierTriple p) : (swapYZ p) t = t ↔ t.y = t.z := by
  constructor
  · intro h
    have := congrArg ZagierTriple.y h
    simpa using this.symm
  · intro hyz
    cases t
    simp at hyz
    subst hyz
    rfl

end ZagierTriple

theorem chapter04_sufficiency (p : ℕ) [hp : Fact p.Prime] (hmod : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  Nat.Prime.sq_add_sq hmod

/-!
### Full characterization

A positive integer n is a sum of two squares iff every prime q ≡ 3 (mod 4)
dividing n appears to an even power.
-/

theorem chapter04_characterization (n : ℕ) :
    (∃ a b : ℕ, a ^ 2 + b ^ 2 = n) ↔
    ∀ q : ℕ, q.Prime → q % 4 = 3 → Even (n.factorization q) := by
  rw [show (∃ a b : ℕ, a ^ 2 + b ^ 2 = n) ↔ ∃ x y : ℕ, n = x ^ 2 + y ^ 2 from
    ⟨fun ⟨a, b, h⟩ => ⟨a, b, h.symm⟩, fun ⟨x, y, h⟩ => ⟨x, y, h.symm⟩⟩,
    Nat.eq_sq_add_sq_iff]
  constructor
  · intro h q hq hq4
    rw [factorization_def _ hq]
    by_cases hqn : q ∈ n.primeFactors
    · exact h q hqn hq4
    · have hpv : padicValNat q n = 0 := by
        rw [padicValNat.eq_zero_iff]
        rcases n.eq_zero_or_pos with rfl | hn
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (fun hdvd =>
            hqn (Nat.mem_primeFactors.mpr ⟨hq, hdvd, hn.ne'⟩)))
      simp [hpv]
  · intro h q hqn hq4
    have hqp := prime_of_mem_primeFactors hqn
    have := h q hqp hq4
    rwa [factorization_def _ hqp] at this

theorem chapter04 : ∀ a b : ℕ, (a ^ 2 + b ^ 2) % 4 ≠ 3 :=
  chapter04_necessity

end ProofsInTheBook.Chapter04
