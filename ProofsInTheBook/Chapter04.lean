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

theorem exists_fixed_of_odd_card_involutive {α : Type*} [Fintype α]
    (e : Equiv.Perm α) (hodd : Odd (Fintype.card α)) (hinv : e ^ 2 = 1) :
    ∃ x : α, e x = x := by
  classical
  by_contra hnone
  have hsupp : e.support = Finset.univ := by
    ext x
    have hx : e x ≠ x := fun hfix => hnone ⟨x, hfix⟩
    simp [Equiv.Perm.mem_support, hx]
  have htwo : 2 ∣ Fintype.card α := by
    simpa [hsupp] using Equiv.Perm.two_dvd_card_support (σ := e) hinv
  exact hodd.not_two_dvd_nat htwo

theorem odd_card_of_involutive_unique_fixed {α : Type*} [Fintype α] [DecidableEq α]
    (f : Function.End α) (hinv : Function.Involutive f)
    (huniq : ∃! x : α, f x = x) : Odd (Fintype.card α) := by
  have hf2 : f ^ 2 = 1 := by
    apply funext
    intro x
    exact hinv x
  have hf : f ^ 2 ^ 1 = 1 := by
    simpa using hf2
  have hmod : Fintype.card α ≡ Fintype.card (Function.fixedPoints f) [MOD 2] := by
    simpa using Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) hf
  have hfixed : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    rcases huniq with ⟨x, hx, hunique⟩
    exact ⟨⟨x, hx⟩, fun y => Subtype.ext (hunique y y.property)⟩
  rw [hfixed] at hmod
  rw [Nat.odd_iff]
  exact hmod

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

The formalization below follows this path: it builds the finite triple type,
the three branches of Zagier's involution, the unique fixed point, the parity
step, and then the swap fixed-point argument.
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

@[ext] theorem ext {p : ℕ} {a b : ZagierTriple p}
    (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a
  cases b
  simp at hx hy hz
  subst hx
  subst hy
  subst hz
  rfl

instance instFintype (p : ℕ) : Fintype (ZagierTriple p) := by
  classical
  let S : Type := {u : Fin (p + 1) × Fin (p + 1) × Fin (p + 1) //
    0 < u.1.val ∧ 0 < u.2.1.val ∧ 0 < u.2.2.val ∧
      u.1.val ^ 2 + 4 * u.2.1.val * u.2.2.val = p}
  let e : ZagierTriple p ≃ S :=
    { toFun := fun t => ⟨(t.x, t.y, t.z), by
        exact ⟨t.x_pos, t.y_pos, t.z_pos, t.equation⟩⟩
      invFun := fun u =>
        { x := u.1.1
          y := u.1.2.1
          z := u.1.2.2
          x_pos := u.2.1
          y_pos := u.2.2.1
          z_pos := u.2.2.2.1
          equation := u.2.2.2.2 }
      left_inv := by
        intro t
        cases t
        rfl
      right_inv := by
        intro u
        rcases u with ⟨⟨x, y, z⟩, hx, hy, hz, heq⟩
        rfl }
  exact Fintype.ofEquiv S e.symm

def canonicalTriple (k : ℕ) (hk : 0 < k) : ZagierTriple (4 * k + 1) where
  x := ⟨1, by omega⟩
  y := ⟨1, by omega⟩
  z := ⟨k, by omega⟩
  x_pos := Nat.zero_lt_one
  y_pos := Nat.zero_lt_one
  z_pos := hk
  equation := by ring

theorem nonempty_of_four_mul_add_one (k : ℕ) (hk : 0 < k) :
    Nonempty (ZagierTriple (4 * k + 1)) :=
  ⟨canonicalTriple k hk⟩

theorem card_pos_of_four_mul_add_one (k : ℕ) (hk : 0 < k) :
    0 < Fintype.card (ZagierTriple (4 * k + 1)) := by
  classical
  exact Fintype.card_pos_iff.mpr ⟨canonicalTriple k hk⟩

private theorem branch_one_equation (x y z : ℕ) (h : x + z ≤ y) :
    (x + 2 * z) ^ 2 + 4 * z * (y - x - z) = x ^ 2 + 4 * y * z := by
  have hcast : ((y - x - z : ℕ) : ℤ) = (y : ℤ) - x - z := by omega
  norm_num [pow_two]
  nlinarith

def branchOne {p : ℕ} (t : ZagierTriple p) (h : t.x.val < t.y.val - t.z.val) :
    ZagierTriple p where
  x := ⟨t.x.val + 2 * t.z.val, by
    have heq := t.equation
    have hx := t.x_pos
    have hy := t.y_pos
    have hz := t.z_pos
    have hzle : 2 * t.z.val ≤ 4 * t.y.val * t.z.val := by nlinarith
    have hxle : t.x.val ≤ t.x.val ^ 2 := by nlinarith
    omega⟩
  y := t.z
  z := ⟨t.y.val - t.x.val - t.z.val, by
    exact lt_of_le_of_lt (le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)) t.y.2⟩
  x_pos := Nat.add_pos_left t.x_pos _
  y_pos := t.z_pos
  z_pos := by
    change 0 < t.y.val - t.x.val - t.z.val
    have hcomm : t.y.val - t.x.val - t.z.val = t.y.val - t.z.val - t.x.val := by omega
    rw [hcomm]
    exact Nat.sub_pos_of_lt h
  equation := by
    have hsum : t.x.val + t.z.val ≤ t.y.val := by omega
    calc
      (t.x.val + 2 * t.z.val) ^ 2 + 4 * t.z.val * (t.y.val - t.x.val - t.z.val)
          = t.x.val ^ 2 + 4 * t.y.val * t.z.val := branch_one_equation _ _ _ hsum
      _ = p := t.equation

private theorem branch_two_equation (x y z : ℕ) (hxy : x ≤ 2 * y) (hyxz : y ≤ x + z) :
    (2 * y - x) ^ 2 + 4 * y * (x + z - y) = x ^ 2 + 4 * y * z := by
  have hcast1 : ((2 * y - x : ℕ) : ℤ) = 2 * (y : ℤ) - x := by omega
  have hcast2 : ((x + z - y : ℕ) : ℤ) = (x : ℤ) + z - y := by omega
  norm_num [pow_two]
  nlinarith

def branchTwo {p : ℕ} (t : ZagierTriple p)
    (hleft : t.y.val - t.z.val < t.x.val) (hright : t.x.val < 2 * t.y.val) :
    ZagierTriple p where
  x := ⟨2 * t.y.val - t.x.val, by
    have heq := t.equation
    have hy := t.y_pos
    have hz := t.z_pos
    have hyle : 2 * t.y.val ≤ 4 * t.y.val * t.z.val := by nlinarith
    omega⟩
  y := t.y
  z := ⟨t.x.val + t.z.val - t.y.val, by
    have heq := t.equation
    have hx := t.x_pos
    have hy := t.y_pos
    have hz := t.z_pos
    have hzle : t.z.val ≤ 4 * t.y.val * t.z.val := by nlinarith
    have hxle : t.x.val ≤ t.x.val ^ 2 := by nlinarith
    omega⟩
  x_pos := by
    change 0 < 2 * t.y.val - t.x.val
    exact Nat.sub_pos_of_lt hright
  y_pos := t.y_pos
  z_pos := by
    change 0 < t.x.val + t.z.val - t.y.val
    have hyxz : t.y.val < t.x.val + t.z.val := by omega
    exact Nat.sub_pos_of_lt hyxz
  equation := by
    have hxy : t.x.val ≤ 2 * t.y.val := by omega
    have hyxz : t.y.val ≤ t.x.val + t.z.val := by omega
    calc
      (2 * t.y.val - t.x.val) ^ 2 + 4 * t.y.val * (t.x.val + t.z.val - t.y.val)
          = t.x.val ^ 2 + 4 * t.y.val * t.z.val := branch_two_equation _ _ _ hxy hyxz
      _ = p := t.equation

private theorem branch_three_equation (x y z : ℕ) (h2y : 2 * y ≤ x) :
    (x - 2 * y) ^ 2 + 4 * (x - y + z) * y = x ^ 2 + 4 * y * z := by
  apply Int.ofNat.inj
  norm_num [pow_two]
  have hyx : y ≤ x := by omega
  have hcast1 : ((x - 2 * y : ℕ) : ℤ) = (x : ℤ) - 2 * y := by omega
  have hcast2 : ((x - y : ℕ) : ℤ) = (x : ℤ) - y := by omega
  rw [hcast1, hcast2]
  ring

def branchThree {p : ℕ} (t : ZagierTriple p) (h : 2 * t.y.val < t.x.val) :
    ZagierTriple p where
  x := ⟨t.x.val - 2 * t.y.val, by
    exact lt_of_le_of_lt (Nat.sub_le _ _) t.x.2⟩
  y := ⟨t.x.val - t.y.val + t.z.val, by
    have heq := t.equation
    have hx := t.x_pos
    have hy := t.y_pos
    have hz := t.z_pos
    have hzle : t.z.val ≤ 4 * t.y.val * t.z.val := by nlinarith
    have hxle : t.x.val ≤ t.x.val ^ 2 := by nlinarith
    omega⟩
  z := t.y
  x_pos := by
    change 0 < t.x.val - 2 * t.y.val
    exact Nat.sub_pos_of_lt h
  y_pos := by
    change 0 < t.x.val - t.y.val + t.z.val
    have hyx : t.y.val < t.x.val := by omega
    exact Nat.add_pos_left (Nat.sub_pos_of_lt hyx) _
  z_pos := t.y_pos
  equation := by
    have h2y : 2 * t.y.val ≤ t.x.val := by omega
    calc
      (t.x.val - 2 * t.y.val) ^ 2 + 4 * (t.x.val - t.y.val + t.z.val) * t.y.val
          = t.x.val ^ 2 + 4 * t.y.val * t.z.val := branch_three_equation _ _ _ h2y
      _ = p := t.equation

theorem ne_y_sub_z_of_prime {p : ℕ} (hp : p.Prime) (t : ZagierTriple p) :
    t.x.val ≠ t.y.val - t.z.val := by
  intro h
  have hx := t.x_pos
  have hsum : t.y.val = t.x.val + t.z.val := by omega
  have heq : (t.x.val + 2 * t.z.val) ^ 2 = p := by
    calc
      (t.x.val + 2 * t.z.val) ^ 2 = t.x.val ^ 2 + 4 * t.y.val * t.z.val := by
        rw [hsum]
        ring
      _ = p := t.equation
  have hprimepow : ((t.x.val + 2 * t.z.val) ^ 2).Prime := by
    simpa [heq] using hp
  exact Nat.Prime.not_prime_pow (x := t.x.val + 2 * t.z.val) (n := 2) (by norm_num) hprimepow

theorem ne_two_mul_y_of_prime_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) :
    t.x.val ≠ 2 * t.y.val := by
  intro h
  have hpeven : Even p := by
    refine even_iff_two_dvd.mpr ?_
    rw [← t.equation]
    rw [h]
    ring_nf
    omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  exact hpodd.not_two_dvd_nat (even_iff_two_dvd.mp hpeven)

def zagierMapOfPrimeNeTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ZagierTriple p → ZagierTriple p := fun t => by
  by_cases h1 : t.x.val < t.y.val - t.z.val
  · exact branchOne t h1
  · by_cases h2 : t.x.val < 2 * t.y.val
    · exact branchTwo t (by
        have hne := ne_y_sub_z_of_prime hp t
        omega) h2
    · exact branchThree t (by
        have hne := ne_two_mul_y_of_prime_ne_two hp hp2 t
        omega)

theorem zagierMap_branchOne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) (h : t.x.val < t.y.val - t.z.val) :
    zagierMapOfPrimeNeTwo hp hp2 (branchOne t h) = t := by
  have h1raw : ¬ t.x.val + 2 * t.z.val < t.z.val - (t.y.val - t.x.val - t.z.val) := by
    omega
  have h2raw : ¬ t.x.val + 2 * t.z.val < 2 * t.z.val := by
    omega
  ext
  all_goals simp [zagierMapOfPrimeNeTwo, branchOne, branchThree, h1raw, h2raw]
  all_goals try omega

theorem zagierMap_branchTwo {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) (hleft : t.y.val - t.z.val < t.x.val)
    (hright : t.x.val < 2 * t.y.val) :
    zagierMapOfPrimeNeTwo hp hp2 (branchTwo t hleft hright) = t := by
  have h1raw : ¬ 2 * t.y.val - t.x.val < t.y.val - (t.x.val + t.z.val - t.y.val) := by
    omega
  have h2raw : 2 * t.y.val - t.x.val < 2 * t.y.val := by
    have hx := t.x_pos
    omega
  ext
  all_goals simp [zagierMapOfPrimeNeTwo, branchTwo, h1raw, h2raw]
  all_goals try omega

theorem zagierMap_branchThree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) (h : 2 * t.y.val < t.x.val) :
    zagierMapOfPrimeNeTwo hp hp2 (branchThree t h) = t := by
  have h1raw : t.x.val - 2 * t.y.val < (t.x.val - t.y.val + t.z.val) - t.y.val := by
    have hz := t.z_pos
    omega
  ext
  all_goals simp [zagierMapOfPrimeNeTwo, branchThree, branchOne, h1raw]
  all_goals try omega

theorem zagierMap_involutive {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Function.Involutive (zagierMapOfPrimeNeTwo hp hp2) := by
  intro t
  by_cases h1 : t.x.val < t.y.val - t.z.val
  · simpa [zagierMapOfPrimeNeTwo, h1] using zagierMap_branchOne hp hp2 t h1
  · by_cases h2 : t.x.val < 2 * t.y.val
    · have hleft : t.y.val - t.z.val < t.x.val := by
        have hne := ne_y_sub_z_of_prime hp t
        omega
      simpa [zagierMapOfPrimeNeTwo, h1, h2] using zagierMap_branchTwo hp hp2 t hleft h2
    · have h3 : 2 * t.y.val < t.x.val := by
        have hne := ne_two_mul_y_of_prime_ne_two hp hp2 t
        omega
      simpa [zagierMapOfPrimeNeTwo, h1, h2] using zagierMap_branchThree hp hp2 t h3

theorem branchOne_ne_self {p : ℕ} (t : ZagierTriple p)
    (h : t.x.val < t.y.val - t.z.val) :
    branchOne t h ≠ t := by
  intro hf
  have hy := congrArg (fun s : ZagierTriple p => s.y.val) hf
  have hz := congrArg (fun s : ZagierTriple p => s.z.val) hf
  simp [branchOne] at hy hz
  omega

theorem branchThree_ne_self {p : ℕ} (t : ZagierTriple p) (h : 2 * t.y.val < t.x.val) :
    branchThree t h ≠ t := by
  intro hf
  have hx := congrArg (fun s : ZagierTriple p => s.x.val) hf
  have hy := t.y_pos
  simp [branchThree] at hx
  omega

theorem branchTwo_fixed_x_eq_y {p : ℕ} (t : ZagierTriple p)
    (hleft : t.y.val - t.z.val < t.x.val) (hright : t.x.val < 2 * t.y.val)
    (hf : branchTwo t hleft hright = t) : t.x.val = t.y.val := by
  have hx := congrArg (fun s : ZagierTriple p => s.x.val) hf
  simp [branchTwo] at hx
  omega

theorem zagierMap_fixed_x_eq_y {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) (hfix : zagierMapOfPrimeNeTwo hp hp2 t = t) :
    t.x.val = t.y.val := by
  by_cases h1 : t.x.val < t.y.val - t.z.val
  · have hf : branchOne t h1 = t := by
      simpa [zagierMapOfPrimeNeTwo, h1] using hfix
    exact False.elim (branchOne_ne_self t h1 hf)
  · by_cases h2 : t.x.val < 2 * t.y.val
    · have hleft : t.y.val - t.z.val < t.x.val := by
        have hne := ne_y_sub_z_of_prime hp t
        omega
      have hf : branchTwo t hleft h2 = t := by
        simpa [zagierMapOfPrimeNeTwo, h1, h2] using hfix
      exact branchTwo_fixed_x_eq_y t hleft h2 hf
    · have h3 : 2 * t.y.val < t.x.val := by
        have hne := ne_two_mul_y_of_prime_ne_two hp hp2 t
        omega
      have hf : branchThree t h3 = t := by
        simpa [zagierMapOfPrimeNeTwo, h1, h2] using hfix
      exact False.elim (branchThree_ne_self t h3 hf)

theorem x_eq_one_of_prime_and_x_eq_y {p : ℕ} (hp : p.Prime) (t : ZagierTriple p)
    (hxy : t.x.val = t.y.val) : t.x.val = 1 := by
  by_contra hne
  have hp_eq : p = t.x.val * (t.x.val + 4 * t.z.val) := by
    calc
      p = t.x.val ^ 2 + 4 * t.y.val * t.z.val := t.equation.symm
      _ = t.x.val * (t.x.val + 4 * t.z.val) := by
        rw [← hxy]
        ring
  have hdiv : t.x.val ∣ p := ⟨t.x.val + 4 * t.z.val, hp_eq⟩
  have hpx : p = t.x.val := (hp.dvd_iff_eq hne).mp hdiv
  have hx := t.x_pos
  have hz := t.z_pos
  nlinarith

theorem zagierMap_fixed_xy_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (t : ZagierTriple p) (hfix : zagierMapOfPrimeNeTwo hp hp2 t = t) :
    t.x.val = 1 ∧ t.y.val = 1 := by
  have hxy := zagierMap_fixed_x_eq_y hp hp2 t hfix
  have hx1 := x_eq_one_of_prime_and_x_eq_y hp t hxy
  constructor
  · exact hx1
  · omega

theorem zagierMap_fixed_unique {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a b : ZagierTriple p}
    (ha : zagierMapOfPrimeNeTwo hp hp2 a = a)
    (hb : zagierMapOfPrimeNeTwo hp hp2 b = b) : a = b := by
  have haxy := zagierMap_fixed_xy_one hp hp2 a ha
  have hbxy := zagierMap_fixed_xy_one hp hp2 b hb
  ext
  · exact haxy.1.trans hbxy.1.symm
  · exact haxy.2.trans hbxy.2.symm
  · have haeq := a.equation
    have hbeq := b.equation
    rw [haxy.1, haxy.2] at haeq
    rw [hbxy.1, hbxy.2] at hbeq
    omega

theorem zagierMap_canonicalTriple_fixed (k : ℕ) (hk : 0 < k)
    (hp : (4 * k + 1).Prime) :
    zagierMapOfPrimeNeTwo hp (by omega : 4 * k + 1 ≠ 2) (canonicalTriple k hk) =
      canonicalTriple k hk := by
  have h1 : ¬ (1 : ℕ) < 1 - k := by omega
  have h2 : (1 : ℕ) < 2 * 1 := by omega
  ext
  all_goals simp [zagierMapOfPrimeNeTwo, canonicalTriple, branchTwo, h1, h2]

theorem existsUnique_zagierMap_fixed_of_four_mul_add_one (k : ℕ) (hk : 0 < k)
    (hp : (4 * k + 1).Prime) :
    ∃! t : ZagierTriple (4 * k + 1),
      zagierMapOfPrimeNeTwo hp (by omega : 4 * k + 1 ≠ 2) t = t := by
  let hp2 : 4 * k + 1 ≠ 2 := by omega
  refine ⟨canonicalTriple k hk, ?_, ?_⟩
  · exact zagierMap_canonicalTriple_fixed k hk hp
  · intro t ht
    exact zagierMap_fixed_unique hp hp2 ht (zagierMap_canonicalTriple_fixed k hk hp)

theorem card_odd_of_four_mul_add_one (k : ℕ) (hk : 0 < k)
    (hp : (4 * k + 1).Prime) : Odd (Fintype.card (ZagierTriple (4 * k + 1))) := by
  classical
  let hp2 : 4 * k + 1 ≠ 2 := by omega
  exact odd_card_of_involutive_unique_fixed
    (zagierMapOfPrimeNeTwo hp hp2)
    (zagierMap_involutive hp hp2)
    (existsUnique_zagierMap_fixed_of_four_mul_add_one k hk hp)

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

theorem exists_sq_add_sq_of_y_eq_z {p : ℕ} (t : ZagierTriple p) (hyz : t.y = t.z) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  refine ⟨t.x.val, 2 * t.y.val, ?_⟩
  have heq := t.equation
  rw [← hyz] at heq
  nlinarith

theorem exists_sq_add_sq_of_swapYZ_fixed {p : ℕ} (t : ZagierTriple p) (hfix : (swapYZ p) t = t) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  exists_sq_add_sq_of_y_eq_z t ((swapYZ_fixed_iff p t).mp hfix)

theorem exists_swapYZ_fixed_of_odd_card {p : ℕ} (hodd : Odd (Fintype.card (ZagierTriple p))) :
    ∃ t : ZagierTriple p, (swapYZ p) t = t := by
  have hinv : (swapYZ p : Equiv.Perm (ZagierTriple p)) ^ 2 = 1 := by
    apply Equiv.ext
    intro t
    cases t
    rfl
  exact exists_fixed_of_odd_card_involutive (swapYZ p) hodd hinv

theorem exists_sq_add_sq_of_four_mul_add_one_prime (k : ℕ) (hk : 0 < k)
    (hp : (4 * k + 1).Prime) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 4 * k + 1 := by
  have hodd := card_odd_of_four_mul_add_one k hk hp
  rcases exists_swapYZ_fixed_of_odd_card hodd with ⟨t, hfix⟩
  exact exists_sq_add_sq_of_swapYZ_fixed t hfix

theorem exists_sq_add_sq_of_prime_mod_four_eq_one (p : ℕ) (hp : p.Prime)
    (hmod : p % 4 = 1) : ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  let k := p / 4
  have hp_eq : p = 4 * k + 1 := by
    omega
  have hk : 0 < k := by
    have hpgt : 1 < p := hp.one_lt
    omega
  have hkprime : (4 * k + 1).Prime := by
    rwa [← hp_eq]
  rcases exists_sq_add_sq_of_four_mul_add_one_prime k hk hkprime with ⟨a, b, h⟩
  refine ⟨a, b, ?_⟩
  rwa [hp_eq]

end ZagierTriple

theorem chapter04_sufficiency (p : ℕ) [hp : Fact p.Prime] (hmod : p % 4 ≠ 3) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := by
  have hp' : p.Prime := hp.out
  by_cases hp2 : p = 2
  · refine ⟨1, 1, ?_⟩
    omega
  · have hodd : Odd p := hp'.odd_of_ne_two hp2
    have hmod2 : p % 2 = 1 := Nat.odd_iff.mp hodd
    have hmod4 : p % 4 = 1 := by omega
    exact ZagierTriple.exists_sq_add_sq_of_prime_mod_four_eq_one p hp' hmod4

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
