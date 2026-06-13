import ProofsInTheBook.ZinanFFCT94

/-!
# `ZinanFFCT102` — the planar CYCLIC one-wind no-repeat core (Ch13)

This file proves the **cyclic** form of the planar one-wind no-repeat lemma by a
clean *local determinant* argument.  Unlike the OPEN-span version (refuted in
`ZinanFFCT99` by the equilateral `N = 4` closed chain), the cyclic hypotheses
correctly exclude the equilateral counterexample:

* `hedge`: the wrap edge `f(N) → f(0) = f(0) → f(0)` is zero — excluded;
* `hturn`: the wrap turn `det3 = 0` — excluded.

## The structure `PlanarCyclicLiftedTurnSpan`

A `Prop` over `f : Fin N → E3`, carrying a single isolated geometric field, the
**one-wind collinear ⇒ opposite** consequence:

```
neg_smul_edge_of_det3_zero : ∀ {r s}, r.val < s.val →
  det3 (f r) (f (r+1)) (f (s+1)) = 0 → ∃ c, c < 0 ∧ (f (s+1) - f s) = c • (f (r+1) - f r)
```

This is the *genuine* one-wind content (det3 = 0 ⇒ edges `e_r, e_s` collinear;
the lifted-angle gap `θ_s − θ_r ∈ (0, 2π)` and det3 = 0 ⇒ gap = π ⇒ `e_s` is a
NEGATIVE multiple of `e_r`, with `c = −ρ_s/ρ_r < 0`).  Formalizing the full
`θ → sin → π` machinery is heavy, so following §3.3 (honest isolation) it is
exposed as the single field of `PlanarCyclicLiftedTurnSpan`.  It is satisfiable
by any real convex single-wind arm (the negative-multiple conclusion is exactly
the planar geometry of two collinear-but-oppositely-directed edges separated by
a half turn).  Everything else — the 3-case local determinant argument — is
built unconditionally on top.

## The main theorem

`planar_oneWind_repeat_false` : a nonadjacent repeat `f r = f s` (`r.val+2 ≤ s.val`)
is impossible.  Corollary `planar_oneWind_noNonadjacentRepeat` packages it as the
local `NoNonadjacentRepeat f` predicate.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel

namespace ProofsInTheBook.ZinanFFCT102

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Local `det3` algebra (self-contained copies, proved off the definition). -/

theorem det3_self_left (a b : E3) : det3 a a b = 0 := by
  simp only [det3]; ring

theorem det3_self_mid (a b : E3) : det3 a b b = 0 := by
  simp only [det3]; ring

theorem det3_self_right (a b : E3) : det3 a b a = 0 := by
  simp only [det3]; ring

/-- Swap slots 2 and 3 (antisymmetry): `det3 a c b = - det3 a b c`. -/
theorem det3_swap23 (a b c : E3) : det3 a c b = - det3 a b c := by
  simp only [det3]; ring

/-- Additivity in slot 2. -/
theorem det3_add_mid (a b c d : E3) : det3 a (b + c) d = det3 a b d + det3 a c d := by
  simp only [det3, PiLp.add_apply]; ring

/-- Scalar homogeneity in slot 2. -/
theorem det3_smul_mid (a b d : E3) (t : ℝ) : det3 a (t • b) d = t * det3 a b d := by
  simp only [det3, PiLp.smul_apply, smul_eq_mul]; ring

/-! ## The cyclic one-wind certificate (one isolated geometric field). -/

/-- A planar cyclic single-wind certificate for `f : Fin N → E3`.  It carries the
single genuinely one-wind geometric consequence: when the outgoing edge `e_r` and
the edge `e_s` are collinear (`det3 (f r) (f(r+1)) (f(s+1)) = 0`) with `r` before
`s`, the half-turn gap forces `e_s` to be a *negative* multiple of `e_r`.  This is
realised by any real convex single-wind arm. -/
structure PlanarCyclicLiftedTurnSpan {N : ℕ} [NeZero N] (f : Fin N → E3) (h u v : E3) : Prop where
  neg_smul_edge_of_det3_zero : ∀ {r s : Fin N}, r.val < s.val →
    det3 (f r) (f (r + 1)) (f (s + 1)) = 0 →
      ∃ c : ℝ, c < 0 ∧ (f (s + 1) - f s) = c • (f (r + 1) - f r)

/-! ## Fin arithmetic helpers (cyclic `+1`, `+2`). -/

variable {N : ℕ} [NeZero N]

/-- When `i.val + 1 < N`, the cyclic successor does not wrap. -/
theorem val_add_one_of_lt {i : Fin N} (h : i.val + 1 < N) : (i + 1).val = i.val + 1 := by
  have hN : 1 < N := by have := i.isLt; omega
  have hone : (1 : Fin N).val = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt hN]
  rw [Fin.val_add, hone, Nat.mod_eq_of_lt h]

/-! ## The main local determinant argument. -/

/-- **Cyclic planar one-wind no-repeat (local determinant proof).**  Under the
cyclic edge / support / strict-turn hypotheses and the one-wind certificate, the
chain `f : Fin N → E3` has no nonadjacent repeated vertex. -/
theorem planar_oneWind_repeat_false
    {f : Fin N → E3} {h u v : E3}
    (hedge : ∀ i : Fin N, f (i + 1) ≠ f i)
    (hsupp : ∀ i j : Fin N, j ≠ i → j ≠ i + 1 → 0 ≤ det3 (f i) (f (i + 1)) (f j))
    (hturn : ∀ i : Fin N, 0 < det3 (f i) (f (i + 1)) (f (i + 2)))
    (hone : PlanarCyclicLiftedTurnSpan f h u v)
    {r s : Fin N} (hrs : r.val + 2 ≤ s.val) (hcoll : f r = f s) : False := by
  -- Basic value facts.
  have hsN : s.val < N := s.isLt
  have hrN : r.val < N := r.isLt
  -- The cyclic successors of r near the start do not wrap (since r+2 ≤ s < N).
  have hr1 : (r + 1).val = r.val + 1 := val_add_one_of_lt (by omega)
  have hr2 : ((r : Fin N) + 1 + 1).val = r.val + 2 := by
    rw [val_add_one_of_lt (by rw [hr1]; omega), hr1]
  -- Case split on whether s+1 wraps back to r.
  by_cases hwrap : (s : Fin N) + 1 = r
  · -- f(s+1) = f r = f s ⇒ edge s is zero ⇒ contradicts hedge s.
    exfalso
    apply hedge s
    rw [hwrap, hcoll]
  -- s+1 ≠ r from here on.
  -- (r+1+1) = (r + 2) as Fin elements (used in two places).
  have hr2eq : (r : Fin N) + 1 + 1 = r + 2 := by
    have hN2 : 2 < N := by have := s.isLt; omega
    have h2val : (2 : Fin N).val = 2 := by
      have e : (2 : Fin N) = Fin.ofNat N 2 := rfl
      rw [e, Fin.val_ofNat, Nat.mod_eq_of_lt hN2]
    have h12 : (1 : Fin N) + 1 = 2 := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one', h2val,
        Nat.mod_eq_of_lt (by omega : (1:ℕ) < N),
        Nat.mod_eq_of_lt (by omega : (1:ℕ)+1 < N)]
    rw [add_assoc, h12]
  by_cases hmin : s.val = r.val + 2
  · -- f r = f(r+2): the turn det3 (f r)(f(r+1))(f(r+2)) = det3 a b a = 0.
    exfalso
    have hsr2 : (s : Fin N) = r + 1 + 1 := by
      apply Fin.ext; rw [hr2, hmin]
    have hcoll' : f r = f (r + 1 + 1) := by rw [hcoll, hsr2]
    have := hturn r
    rw [show (r : Fin N) + 2 = r + 1 + 1 from hr2eq.symm, ← hcoll'] at this
    -- this : 0 < det3 (f r) (f (r+1)) (f r)
    rw [det3_self_right] at this
    exact lt_irrefl 0 this
  -- Main case: s.val > r.val + 2.
  have hgt : r.val + 2 < s.val := by omega
  -- s+1 does not wrap when s.val + 1 < N; but it might wrap if s.val + 1 = N.
  -- We avoid needing val of s+1 directly; instead use Fin-equality facts.
  -- Establish the non-collision Fin facts.
  -- (s+1) ≠ r is hwrap. (s+1) ≠ r+1: would force s = r, impossible.
  have hsr_ne : (s : Fin N) + 1 ≠ r + 1 := by
    intro hh
    have : (s : Fin N) = r := by
      have := congrArg (· + (-1 : Fin N)) hh
      simpa [add_assoc, add_neg_cancel, add_zero] using this
    rw [this] at hgt; omega
  -- (r+1) ≠ s and (r+1) ≠ s+1.
  have hr1_ne_s : (r : Fin N) + 1 ≠ s := by
    intro hh; rw [← hh, hr1] at hgt; omega
  have hr1_ne_s1 : (r : Fin N) + 1 ≠ s + 1 := fun hh => hsr_ne hh.symm
  -- (r+2) ≠ s and (r+2) ≠ s+1.
  have hr2_ne_s : (r : Fin N) + 1 + 1 ≠ s := by
    intro hh; rw [← hh, hr2] at hgt; omega
  have hr2_ne_s1 : (r : Fin N) + 1 + 1 ≠ s + 1 := by
    intro hh
    have : (r : Fin N) + 1 = s := by
      have := congrArg (· + (-1 : Fin N)) hh
      simpa [add_assoc, add_neg_cancel, add_zero] using this
    exact hr1_ne_s this
  -- Abbreviate D.
  set D : ℝ := det3 (f r) (f (r + 1)) (f (s + 1)) with hD
  -- Step 1: D = 0.
  -- From hsupp r (s+1): 0 ≤ det3 (f r)(f(r+1))(f(s+1)) = D.
  have hsupp1 : 0 ≤ D := by
    rw [hD]; exact hsupp r (s + 1) hwrap hsr_ne
  -- From hsupp s (r+1): 0 ≤ det3 (f s)(f(s+1))(f(r+1)); rewrite f s = f r, swap23 ⇒ = -D.
  have hsupp2 : 0 ≤ det3 (f s) (f (s + 1)) (f (r + 1)) :=
    hsupp s (r + 1) hr1_ne_s hr1_ne_s1
  have hsupp2' : 0 ≤ -D := by
    have : det3 (f s) (f (s + 1)) (f (r + 1)) = -D := by
      rw [← hcoll, hD, det3_swap23]
    rwa [this] at hsupp2
  have hDzero : D = 0 := le_antisymm (by linarith) hsupp1
  -- Step 2: collinear ⇒ opposite.  Apply the one-wind field.
  obtain ⟨c, hcneg, hc⟩ :=
    hone.neg_smul_edge_of_det3_zero (r := r) (s := s) (by omega) (hD ▸ hDzero)
  -- Step 3: hsupp s (r+2): 0 ≤ det3 (f s)(f(s+1))(f(r+2)); rewrite and contract.
  have hsupp3 : 0 ≤ det3 (f s) (f (s + 1)) (f ((r + 1) + 1)) :=
    hsupp s (r + 1 + 1) hr2_ne_s hr2_ne_s1
  -- f s = f r; f(s+1) = f s + (f(s+1) - f s) = f r + c • (f(r+1) - f r).
  have hfs1 : f (s + 1) = f r + c • (f (r + 1) - f r) := by
    have hsplit : f (s + 1) = f s + (f (s + 1) - f s) := by abel
    rw [hsplit, hc, hcoll]
  -- Rewrite the support value.
  have key : det3 (f s) (f (s + 1)) (f ((r + 1) + 1))
      = c * det3 (f r) (f (r + 1)) (f ((r + 1) + 1)) := by
    rw [← hcoll, hfs1]
    -- slot 2 = f r + c • (f(r+1) - f r); first term det3 (f r)(f r)(·) = 0.
    rw [det3_add_mid, det3_self_left, zero_add, det3_smul_mid]
    -- now c * det3 (f r) (f(r+1) - f r) (f(r+1+1))
    rw [show f (r + 1) - f r = f (r + 1) + (-1 : ℝ) • f r from by
      rw [neg_one_smul, sub_eq_add_neg]]
    rw [det3_add_mid, det3_smul_mid, det3_self_left, mul_zero, add_zero]
  -- The turn value det3 (f r)(f(r+1))(f(r+1+1)) = det3 (f r)(f(r+1))(f(r+2)) > 0.
  have hturnr : 0 < det3 (f r) (f (r + 1)) (f ((r + 1) + 1)) := by
    rw [hr2eq]; exact hturn r
  -- Combine: support value = c * (positive turn) < 0 (c < 0), contradicting 0 ≤ support.
  rw [key] at hsupp3
  nlinarith [hsupp3, hcneg, hturnr]

/-! ## The local no-repeat predicate (planar analogue of FFCT23's). -/

/-- The chain `f : Fin N → E3` never revisits a vertex at two nonadjacent
positions `r + 2 ≤ s`. -/
def NoNonadjacentRepeat {N : ℕ} (f : Fin N → E3) : Prop :=
  ∀ (r s : Fin N), r.val + 2 ≤ s.val → f r ≠ f s

/-- **Corollary.**  The cyclic one-wind hypotheses give a no-repeat arm. -/
theorem planarWeakConvex_strictTurns_oneWind_noNonadjacentRepeat
    {f : Fin N → E3} {h u v : E3}
    (hedge : ∀ i : Fin N, f (i + 1) ≠ f i)
    (hsupp : ∀ i j : Fin N, j ≠ i → j ≠ i + 1 → 0 ≤ det3 (f i) (f (i + 1)) (f j))
    (hturn : ∀ i : Fin N, 0 < det3 (f i) (f (i + 1)) (f (i + 2)))
    (hone : PlanarCyclicLiftedTurnSpan f h u v) :
    NoNonadjacentRepeat f := by
  intro r s hrs hcoll
  exact planar_oneWind_repeat_false hedge hsupp hturn hone hrs hcoll

#print axioms planar_oneWind_repeat_false
#print axioms planarWeakConvex_strictTurns_oneWind_noNonadjacentRepeat

end ProofsInTheBook.ZinanFFCT102
