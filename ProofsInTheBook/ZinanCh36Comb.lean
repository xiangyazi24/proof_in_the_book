import ProofsInTheBook.ZinanCh36Theta

/-!
# `ZinanCh36Comb` — the pure-combinatorics master theorem of the Ch36 alternation pipeline

This file is standalone finite combinatorics: NO polygon types, NO geometry.  It reuses the
repo's `Alt` predicate (`ProofsInTheBook.PolygonWindingBound.Alt`, re-exported through
`ZinanCh36Theta`).  The headline is `alt_of_twoSide_noncrossing_cycle`: a single ν-cycle on a
finite τ-labelled set, with a sign `σ` that flips along ν and same-colour chords that never
τ-interleave, has alternating signs when read off in τ-sorted order.

The connectedness hypothesis (`hcycle`: the whole set is one ν-orbit) is ESSENTIAL: without it
`(+,+,-,-)` with matchings `(1,4),(2,3)` is a counterexample.
-/

namespace ProofsInTheBook
namespace ZinanCh36Comb

open scoped BigOperators

/-- The "linked"/interleaving predicate on two unordered τ-chords `{a,b}` and `{c,d}`:
the intervals cross (one min inside the other interval, maxes likewise) rather than nest or
sit disjoint. -/
def TauInterleaves {ι : Type*} (τ : ι → ℝ) (a b c d : ι) : Prop :=
  (min (τ a) (τ b) < min (τ c) (τ d) ∧ min (τ c) (τ d) < max (τ a) (τ b) ∧
      max (τ a) (τ b) < max (τ c) (τ d)) ∨
  (min (τ c) (τ d) < min (τ a) (τ b) ∧ min (τ a) (τ b) < max (τ c) (τ d) ∧
      max (τ c) (τ d) < max (τ a) (τ b))

open ProofsInTheBook.PolygonWindingBound (Alt)

/-! ## §1. Alt from "no two τ-adjacent elements share a sign"

`Alt (L.map σ)` unfolds to: every consecutive pair `a, b` of `L` has `σ a ≠ σ b`.  We package
that as a `List.Chain'` / direct recursion so the head-pair obligation is exactly the core
no-adjacency lemma. -/

/-- If consecutive elements of `L` always have distinct `σ`, then `L.map σ` is `Alt`. -/
theorem alt_map_of_chain {ι : Type*} (σ : ι → ℤ) :
    ∀ {L : List ι}, List.IsChain (fun a b => σ a ≠ σ b) L → Alt (L.map σ)
  | [], _ => by simp [Alt]
  | [_], _ => by simp [Alt]
  | (a :: b :: t), h => by
      rw [List.isChain_cons_cons] at h
      refine ⟨h.1, ?_⟩
      have := alt_map_of_chain σ h.2
      simpa using this

/-! ## §2. The ν-cycle: bijectivity, the sign formula, and parity

`hcycle` (single orbit) + `ν` mapping `S` into `S` + finiteness make `ν` a cyclic permutation
of `S`.  `σ` flips along `ν`, so `σ (ν^[i] a) = (-1)^i • σ a`, and going once around the cycle
forces the orbit length to be even. -/

section Cycle
variable {ι : Type*} [DecidableEq ι]
variable {S : Finset ι} {τ : ι → ℝ} {σ : ι → ℤ} {ν : ι → ι}

/-- Iterating ν stays in `S`. -/
theorem iterate_mem (hνmem : ∀ a ∈ S, ν a ∈ S) {a : ι} (ha : a ∈ S) :
    ∀ k : ℕ, ν^[k] a ∈ S := by
  intro k
  induction k with
  | zero => simpa using ha
  | succ n ih => rw [Function.iterate_succ_apply']; exact hνmem _ ih

/-- The sign after `k` ν-steps is `(-1)^k` times the start sign. -/
theorem sigma_iterate (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a) {a : ι} (ha : a ∈ S) :
    ∀ k : ℕ, σ (ν^[k] a) = (-1) ^ k * σ a := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', hflip _ (iterate_mem hνmem ha n), ih, pow_succ]
      ring

/-- **Parity.**  If `ν^[k] a = b` with `a, b ∈ S` and `σ a = σ b ≠ 0`, then `k` is even. -/
theorem even_of_reaches_same_sign (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a) {a b : ι} (ha : a ∈ S)
    (hσa : σ a = 1 ∨ σ a = -1) (hσe : σ a = σ b) {k : ℕ} (hk : ν^[k] a = b) :
    Even k := by
  have hsig := sigma_iterate hνmem hflip ha k
  rw [hk, ← hσe] at hsig
  -- σ a = (-1)^k * σ a with σ a = ±1 forces (-1)^k = 1, i.e. k even.
  rcases Nat.even_or_odd k with he | ho
  · exact he
  · exfalso
    rw [ho.neg_one_pow] at hsig
    rcases hσa with h | h <;> rw [h] at hsig <;> norm_num at hsig

end Cycle

/-! ## §3. Gap geometry: τ-adjacent endpoints split `S` into two sides

If `a, b` are τ-adjacent in `S` (nothing of `S` strictly between), then every element of `S`
lands on one of the two closed sides `τ x ≤ τ a` or `τ x ≥ τ b`. -/

section Gap
variable {ι : Type*} {S : Finset ι} {τ : ι → ℝ}

/-- With nothing of `S` strictly between `a` and `b` (`τ a < τ b`), every `x ∈ S` has
`τ x ≤ τ a` or `τ x ≥ τ b`. -/
theorem side_of_adjacent {a b : ι} (hab : τ a < τ b)
    (hgap : ∀ z ∈ S, ¬ (τ a < τ z ∧ τ z < τ b)) {x : ι} (hx : x ∈ S) :
    τ x ≤ τ a ∨ τ b ≤ τ x := by
  by_contra h
  push_neg at h
  exact hgap x hx ⟨h.1, h.2⟩

end Gap

section Axioms
open ProofsInTheBook.ZinanCh36Comb
#print axioms alt_map_of_chain
#print axioms sigma_iterate
#print axioms even_of_reaches_same_sign
#print axioms side_of_adjacent
end Axioms

end ZinanCh36Comb
end ProofsInTheBook
