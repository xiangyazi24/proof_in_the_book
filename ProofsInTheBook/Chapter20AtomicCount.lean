import ProofsInTheBook.Chapter20

/-!
# Chapter 20 (Monsky) — abstract atomic double-count

The list-multiplicity analogue of the full-edge double-count
`sum_triangleLocalRGCount_mod_two_eq_oddEdgeRedGreenCount`.  Stated abstractly
for a finite family of edge-lists `f : Fin n → List (Sym2 V)`, so the dissection
engine instantiates it with `f := triAtomicEdges D`.  Engine-independent: depends
only on `Chapter20`.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Multiplicity of an unordered edge across a finite family of edge-lists. -/
def familyEdgeMult {n : ℕ} (f : Fin n → List (Sym2 V)) (e : Sym2 V) : ℕ :=
  ∑ i : Fin n, (f i).count e

/-- The red–green count of one edge-list equals the indicator-weighted sum of
edge multiplicities over the (finite) edge type. -/
theorem listEdgeRGCount_eq_sum_count (l : List (Sym2 V)) (color : V → MonskyColor) :
    listEdgeRGCount l color = ∑ e : Sym2 V, l.count e * edgeRGIndicator color e := by
  classical
  unfold listEdgeRGCount
  induction l with
  | nil => simp
  | cons a t ih =>
      have key : (∑ e : Sym2 V, (a :: t).count e * edgeRGIndicator color e)
          = (∑ e : Sym2 V, t.count e * edgeRGIndicator color e) + edgeRGIndicator color a := by
        have hpt : ∀ e : Sym2 V, (a :: t).count e * edgeRGIndicator color e
            = t.count e * edgeRGIndicator color e
              + (if a = e then edgeRGIndicator color e else 0) := by
          intro e
          rw [List.count_cons]
          rcases eq_or_ne a e with h | h
          · subst h; simp [add_mul]
          · simp [h, Ne.symm h]
        rw [Finset.sum_congr rfl (fun e _ => hpt e), Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_ite_eq Finset.univ a (fun e => edgeRGIndicator color e)]
        simp
      rw [List.filter_cons, key]
      rcases edgeRGIndicator_eq_zero_or_one color a with h0 | h1
      · simp [h0, ih]
      · simp [h1, ih, List.length_cons]

/-- Summed over the family, the red–green count is the indicator-weighted sum of
family multiplicities. -/
theorem sum_listEdgeRGCount_eq_sum_familyMult {n : ℕ}
    (f : Fin n → List (Sym2 V)) (color : V → MonskyColor) :
    (∑ i : Fin n, listEdgeRGCount (f i) color) =
      ∑ e : Sym2 V, familyEdgeMult f e * edgeRGIndicator color e := by
  classical
  simp_rw [listEdgeRGCount_eq_sum_count]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [familyEdgeMult, Finset.sum_mul]

/-- Per-edge mod-2 reduction (mirrors `edgeMultiplicity_mul_indicator_mod_two`). -/
theorem familyEdgeMult_mul_indicator_mod_two {n : ℕ}
    (f : Fin n → List (Sym2 V)) (color : V → MonskyColor) (e : Sym2 V) :
    (familyEdgeMult f e * edgeRGIndicator color e) % 2 =
      if edgeRGIndicator color e = 1 ∧ Odd (familyEdgeMult f e) then 1 else 0 := by
  rcases edgeRGIndicator_eq_zero_or_one color e with hzero | hone
  · simp [hzero]
  · by_cases hodd : Odd (familyEdgeMult f e)
    · simp [hone, hodd, Nat.odd_iff.mp hodd]
    · have heven : Even (familyEdgeMult f e) := Nat.not_odd_iff_even.mp hodd
      simp [hone, hodd, Nat.even_iff.mp heven]

private theorem sum_nat_mod_two_eq_sum_mod_two' {α : Type*} (s : Finset α) (g : α → ℕ) :
    (∑ x ∈ s, g x) % 2 = (∑ x ∈ s, g x % 2) % 2 := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      conv_lhs => rw [Nat.add_mod (g a) _ 2, ih]
      conv_rhs => rw [Nat.add_mod (g a % 2) _ 2]
      simp

/-- **Atomic double-count.** Summed red–green counts over the family agree, mod 2,
with the number of red–green edges of odd family-multiplicity. -/
theorem sum_listEdgeRGCount_mod_two {n : ℕ}
    (f : Fin n → List (Sym2 V)) (color : V → MonskyColor) :
    (∑ i : Fin n, listEdgeRGCount (f i) color) % 2 =
      (Finset.univ.filter fun e : Sym2 V =>
        edgeRGIndicator color e = 1 ∧ Odd (familyEdgeMult f e)).card % 2 := by
  classical
  rw [sum_listEdgeRGCount_eq_sum_familyMult]
  calc
    (∑ e : Sym2 V, familyEdgeMult f e * edgeRGIndicator color e) % 2
        = (∑ e : Sym2 V, (familyEdgeMult f e * edgeRGIndicator color e) % 2) % 2 := by
          exact sum_nat_mod_two_eq_sum_mod_two' _ _
    _ = (∑ e : Sym2 V,
          if edgeRGIndicator color e = 1 ∧ Odd (familyEdgeMult f e) then 1 else 0) % 2 := by
          congr 1
          exact Finset.sum_congr rfl fun e _ =>
            familyEdgeMult_mul_indicator_mod_two f color e
    _ = (Finset.univ.filter fun e : Sym2 V =>
          edgeRGIndicator color e = 1 ∧ Odd (familyEdgeMult f e)).card % 2 := by
          rw [Finset.card_filter]

end ProofsInTheBook.Chapter20
