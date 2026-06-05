import ProofsInTheBook.PlanarMapCutCapSigma
import ProofsInTheBook.PlanarMapEulerInequality

/-!
# Orbit-count machinery for the cut-and-cap surgery (toward `CutSigmaCounts`)

The Chapter 35 Jordan bundle `CutSigmaCounts` (`PlanarMapCutCapSigma.lean`) has
three open fields about the *concrete* cut map `C.cutCapMap`:

* `vertex_count` : `V' = V + k`;
* `face_count`   : `F' = F + 2`;
* `connected_of_dual_path`.

The design's route for the two count fields is **transposition cycle counting**:
realise the concrete `cutSigmaPerm` (resp. `φ' = σ' α'`) as `σ ⊕ 1` (caps as fixed
points) right-multiplied by an explicit product of `3k` transpositions and apply
the dichotomy `numCycles_mul_swap_dichotomy` (`PermTranspositionCycleCount.lean`)
once per swap, with the signs fixed by the cap reversal.

This file builds and **fully verifies the complete reusable machinery** that route
requires (none of it existed before):

* `numCycles_mul_swap_of_sameCycle` — the split (`+1`) half of the dichotomy;
* `sameCycle_mul_swap_of_cycle_avoids` — `SameCycle` transport across a swap whose
  two points lie outside the relevant cycle (needed to carry the per-step
  same/different-cycle invariant through the partial products of disjoint swaps);
* `numCycles_mul_listSwap_splits` / `numCycles_mul_listSwap_merges` — count change
  for multiplying by a *list* of transpositions, each splitting (resp. merging)
  the running product (`±length`);
* `numCycles_sumCongr_one` — `numCycles (σ ⊕ 1) = numCycles σ + card β`, via an
  explicit orbit-quotient `Equiv`;
* the cut-map bridges `sigmaLift = σ ⊕ 1` with `numCycles sigmaLift = V + 2k`, and
  the named bank-end / cap darts of the swap decomposition.

The mathematical decomposition is recorded in the section docstring below and has
been verified by hand on all five cut-dart cases:
`cutSigmaPerm = sigmaLift * (∏ swap ℓ_i^± c_i^±) * (∏ swap c_i^+ c_i^-)`, the first
`2k` swaps merging the two fixed caps into the `σ`-orbit at `v_i` (`-2k`), the last
`k` swaps splitting each merged orbit into its two banks (`+k`), net `V + k`; the
analogous `φ'` decomposition gives `F + 2`.

**Honest scope.**  The three `CutSigmaCounts` fields are *not* discharged here:
closing them needs (a) the `ext` evaluation of the `3k`-swap product on each dart
and (b) discharging the `3k` per-step `SameCycle` side-conditions against the
partial products, plus the design §4 Part A/B connectivity lift.  That assembly is
left open; what lands here is the verified counting toolkit it reduces to.

No `sorry`/`axiom`/`admit`/`native_decide` in this file.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## General `numCycles` facts about disjoint transposition products

The vertex/face counts are computed by repeatedly multiplying a permutation by a
single transposition and applying `numCycles_mul_swap_dichotomy`.  The two
building blocks below isolate the *sign* of one such multiplication:

* multiplying by a swap of two darts in the **same** cycle splits it (`+1`);
* multiplying by a swap of two darts in **different** cycles merges them (`-1`).

`numCycles_mul_swap_of_not_sameCycle` already supplies the merge direction.  We
add the split direction and a `SameCycle`-transport lemma across a disjoint swap. -/

namespace CutCapCount

/-- Multiplying by a transposition of two darts in the **same** cycle raises the
cycle count by one (the split case of the dichotomy). -/
theorem numCycles_mul_swap_of_sameCycle (p : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hsc : p.SameCycle a b) :
    _root_.numCycles (p * Equiv.swap a b) = _root_.numCycles p + 1 := by
  rcases _root_.numCycles_mul_swap_dichotomy p hab with h | h
  · exact h
  · -- the `-1` branch would force `a, b` in different cycles; contradiction.
    exfalso
    -- `q := p * swap a b`.  If it dropped the count, the merge characterization
    -- says `a, b` were in different `p`-cycles, contradicting `hsc`.
    -- Use: count drops ⟹ not sameCycle (else the dichotomy is the `+1` branch).
    have hne := PermTranspositionCycleCount.numCycles_mul_swap_ne p hab
    -- From `h : numCycles q + 1 = numCycles p` we get `numCycles q ≠ numCycles p`.
    -- But also the split branch (which holds for sameCycle) gives `+1`.  We close
    -- by ruling out the merge branch directly via `le_mul_swap_of_sameCycle`.
    have hle : _root_.numCycles p ≤ _root_.numCycles (p * Equiv.swap a b) :=
      PermTranspositionCycleCount.numCycles_le_mul_swap_of_sameCycle p hsc
    omega

/-- If `a`'s `p`-cycle avoids both `u` and `v`, then iterating `p * swap u v`
from `a` agrees with iterating `p`. -/
theorem pow_mul_swap_apply_of_not_sameCycle (p : Equiv.Perm D) {u v a : D}
    (hu : ¬ p.SameCycle a u) (hv : ¬ p.SameCycle a v) :
    ∀ n : ℕ, ((p * Equiv.swap u v) ^ n) a = (p ^ n) a := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hne_u : (p ^ n) a ≠ u := by
        intro h; exact hu ⟨(n : ℤ), by simpa [zpow_natCast] using h⟩
      have hne_v : (p ^ n) a ≠ v := by
        intro h; exact hv ⟨(n : ℤ), by simpa [zpow_natCast] using h⟩
      rw [pow_succ', mul_apply, ih, pow_succ', mul_apply, mul_apply,
        Equiv.swap_apply_of_ne_of_ne hne_u hne_v]

/-- **Disjoint-swap `SameCycle` transport.**  If `a`'s `p`-cycle avoids `u` and
`v`, then `p.SameCycle a b` transfers to `p * swap u v`. -/
theorem sameCycle_mul_swap_of_cycle_avoids (p : Equiv.Perm D) {u v a b : D}
    (hu : ¬ p.SameCycle a u) (hv : ¬ p.SameCycle a v)
    (hab : p.SameCycle a b) : (p * Equiv.swap u v).SameCycle a b := by
  obtain ⟨n, hn⟩ := hab.exists_nat_pow_eq
  exact ⟨(n : ℤ), by
    rw [zpow_natCast, pow_mul_swap_apply_of_not_sameCycle p hu hv n, hn]⟩

/-- **Split lemma for a list of transpositions, each splitting the running
product.**  If `l = [(u₀,v₀), …]` and, writing `Pⱼ` for `p` times the product of
the first `j` swaps (built on the right), each pair `(uⱼ,vⱼ)` is distinct and in
the **same** `Pⱼ`-cycle, then the cycle count rises by `l.length`. -/
theorem numCycles_mul_listSwap_splits (p : Equiv.Perm D) :
    ∀ l : List (D × D),
      (∀ j : Fin l.length,
        (l.get j).1 ≠ (l.get j).2 ∧
          (p * ((l.take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
            (l.get j).1 (l.get j).2) →
      _root_.numCycles (p * (l.map (fun w => Equiv.swap w.1 w.2)).prod)
        = _root_.numCycles p + l.length := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton t a ih =>
      intro hsplit
      -- The running products for the prefix `t` match those for `t ++ [a]`.
      have hpre : ∀ j : Fin t.length,
          (t.get j).1 ≠ (t.get j).2 ∧
            (p * ((t.take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
              (t.get j).1 (t.get j).2 := by
        intro j
        have hj : (j : ℕ) < (t ++ [a]).length := by
          simp only [List.length_append, List.length_singleton]; omega
        have hget : (t ++ [a]).get ⟨j, hj⟩ = t.get j := by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_left j.isLt]
        have htake : (t ++ [a]).take j = t.take j := by
          rw [List.take_append_of_le_length (by omega)]
        have := hsplit ⟨j, hj⟩
        rw [hget, htake] at this
        exact this
      have ihres := ih hpre
      -- Last element `a`: splits the product of the prefix.
      have hlast : ((t ++ [a]).length - 1) = t.length := by
        simp only [List.length_append, List.length_singleton]; omega
      have hjlast : t.length < (t ++ [a]).length := by
        simp only [List.length_append, List.length_singleton]; omega
      have hgetlast : (t ++ [a]).get ⟨t.length, hjlast⟩ = a := by
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (le_refl _)]
        simp
      have htakelast : (t ++ [a]).take t.length = t := by
        rw [List.take_append_of_le_length (le_refl _), List.take_length]
      have hsa := hsplit ⟨t.length, hjlast⟩
      rw [hgetlast, htakelast] at hsa
      obtain ⟨hane, hasc⟩ := hsa
      -- Now compute the count for the full product.
      have hprodappend :
          ((t ++ [a]).map (fun w => Equiv.swap w.1 w.2)).prod
            = (t.map (fun w => Equiv.swap w.1 w.2)).prod * Equiv.swap a.1 a.2 := by
        simp [List.map_append]
      rw [hprodappend, ← mul_assoc]
      rw [numCycles_mul_swap_of_sameCycle _ hane hasc, ihres]
      simp only [List.length_append, List.length_singleton]
      omega

/-- **Merge lemma for a list of transpositions, each merging the running
product.**  If each pair `(uⱼ,vⱼ)` is distinct and in **different** `Pⱼ`-cycles,
then the cycle count *drops* by `l.length`. -/
theorem numCycles_mul_listSwap_merges (p : Equiv.Perm D) :
    ∀ l : List (D × D),
      (∀ j : Fin l.length,
        (l.get j).1 ≠ (l.get j).2 ∧
          ¬ (p * ((l.take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
            (l.get j).1 (l.get j).2) →
      _root_.numCycles (p * (l.map (fun w => Equiv.swap w.1 w.2)).prod) + l.length
        = _root_.numCycles p := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton t a ih =>
      intro hmerge
      have hpre : ∀ j : Fin t.length,
          (t.get j).1 ≠ (t.get j).2 ∧
            ¬ (p * ((t.take j).map (fun w => Equiv.swap w.1 w.2)).prod).SameCycle
              (t.get j).1 (t.get j).2 := by
        intro j
        have hj : (j : ℕ) < (t ++ [a]).length := by
          simp only [List.length_append, List.length_singleton]; omega
        have hget : (t ++ [a]).get ⟨j, hj⟩ = t.get j := by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_left j.isLt]
        have htake : (t ++ [a]).take j = t.take j := by
          rw [List.take_append_of_le_length (by omega)]
        have := hmerge ⟨j, hj⟩
        rw [hget, htake] at this
        exact this
      have ihres := ih hpre
      have hjlast : t.length < (t ++ [a]).length := by
        simp only [List.length_append, List.length_singleton]; omega
      have hgetlast : (t ++ [a]).get ⟨t.length, hjlast⟩ = a := by
        simp only [List.get_eq_getElem]
        rw [List.getElem_append_right (le_refl _)]; simp
      have htakelast : (t ++ [a]).take t.length = t := by
        rw [List.take_append_of_le_length (le_refl _), List.take_length]
      have hsa := hmerge ⟨t.length, hjlast⟩
      rw [hgetlast, htakelast] at hsa
      obtain ⟨hane, hansc⟩ := hsa
      have hprodappend :
          ((t ++ [a]).map (fun w => Equiv.swap w.1 w.2)).prod
            = (t.map (fun w => Equiv.swap w.1 w.2)).prod * Equiv.swap a.1 a.2 := by
        simp [List.map_append]
      rw [hprodappend, ← mul_assoc]
      have hstep := _root_.numCycles_mul_swap_of_not_sameCycle
        (p * (t.map (fun w => Equiv.swap w.1 w.2)).prod) hane hansc
      simp only [List.length_append, List.length_singleton]
      omega

/-! ### Cycle count of a sum-extended permutation

`Equiv.Perm.sumCongr σ 1` acts as `σ` on the left summand and as the identity on
the right summand.  Its cycle count is `numCycles σ + card β` (the right summand
contributes `card β` fixed-point cycles). -/

section SumCongr

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

@[simp] lemma sumCongr_one_apply_inl (σ : Equiv.Perm α) (a : α) :
    (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)) (Sum.inl a) = Sum.inl (σ a) := by
  simp

@[simp] lemma sumCongr_one_apply_inr (σ : Equiv.Perm α) (b : β) :
    (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)) (Sum.inr b) = Sum.inr b := by
  simp

/-- A power of `sumCongr σ 1` acts as `σ ^ n` on the left summand. -/
lemma sumCongr_one_pow_inl (σ : Equiv.Perm α) (n : ℕ) (a : α) :
    ((Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)) ^ n) (Sum.inl a)
      = Sum.inl ((σ ^ n) a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ih, sumCongr_one_apply_inl]

/-- A power of `sumCongr σ 1` fixes the right summand. -/
lemma sumCongr_one_pow_inr (σ : Equiv.Perm α) (n : ℕ) (b : β) :
    ((Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)) ^ n) (Sum.inr b) = Sum.inr b := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, sumCongr_one_apply_inr]

lemma sameCycle_sumCongr_one_inl_inl (σ : Equiv.Perm α) (a a' : α) :
    (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)).SameCycle (Sum.inl a) (Sum.inl a')
      ↔ σ.SameCycle a a' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    refine ⟨(m : ℤ), ?_⟩
    rw [zpow_natCast]
    rw [sumCongr_one_pow_inl] at hm
    exact Sum.inl.inj hm
  · intro h
    obtain ⟨m, hm⟩ := SameCycle.exists_nat_pow_eq h
    exact ⟨(m : ℤ), by rw [zpow_natCast, sumCongr_one_pow_inl, hm]⟩

lemma sameCycle_sumCongr_one_inr_inr (σ : Equiv.Perm α) (b b' : β) :
    (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)).SameCycle (Sum.inr b) (Sum.inr b')
      ↔ b = b' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    rw [sumCongr_one_pow_inr] at hm; exact Sum.inr.inj hm
  · rintro rfl; exact SameCycle.rfl

lemma sameCycle_sumCongr_one_not_inl_inr (σ : Equiv.Perm α) (a : α) (b : β) :
    ¬ (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)).SameCycle (Sum.inl a) (Sum.inr b) := by
  intro h
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  rw [sumCongr_one_pow_inl] at hm
  exact Sum.inl_ne_inr hm

/-- The orbit-quotient bijection for the sum extension. -/
noncomputable def sumCongrOneOrbitEquiv (σ : Equiv.Perm α) :
    Quotient (SameCycle.setoid (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)))
      ≃ Quotient (SameCycle.setoid σ) ⊕ β := by
  classical
  refine
    { toFun := Quotient.lift
        (fun x => match x with
          | Sum.inl a => Sum.inl (Quotient.mk (SameCycle.setoid σ) a)
          | Sum.inr b => Sum.inr b) ?_
      invFun := fun s => match s with
        | Sum.inl q => Quotient.lift
            (fun a => Quotient.mk (SameCycle.setoid (Equiv.Perm.sumCongr σ
              (1 : Equiv.Perm β))) (Sum.inl a)) ?_ q
        | Sum.inr b => Quotient.mk _ (Sum.inr b)
      left_inv := ?_
      right_inv := ?_ }
  · -- well-defined forward
    intro x y hxy
    change (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β)).SameCycle x y at hxy
    rcases x with a | b <;> rcases y with a' | b'
    · exact congrArg Sum.inl (Quotient.sound
        ((sameCycle_sumCongr_one_inl_inl σ a a').mp hxy))
    · exact absurd hxy (sameCycle_sumCongr_one_not_inl_inr σ a b')
    · exact absurd hxy.symm (sameCycle_sumCongr_one_not_inl_inr σ a' b)
    · exact congrArg Sum.inr ((sameCycle_sumCongr_one_inr_inr σ b b').mp hxy)
  · -- well-defined inverse on left
    intro a a' haa'
    change σ.SameCycle a a' at haa'
    exact Quotient.sound ((sameCycle_sumCongr_one_inl_inl σ a a').mpr haa')
  · -- left_inv
    intro q
    refine Quotient.inductionOn q ?_
    rintro (a | b) <;> rfl
  · -- right_inv
    rintro (q | b)
    · refine Quotient.inductionOn q ?_; intro a; rfl
    · rfl

/-- The cycle count of `sumCongr σ 1` is `numCycles σ + card β`. -/
theorem numCycles_sumCongr_one (σ : Equiv.Perm α) :
    _root_.numCycles (Equiv.Perm.sumCongr σ (1 : Equiv.Perm β))
      = _root_.numCycles σ + Fintype.card β := by
  classical
  unfold _root_.numCycles
  rw [Fintype.card_congr (sumCongrOneOrbitEquiv σ), Fintype.card_sum]

end SumCongr

end CutCapCount

/-! ## The cut-map vertex count `V' = V + k`

We realise the concrete `cutSigmaPerm` as the sum-extension `σ ⊕ 1` of `M.σ`
(caps as fixed points) right-multiplied by an explicit product of `3k`
transpositions: for each cycle index `i`, two **insertion** swaps
`swap(ℓ_i^+, c_i^+)`, `swap(ℓ_i^-, c_i^-)` that splice the two caps into the
`σ`-orbit at `v_i` (merging the two fixed caps into it), followed by one
**split** swap `swap(c_i^+, c_i^-)` that separates the merged orbit into its two
banks. -/

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

/-- `σ` extended to the cut-dart set with the `2k` caps as fixed points. -/
noncomputable def sigmaLift (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  Equiv.Perm.sumCongr M.σ (1 : Equiv.Perm (Fin C.len ⊕ Fin C.len))

@[simp] lemma sigmaLift_inl (C : SimplePrimalCycle M) (d : D) :
    C.sigmaLift (Sum.inl d) = Sum.inl (M.σ d) := by
  simp [sigmaLift]

@[simp] lemma sigmaLift_inr (C : SimplePrimalCycle M) (c : Fin C.len ⊕ Fin C.len) :
    C.sigmaLift (Sum.inr c) = Sum.inr c := by
  simp [sigmaLift]

/-- The cycle count of `sigmaLift` is `V + 2k`. -/
lemma numCycles_sigmaLift (C : SimplePrimalCycle M) :
    _root_.numCycles C.sigmaLift = M.V + 2 * C.len := by
  rw [sigmaLift, numCycles_sumCongr_one, M.V_eq_numCycles]
  simp [Fintype.card_sum, Fintype.card_fin]; ring

/-- The `+`-bank-end dart `ℓ_i^+ = σ⁻¹ p_i`. -/
noncomputable def lEndPlus (C : SimplePrimalCycle M) (i : Fin C.len) : C.CutDart :=
  Sum.inl (M.σ.symm (C.pDart i))

/-- The `−`-bank-end dart `ℓ_i^- = σ⁻¹ q_i`. -/
noncomputable def lEndMinus (C : SimplePrimalCycle M) (i : Fin C.len) : C.CutDart :=
  Sum.inl (M.σ.symm (C.qDart i))

/-- The `+`-cap dart. -/
def capP (C : SimplePrimalCycle M) (i : Fin C.len) : C.CutDart := Sum.inr (Sum.inl i)
/-- The `−`-cap dart. -/
def capM (C : SimplePrimalCycle M) (i : Fin C.len) : C.CutDart := Sum.inr (Sum.inr i)

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap
