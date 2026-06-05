import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

open Equiv Equiv.Perm Function

variable {D : Type*} [Fintype D] [DecidableEq D]

noncomputable def numCycles (p : Equiv.Perm D) : ℕ := by
  classical
  exact Fintype.card (Quotient (SameCycle.setoid p))

namespace PermTranspositionCycleCount

open scoped Finset

def mergeRel (p : Equiv.Perm D) (a b x y : D) : Prop :=
  p.SameCycle x y ∨
    (p.SameCycle x a ∧ p.SameCycle y b) ∨
      (p.SameCycle x b ∧ p.SameCycle y a)

lemma mergeRel_refl (p : Equiv.Perm D) (a b x : D) :
    mergeRel p a b x x := by
  exact Or.inl SameCycle.rfl

lemma mergeRel_symm {p : Equiv.Perm D} {a b x y : D} :
    mergeRel p a b x y → mergeRel p a b y x := by
  rintro (h | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨hyb, hxa⟩)
  · exact Or.inr (Or.inl ⟨hya, hxb⟩)

lemma mergeRel_trans {p : Equiv.Perm D} {a b x y z : D} :
    mergeRel p a b x y → mergeRel p a b y z → mergeRel p a b x z := by
  intro hxy hyz
  rcases hxy with hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
  · rcases hyz with hyz | ⟨hya, hzb⟩ | ⟨hyb, hza⟩
    · exact Or.inl (hxy.trans hyz)
    · exact Or.inr (Or.inl ⟨hxy.trans hya, hzb⟩)
    · exact Or.inr (Or.inr ⟨hxy.trans hyb, hza⟩)
  · rcases hyz with hyz | ⟨hya, hzb⟩ | ⟨hyb', hza⟩
    · exact Or.inr (Or.inl ⟨hxa, hyz.symm.trans hyb⟩)
    · exact Or.inr (Or.inl ⟨hxa, hzb⟩)
    · exact Or.inl (hxa.trans hza.symm)
  · rcases hyz with hyz | ⟨hya', hzb⟩ | ⟨hyb, hza⟩
    · exact Or.inr (Or.inr ⟨hxb, hyz.symm.trans hya⟩)
    · exact Or.inl (hxb.trans hzb.symm)
    · exact Or.inr (Or.inr ⟨hxb, hza⟩)

lemma mergeRel_step (p : Equiv.Perm D) (a b z : D) :
    mergeRel p a b z ((p * Equiv.swap a b) z) := by
  by_cases hza : z = a
  · subst hza
    refine Or.inr (Or.inl ⟨SameCycle.rfl, ?_⟩)
    rw [mul_apply, Equiv.swap_apply_left]
    exact sameCycle_apply_left.mpr SameCycle.rfl
  · by_cases hzb : z = b
    · subst hzb
      refine Or.inr (Or.inr ⟨SameCycle.rfl, ?_⟩)
      rw [mul_apply, Equiv.swap_apply_right]
      exact sameCycle_apply_left.mpr SameCycle.rfl
    · refine Or.inl ?_
      rw [mul_apply, Equiv.swap_apply_of_ne_of_ne hza hzb]
      exact sameCycle_apply_right.mpr SameCycle.rfl

lemma mergeRel_pow_apply (p : Equiv.Perm D) (a b x : D) (n : ℕ) :
    mergeRel p a b x (((p * Equiv.swap a b) ^ n) x) := by
  induction n with
  | zero =>
      simpa using mergeRel_refl p a b x
  | succ n ih =>
      rw [pow_succ', mul_apply]
      exact mergeRel_trans ih (mergeRel_step p a b (((p * Equiv.swap a b) ^ n) x))

lemma mergeRel_of_sameCycle_mul_swap {p : Equiv.Perm D} {a b x y : D} :
    (p * Equiv.swap a b).SameCycle x y → mergeRel p a b x y := by
  rintro ⟨i, hi⟩
  cases i with
  | ofNat n =>
      rw [← hi]
      exact mergeRel_pow_apply p a b x n
  | negSucc n =>
      have hxy : ((p * Equiv.swap a b) ^ (n + 1)) y = x := by
        rw [← hi]
        simp [zpow_negSucc, pow_succ]
      have hyx : mergeRel p a b y x := by
        simpa [hxy] using mergeRel_pow_apply p a b y (n + 1)
      exact mergeRel_symm hyx

lemma mergeRel_of_base_sameCycle {p : Equiv.Perm D} {a b x y : D}
    (hab : p.SameCycle a b) :
    mergeRel p a b x y → p.SameCycle x y := by
  rintro (h | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩)
  · exact h
  · exact hxa.trans (hab.trans hyb.symm)
  · exact hxb.trans (hab.symm.trans hya.symm)

lemma mul_swap_pow_succ_apply_left_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hnsc : ¬ p.SameCycle a b) :
    ∀ n : ℕ, n < orderOf (p.cycleOf b) →
      (((p * Equiv.swap a b) ^ (n + 1)) a = (p ^ (n + 1)) b)
  | 0, _ => by
      simp [mul_apply]
  | n + 1, hnlt => by
      have hnlt' : n < orderOf (p.cycleOf b) := lt_trans (Nat.lt_succ_self n) hnlt
      have ih := mul_swap_pow_succ_apply_left_of_not_sameCycle p hnsc n hnlt'
      rw [pow_succ', mul_apply, ih, mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne]
      · rw [pow_succ', mul_apply]
        simp [pow_succ', mul_apply]
      · intro ha
        apply hnsc
        have hba : p.SameCycle b a :=
          ⟨((n + 1 : ℕ) : ℤ), by simpa [zpow_natCast] using ha⟩
        exact hba.symm
      · intro hb
        have hpbn : p b ≠ b := by
          intro hpb
          have hcycle : p.cycleOf b = 1 := (cycleOf_eq_one_iff p).mpr hpb
          rw [hcycle, orderOf_one] at hnlt
          omega
        have hcb : p.cycleOf b b ≠ b := by
          simpa using hpbn
        have hcyclePow : (p.cycleOf b ^ (n + 1)) b = b := by
          simpa using hb
        have hpowOne : p.cycleOf b ^ (n + 1) = 1 :=
          ((isCycle_cycleOf p hpbn).pow_eq_one_iff' hcb).mpr hcyclePow
        exact pow_ne_one_of_lt_orderOf (by omega : n + 1 ≠ 0) hnlt hpowOne

lemma sameCycle_mul_swap_self_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hnsc : ¬ p.SameCycle a b) :
    (p * Equiv.swap a b).SameCycle a b := by
  let m := orderOf (p.cycleOf b)
  have hmpos : 0 < m := orderOf_pos (p.cycleOf b)
  cases hm : m with
  | zero =>
      omega
  | succ n =>
      refine ⟨((n + 1 : ℕ) : ℤ), ?_⟩
      have hnlt : n < orderOf (p.cycleOf b) := by
        simpa [m, hm] using Nat.lt_succ_self n
      have hq := mul_swap_pow_succ_apply_left_of_not_sameCycle p hnsc n hnlt
      have hp : (p ^ (n + 1)) b = b := by
        have hc : (p.cycleOf b ^ (n + 1)) b = b := by
          have : p.cycleOf b ^ orderOf (p.cycleOf b) = 1 := pow_orderOf_eq_one _
          simpa [m, hm] using congrFun (congrArg DFunLike.coe this) b
        simpa using hc
      change ((p * Equiv.swap a b) ^ (n + 1 : ℕ)) a = b
      exact hq.trans hp

lemma sameCycle_le_mul_swap_of_not_sameCycle
    (p : Equiv.Perm D) {a b x y : D} (hnsc : ¬ p.SameCycle a b)
    (hxy : p.SameCycle x y) :
    (p * Equiv.swap a b).SameCycle x y := by
  let q := p * Equiv.swap a b
  have hqab : q.SameCycle a b := sameCycle_mul_swap_self_of_not_sameCycle p hnsc
  have hstep : ∀ z : D, q.SameCycle z (p z) := by
    intro z
    by_cases hza : z = a
    · subst z
      exact hqab.trans (by simpa [q, mul_apply] using (SameCycle.rfl : q.SameCycle b b).apply_right)
    · by_cases hzb : z = b
      · subst z
        exact hqab.symm.trans
          (by simpa [q, mul_apply] using (SameCycle.rfl : q.SameCycle a a).apply_right)
      · have hz : q z = p z := by simp [q, mul_apply, Equiv.swap_apply_of_ne_of_ne hza hzb]
        exact hz ▸ SameCycle.rfl.apply_right
  have hpow : ∀ n : ℕ, q.SameCycle x ((p ^ n) x) := by
    intro n
    induction n with
    | zero =>
        exact SameCycle.rfl
    | succ n ih =>
        rw [pow_succ', mul_apply]
        exact ih.trans (hstep ((p ^ n) x))
  obtain ⟨n, hn⟩ := hxy.exists_nat_pow_eq
  simpa [hn] using hpow n

lemma sameCycle_mul_swap_iff_mergeRel_of_not_sameCycle
    (p : Equiv.Perm D) {a b x y : D} (hnsc : ¬ p.SameCycle a b) :
    (p * Equiv.swap a b).SameCycle x y ↔ mergeRel p a b x y := by
  constructor
  · exact mergeRel_of_sameCycle_mul_swap
  · intro h
    let q := p * Equiv.swap a b
    have hqab : q.SameCycle a b := sameCycle_mul_swap_self_of_not_sameCycle p hnsc
    rcases h with hxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
    · exact sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxy
    · exact (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxa).trans
        (hqab.trans (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hyb.symm))
    · exact (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxb).trans
        (hqab.symm.trans (sameCycle_le_mul_swap_of_not_sameCycle p hnsc hya.symm))

noncomputable def orbitEquivFixedOrCycles (p : Equiv.Perm D) :
    Quotient (SameCycle.setoid p) ≃ Function.fixedPoints p ⊕ p.cycleFactorsFinset := by
  classical
  refine
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left
      right_inv := ?right }
  · refine Quotient.lift ?_ ?_
    · intro x
      by_cases hx : p x = x
      · exact Sum.inl ⟨x, by simpa [Function.mem_fixedPoints_iff] using hx⟩
      · exact Sum.inr ⟨p.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)⟩
    · intro x y hxy
      change p.SameCycle x y at hxy
      by_cases hx : p x = x
      · have hy : p y = y := (hxy.apply_eq_self_iff).mp hx
        have hxy' : x = y := hxy.eq_of_left hx
        subst hxy'
        simp [hx, hy]
      · have hy : p y ≠ y := fun hy => hx ((hxy.apply_eq_self_iff).mpr hy)
        simp [hx, hy]
        exact hxy.cycleOf_eq
  · intro s
    rcases s with fp | c
    · exact Quotient.mk (SameCycle.setoid p) fp.1
    · let y : D := Classical.choose
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      exact Quotient.mk (SameCycle.setoid p) y
  · intro q
    refine Quotient.inductionOn q ?_
    intro x
    by_cases hx : p x = x
    · simp [hx, Function.mem_fixedPoints_iff]
    · dsimp
      simp [hx]
      let c : p.cycleFactorsFinset :=
        ⟨p.cycleOf x, cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr hx)⟩
      let y : D := Classical.choose
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hy : y ∈ (p.cycleOf x).support :=
        Classical.choose_spec
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hy' : p.SameCycle x y := by
        have := (mem_support_cycleOf_iff (f := p) (x := x) (y := y)).mp hy
        exact this.1
      exact Quotient.sound hy'.symm
  · intro s
    rcases s with fp | c
    · have hfp : p fp.1 = fp.1 := Function.mem_fixedPoints_iff.mp fp.2
      simp [hfp]
    · let y : D := Classical.choose
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hyc : y ∈ (c : Equiv.Perm D).support :=
        Classical.choose_spec
          (IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.2).1)
      have hyp : y ∈ p.support := mem_cycleFactorsFinset_support_le c.2 hyc
      have hy : p y ≠ y := mem_support.mp hyp
      have hcy : c.1 = p.cycleOf y := cycle_is_cycleOf hyc c.2
      dsimp
      rw [dif_neg hy]
      exact congrArg (fun e : p.cycleFactorsFinset => Sum.inr e) (Subtype.ext hcy.symm)

lemma numCycles_eq_fixed_add_cycleType_card (p : Equiv.Perm D) :
    numCycles p =
      Fintype.card (Function.fixedPoints p) + Multiset.card p.cycleType := by
  classical
  unfold numCycles
  calc
    Fintype.card (Quotient (SameCycle.setoid p))
        = Fintype.card (Function.fixedPoints p ⊕ p.cycleFactorsFinset) :=
          Fintype.card_congr (orbitEquivFixedOrCycles p)
    _ = Fintype.card (Function.fixedPoints p) + Fintype.card p.cycleFactorsFinset := by
          simp
    _ = Fintype.card (Function.fixedPoints p) + Multiset.card p.cycleType := by
          rw [cycleType_def]
          simp

lemma numCycles_eq_card_sub_support_add_cycleType_card (p : Equiv.Perm D) :
    numCycles p =
      Fintype.card D - p.support.card + Multiset.card p.cycleType := by
  rw [numCycles_eq_fixed_add_cycleType_card, Equiv.Perm.card_fixedPoints,
    Equiv.Perm.sum_cycleType]

theorem numCycles_mul_swap_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) (hnsc : ¬ p.SameCycle a b) :
    numCycles (p * Equiv.swap a b) + 1 = numCycles p := by
  classical
  let q : Equiv.Perm D := p * Equiv.swap a b
  let P := Quotient (SameCycle.setoid p)
  let Q := Quotient (SameCycle.setoid q)
  let A : P := Quotient.mk (SameCycle.setoid p) a
  let B : P := Quotient.mk (SameCycle.setoid p) b
  have hAB : A ≠ B := by
    intro h
    exact hnsc (Quotient.exact h)
  have hpq : ∀ {x y : D}, p.SameCycle x y → q.SameCycle x y := by
    intro x y hxy
    exact sameCycle_le_mul_swap_of_not_sameCycle p hnsc hxy
  let mergeMap : P → Q := Quotient.map' id (fun x y hxy => hpq hxy)
  let f : {u : P // u ≠ B} → Q := fun u => mergeMap u.1
  have hsurj : Function.Surjective f := by
    intro v
    refine Quotient.inductionOn v ?_
    intro x
    by_cases hxB : (Quotient.mk (SameCycle.setoid p) x : P) = B
    · refine ⟨⟨A, hAB⟩, ?_⟩
      have hxb : p.SameCycle x b := Quotient.exact hxB
      have hqxa : q.SameCycle x a :=
        (hpq hxb).trans (sameCycle_mul_swap_self_of_not_sameCycle p hnsc).symm
      apply Quotient.sound hqxa.symm
    · refine ⟨⟨Quotient.mk (SameCycle.setoid p) x, hxB⟩, ?_⟩
      rfl
  have hinj : Function.Injective f := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
    apply Subtype.ext
    dsimp [f, mergeMap] at huv
    revert hu hv huv
    refine Quotient.inductionOn₂ u v ?_
    intro x y hxB hyB hxy
    simp only [Quotient.map'_mk'', id_eq] at hxy
    have hqxy : q.SameCycle x y := Quotient.exact hxy
    have hR : mergeRel p a b x y :=
      (sameCycle_mul_swap_iff_mergeRel_of_not_sameCycle p hnsc).mp hqxy
    rcases hR with hpxy | ⟨hxa, hyb⟩ | ⟨hxb, hya⟩
    · exact Quotient.sound hpxy
    · exfalso
      exact hyB (Quotient.sound hyb)
    · exfalso
      exact hxB (Quotient.sound hxb)
  have hcard_equiv : Fintype.card {u : P // u ≠ B} = Fintype.card Q :=
    Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  have hsub_card : Fintype.card {u : P // u ≠ B} + 1 = Fintype.card P := by
    have hcompl :
        Fintype.card {u : P // u ≠ B} = Fintype.card P - 1 := by
      simpa [Fintype.card_subtype_eq B] using
        (Fintype.card_subtype_compl (fun u : P => u = B))
    have hpos : 0 < Fintype.card P := Fintype.card_pos_iff.mpr ⟨B⟩
    omega
  unfold numCycles
  change Fintype.card Q + 1 = Fintype.card P
  rw [← hcard_equiv]
  exact hsub_card

lemma sign_eq_of_numCycles_eq (p q : Equiv.Perm D)
    (hnum : numCycles p = numCycles q) :
    Equiv.Perm.sign p = Equiv.Perm.sign q := by
  classical
  have hpnum :
      numCycles p = Fintype.card D - p.cycleType.sum + Multiset.card p.cycleType := by
    rw [numCycles_eq_fixed_add_cycleType_card, Equiv.Perm.card_fixedPoints]
  have hqnum :
      numCycles q = Fintype.card D - q.cycleType.sum + Multiset.card q.cycleType := by
    rw [numCycles_eq_fixed_add_cycleType_card, Equiv.Perm.card_fixedPoints]
  have hmod :
      (p.cycleType.sum + Multiset.card p.cycleType) % 2 =
        (q.cycleType.sum + Multiset.card q.cycleType) % 2 := by
    have hp_le := p.sum_cycleType_le
    have hq_le := q.sum_cycleType_le
    omega
  apply Units.ext
  rw [Equiv.Perm.sign_of_cycleType, Equiv.Perm.sign_of_cycleType]
  simp [neg_one_pow_eq_pow_mod_two, hmod]

lemma numCycles_mul_swap_ne (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) :
    numCycles (p * Equiv.swap a b) ≠ numCycles p := by
  intro hnum
  have hsign_eq := sign_eq_of_numCycles_eq (p * Equiv.swap a b) p hnum
  have hsign_neg :
      Equiv.Perm.sign (p * Equiv.swap a b) = -Equiv.Perm.sign p := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
    simp
  rw [hsign_neg] at hsign_eq
  have hself : Equiv.Perm.sign p = -Equiv.Perm.sign p := hsign_eq.symm
  have hone : (1 : ℤˣ) = -1 := by
    calc
      (1 : ℤˣ) = (Equiv.Perm.sign p)⁻¹ * Equiv.Perm.sign p := by simp
      _ = (Equiv.Perm.sign p)⁻¹ * (-Equiv.Perm.sign p) := by
        exact congrArg ((Equiv.Perm.sign p)⁻¹ * ·) hself
      _ = -1 := by
        rw [mul_neg, inv_mul_cancel]
  have hval := congrArg Units.val hone
  norm_num at hval

lemma numCycles_le_mul_swap_of_sameCycle
    (p : Equiv.Perm D) {a b : D} (hsc : p.SameCycle a b) :
    numCycles p ≤ numCycles (p * Equiv.swap a b) := by
  classical
  let q : Equiv.Perm D := p * Equiv.swap a b
  let P := Quotient (SameCycle.setoid p)
  let Q := Quotient (SameCycle.setoid q)
  have hrel : ∀ {x y : D}, q.SameCycle x y → p.SameCycle x y := by
    intro x y hxy
    exact mergeRel_of_base_sameCycle hsc (mergeRel_of_sameCycle_mul_swap hxy)
  let g : Q → P := Quotient.map' id (fun x y hxy => hrel hxy)
  have hsurj : Function.Surjective g := by
    intro u
    refine Quotient.inductionOn u ?_
    intro x
    exact ⟨Quotient.mk (SameCycle.setoid q) x, rfl⟩
  unfold numCycles
  change Fintype.card P ≤ Fintype.card Q
  exact Fintype.card_le_of_surjective g hsurj

theorem numCycles_mul_swap_dichotomy
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) :
    numCycles (p * Equiv.swap a b) = numCycles p + 1 ∨
    numCycles (p * Equiv.swap a b) + 1 = numCycles p := by
  by_cases hnsc : ¬ p.SameCycle a b
  · exact Or.inr (numCycles_mul_swap_of_not_sameCycle p hab hnsc)
  · have hsc : p.SameCycle a b := by simpa using Classical.not_not.mp hnsc
    let q : Equiv.Perm D := p * Equiv.swap a b
    have hp_le_q : numCycles p ≤ numCycles q :=
      numCycles_le_mul_swap_of_sameCycle p hsc
    by_cases hqsc : q.SameCycle a b
    · have hq_le_p : numCycles q ≤ numCycles p := by
        have h := numCycles_le_mul_swap_of_sameCycle q hqsc
        simpa [q, mul_assoc] using h
      have heq : numCycles q = numCycles p := le_antisymm hq_le_p hp_le_q
      exact False.elim (numCycles_mul_swap_ne p hab heq)
    · have h := numCycles_mul_swap_of_not_sameCycle q hab hqsc
      exact Or.inl (by simpa [q, mul_assoc] using h.symm)

end PermTranspositionCycleCount

theorem numCycles_mul_swap_dichotomy
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) :
    numCycles (p * Equiv.swap a b) = numCycles p + 1 ∨
    numCycles (p * Equiv.swap a b) + 1 = numCycles p :=
  PermTranspositionCycleCount.numCycles_mul_swap_dichotomy p hab

theorem numCycles_mul_swap_of_not_sameCycle
    (p : Equiv.Perm D) {a b : D} (hab : a ≠ b) (hnsc : ¬ p.SameCycle a b) :
    numCycles (p * Equiv.swap a b) + 1 = numCycles p :=
  PermTranspositionCycleCount.numCycles_mul_swap_of_not_sameCycle p hab hnsc
