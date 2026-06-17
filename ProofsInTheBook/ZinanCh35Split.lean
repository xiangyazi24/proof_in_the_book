import ProofsInTheBook.ZinanCh35CountRoute

/-!
# Chapter 35: the actual-split count bound, closed UNCONDITIONALLY (the seam conjugacy)

This file proves the split-count bound consumed by
`ZinanCh35CountRoute.numCycles_phiLift_faceCorr2_lower_of_splitsEnough`:

  `FaceCorrWord.concatLen Ls + 2 ≤ 2 * (C.actualSplitFinset Ls).card + 2 * C.len`

for every cycle-list certificate `H : C.FaceCorrCycleLists Ls` — with **no** ambient
hypotheses (no connectivity, no Euler characteristic: the bound is genus-free, as the
kernel anchors of `ZinanCh35TorusAnchor.lean` suggested).  In fact the bound holds with
slack `0`: it is an exact equality (`concatLen_add_two_eq_splits`).

## The decisive structural fact: the seam conjugacy

By the proven telescope (`numCycles_prefix_telescopes` +
`sum_stepDelta_eq_neg_m_add_two_actualSplits`), the split bound is *equivalent* to the
face-count lower bound `numCycles φ'₂ ≥ F + 2`.  We close the latter — indeed the exact
count `numCycles φ'₂ = F + 2`, the named open core `NumCyclesCutPhi2` — by exhibiting an
explicit conjugacy.  Reading the corrected surgery pointwise:

* `φ'₂ (inl (dart i)) = inl (dart (nextIdx i))` and
  `φ'₂ (inl (α (dart i))) = inl (α (dart (prevIdx i)))` **unconditionally**
  (`cutCapPhi2_dart`, `cutCapPhi2_alpha_dart`): the `2k` seam darts form two new
  `k`-cycles — the two new faces;
* on the complement (ordinary darts + the `2k` caps), `φ'₂` is **conjugate to `φ`**:
  under the *seam swap* `e` that exchanges the seam darts with the caps
  (`inl (dart i) ↦ c_i⁺`, `inl (α (dart i)) ↦ c_i⁻`, `c_i⁺ ↦ inl (α (dart i))`,
  `c_i⁻ ↦ inl (dart i)`, identity on ordinary darts), every cap divert of the
  pointwise φ'₂ case table becomes a clean `φ`-step.  Concretely, the single
  transport identity `e (σ'₂ (inl d)) = inl (σ d)` (`seamSwapFun_cutSigma2_inl`)
  holds for **all** `d : D` — the cap diverts `σ'₂ d = c⁺/c⁻` land, after `e`,
  exactly on `inl (σ d)` because the caps are stand-ins for the bank-start darts.

Together: `e · φ'₂ · e⁻¹ = φ ⊕ (nextIdx ⊕ prevIdx)` (`seamSwap_phi2_conj`), whence

  `numCycles φ'₂ = numCycles φ + 1 + 1 = F + 2`    (`numCycles_cutCapPhi2`).

This closes the previously named open core (`numCyclesCutPhi2_holds : C.NumCyclesCutPhi2`)
and, through the telescope read backwards, the split-count bound — so the conditional
count-route results of `ZinanCh35CountRoute.lean` all discharge:

* `splitsEnough` / `splitsEnough_all` — the hsplits bound (this task's target);
* `faceCorrSplitCertUnconditional : C.FaceCorrSplitCert` — every simple primal cycle
  carries a split certificate;
* `cutCapMap2_F_unconditional : (cutCapMap2).F = M.F + 2`;
* `jordan_simple_cycle2_of_gates` and the `NearTriangulation` separation wrappers,
  now conditional only on the connectivity gates.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function

namespace ProofsInTheBook.PlanarMap

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CutCapCount

/-! ## Generic `numCycles` additivity over `sumCongr` (both summands arbitrary)

`PlanarMapCutCapCounts.lean` proves `numCycles (σ ⊕ 1) = numCycles σ + card β`.  We need
the general two-summand version `numCycles (f ⊕ g) = numCycles f + numCycles g`, by the
same orbit-quotient bijection. -/

section SumCongrTwo

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

@[simp] lemma sumCongr_apply_inl (f : Equiv.Perm α) (g : Equiv.Perm β) (a : α) :
    (Equiv.Perm.sumCongr f g) (Sum.inl a) = Sum.inl (f a) := by simp

@[simp] lemma sumCongr_apply_inr (f : Equiv.Perm α) (g : Equiv.Perm β) (b : β) :
    (Equiv.Perm.sumCongr f g) (Sum.inr b) = Sum.inr (g b) := by simp

lemma sumCongr_pow_apply_inl (f : Equiv.Perm α) (g : Equiv.Perm β) (n : ℕ) (a : α) :
    ((Equiv.Perm.sumCongr f g) ^ n) (Sum.inl a) = Sum.inl ((f ^ n) a) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ih, sumCongr_apply_inl]

lemma sumCongr_pow_apply_inr (f : Equiv.Perm α) (g : Equiv.Perm β) (n : ℕ) (b : β) :
    ((Equiv.Perm.sumCongr f g) ^ n) (Sum.inr b) = Sum.inr ((g ^ n) b) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      ih, sumCongr_apply_inr]

lemma sameCycle_sumCongr_inl_inl (f : Equiv.Perm α) (g : Equiv.Perm β) (a a' : α) :
    (Equiv.Perm.sumCongr f g).SameCycle (Sum.inl a) (Sum.inl a')
      ↔ f.SameCycle a a' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    rw [sumCongr_pow_apply_inl] at hm
    exact ⟨(m : ℤ), by rw [zpow_natCast]; exact Sum.inl.inj hm⟩
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    exact ⟨(m : ℤ), by rw [zpow_natCast, sumCongr_pow_apply_inl, hm]⟩

lemma sameCycle_sumCongr_inr_inr (f : Equiv.Perm α) (g : Equiv.Perm β) (b b' : β) :
    (Equiv.Perm.sumCongr f g).SameCycle (Sum.inr b) (Sum.inr b')
      ↔ g.SameCycle b b' := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    rw [sumCongr_pow_apply_inr] at hm
    exact ⟨(m : ℤ), by rw [zpow_natCast]; exact Sum.inr.inj hm⟩
  · intro h
    obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
    exact ⟨(m : ℤ), by rw [zpow_natCast, sumCongr_pow_apply_inr, hm]⟩

lemma not_sameCycle_sumCongr_inl_inr (f : Equiv.Perm α) (g : Equiv.Perm β)
    (a : α) (b : β) :
    ¬ (Equiv.Perm.sumCongr f g).SameCycle (Sum.inl a) (Sum.inr b) := by
  intro h
  obtain ⟨m, hm⟩ := h.exists_nat_pow_eq
  rw [sumCongr_pow_apply_inl] at hm
  exact Sum.inl_ne_inr hm

/-- The orbit-quotient bijection for a two-summand `sumCongr`. -/
noncomputable def sumCongrOrbitEquiv (f : Equiv.Perm α) (g : Equiv.Perm β) :
    Quotient (SameCycle.setoid (Equiv.Perm.sumCongr f g))
      ≃ Quotient (SameCycle.setoid f) ⊕ Quotient (SameCycle.setoid g) := by
  classical
  refine
    { toFun := Quotient.lift
        (fun x => match x with
          | Sum.inl a => Sum.inl (Quotient.mk (SameCycle.setoid f) a)
          | Sum.inr b => Sum.inr (Quotient.mk (SameCycle.setoid g) b)) ?_
      invFun := fun s => match s with
        | Sum.inl q => Quotient.lift
            (fun a => Quotient.mk (SameCycle.setoid (Equiv.Perm.sumCongr f g))
              (Sum.inl a)) ?_ q
        | Sum.inr q => Quotient.lift
            (fun b => Quotient.mk (SameCycle.setoid (Equiv.Perm.sumCongr f g))
              (Sum.inr b)) ?_ q
      left_inv := ?_
      right_inv := ?_ }
  · -- well-defined forward
    intro x y hxy
    change (Equiv.Perm.sumCongr f g).SameCycle x y at hxy
    rcases x with a | b <;> rcases y with a' | b'
    · exact congrArg Sum.inl (Quotient.sound
        ((sameCycle_sumCongr_inl_inl f g a a').mp hxy))
    · exact absurd hxy (not_sameCycle_sumCongr_inl_inr f g a b')
    · exact absurd hxy.symm (not_sameCycle_sumCongr_inl_inr f g a' b)
    · exact congrArg Sum.inr (Quotient.sound
        ((sameCycle_sumCongr_inr_inr f g b b').mp hxy))
  · -- well-defined inverse on the left summand
    intro a a' haa'
    change f.SameCycle a a' at haa'
    exact Quotient.sound ((sameCycle_sumCongr_inl_inl f g a a').mpr haa')
  · -- well-defined inverse on the right summand
    intro b b' hbb'
    change g.SameCycle b b' at hbb'
    exact Quotient.sound ((sameCycle_sumCongr_inr_inr f g b b').mpr hbb')
  · -- left_inv
    intro q
    refine Quotient.inductionOn q ?_
    rintro (a | b) <;> rfl
  · -- right_inv
    rintro (q | q)
    · refine Quotient.inductionOn q ?_; intro a; rfl
    · refine Quotient.inductionOn q ?_; intro b; rfl

/-- **`numCycles` is additive over `sumCongr`** (both summands arbitrary). -/
theorem numCycles_sumCongr (f : Equiv.Perm α) (g : Equiv.Perm β) :
    _root_.numCycles (Equiv.Perm.sumCongr f g)
      = _root_.numCycles f + _root_.numCycles g := by
  classical
  unfold _root_.numCycles
  rw [Fintype.card_congr (sumCongrOrbitEquiv f g), Fintype.card_sum]

end SumCongrTwo

/-- A permutation all of whose points are `SameCycle` has exactly one cycle. -/
lemma numCycles_eq_one_of_forall_sameCycle {γ : Type*} [Fintype γ] [DecidableEq γ]
    [Nonempty γ] (p : Equiv.Perm γ) (h : ∀ x y : γ, p.SameCycle x y) :
    _root_.numCycles p = 1 := by
  classical
  unfold _root_.numCycles
  rw [Fintype.card_eq_one_iff]
  refine ⟨Quotient.mk (SameCycle.setoid p) (Classical.arbitrary γ), ?_⟩
  intro q
  refine Quotient.inductionOn q ?_
  intro x
  exact Quotient.sound (h x (Classical.arbitrary γ))

end CutCapCount

namespace SimplePrimalCycle

open ForcedSplits FaceCorrWord SeamChain CutCapCount

variable {M : CombMap D}

/-! ## The two seam rotations are single cycles -/

lemma nextIdxEquiv_pow_apply (C : SimplePrimalCycle M) (n : ℕ) (i : Fin C.len) :
    (C.nextIdxEquiv ^ n) i = ⟨(i.1 + n) % C.len, Nat.mod_lt _ C.len_pos⟩ := by
  induction n with
  | zero =>
      apply Fin.ext
      simp [Nat.mod_eq_of_lt i.isLt]
  | succ n ih =>
      apply Fin.ext
      rw [pow_succ', Equiv.Perm.mul_apply, ih, nextIdxEquiv_apply, nextIdx_val,
        Nat.mod_add_mod]
      congr 1

lemma sameCycle_nextIdxEquiv (C : SimplePrimalCycle M) (x y : Fin C.len) :
    C.nextIdxEquiv.SameCycle x y := by
  refine ⟨((y.1 + C.len - x.1 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, C.nextIdxEquiv_pow_apply]
  apply Fin.ext
  show (x.1 + (y.1 + C.len - x.1)) % C.len = y.1
  have hx := x.isLt
  have hy := y.isLt
  have hxy : x.1 + (y.1 + C.len - x.1) = y.1 + C.len := by omega
  rw [hxy, Nat.add_mod_right, Nat.mod_eq_of_lt hy]

lemma numCycles_nextIdxEquiv (C : SimplePrimalCycle M) :
    _root_.numCycles C.nextIdxEquiv = 1 := by
  haveI : Nonempty (Fin C.len) := ⟨⟨0, C.len_pos⟩⟩
  exact CutCapCount.numCycles_eq_one_of_forall_sameCycle _ C.sameCycle_nextIdxEquiv

lemma numCycles_nextIdxEquiv_inv (C : SimplePrimalCycle M) :
    _root_.numCycles (C.nextIdxEquiv⁻¹) = 1 := by
  haveI : Nonempty (Fin C.len) := ⟨⟨0, C.len_pos⟩⟩
  exact CutCapCount.numCycles_eq_one_of_forall_sameCycle _
    (fun x y => (Equiv.Perm.sameCycle_inv).mpr (C.sameCycle_nextIdxEquiv x y))

/-! ## The seam swap `e`

The conjugator: exchange each seam dart with the cap it is `α'`-paired *across* —
`inl (dart i) ↦ c_i⁺` and `inl (α (dart i)) ↦ c_i⁻`, while `c_i⁺ ↦ inl (α (dart i))`
and `c_i⁻ ↦ inl (dart i)` (note the sign crossing: the cap goes to the *other* seam
dart of its edge, which is what aligns the cap diverts of `σ'₂` with clean `φ`-steps).
Ordinary darts are fixed. -/

/-- A dart equal to no bank-start (`p`/`q`) dart is not a cycle dart. -/
lemma notMem_dartSet_of_ne_bankStarts (C : SimplePrimalCycle M) {x : D}
    (hp : ∀ i, x ≠ C.pDart i) (hq : ∀ i, x ≠ C.qDart i) : x ∉ C.dartSet := by
  intro hmem
  rw [C.mem_dartSet_iff] at hmem
  obtain ⟨i, hi | hi⟩ := hmem
  · exact hq i (by rw [qDart_def]; exact hi)
  · refine hp (C.nextIdx i) ?_
    rw [pDart_def, C.prevIdx_nextIdx]
    exact hi

open Classical in
/-- Forward map of the seam swap. -/
noncomputable def seamSwapFun (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.cycleKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inl i)   -- dart i ↦ c_i⁺
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inr i)   -- α (dart i) ↦ c_i⁻
      | Sum.inr () => Sum.inl d                      -- ordinary: fixed
  | Sum.inr (Sum.inl i) => Sum.inl (M.α (C.dart i))  -- c_i⁺ ↦ α (dart i)
  | Sum.inr (Sum.inr i) => Sum.inl (C.dart i)        -- c_i⁻ ↦ dart i

open Classical in
/-- Inverse map of the seam swap. -/
noncomputable def seamSwapInvFun (C : SimplePrimalCycle M) : C.CutDart → C.CutDart :=
  fun x => match x with
  | Sum.inl d =>
      match C.cycleKind d with
      | Sum.inl (Sum.inl i) => Sum.inr (Sum.inr i)   -- dart i ↦ c_i⁻
      | Sum.inl (Sum.inr i) => Sum.inr (Sum.inl i)   -- α (dart i) ↦ c_i⁺
      | Sum.inr () => Sum.inl d
  | Sum.inr (Sum.inl i) => Sum.inl (C.dart i)        -- c_i⁺ ↦ dart i
  | Sum.inr (Sum.inr i) => Sum.inl (M.α (C.dart i))  -- c_i⁻ ↦ α (dart i)

lemma seamSwapFun_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapFun (Sum.inl (C.dart i)) = Sum.inr (Sum.inl i) := by
  show (match C.cycleKind (C.dart i) with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inl j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inr j)
    | Sum.inr () => Sum.inl (C.dart i)) = _
  rw [C.cycleKind_dart]

lemma seamSwapFun_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapFun (Sum.inl (M.α (C.dart i))) = Sum.inr (Sum.inr i) := by
  show (match C.cycleKind (M.α (C.dart i)) with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inl j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inr j)
    | Sum.inr () => Sum.inl (M.α (C.dart i))) = _
  rw [C.cycleKind_alpha_dart]

lemma seamSwapFun_other (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet) :
    C.seamSwapFun (Sum.inl d) = Sum.inl d := by
  show (match C.cycleKind d with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inl j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inr j)
    | Sum.inr () => Sum.inl d) = _
  rw [C.cycleKind_other h]

@[simp] lemma seamSwapFun_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapFun (Sum.inr (Sum.inl i)) = Sum.inl (M.α (C.dart i)) := rfl

@[simp] lemma seamSwapFun_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapFun (Sum.inr (Sum.inr i)) = Sum.inl (C.dart i) := rfl

lemma seamSwapInvFun_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapInvFun (Sum.inl (C.dart i)) = Sum.inr (Sum.inr i) := by
  show (match C.cycleKind (C.dart i) with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inr j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inl j)
    | Sum.inr () => Sum.inl (C.dart i)) = _
  rw [C.cycleKind_dart]

lemma seamSwapInvFun_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapInvFun (Sum.inl (M.α (C.dart i))) = Sum.inr (Sum.inl i) := by
  show (match C.cycleKind (M.α (C.dart i)) with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inr j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inl j)
    | Sum.inr () => Sum.inl (M.α (C.dart i))) = _
  rw [C.cycleKind_alpha_dart]

lemma seamSwapInvFun_other (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet) :
    C.seamSwapInvFun (Sum.inl d) = Sum.inl d := by
  show (match C.cycleKind d with
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inr j)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inl j)
    | Sum.inr () => Sum.inl d) = _
  rw [C.cycleKind_other h]

@[simp] lemma seamSwapInvFun_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapInvFun (Sum.inr (Sum.inl i)) = Sum.inl (C.dart i) := rfl

@[simp] lemma seamSwapInvFun_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamSwapInvFun (Sum.inr (Sum.inr i)) = Sum.inl (M.α (C.dart i)) := rfl

lemma seamSwap_leftInverse (C : SimplePrimalCycle M) :
    Function.LeftInverse C.seamSwapInvFun C.seamSwapFun := by
  intro x
  rcases x with d | (i | i)
  · rcases hk : C.cycleKind d with (i | i) | u
    · have hd : d = C.dart i := C.cycleKind_eq_inl_inl hk
      subst hd
      rw [C.seamSwapFun_dart, C.seamSwapInvFun_capP]
    · have hd : d = M.α (C.dart i) := C.cycleKind_eq_inl_inr hk
      subst hd
      rw [C.seamSwapFun_alpha_dart, C.seamSwapInvFun_capM]
    · have hd : d ∉ C.dartSet := C.cycleKind_eq_inr hk
      rw [C.seamSwapFun_other hd, C.seamSwapInvFun_other hd]
  · rw [C.seamSwapFun_capP, C.seamSwapInvFun_alpha_dart]
  · rw [C.seamSwapFun_capM, C.seamSwapInvFun_dart]

lemma seamSwap_rightInverse (C : SimplePrimalCycle M) :
    Function.RightInverse C.seamSwapInvFun C.seamSwapFun := by
  intro x
  rcases x with d | (i | i)
  · rcases hk : C.cycleKind d with (i | i) | u
    · have hd : d = C.dart i := C.cycleKind_eq_inl_inl hk
      subst hd
      rw [C.seamSwapInvFun_dart, C.seamSwapFun_capM]
    · have hd : d = M.α (C.dart i) := C.cycleKind_eq_inl_inr hk
      subst hd
      rw [C.seamSwapInvFun_alpha_dart, C.seamSwapFun_capP]
    · have hd : d ∉ C.dartSet := C.cycleKind_eq_inr hk
      rw [C.seamSwapInvFun_other hd, C.seamSwapFun_other hd]
  · rw [C.seamSwapInvFun_capP, C.seamSwapFun_dart]
  · rw [C.seamSwapInvFun_capM, C.seamSwapFun_alpha_dart]

/-- The seam swap as a permutation of the cut-dart set. -/
noncomputable def seamSwap (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart where
  toFun := C.seamSwapFun
  invFun := C.seamSwapInvFun
  left_inv := C.seamSwap_leftInverse
  right_inv := C.seamSwap_rightInverse

@[simp] lemma seamSwap_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.seamSwap x = C.seamSwapFun x := rfl

/-! ## The seam model `φ ⊕ (nextIdx ⊕ prevIdx)` -/

@[simp] lemma nextIdxEquiv_inv_apply (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.nextIdxEquiv⁻¹ i = C.prevIdx i := rfl

/-- The conjugacy model of `φ'₂`: the old face permutation on ordinary darts, with the
two cap slots rotating as the two new seam faces (`+` forward, `−` backward). -/
noncomputable def seamModel (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  Equiv.Perm.sumCongr M.φ (Equiv.Perm.sumCongr C.nextIdxEquiv C.nextIdxEquiv⁻¹)

@[simp] lemma seamModel_inl (C : SimplePrimalCycle M) (d : D) :
    C.seamModel (Sum.inl d) = Sum.inl (M.φ d) := by
  simp [seamModel]

@[simp] lemma seamModel_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamModel (Sum.inr (Sum.inl i)) = Sum.inr (Sum.inl (C.nextIdx i)) := by
  simp [seamModel]

@[simp] lemma seamModel_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.seamModel (Sum.inr (Sum.inr i)) = Sum.inr (Sum.inr (C.prevIdx i)) := by
  simp [seamModel]

/-! ## The transport identity and the conjugacy -/

/-- **The transport identity.**  For *every* dart `d : D`, the seam swap carries
`σ'₂ (inl d)` to `inl (σ d)`: clean steps are untouched, and the two cap diverts
(`σ d = p_j` ⟹ `σ'₂ (inl d) = c_{prevIdx j}⁺ ↦ inl (α (dart (prevIdx j))) = inl (p_j)`;
`σ d = q_j` ⟹ `σ'₂ (inl d) = c_j⁻ ↦ inl (dart j) = inl (q_j)`) land exactly on the
bank-start the cap stands in for. -/
lemma seamSwapFun_cutSigma2_inl (C : SimplePrimalCycle M) (e : D) :
    C.seamSwapFun (C.cutSigma2 (Sum.inl e)) = Sum.inl (M.σ e) := by
  rcases hd : C.divertKind e with (j | j) | u
  · have hσ : M.σ e = C.pDart j := C.divertKind_eq_plus hd
    rw [C.cutSigma2_inl_plus hd, C.seamSwapFun_capP, hσ, pDart_def]
  · have hσ : M.σ e = C.qDart j := C.divertKind_eq_minus hd
    rw [C.cutSigma2_inl_minus hd, C.seamSwapFun_capM, hσ, qDart_def]
  · obtain ⟨hp, hq⟩ := C.divertKind_eq_none hd
    rw [C.cutSigma2_inl_none hd,
      C.seamSwapFun_other (C.notMem_dartSet_of_ne_bankStarts hp hq)]

/-- **Pointwise intertwining**: `e ∘ φ'₂ = seamModel ∘ e` on every cut dart. -/
lemma seamSwapFun_phi2 (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.seamSwapFun ((C.cutCapMap2).φ x) = C.seamModel (C.seamSwapFun x) := by
  rcases x with d | (i | i)
  · rcases hk : C.cycleKind d with (i | i) | u
    · -- seam dart `dart i`: φ'₂ threads it forward; the model rotates its `+`-slot
      have hd : d = C.dart i := C.cycleKind_eq_inl_inl hk
      subst hd
      rw [cutCapPhi2_dart, C.seamSwapFun_dart, C.seamSwapFun_dart, C.seamModel_capP]
    · -- seam dart `α (dart i)`: φ'₂ threads it backward; the model rotates its `−`-slot
      have hd : d = M.α (C.dart i) := C.cycleKind_eq_inl_inr hk
      subst hd
      rw [cutCapPhi2_alpha_dart, pDart_def, C.seamSwapFun_alpha_dart,
        C.seamSwapFun_alpha_dart, C.seamModel_capM]
    · -- ordinary dart: φ'₂ = (transported) φ
      have hd : d ∉ C.dartSet := C.cycleKind_eq_inr hk
      rw [cutCapPhi2_apply, C.cutAlpha_other hd, C.seamSwapFun_cutSigma2_inl,
        C.seamSwapFun_other hd, C.seamModel_inl, CombMap.φ, Equiv.Perm.mul_apply]
  · -- `c_i⁺` stands in for `α (dart i)`: `φ'₂ (c_i⁺) = σ'₂ (inl (dart i))` transports
    -- to `inl (σ (dart i)) = inl (φ (α (dart i)))`
    rw [cutCapPhi2_apply, cutAlpha_capPlus, C.seamSwapFun_cutSigma2_inl,
      C.seamSwapFun_capP, C.seamModel_inl, CombMap.φ, Equiv.Perm.mul_apply,
      M.alpha_alpha]
  · -- `c_i⁻` stands in for `dart i`: `φ'₂ (c_i⁻) = σ'₂ (inl (α (dart i)))` transports
    -- to `inl (σ (α (dart i))) = inl (φ (dart i))`
    rw [cutCapPhi2_apply, cutAlpha_capMinus, C.seamSwapFun_cutSigma2_inl,
      C.seamSwapFun_capM, C.seamModel_inl, CombMap.φ, Equiv.Perm.mul_apply]

/-- The intertwining as a product identity. -/
theorem seamSwap_mul_phi2 (C : SimplePrimalCycle M) :
    C.seamSwap * (C.cutCapMap2).φ = C.seamModel * C.seamSwap := by
  ext x
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  simp only [seamSwap_apply]
  exact C.seamSwapFun_phi2 x

/-- **The seam conjugacy**: `e · φ'₂ · e⁻¹ = φ ⊕ (nextIdx ⊕ prevIdx)`. -/
theorem seamSwap_phi2_conj (C : SimplePrimalCycle M) :
    C.seamSwap * (C.cutCapMap2).φ * C.seamSwap⁻¹ = C.seamModel := by
  rw [seamSwap_mul_phi2, mul_assoc, mul_inv_cancel, mul_one]

/-! ## The unconditional face count `F' = F + 2` -/

/-- The model has `F + 2` cycles: `F` old faces plus the two seam rotations. -/
theorem numCycles_seamModel (C : SimplePrimalCycle M) :
    _root_.numCycles C.seamModel = M.F + 2 := by
  rw [seamModel, CutCapCount.numCycles_sumCongr, CutCapCount.numCycles_sumCongr,
    C.numCycles_nextIdxEquiv, C.numCycles_nextIdxEquiv_inv, ← M.F_eq_numCycles]

/-- **The corrected face-cycle count, closed unconditionally and genus-free:**
`numCycles φ'₂ = M.F + 2`.  By conjugation invariance through the seam conjugacy. -/
theorem numCycles_cutCapPhi2 (C : SimplePrimalCycle M) :
    _root_.numCycles ((C.cutCapMap2).φ) = M.F + 2 := by
  have h := CutCapCount.numCycles_conj C.seamSwap ((C.cutCapMap2).φ)
  rw [C.seamSwap_phi2_conj] at h
  rw [← h]
  exact C.numCycles_seamModel

/-- **The previously named open core of the corrected Chapter 35 face count, now a
theorem**: every simple primal cycle satisfies `NumCyclesCutPhi2`. -/
theorem numCyclesCutPhi2_holds (C : SimplePrimalCycle M) : C.NumCyclesCutPhi2 := by
  show _root_.numCycles ((C.cutCapMap2).φ) = M.F + 2
  exact C.numCycles_cutCapPhi2

/-- **`F' = F + 2`, unconditionally.**  The `face_count` field of `CutSigmaCounts2`. -/
theorem cutCapMap2_F_unconditional (C : SimplePrimalCycle M) :
    (C.cutCapMap2).F = M.F + 2 :=
  C.cutCapMap2_F C.numCyclesCutPhi2_holds

/-- The factored form consumed by the telescope. -/
theorem numCycles_phiLift_mul_faceCorr2 (C : SimplePrimalCycle M) :
    _root_.numCycles (C.phiLift * C.faceCorr2) = M.F + 2 := by
  rw [← C.cutCapPhi2_eq_phiLift_mul]
  exact C.numCycles_cutCapPhi2

/-! ## The split-count bound (the task target), with slack 0

The telescope `numCycles (phiLift · faceCorr₂) − numCycles phiLift = −m + 2·s` is
already proven (`numCycles_prefix_telescopes` +
`sum_stepDelta_eq_neg_m_add_two_actualSplits`); substituting the two exact counts
`F + 2` and `F + 2·len` turns it into the exact split-count identity. -/

/-- **The exact split-count identity**: for every cycle-list certificate,
`concatLen Ls + 2 = 2 · #(actual splits) + 2 · len` — the hsplits bound holds with
slack `0`, for every cut, every genus. -/
theorem concatLen_add_two_eq_splits (C : SimplePrimalCycle M)
    {Ls : List (List C.CutDart)} (H : C.FaceCorrCycleLists Ls) :
    FaceCorrWord.concatLen Ls + 2
      = 2 * (C.actualSplitFinset Ls).card + 2 * C.len := by
  classical
  let W : Fin (FaceCorrWord.concatLen Ls) → ForcedSplits.Swap C.CutDart :=
    FaceCorrWord.concatWord Ls
  have hpos0 : ∀ L ∈ Ls, 0 < L.length := by
    intro L hL
    have := H.pos L hL
    omega
  have hprefix :
      ForcedSplits.prefixPerm C.phiLift W (FaceCorrWord.concatLen Ls)
        = C.phiLift * C.faceCorr2 := by
    dsimp [W]
    rw [FaceCorrWord.prefixPerm_concatWord C.phiLift Ls hpos0, H.factor]
  have htel := ForcedSplits.numCycles_prefix_telescopes C.phiLift W
  have hsum := ForcedSplits.sum_stepDelta_eq_neg_m_add_two_actualSplits
    C.phiLift W (fun j => C.concatWord_ne_of_nodup H j)
  have hdiff :
      (numCycles (ForcedSplits.prefixPerm C.phiLift W (FaceCorrWord.concatLen Ls)) : ℤ)
        - (numCycles C.phiLift : ℤ)
        =
      -(FaceCorrWord.concatLen Ls : ℤ)
        + 2 * ((C.actualSplitFinset Ls).card : ℤ) := by
    rw [SimplePrimalCycle.actualSplitFinset, htel, hsum]
  rw [hprefix] at hdiff
  rw [C.numCycles_phiLift_mul_faceCorr2, C.numCycles_phiLift] at hdiff
  push_cast at hdiff
  omega

/-- **The hsplits bound** (the exact statement consumed by
`numCycles_phiLift_faceCorr2_lower_of_splitsEnough`), unconditional. -/
theorem splitsEnough (C : SimplePrimalCycle M)
    {Ls : List (List C.CutDart)} (H : C.FaceCorrCycleLists Ls) :
    FaceCorrWord.concatLen Ls + 2
      ≤ 2 * (C.actualSplitFinset Ls).card + 2 * C.len :=
  le_of_eq (C.concatLen_add_two_eq_splits H)

/-- The `∀`-form consumed by the `_all` count-route plumbing. -/
theorem splitsEnough_all (C : SimplePrimalCycle M) :
    ∀ Ls : List (List C.CutDart), C.FaceCorrCycleLists Ls →
      FaceCorrWord.concatLen Ls + 2
        ≤ 2 * (C.actualSplitFinset Ls).card + 2 * C.len :=
  fun _ H => C.splitsEnough H

/-! ## Discharged consumers -/

/-- The count-route lower bound, now unconditional. -/
theorem numCycles_phiLift_faceCorr2_lower_unconditional (C : SimplePrimalCycle M) :
    (numCycles (C.phiLift * C.faceCorr2) : ℤ) ≥ (M.F : ℤ) + 2 :=
  C.numCycles_phiLift_faceCorr2_lower_of_splitsEnough_all C.splitsEnough_all

/-- **Every simple primal cycle carries a split certificate** — the
`FaceCorrSplitCert` residue of `FaceCorrWord.lean`, discharged. -/
noncomputable def faceCorrSplitCertUnconditional (C : SimplePrimalCycle M) :
    C.FaceCorrSplitCert :=
  C.faceCorrSplitCert_of_splitsEnough C.splitsEnough_all

/-- The lower-bound Jordan theorem, now conditional only on the Euler hypothesis and
the connectivity gates (the split certificate is supplied unconditionally). -/
theorem jordan_simple_cycle2_of_gates (C : SimplePrimalCycle M)
    (hchi : M.eulerChar = 2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_lower_of_splitCert C.faceCorrSplitCertUnconditional
    hchi hconn i

end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle

/-- `SphereChordSeparation` from the corrected gate data alone: the face-count side of
`ChordJordanInputLower'` is supplied by the unconditional split certificate. -/
theorem sphereChordSeparation_of_gates {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hgate : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h))) :
    hNT.SphereChordSeparation h :=
  hNT.sphereChordSeparation_of_inputLower' h C hsub
    ⟨C.faceCorrSplitCertUnconditional, hgate⟩ i₀ hleft hright

/-- `Separates` from the corrected gate data alone. -/
theorem separates_of_gates {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hgate : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  hNT.separates_of_inputLower' data C hsub
    ⟨C.faceCorrSplitCertUnconditional, hgate⟩ i₀ hleft hright

end CombMap.NearTriangulation

end ProofsInTheBook.PlanarMap

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.CutCapCount.numCycles_sumCongr
#print axioms ProofsInTheBook.PlanarMap.CombMap.CutCapCount.numCycles_eq_one_of_forall_sameCycle
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.seamSwap_phi2_conj
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.numCycles_seamModel
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.numCycles_cutCapPhi2
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.numCyclesCutPhi2_holds
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.cutCapMap2_F_unconditional
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.numCycles_phiLift_mul_faceCorr2
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.concatLen_add_two_eq_splits
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.splitsEnough
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.splitsEnough_all
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.numCycles_phiLift_faceCorr2_lower_unconditional
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.faceCorrSplitCertUnconditional
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.jordan_simple_cycle2_of_gates
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.sphereChordSeparation_of_gates
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.separates_of_gates
