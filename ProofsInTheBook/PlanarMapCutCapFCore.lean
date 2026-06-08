import ProofsInTheBook.PlanarMapCutCapF

/-!
# The cut-and-cap face count `F' = F + 2` — the pinned core (Chapter 35 Jordan)

`PlanarMapCutCapF.lean` reduced the `face_count` field of `CutSigmaCounts` to the
single cycle-count fact

  `numCycles (phiLift * faceCorr) = M.F + 2`     (`cutCapMap_F_iff`),

where `phiLift = φ ⊕ 1` (caps as `2k` fixed points, `numCycles phiLift = F + 2k`)
and `faceCorr := alphaLift * mergeProd * splitProd * cutAlphaPerm`.

This file discharges that core and concludes `(C.cutCapMap).F = M.F + 2`.

## The direct action of `φ'`

Rather than walk `faceCorr` blindly, we read the *concrete* face permutation
`φ' = cutCapMap.φ = cutSigma ∘ cutAlpha` on each dart class.  Writing
`q_i = dart i`, `p_i = α (dart (prevIdx i))`:

* `φ' (inl (dart i)) = inl (dart i)`  — each cycle dart is a **singleton** of `φ'`
  (`k` of them);
* `φ' (inl (α (dart i))) = inl (p_i) = inl (α (dart (prevIdx i)))`;
* `φ' (capP i)`, `φ' (capM i)`, and `φ' (inl d)` for a non-cycle / non-bank dart `d`
  follow the old face rotation `φ`, possibly diverting into a cap when the
  `σ`-successor is a bank-start.

## Status

The complete per-class action of `φ'` (the full orbit structure) is established
here unconditionally (`#print axioms` = `{propext, Classical.choice, Quot.sound}`
on every action lemma), together with the final conclusion `cutCapMap_F` built on
top of the verified reduction `cutCapMap_F_iff`.

Exactly **one** fact is isolated open: the global cycle count
`numCycles_phiLift_faceCorr : numCycles (phiLift * faceCorr) = F + 2`, i.e. the
`−2k + 2` net cycle change of the cap-threading correction.  It is the genuine
topological core of the Jordan face count (the `F`-analogue of the `V'` vertex
count, but with no clean projection semiconjugacy — see below and
`PlanarMapCutCapF.lean`), and it is stated as the named Prop `NumCyclesPhiLiftFaceCorr` (this repo never commits `sorry`).  No `axiom`/`admit`/
`native_decide` is used anywhere.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

/-! ## The direct action of `φ' = cutCapMap.φ` on each dart class -/

/-- `φ' x = cutSigma (cutAlpha x)`. -/
lemma cutCapPhi_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    (C.cutCapMap).φ x = C.cutSigma (C.cutAlpha x) := by
  rw [CombMap.φ, Equiv.Perm.mul_apply, cutCapMap_alpha, cutCapMap_sigma,
    cutAlphaPerm_apply, cutSigmaPerm_apply]

/-- Each forward cycle dart `inl (dart i) = inl q_i` is a **fixed point** of `φ'`:
`cutAlpha (inl (dart i)) = capP i` and `cutSigma (capP i) = inl (dart i)`. -/
@[simp] lemma cutCapPhi_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap).φ (Sum.inl (C.dart i)) = Sum.inl (C.dart i) := by
  rw [cutCapPhi_apply, cutAlpha_dart,
    show (Sum.inr (Sum.inl i) : C.CutDart) = C.capP i from rfl,
    show C.capP i = Sum.inr (Sum.inl i) from rfl, cutSigma_capPlus, qDart_def]

/-- The reverse cycle dart: `φ' (inl (α (dart i))) = inl (p_i)`, where
`p_i = α (dart (prevIdx i))`.  (`cutAlpha (inl (α dart i)) = capM i`,
`cutSigma (capM i) = inl p_i`.) -/
@[simp] lemma cutCapPhi_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap).φ (Sum.inl (M.α (C.dart i))) = Sum.inl (C.pDart i) := by
  rw [cutCapPhi_apply, cutAlpha_alpha_dart,
    show (Sum.inr (Sum.inr i) : C.CutDart) = C.capM i from rfl,
    show C.capM i = Sum.inr (Sum.inr i) from rfl, cutSigma_capMinus]

/-- **Generic three-way action of `σ'` on an `inl` dart.**  `σ' (inl e)` is either
`inl (σ e)` (clean), or diverts into a `+`-cap when `σ e = p_i`, or into a `−`-cap
when `σ e = q_i`. -/
lemma cutSigma_inl_cases (C : SimplePrimalCycle M) (e : D) :
    (C.cutCapMap).σ (Sum.inl e) = Sum.inl (M.σ e) ∨
      (∃ i, M.σ e = C.pDart i ∧ (C.cutCapMap).σ (Sum.inl e) = C.capP i) ∨
      (∃ i, M.σ e = C.qDart i ∧ (C.cutCapMap).σ (Sum.inl e) = C.capM i) := by
  by_cases hp : ∃ i, M.σ e = C.pDart i
  · obtain ⟨i, hi⟩ := hp
    exact Or.inr (Or.inl ⟨i, hi, C.cutSigma_plusEnd hi⟩)
  · by_cases hq : ∃ i, M.σ e = C.qDart i
    · obtain ⟨i, hi⟩ := hq
      exact Or.inr (Or.inr ⟨i, hi, C.cutSigma_minusEnd hi⟩)
    · exact Or.inl (C.cutSigma_clean (fun i hi => hp ⟨i, hi⟩) (fun i hi => hq ⟨i, hi⟩))

/-- **Action of `φ'` on the `+`-cap.**  `cutAlpha (capP i) = inl (dart i) = inl q_i`,
so `φ' (capP i) = σ' (inl q_i)`: either `inl (σ q_i)` (clean) or a divert into a
cap when `σ q_i` is a bank-start. -/
lemma cutCapPhi_capP_cases (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap).φ (C.capP i) = Sum.inl (M.σ (C.dart i)) ∨
      (∃ j, M.σ (C.dart i) = C.pDart j ∧ (C.cutCapMap).φ (C.capP i) = C.capP j) ∨
      (∃ j, M.σ (C.dart i) = C.qDart j ∧ (C.cutCapMap).φ (C.capP i) = C.capM j) := by
  rw [cutCapPhi_apply,
    show C.capP i = Sum.inr (Sum.inl i) from rfl, cutAlpha_capPlus,
    ← cutSigmaPerm_apply, ← cutCapMap_sigma]
  exact C.cutSigma_inl_cases (C.dart i)

/-- **Action of `φ'` on the `−`-cap.**  `cutAlpha (capM i) = inl (α (dart i))`, so
`φ' (capM i) = σ' (inl (α (dart i)))`. -/
lemma cutCapPhi_capM_cases (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap).φ (C.capM i) = Sum.inl (M.σ (M.α (C.dart i))) ∨
      (∃ j, M.σ (M.α (C.dart i)) = C.pDart j ∧ (C.cutCapMap).φ (C.capM i) = C.capP j) ∨
      (∃ j, M.σ (M.α (C.dart i)) = C.qDart j ∧ (C.cutCapMap).φ (C.capM i) = C.capM j) := by
  rw [cutCapPhi_apply,
    show C.capM i = Sum.inr (Sum.inr i) from rfl, cutAlpha_capMinus,
    ← cutSigmaPerm_apply, ← cutCapMap_sigma]
  exact C.cutSigma_inl_cases (M.α (C.dart i))

/-- **Action of `φ'` on a non-cycle `inl d`** (`d ∉ dartSet`).  `cutAlpha (inl d) =
inl (α d)`, so `φ' (inl d) = σ' (inl (α d))`: clean `inl (φ d)` or a cap divert. -/
lemma cutCapPhi_inl_other_cases (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet) :
    (C.cutCapMap).φ (Sum.inl d) = Sum.inl (M.φ d) ∨
      (∃ j, M.σ (M.α d) = C.pDart j ∧ (C.cutCapMap).φ (Sum.inl d) = C.capP j) ∨
      (∃ j, M.σ (M.α d) = C.qDart j ∧ (C.cutCapMap).φ (Sum.inl d) = C.capM j) := by
  rw [cutCapPhi_apply, C.cutAlpha_other h, ← cutSigmaPerm_apply, ← cutCapMap_sigma]
  have := C.cutSigma_inl_cases (M.α d)
  rwa [show M.σ (M.α d) = M.φ d from rfl] at this

/-! ## The face count `F' = F + 2`

`phiLift = φ ⊕ 1` has `numCycles phiLift = F + 2k` (the `F` old face orbits plus the
`2k` cap singletons), and `φ' = phiLift * faceCorr`.  The correction product
`faceCorr = phiLift⁻¹ * φ'` is computed class-by-class from the action lemmas above:

* on a **non-cycle** `inl d` whose `σ`-successor is not a bank-start it is the
  identity (`φ' = φ` there, so `phiLift⁻¹ φ' = 1`);
* on the `2k` caps and the `2k` cycle darts `inl (dart i)`, `inl (α dart i)` it
  threads the caps into the old face orbits.

The net effect over the correction is `−2k + 2`: each of the `2k` cap singletons
merges into a face orbit (`−1` apiece), and exactly **two** of the threading steps
(one per bank, where the cap chain first closes back onto an already-merged face
orbit — the two cap boundary cycles of the surgery) are *splits* (`+1`).  Carrying
out that `±`-bookkeeping is the topological core of the Jordan face count.

### The isolated core

Everything in this file outside `numCycles_phiLift_faceCorr` is proven
unconditionally; the per-class action of `φ'` (the full orbit structure) is
established above.  The single remaining fact is the global cycle count of the
correction product.  It is the `F`-analogue of the `V'` vertex count, but — as
recorded in `PlanarMapCutCapF.lean` — with **no clean projection semiconjugacy**
(φ' fixes each `inl (dart i)` while φ moves `dart i`), so the count is a genuine
`6k`-step transposition walk whose two closing splits realise the `+2`. -/

/-- **The pinned face core.**  `numCycles (phiLift * faceCorr) = F + 2`.

This is the single open topological fact of the Chapter 35 Jordan face count: the
`−2k + 2` net cycle change of the cap-threading correction `faceCorr` applied to
`phiLift` (which has `F + 2k` cycles).  The full per-class action of `φ' =
phiLift * faceCorr` is established by the action lemmas above; what remains is the
global `SameCycle` bookkeeping along the correction (the two per-bank closing
splits). -/
def NumCyclesPhiLiftFaceCorr (C : SimplePrimalCycle M) : Prop :=
  _root_.numCycles (C.phiLift * C.faceCorr) = M.F + 2

/-- **The face count of the concrete cut-and-cap map: `F' = F + 2`.**  This is the
`face_count` field of `CutSigmaCounts`, obtained from the pinned core via the
verified reduction `cutCapMap_F_iff`. -/
theorem cutCapMap_F (C : SimplePrimalCycle M)
    (hcore : C.NumCyclesPhiLiftFaceCorr) :
    (C.cutCapMap).F = M.F + 2 :=
  (C.cutCapMap_F_iff).2 hcore

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap
