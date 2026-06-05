import ProofsInTheBook.PlanarMapCutCapV

/-!
# The cut-and-cap face count `F' = F + 2` (Chapter 35 Jordan lemma)

This file closes the `face_count` field of `CutSigmaCounts`
(`PlanarMapCutCapSigma.lean`) for the concrete cut map `C.cutCapMap`:

  `(C.cutCapMap).F = M.F + 2`.

Recall `F = numCycles φ` with `φ = σ * α`, and for the cut map
`φ' = cutSigmaPerm * cutAlphaPerm`.

## The reference and the free algebraic decomposition

Let `alphaLift = α ⊕ 1` and `phiLift = φ ⊕ 1 = (σ*α) ⊕ 1` (caps as `2k` fixed
points).  Then `numCycles phiLift = F + 2k`.  Since the lift `⊕ 1` is a monoid
homomorphism, `phiLift = sigmaLift * alphaLift`, and the V' theorem
`cutSigmaPerm = sigmaLift * mergeProd * splitProd` gives the **free** identity

  `φ' = cutSigmaPerm * cutAlphaPerm = phiLift * G`,
  `G := alphaLift * mergeProd * splitProd * cutAlphaPerm`,

with no case analysis (pure associativity + `alphaLift * alphaLift = 1`).  The
target then reads `numCycles (phiLift * G) = numCycles phiLift - 2k + 2`.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace CutCapCount

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **Cycle count is conjugation-invariant.** -/
lemma numCycles_conj (g f : Equiv.Perm E) :
    _root_.numCycles (g * f * g⁻¹) = _root_.numCycles f := by
  classical
  unfold _root_.numCycles
  refine Fintype.card_congr (Quotient.congr g⁻¹ ?_)
  intro x y
  show (g * f * g⁻¹).SameCycle x y ↔ f.SameCycle (g⁻¹ x) (g⁻¹ y)
  exact Equiv.Perm.sameCycle_conj

/-- **`numCycles` is invariant under swapping factors** (`AB ~ BA`). -/
lemma numCycles_mul_comm (a b : Equiv.Perm E) :
    _root_.numCycles (a * b) = _root_.numCycles (b * a) := by
  have h : b * a = a⁻¹ * (a * b) * a⁻¹⁻¹ := by group
  rw [h, numCycles_conj]

end CutCapCount

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

/-! ## The lifted edge involution `alphaLift = α ⊕ 1` and `phiLift = φ ⊕ 1` -/

/-- `α` extended to the cut-dart set with the `2k` caps as fixed points. -/
noncomputable def alphaLift (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  Equiv.Perm.sumCongr M.α (1 : Equiv.Perm (Fin C.len ⊕ Fin C.len))

@[simp] lemma alphaLift_inl (C : SimplePrimalCycle M) (d : D) :
    C.alphaLift (Sum.inl d) = Sum.inl (M.α d) := by simp [alphaLift]

@[simp] lemma alphaLift_inr (C : SimplePrimalCycle M) (c : Fin C.len ⊕ Fin C.len) :
    C.alphaLift (Sum.inr c) = Sum.inr c := by simp [alphaLift]

/-- `φ = σ*α` extended to the cut-dart set, caps as fixed points. -/
noncomputable def phiLift (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  Equiv.Perm.sumCongr M.φ (1 : Equiv.Perm (Fin C.len ⊕ Fin C.len))

@[simp] lemma phiLift_inl (C : SimplePrimalCycle M) (d : D) :
    C.phiLift (Sum.inl d) = Sum.inl (M.φ d) := by simp [phiLift]

@[simp] lemma phiLift_inr (C : SimplePrimalCycle M) (c : Fin C.len ⊕ Fin C.len) :
    C.phiLift (Sum.inr c) = Sum.inr c := by simp [phiLift]

/-- `alphaLift` is an involution. -/
lemma alphaLift_mul_self (C : SimplePrimalCycle M) :
    C.alphaLift * C.alphaLift = 1 := by
  rw [alphaLift, Equiv.Perm.sumCongr_mul, M.α_invol, one_mul, Equiv.Perm.sumCongr_one]

/-- `phiLift = sigmaLift * alphaLift`: the lift is multiplicative. -/
lemma phiLift_eq (C : SimplePrimalCycle M) :
    C.phiLift = C.sigmaLift * C.alphaLift := by
  rw [phiLift, sigmaLift, alphaLift, Equiv.Perm.sumCongr_mul, one_mul, CombMap.φ]

/-- The cycle count of `phiLift` is `F + 2k`. -/
lemma numCycles_phiLift (C : SimplePrimalCycle M) :
    _root_.numCycles C.phiLift = M.F + 2 * C.len := by
  rw [phiLift, numCycles_sumCongr_one, M.F_eq_numCycles]
  simp [Fintype.card_sum, Fintype.card_fin]; ring

/-! ## The free algebraic decomposition `φ' = phiLift * G` -/

/-- The right factor `G = alphaLift * mergeProd * splitProd * cutAlphaPerm`. -/
noncomputable def faceCorr (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  C.alphaLift * C.mergeProd * C.splitProd * C.cutAlphaPerm

/-- **The face permutation of the cut map factors through `phiLift`.**

`φ' = cutSigmaPerm * cutAlphaPerm = phiLift * G`, a pure-associativity consequence
of the V' decomposition `cutSigmaPerm = sigmaLift * mergeProd * splitProd` and
`phiLift = sigmaLift * alphaLift` (with `alphaLift` an involution). -/
theorem cutCapPhi_eq_phiLift_mul (C : SimplePrimalCycle M) :
    (C.cutCapMap).φ = C.phiLift * C.faceCorr := by
  rw [CombMap.φ, cutCapMap_sigma, cutCapMap_alpha, C.cutSigmaPerm_eq_sigmaLift_mul,
    faceCorr, phiLift_eq]
  -- phiLift * G = (sigmaLift*alphaLift)*(alphaLift*mergeProd*splitProd*cutAlphaPerm)
  --             = sigmaLift*mergeProd*splitProd*cutAlphaPerm
  rw [show C.sigmaLift * C.alphaLift *
        (C.alphaLift * C.mergeProd * C.splitProd * C.cutAlphaPerm)
      = C.sigmaLift * (C.alphaLift * C.alphaLift) * C.mergeProd * C.splitProd
          * C.cutAlphaPerm by group,
    C.alphaLift_mul_self, mul_one]

/-- The target reduces to a `numCycles` statement about `phiLift * G`. -/
theorem cutCapMap_F_iff (C : SimplePrimalCycle M) :
    (C.cutCapMap).F = M.F + 2 ↔
      _root_.numCycles (C.phiLift * C.faceCorr) = M.F + 2 := by
  rw [CombMap.F_eq_numCycles, cutCapPhi_eq_phiLift_mul]

/-! ## The `merged * capCycleProd` regrouping

A second regrouping: since `cutSigmaPerm = sigmaLift * mergeProd * splitProd` and
`merged = sigmaLift * mergeProd` (the V' "merged" permutation, with
`numCycles merged = V`),

  `φ' = cutSigmaPerm * cutAlphaPerm = merged * (splitProd * cutAlphaPerm)`.

Here `capCycleProd := splitProd * cutAlphaPerm`.  On the `2k` cycle darts and the
`2k` caps it acts by the `k` pairwise **disjoint 4-cycles**

  `inl(dart i) ↦ c_i^- ↦ inl(α dart i) ↦ c_i^+ ↦ inl(dart i)`,

and on a non-cycle `inl d` it acts as the old pairing `inl d ↦ inl(α d)` (so
`capCycleProd` is *not* close to the identity — it carries the full `α`-involution
on non-cycle darts).  The clean small-perturbation form for swap counting is
instead `φ' = phiLift * faceCorr` (above), with `faceCorr` fixing every non-cycle
dart whose `σ`-successor is not a bank-start. -/

/-- `capCycleProd = splitProd * cutAlphaPerm`. -/
noncomputable def capCycleProd (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  C.splitProd * C.cutAlphaPerm

/-- **The useful regrouping `φ' = merged * capCycleProd`.** -/
theorem cutCapPhi_eq_merged_mul (C : SimplePrimalCycle M) :
    (C.cutCapMap).φ = C.merged * C.capCycleProd := by
  rw [CombMap.φ, cutCapMap_sigma, cutCapMap_alpha, C.cutSigmaPerm_eq_sigmaLift_mul,
    merged, capCycleProd, mul_assoc]

/-! ### The action of `capCycleProd` (the disjoint 4-cycles)

`capCycleProd = splitProd * cutAlphaPerm`.  Applying `cutAlpha` first, then
`splitProd`, gives, for each `i`, the 4-cycle
`inl(dart i) ↦ c_i^- ↦ inl(α dart i) ↦ c_i^+ ↦ inl(dart i)`, and on a non-cycle
`inl d` it acts as the old pairing `inl d ↦ inl(α d)`. -/

@[simp] lemma capCycleProd_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.capCycleProd (Sum.inl (C.dart i)) = C.capM i := by
  rw [capCycleProd, Equiv.Perm.mul_apply, cutAlphaPerm_apply, cutAlpha_dart,
    show (Sum.inr (Sum.inl i) : C.CutDart) = C.capP i from rfl, splitProd_capP]

@[simp] lemma capCycleProd_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.capCycleProd (C.capM i) = Sum.inl (M.α (C.dart i)) := by
  rw [capCycleProd, Equiv.Perm.mul_apply, capM, cutAlphaPerm_apply, cutAlpha_capMinus,
    splitProd_inl]

@[simp] lemma capCycleProd_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.capCycleProd (Sum.inl (M.α (C.dart i))) = C.capP i := by
  rw [capCycleProd, Equiv.Perm.mul_apply, cutAlphaPerm_apply, cutAlpha_alpha_dart,
    show (Sum.inr (Sum.inr i) : C.CutDart) = C.capM i from rfl, splitProd_capM]

@[simp] lemma capCycleProd_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.capCycleProd (C.capP i) = Sum.inl (C.dart i) := by
  rw [capCycleProd, Equiv.Perm.mul_apply, capP, cutAlphaPerm_apply, cutAlpha_capPlus,
    splitProd_inl]

/-- On a non-cycle `inl d` (`d ∉ dartSet`), `capCycleProd` acts as the old pairing
`α`. -/
lemma capCycleProd_inl_other (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet) :
    C.capCycleProd (Sum.inl d) = Sum.inl (M.α d) := by
  rw [capCycleProd, Equiv.Perm.mul_apply, cutAlphaPerm_apply, C.cutAlpha_other h,
    splitProd_inl]

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap
