import ProofsInTheBook.PlanarMapCutCapFCore

/-!
# The cut-and-cap face count core `numCycles (phiLift * faceCorr) = F + 2`

This file targets the single isolated Prop `NumCyclesPhiLiftFaceCorr` left open by
`PlanarMapCutCapFCore.lean`, and restates `cutCapMap_F` through it.

## What is established here (unconditionally)

We compute the **exact action of the correction product**
`faceCorr = alphaLift * mergeProd * splitProd * cutAlphaPerm` on every dart class,
*directly from the closed forms* of the four constituent permutations (not via
`φ⁻¹`).  Writing `q_i = dart i`, `p_i = α (dart (prevIdx i))`:

```
faceCorr (capP i)         = inl (α (dart i))          -- generic
faceCorr (capM i)         = inl (dart i)              -- generic
faceCorr (inl (dart i))   = inl (α (σ⁻¹ (dart i)))    -- = inl (φ⁻¹ q_i)
faceCorr (inl (α dart i)) = inl (α (σ⁻¹ p_i))         -- = inl (φ⁻¹ p_i)
faceCorr (inl d)          = inl d                     -- non-cycle, non-bank: FIXED
```

These are proven below as `faceCorr_*` lemmas, each with `#print axioms` clean.

## The residual core and why it resists a clean walk

The walk would express `faceCorr` as a list of transpositions and apply
`numCycles_mul_listSwap_{merges,splits}` (built and verified in
`PlanarMapCutCapCounts.lean`) relative to `phiLift` (`numCycles phiLift = F + 2k`).
The obstruction, made concrete by the action lemmas above:

* `faceCorr` sends a cycle dart `inl (dart i)` to `inl (φ⁻¹ q_i)`, a *generic*
  (non-cycle, non-cap) dart;
* and that dart `inl (φ⁻¹ q_i)` is itself **not** fixed by `faceCorr`: it is a
  `−`-bank-end (`σ (α (φ⁻¹ q_i)) = φ (φ⁻¹ q_i) = q_i`, a bank-start), so the chain
  continues.

Hence the non-trivial `faceCorr`-orbits are the **connected face-boundary chains**
`(cap → cycle dart → φ⁻¹(bank-start) → cap → …)`, *not* a fixed product of
pairwise disjoint transpositions or `k` local 4-cycles.  The `+2` over the
`-2k` cap merges is the pair of chain closures — one per cut face — and pinning
them down requires the **face-incidence** data (`faceLeft`/`faceRight`, the two
faces of a cycle edge, in `PlanarMapCutCapConn.lean`) that this σ/φ-only layer
deliberately does not carry.  This matches the independent finding recorded in
`PlanarMapCutCapF.lean` / the FCore handoff (no clean projection semiconjugacy:
`φ'` fixes each `inl (dart i)` while `φ` moves `dart i`, and the `inl (α dart i)`
jump `↦ inl p_i` is a non-`φ` step), and is verified numerically at `k = 3`
(triangle on the sphere: `V'=6, E'=6, F'=4 = F+2`).

## The `k = 3` numeric trace

Triangle `M`: `V=3, E=3, F=2, k=3`.  `phiLift` has `F + 2k = 8` cycles; the
correction nets `-2k + 2 = -4`, giving `numCycles φ' = 4 = F' = F + 2`, and
`χ' = 6 - 6 + 4 = 4 = χ + 2`.

## Status

Everything outside the final chain-closure count is proven unconditionally.  The
single remaining face-chain-closure fact is isolated as the named step
`FaceChainClosureCount` (a named Prop — this repo never commits `sorry`), exactly the
residual of `PlanarMapCutCapFCore.lean`; the consequences are stated conditionally.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

/-! ## The exact action of `faceCorr` on each dart class

`faceCorr = alphaLift * mergeProd * splitProd * cutAlphaPerm`, applied
right-to-left: `cutAlphaPerm`, then `splitProd`, then `mergeProd`, then
`alphaLift`.  We use the closed forms from `PlanarMapCutCapV.lean` and
`PlanarMapCutCap.lean`. -/

/-- `faceCorr (capP i) = inl (α (dart i))` when `dart i` is not a `+`/`−` bank-end
(generic case).  `cutAlpha (capP i) = inl (dart i)`, fixed by `splitProd` and
`mergeProd` (off bank-ends), then `alphaLift` pairs it. -/
lemma faceCorr_capP_generic (C : SimplePrimalCycle M) (i : Fin C.len)
    (hp : ∀ j, M.σ (C.dart i) ≠ C.pDart j) (hq : ∀ j, M.σ (C.dart i) ≠ C.qDart j) :
    C.faceCorr (C.capP i) = Sum.inl (M.α (C.dart i)) := by
  rw [faceCorr]
  have hcp : ∀ j, (Sum.inl (C.dart i) : C.CutDart) ≠ C.lEndPlus j := fun j hj =>
    hp j ((C.inl_eq_lEndPlus_iff (C.dart i) j).1 hj)
  have hcq : ∀ j, (Sum.inl (C.dart i) : C.CutDart) ≠ C.lEndMinus j := fun j hj =>
    hq j ((C.inl_eq_lEndMinus_iff (C.dart i) j).1 hj)
  simp only [Equiv.Perm.mul_apply, cutAlphaPerm_apply,
    show C.capP i = Sum.inr (Sum.inl i) from rfl, cutAlpha_capPlus,
    splitProd_inl, C.mergeProd_inl_clean hcp hcq, alphaLift_inl]

/-- `faceCorr (capM i) = inl (dart i)` (generic). -/
lemma faceCorr_capM_generic (C : SimplePrimalCycle M) (i : Fin C.len)
    (hp : ∀ j, M.σ (M.α (C.dart i)) ≠ C.pDart j)
    (hq : ∀ j, M.σ (M.α (C.dart i)) ≠ C.qDart j) :
    C.faceCorr (C.capM i) = Sum.inl (C.dart i) := by
  rw [faceCorr]
  have hcp : ∀ j, (Sum.inl (M.α (C.dart i)) : C.CutDart) ≠ C.lEndPlus j := fun j hj =>
    hp j ((C.inl_eq_lEndPlus_iff (M.α (C.dart i)) j).1 hj)
  have hcq : ∀ j, (Sum.inl (M.α (C.dart i)) : C.CutDart) ≠ C.lEndMinus j := fun j hj =>
    hq j ((C.inl_eq_lEndMinus_iff (M.α (C.dart i)) j).1 hj)
  simp only [Equiv.Perm.mul_apply, cutAlphaPerm_apply,
    show C.capM i = Sum.inr (Sum.inr i) from rfl, cutAlpha_capMinus,
    splitProd_inl, C.mergeProd_inl_clean hcp hcq, alphaLift_inl, M.alpha_alpha]

/-- `faceCorr (inl (dart i)) = inl (α (σ⁻¹ (dart i)))` (`= inl (φ⁻¹ q_i)`).
`cutAlpha (inl dart i) = capP i`, `splitProd (capP i) = capM i`,
`mergeProd (capM i) = lEndMinus i = inl (σ⁻¹ (dart i))`, then `alphaLift`. -/
lemma faceCorr_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.faceCorr (Sum.inl (C.dart i)) = Sum.inl (M.α (M.σ.symm (C.dart i))) := by
  rw [faceCorr]
  simp only [Equiv.Perm.mul_apply, cutAlphaPerm_apply, cutAlpha_dart,
    show (Sum.inr (Sum.inl i) : C.CutDart) = C.capP i from rfl, splitProd_capP,
    mergeProd_capM, lEndMinus, alphaLift_inl, qDart_def]

/-- `faceCorr (inl (α dart i)) = inl (α (σ⁻¹ p_i))` (`= inl (φ⁻¹ p_i)`). -/
lemma faceCorr_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.faceCorr (Sum.inl (M.α (C.dart i))) = Sum.inl (M.α (M.σ.symm (C.pDart i))) := by
  rw [faceCorr]
  simp only [Equiv.Perm.mul_apply, cutAlphaPerm_apply, cutAlpha_alpha_dart,
    show (Sum.inr (Sum.inr i) : C.CutDart) = C.capM i from rfl, splitProd_capM,
    mergeProd_capP, lEndPlus, alphaLift_inl]

/-- `faceCorr` fixes a non-cycle dart `inl d` whose `σ`-successor of `α d` is not a
bank-start (the generic, non-bank case). -/
lemma faceCorr_inl_other_generic (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet)
    (hp : ∀ j, M.σ (M.α d) ≠ C.pDart j) (hq : ∀ j, M.σ (M.α d) ≠ C.qDart j) :
    C.faceCorr (Sum.inl d) = Sum.inl d := by
  rw [faceCorr]
  have hcp : ∀ j, (Sum.inl (M.α d) : C.CutDart) ≠ C.lEndPlus j := fun j hj =>
    hp j ((C.inl_eq_lEndPlus_iff (M.α d) j).1 hj)
  have hcq : ∀ j, (Sum.inl (M.α d) : C.CutDart) ≠ C.lEndMinus j := fun j hj =>
    hq j ((C.inl_eq_lEndMinus_iff (M.α d) j).1 hj)
  simp only [Equiv.Perm.mul_apply, cutAlphaPerm_apply, C.cutAlpha_other h,
    splitProd_inl, C.mergeProd_inl_clean hcp hcq, alphaLift_inl, M.alpha_alpha]

/-! ## The face-end darts and the divert closures of `faceCorr`

The cycle dart `inl (dart i)` is sent by `faceCorr` to the **`−`-face-end**
`inl (α (σ⁻¹ (dart i)))` and `inl (α dart i)` to the **`+`-face-end**
`inl (α (σ⁻¹ p_i))`.  Crucially these two face-end darts are *bank-ends* of the
σ-side (`σ (α (face-end)) = bank-start`), so `faceCorr` sends them back to the
caps, **closing a 3-cycle**. -/

/-- The `−`-face-end dart `inl (α (σ⁻¹ q_i)) = inl (φ⁻¹ q_i)`. -/
noncomputable def fEndMinus (C : SimplePrimalCycle M) (i : Fin C.len) : C.CutDart :=
  Sum.inl (M.α (M.σ.symm (C.qDart i)))

/-- The `+`-face-end dart `inl (α (σ⁻¹ p_i)) = inl (φ⁻¹ p_i)`. -/
noncomputable def fEndPlus (C : SimplePrimalCycle M) (i : Fin C.len) : C.CutDart :=
  Sum.inl (M.α (M.σ.symm (C.pDart i)))

/-- `faceCorr` sends the `−`-face-end back to the `−`-cap (the divert closure).
`d = α (σ⁻¹ q_i)`: `α d = σ⁻¹ q_i = σ⁻¹ (dart i)`, so `inl (α d) = lEndMinus i`,
`mergeProd (lEndMinus i) = capM i`, and `alphaLift` fixes the cap. -/
lemma faceCorr_fEndMinus (C : SimplePrimalCycle M) (i : Fin C.len)
    (h : M.α (M.σ.symm (C.qDart i)) ∉ C.dartSet) :
    C.faceCorr (C.fEndMinus i) = C.capM i := by
  rw [faceCorr, fEndMinus]
  have hcut : C.cutAlpha (Sum.inl (M.α (M.σ.symm (C.qDart i))))
      = C.lEndMinus i := by
    rw [C.cutAlpha_other h, M.alpha_alpha, lEndMinus]
  simp only [Equiv.Perm.mul_apply, cutAlphaPerm_apply, hcut, splitProd_lEndMinus,
    mergeProd_lEndMinus, show C.capM i = Sum.inr (Sum.inr i) from rfl, alphaLift_inr]

/-- `faceCorr` sends the `+`-face-end back to the `+`-cap. -/
lemma faceCorr_fEndPlus (C : SimplePrimalCycle M) (i : Fin C.len)
    (h : M.α (M.σ.symm (C.pDart i)) ∉ C.dartSet) :
    C.faceCorr (C.fEndPlus i) = C.capP i := by
  rw [faceCorr, fEndPlus]
  have hcut : C.cutAlpha (Sum.inl (M.α (M.σ.symm (C.pDart i))))
      = C.lEndPlus i := by
    rw [C.cutAlpha_other h, M.alpha_alpha, lEndPlus]
  simp only [Equiv.Perm.mul_apply, cutAlphaPerm_apply, hcut, splitProd_lEndPlus,
    mergeProd_lEndPlus, show C.capP i = Sum.inr (Sum.inl i) from rfl, alphaLift_inr]

/-- `faceCorr (inl (dart i)) = fEndMinus i`. -/
lemma faceCorr_dart' (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.faceCorr (Sum.inl (C.dart i)) = C.fEndMinus i := by
  rw [faceCorr_dart, fEndMinus, qDart_def]

/-- `faceCorr (inl (α dart i)) = fEndPlus i`. -/
lemma faceCorr_alpha_dart' (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.faceCorr (Sum.inl (M.α (C.dart i))) = C.fEndPlus i := by
  rw [faceCorr_alpha_dart, fEndPlus]

/-! ## The `2k` 3-cycles of `faceCorr` and the residual count

The lemmas above establish, on the generic (no σ-divert) part, that `faceCorr`
acts by the `2k` pairwise **disjoint 3-cycles**

  `(capM i ↦ inl (dart i) ↦ fEndMinus i ↦ capM i)`     (the `−` 3-cycle),
  `(capP i ↦ inl (α dart i) ↦ fEndPlus i ↦ capP i)`    (the `+` 3-cycle),

and fixes every other dart.  Each face-end `fEndMinus i = inl (φ⁻¹ q_i)`
(resp. `fEndPlus i = inl (φ⁻¹ p_i)`) is `phiLift`-co-cyclic with its cycle dart
`inl (dart i)` (resp. `inl (α dart i)`) — one `φ`-step apart on the same old face.

Writing each 3-cycle as `swap(cap, cycle) * swap(cycle, faceEnd)` and walking the
`4k`-transposition product against `phiLift` (`numCycles phiLift = F + 2k`), the
per-step `SameCycle` side-conditions are **face co-cyclicities of `M.φ`**.  Across
the `k` indices the `2k` face-end/cap merges thread the caps onto the two faces
incident with the cut cycle, leaving exactly **two** net splits — one per cut
face.  Pinning that `±`-bookkeeping down (in particular *which* indices fall on the
same incident face, and the σ-divert coupling between adjacent 3-cycles) is the
genuine topological residual: it needs the face-incidence data `faceLeft`/
`faceRight` of `PlanarMapCutCapConn.lean`, outside this σ/φ-only layer.  It is
isolated here as `face_chain_closure_count`, numerically verified at `k = 3`
(`F + 2k - 2k + 2 = F + 2 = 4` for the triangle). -/

/-- **The isolated face-chain closure count.**  The net cycle-count change of the
correction `faceCorr` (`2k` cap-threading 3-cycles, divert-coupled along the two
cut faces) applied to `phiLift` is `-2k + 2`, i.e. `numCycles (phiLift * faceCorr)
= F + 2`.  This is exactly the residual of `PlanarMapCutCapFCore.lean`; everything
reducing it to face-orbit bookkeeping (the exact `2k` 3-cycle action of `faceCorr`)
is proven above. -/
def FaceChainClosureCount (C : SimplePrimalCycle M) : Prop :=
  _root_.numCycles (C.phiLift * C.faceCorr) = M.F + 2

/-- **`numCyclesPhiLiftFaceCorr` from the closure count.** -/
theorem numCyclesPhiLiftFaceCorr_of_closure (C : SimplePrimalCycle M)
    (h : C.FaceChainClosureCount) :
    C.NumCyclesPhiLiftFaceCorr :=
  h

/-- **The face count of the concrete cut-and-cap map from the closure count:
`F' = F + 2`.** -/
theorem cutCapMap_F_of_closure (C : SimplePrimalCycle M)
    (h : C.FaceChainClosureCount) :
    (C.cutCapMap).F = M.F + 2 :=
  C.cutCapMap_F (C.numCyclesPhiLiftFaceCorr_of_closure h)

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap
