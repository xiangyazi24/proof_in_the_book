import ProofsInTheBook.PlanarMapCutCapSigma2
import ProofsInTheBook.PlanarMapCutCapFCore

/-!
# The CORRECTED cut-and-cap counts `V' = V + k`, `F' = F + 2` (Chapter 35 Jordan)

This file closes the count fields of `CutSigmaCounts2`
(`PlanarMapCutCapSigma2.lean`) for the **corrected** cut map `C.cutCapMap2`:

* `V' = (cutCapMap2).V = M.V + C.len`  — **proved unconditionally**;
* `F' = (cutCapMap2).F = M.F + 2`      — reduced to one named corrected-map core;
* assembly: the narrowest chord-separation theorem for the corrected map.

## The key observation: `σ'₂` is conjugate to `σ'` (the buggy rotation)

The corrected vertex rotation `cutSigma2` differs from the buggy `cutSigma`
(`PlanarMapCutCapSigma.lean`) **only** at the `+`-cap wiring:

```
σ'  (ℓ_i^+) = c_i^+               σ'  (c_i^+) = q_i                   -- buggy
σ'₂ (ℓ_i^+) = c_{prevIdx i}^+     σ'₂ (c_i^+) = dart (nextIdx i) = q_{nextIdx i}  -- corrected
```

and agrees on the `−`-bank, the caps `c_i^-`, and every clean `inl d`.  This is
*exactly* an index shift of the `+`-caps: writing `g` for the permutation that
sends `c_i^+ ↦ c_{nextIdx i}^+` and fixes every `inl d` and every `c_i^-`, one
checks dart-by-dart that

```
g (σ'₂ x) = σ' (g x)      for all x,   i.e.   σ'₂ = g⁻¹ · σ' · g.
```

(The cap-shift consumes the `prevIdx`/`nextIdx` discrepancy via
`nextIdx_prevIdx`.)  Since `numCycles` is conjugation-invariant
(`CutCapCount.numCycles_conj`), the corrected vertex count equals the buggy one,
which is already proved to be `V + k` (`numCycles_cutSigmaPerm`,
`PlanarMapCutCapV.lean`).  This ports `V'` with no re-run of the `963`-line
transposition machinery.

## The face count `F' = F + 2` (the genuine new content of the fix)

`α'` is unchanged, so `φ'₂ = σ'₂ · α'`.  The conjugation does **not** carry over
to `φ` (`g` does not commute with `α'`), so `F'` is not obtained for free — it is
the genuine topological core that the fix repairs (the buggy map has the wrong
`F'`).  We establish the per-class action of `φ'₂` and reduce `F' = F + 2` to the
single corrected cycle-count fact `NumCyclesCutPhi2`, isolated as a named `Prop`
(this repo never commits `sorry`).  The kernel arbitration
(`PlanarMapCutCapEval.lean`) confirms it on the triangle (`F' = 4 = F + 2`) and
tetrahedron (`F' = 6 = F + 2`).

No `sorry`/`axiom`/`admit`/`native_decide`.
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

/-! ## The `+`-cap index-shift conjugator `g`

`nextIdx` is a bijection of `Fin C.len` (two-sided inverse `prevIdx`).  We lift it
to a permutation of the cut-dart set fixing every `inl d` and every `c_i^-`, and
shifting `c_i^+ ↦ c_{nextIdx i}^+`. -/

/-- `nextIdx` as an `Equiv.Perm (Fin C.len)`, with inverse `prevIdx`. -/
def nextIdxEquiv (C : SimplePrimalCycle M) : Equiv.Perm (Fin C.len) where
  toFun := C.nextIdx
  invFun := C.prevIdx
  left_inv := C.prevIdx_nextIdx
  right_inv := C.nextIdx_prevIdx

@[simp] lemma nextIdxEquiv_apply (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.nextIdxEquiv i = C.nextIdx i := rfl

@[simp] lemma nextIdxEquiv_symm_apply (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.nextIdxEquiv.symm i = C.prevIdx i := rfl

/-- The `+`-cap index-shift conjugator: identity on `D` and on the `−`-caps,
`c_i^+ ↦ c_{nextIdx i}^+` on the `+`-caps. -/
def capShift (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  Equiv.Perm.sumCongr (1 : Equiv.Perm D)
    (Equiv.Perm.sumCongr C.nextIdxEquiv (1 : Equiv.Perm (Fin C.len)))

@[simp] lemma capShift_inl (C : SimplePrimalCycle M) (d : D) :
    C.capShift (Sum.inl d) = Sum.inl d := by simp [capShift]

@[simp] lemma capShift_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.capShift (Sum.inr (Sum.inl i)) = Sum.inr (Sum.inl (C.nextIdx i)) := by
  simp [capShift]

@[simp] lemma capShift_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.capShift (Sum.inr (Sum.inr i)) = Sum.inr (Sum.inr i) := by simp [capShift]

@[simp] lemma capShift_symm_inl (C : SimplePrimalCycle M) (d : D) :
    C.capShift.symm (Sum.inl d) = Sum.inl d := by
  simp [capShift]

@[simp] lemma capShift_symm_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.capShift.symm (Sum.inr (Sum.inl i)) = Sum.inr (Sum.inl (C.prevIdx i)) := by
  simp [capShift]

@[simp] lemma capShift_symm_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.capShift.symm (Sum.inr (Sum.inr i)) = Sum.inr (Sum.inr i) := by
  simp [capShift]

/-! ## The conjugation `σ'₂ = g⁻¹ · σ' · g`

We prove the equivalent form `g (σ'₂ x) = σ' (g x)` on each dart class, then turn
it into the conjugation identity. -/

/-- The conjugation intertwiner: `g ∘ σ'₂ = σ' ∘ g`. -/
lemma capShift_cutSigma2 (C : SimplePrimalCycle M) (x : C.CutDart) :
    C.capShift (C.cutSigma2 x) = C.cutSigma (C.capShift x) := by
  rcases x with d | (i | i)
  · -- inl d : classify by divertKind d (shared by cutSigma and cutSigma2)
    rcases hd : C.divertKind d with (i | i) | u
    · -- ℓ_i^+ : σ'₂ ↦ c_{prevIdx i}^+, shifted back to c_i^+ = σ' (inl d)
      rw [C.cutSigma2_inl_plus hd, capShift_capP, C.nextIdx_prevIdx, capShift_inl,
        C.cutSigma_inl_plus hd]
    · -- ℓ_i^- : both ↦ c_i^-, g fixes inl d and c_i^-
      rw [C.cutSigma2_inl_minus hd, capShift_capM, capShift_inl, C.cutSigma_inl_minus hd]
    · -- clean : both ↦ inl (σ d), g fixes both inl darts
      rw [C.cutSigma2_inl_none hd, capShift_inl, capShift_inl, C.cutSigma_inl_none hd]
  · -- c_i^+ : σ'₂ (c_i^+) = inl (dart (nextIdx i)) = inl (q_{nextIdx i})
    rw [C.cutSigma2_capPlus, capShift_inl, capShift_capP, C.cutSigma_capPlus, qDart_def]
  · -- c_i^- : σ'₂ (c_i^-) = inl (p_i); g fixes c_i^- and inl (p_i)
    rw [C.cutSigma2_capMinus, capShift_inl, capShift_capM, C.cutSigma_capMinus]

/-- **The conjugation identity** `σ'₂ = g⁻¹ · σ' · g`. -/
theorem cutSigmaPerm2_eq_conj (C : SimplePrimalCycle M) :
    C.cutSigmaPerm2 = C.capShift⁻¹ * C.cutSigmaPerm * C.capShift := by
  ext x
  rw [cutSigmaPerm2_apply, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul,
    Function.comp_apply, Function.comp_apply, cutSigmaPerm_apply]
  -- goal: cutSigma2 x = capShift⁻¹ (cutSigma (capShift x))
  rw [← C.capShift_cutSigma2 x]
  exact (C.capShift.symm_apply_apply _).symm

/-! ## The vertex count `V' = V + k` (ported by conjugation) -/

/-- **The corrected cut-and-cap rotation has `V + k` cycles.**  By the conjugation
`σ'₂ = g⁻¹ σ' g` and conjugation-invariance of `numCycles`, this equals the buggy
count, already proved to be `V + k`. -/
theorem numCycles_cutSigmaPerm2 (C : SimplePrimalCycle M) :
    _root_.numCycles C.cutSigmaPerm2 = M.V + C.len := by
  rw [cutSigmaPerm2_eq_conj]
  rw [show C.capShift⁻¹ * C.cutSigmaPerm * C.capShift
        = C.capShift⁻¹ * C.cutSigmaPerm * (C.capShift⁻¹)⁻¹ by rw [inv_inv]]
  rw [CutCapCount.numCycles_conj, numCycles_cutSigmaPerm]

/-- **The vertex count of the corrected cut-and-cap map: `V' = V + k`.**  This is
the `vertex_count` field of `CutSigmaCounts2`. -/
theorem cutCapMap2_V (C : SimplePrimalCycle M) :
    (C.cutCapMap2).V = M.V + C.len := by
  rw [CombMap.V_eq_numCycles, cutCapMap2_sigma, numCycles_cutSigmaPerm2]

-- Triangle anchor (`PlanarMapCutCapEval.lean`):  V' = 6 = V + k = 3 + 3.

/-! ## The face count `F' = F + 2`

`α'` is unchanged (`cutAlphaPerm`), so `φ'₂ = (cutCapMap2).φ = σ'₂ · α'`.  We first
read the *concrete* action of `φ'₂` on each dart class (mirroring the buggy
`PlanarMapCutCapFCore.lean`, but with the corrected `+`-cap threading).  Unlike the
buggy map — where each forward cycle dart `inl (dart i)` was a `φ'`-fixed point and
the cap shards shattered into too many orbits — here

```
φ'₂ (inl (dart i))   = inl (dart (nextIdx i))     -- forward cycle darts now thread!
φ'₂ (inl (α dart i)) = inl (p_i)
```

so the corrected `+`-cap wiring genuinely re-routes the forward cycle darts.  These
exact action lemmas are the inputs to the design's orbit bijection
(old faces survive rerouted; the two cap chains are the two new faces). -/

/-- `φ'₂ x = cutSigma2 (cutAlpha x)`. -/
lemma cutCapPhi2_apply (C : SimplePrimalCycle M) (x : C.CutDart) :
    (C.cutCapMap2).φ x = C.cutSigma2 (C.cutAlpha x) := by
  rw [CombMap.φ, Equiv.Perm.mul_apply, cutCapMap2_alpha, cutCapMap2_sigma,
    cutAlphaPerm_apply, cutSigmaPerm2_apply]

/-- **Corrected forward cycle dart action.**  `φ'₂ (inl (dart i)) = inl (dart
(nextIdx i))`: the forward cycle darts now thread forward (the fix), where in the
buggy map they were fixed points. -/
@[simp] lemma cutCapPhi2_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap2).φ (Sum.inl (C.dart i)) = Sum.inl (C.dart (C.nextIdx i)) := by
  rw [cutCapPhi2_apply, cutAlpha_dart,
    show (Sum.inr (Sum.inl i) : C.CutDart) = C.capP i from rfl,
    show C.capP i = Sum.inr (Sum.inl i) from rfl, cutSigma2_capPlus]

/-- The reverse cycle dart: `φ'₂ (inl (α (dart i))) = inl (p_i)` (unchanged from the
buggy map, since the `−`-bank wiring is unchanged). -/
@[simp] lemma cutCapPhi2_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap2).φ (Sum.inl (M.α (C.dart i))) = Sum.inl (C.pDart i) := by
  rw [cutCapPhi2_apply, cutAlpha_alpha_dart,
    show (Sum.inr (Sum.inr i) : C.CutDart) = C.capM i from rfl,
    show C.capM i = Sum.inr (Sum.inr i) from rfl, cutSigma2_capMinus]

/-- **Generic three-way action of `σ'₂` on an `inl` dart.**  `σ'₂ (inl e)` is either
`inl (σ e)` (clean), diverts into the *previous* `+`-cap when `σ e = p_i`, or into
the `−`-cap when `σ e = q_i`. -/
lemma cutSigma2_inl_cases (C : SimplePrimalCycle M) (e : D) :
    (C.cutCapMap2).σ (Sum.inl e) = Sum.inl (M.σ e) ∨
      (∃ i, M.σ e = C.pDart i ∧
        (C.cutCapMap2).σ (Sum.inl e) = Sum.inr (Sum.inl (C.prevIdx i))) ∨
      (∃ i, M.σ e = C.qDart i ∧
        (C.cutCapMap2).σ (Sum.inl e) = Sum.inr (Sum.inr i)) := by
  by_cases hp : ∃ i, M.σ e = C.pDart i
  · obtain ⟨i, hi⟩ := hp
    exact Or.inr (Or.inl ⟨i, hi, C.cutSigma2_plusEnd hi⟩)
  · by_cases hq : ∃ i, M.σ e = C.qDart i
    · obtain ⟨i, hi⟩ := hq
      exact Or.inr (Or.inr ⟨i, hi, C.cutSigma2_minusEnd hi⟩)
    · exact Or.inl (C.cutSigma2_clean (fun i hi => hp ⟨i, hi⟩) (fun i hi => hq ⟨i, hi⟩))

/-- **Action of `φ'₂` on the `+`-cap.**  `cutAlpha (capP i) = inl (dart i)`, so
`φ'₂ (capP i) = σ'₂ (inl (q_i))`. -/
lemma cutCapPhi2_capP_cases (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap2).φ (C.capP i) = Sum.inl (M.σ (C.dart i)) ∨
      (∃ j, M.σ (C.dart i) = C.pDart j ∧
        (C.cutCapMap2).φ (C.capP i) = Sum.inr (Sum.inl (C.prevIdx j))) ∨
      (∃ j, M.σ (C.dart i) = C.qDart j ∧
        (C.cutCapMap2).φ (C.capP i) = Sum.inr (Sum.inr j)) := by
  rw [cutCapPhi2_apply, show C.capP i = Sum.inr (Sum.inl i) from rfl, cutAlpha_capPlus,
    ← cutSigmaPerm2_apply, ← cutCapMap2_sigma]
  exact C.cutSigma2_inl_cases (C.dart i)

/-- **Action of `φ'₂` on the `−`-cap.**  `cutAlpha (capM i) = inl (α (dart i))`, so
`φ'₂ (capM i) = σ'₂ (inl (α (dart i)))`. -/
lemma cutCapPhi2_capM_cases (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap2).φ (C.capM i) = Sum.inl (M.σ (M.α (C.dart i))) ∨
      (∃ j, M.σ (M.α (C.dart i)) = C.pDart j ∧
        (C.cutCapMap2).φ (C.capM i) = Sum.inr (Sum.inl (C.prevIdx j))) ∨
      (∃ j, M.σ (M.α (C.dart i)) = C.qDart j ∧
        (C.cutCapMap2).φ (C.capM i) = Sum.inr (Sum.inr j)) := by
  rw [cutCapPhi2_apply, show C.capM i = Sum.inr (Sum.inr i) from rfl, cutAlpha_capMinus,
    ← cutSigmaPerm2_apply, ← cutCapMap2_sigma]
  exact C.cutSigma2_inl_cases (M.α (C.dart i))

/-- **Action of `φ'₂` on a non-cycle `inl d`** (`d ∉ dartSet`).  `cutAlpha (inl d) =
inl (α d)`, so `φ'₂ (inl d) = σ'₂ (inl (α d))`: clean `inl (φ d)` or a cap divert. -/
lemma cutCapPhi2_inl_other_cases (C : SimplePrimalCycle M) {d : D} (h : d ∉ C.dartSet) :
    (C.cutCapMap2).φ (Sum.inl d) = Sum.inl (M.φ d) ∨
      (∃ j, M.σ (M.α d) = C.pDart j ∧
        (C.cutCapMap2).φ (Sum.inl d) = Sum.inr (Sum.inl (C.prevIdx j))) ∨
      (∃ j, M.σ (M.α d) = C.qDart j ∧
        (C.cutCapMap2).φ (Sum.inl d) = Sum.inr (Sum.inr j)) := by
  rw [cutCapPhi2_apply, C.cutAlpha_other h, ← cutSigmaPerm2_apply, ← cutCapMap2_sigma]
  have := C.cutSigma2_inl_cases (M.α d)
  rwa [show M.σ (M.α d) = M.φ d from rfl] at this

/-! ### The reduction to the corrected face-cycle count

`F' = numCycles φ'₂`, and `φ'₂ = cutSigmaPerm2 * cutAlphaPerm`.  We isolate the
single corrected cycle-count fact as the named `Prop` `NumCyclesCutPhi2`.  Unlike
the buggy `NumCyclesPhiLiftFaceCorr` (`PlanarMapCutCapFCore.lean`) — whose value
was *not* `F + 2` for the buggy map — here the value `F + 2` is the genuine design
number, kernel-verified on the triangle (`F' = 4`) and tetrahedron (`F' = 6`).

The full per-class action of `φ'₂` is established unconditionally above; what
remains is the global orbit count along the corrected cap threading (the design's
"every old face survives as one φ'₂-orbit, plus exactly the two cap chains"), which
is the `F`-analogue of the `V'` count but — as in the buggy file — without a clean
projection semiconjugacy. -/

/-- **The pinned corrected face core.**  `numCycles φ'₂ = F + 2` for the corrected
cut map.  This is the single isolated topological fact of the corrected Chapter 35
face count: the two cap chains are exactly two new `φ'₂`-orbits and every old face
survives (rerouted) as exactly one.  Kernel-anchored at `F' = 4` (triangle),
`F' = 6` (tetrahedron). -/
def NumCyclesCutPhi2 (C : SimplePrimalCycle M) : Prop :=
  _root_.numCycles ((C.cutCapMap2).φ) = M.F + 2

/-- **The face count of the corrected cut-and-cap map: `F' = F + 2`**, obtained from
the pinned corrected core.  This is the `face_count` field of `CutSigmaCounts2`. -/
theorem cutCapMap2_F (C : SimplePrimalCycle M) (hcore : C.NumCyclesCutPhi2) :
    (C.cutCapMap2).F = M.F + 2 := by
  rw [CombMap.F_eq_numCycles]; exact hcore

-- Triangle anchor (`PlanarMapCutCapEval.lean`):  F' = 4 = F + 2 = 2 + 2.

/-! ## Assembly: `CutSigmaCounts2` and the corrected Jordan / chord-separation lemma

`V'` is closed unconditionally; `F'` is closed from the corrected core
`NumCyclesCutPhi2`; the connectivity field `connected_of_dual_path` is the one
remaining parameter (the `dps`/`conn` layers are ported separately, mirroring the
buggy `PlanarMapCutCapConn.lean`).  We assemble `CutSigmaCounts2` from these and
thread it through the verified `jordan_simple_cycle_of_counts2`
(`PlanarMapCutCapSigma2.lean`). -/

/-- **Assemble `CutSigmaCounts2`** from the proved `V'`, the corrected face core
`hcore`, and the per-edge connectivity parameter `hconn`. -/
theorem cutSigmaCounts2_of_core_of_conn (C : SimplePrimalCycle M)
    (hcore : C.NumCyclesCutPhi2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected) :
    CutSigmaCounts2 M C where
  vertex_count := C.cutCapMap2_V
  face_count := C.cutCapMap2_F hcore
  connected_of_dual_path := hconn

/-- **The Jordan lemma for the corrected cut-and-cap map**, conditional only on the
corrected face core `hcore`, the per-edge connectivity parameter `hconn`, and the
sanctioned Euler inequality `chi_le`.  `V'` is unconditional; `F'` rests on the one
named corrected core; connectivity is the single isolated parameter. -/
theorem jordan_simple_cycle2_of_core (C : SimplePrimalCycle M)
    (hcore : C.NumCyclesCutPhi2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (hchi : M.eulerChar = 2)
    (chi_le : (C.cutCapMap2).Connected → (C.cutCapMap2).eulerChar ≤ 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  jordan_simple_cycle_of_counts2
    (C.cutSigmaCounts2_of_core_of_conn hcore hconn) hchi chi_le i

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap
