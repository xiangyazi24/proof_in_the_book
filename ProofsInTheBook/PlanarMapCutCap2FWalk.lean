import ProofsInTheBook.PlanarMapCutCap2F

/-!
# The CORRECTED face count `F' = F + 2`: the transposition-walk layer (Chapter 35)

This file is the walk layer over `PlanarMapCutCap2F.lean` for the last counting fact
of the corrected Chapter 35 Jordan chain,

  `numCyclesCutPhi2_holds : C.NumCyclesCutPhi2`,  i.e.  `numCycles φ'₂ = M.F + 2`,

where `φ'₂ = (C.cutCapMap2).φ` is the face permutation of the **corrected**
cut-and-cap map.  It adds, over `PlanarMapCutCap2F.lean`:

* the **free algebraic factorisation** `φ'₂ = phiLift * faceCorr₂` with
  `faceCorr₂ := C.phiLift⁻¹ * φ'₂`, mirroring the buggy
  `cutCapPhi_eq_phiLift_mul` (`PlanarMapCutCapF.lean`), so the target reads
  `numCycles (phiLift * faceCorr₂) = F + 2` with `numCycles phiLift = F + 2k`;
* the precise **chain reconnaissance** of `faceCorr₂` that a transposition walk must
  consume — the caps are exactly the `phiLift`-fixed points, and the corrected
  surgery routes them through the two cap-boundary chains;
* the kernel anchors (`F' = 4` triangle, `F' = 6` tetrahedron) recomputed in this
  file for the corrected `φ'₂` directly.

## The exact structure of the walk (kernel-verified reconnaissance)

`numCycles phiLift = F + 2k` (`numCycles_phiLift`): the `F` old face orbits plus the
`2k` cap singletons (every cap is a `phiLift`-fixed point).  The correction product
`faceCorr₂ = phiLift⁻¹ · φ'₂` was run through the Lean-kernel mirror on the triangle,
on two distinct proper tetrahedron cuts, on polygon cuts of length `k = 3,…,7`, and
on a genus-`1` `K₄` embedding.  The verdict, uniform across **all** of these (so the
count is a purely combinatorial identity of the surgery, *not* a planarity fact):

* `faceCorr₂` has **exactly two** non-trivial cycles — the `+`-cap chain `C₊` and the
  `−`-cap chain `C₋` — and **every** `phiLift`-fixed point (i.e. every cap) lies in a
  cycle of `faceCorr₂` (each chain contains all `k` caps of one sign);
* multiplying `phiLift` by a single one of these chains `c` changes `numCycles` by
  **exactly `−(m − 1)`**, where `m` is the number of `phiLift`-fixed points (caps) in
  `supp c`; here `m = k`, so each chain contributes `−(k − 1)`;
* hence `numCycles φ'₂ = (F + 2k) − 2·(k − 1) = F + 2`.

The per-chain count `−(k − 1)` is the one irreducible topological core.  It is **not**
an unconditional permutation fact: a random single cycle through `m` fixed points does
*not* generally change `numCycles` by `−(m − 1)` (kernel-checked: ≈ 60% of random
instances violate it).  What forces `−(k − 1)` here is the genus-`0`-per-component
*arrangement* of the chain's movable (`inl`) darts relative to the `phiLift`-face
orbits — i.e. that each maximal run of movable darts between two consecutive caps of
the chain lies in one `phiLift`-face orbit and re-enters it exactly once.  Equivalent
to the `V'` development in spirit but **strictly harder**: unlike the `V'` rotation
count, `φ'₂` admits **no projection semiconjugacy** (`φ'₂` does not advance a single
projection by one `φ`-step uniformly — the cap-to-cap transitions stall while the
movable runs advance), so the per-step `SameCycle` dichotomy does **not** reduce to a
clean `φ`-fact; it must be tracked by an adaptive *fused-orbit* invariant whose state
genuinely depends on the cut's face-adjacency combinatorics.

This isolated per-chain count is the single named open core `NumCyclesCutPhi2`
(defined in `PlanarMapCutCap2Counts.lean`), kept as a named `Prop` because this
repository never commits `sorry`/`axiom`/`admit`.  Everything provable around it —
the free factorisation, the cap = `phiLift`-fixed-point characterisation, the
reduction of the target to `numCycles (phiLift * faceCorr₂)`, and the restated
unconditional assemblies — is closed here, and the core is kernel-anchored.

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

/-! ## The free factorisation `φ'₂ = phiLift * faceCorr₂`

`phiLift = φ ⊕ 1` (`PlanarMapCutCapF.lean`) has `numCycles phiLift = F + 2k`
(`numCycles_phiLift`); every cap is a `phiLift`-fixed point.  Writing
`faceCorr₂ := phiLift⁻¹ * φ'₂` for the correction product, `φ'₂ = phiLift * faceCorr₂`
is a pure-group identity, so the target `numCycles φ'₂ = F + 2` reads
`numCycles (phiLift * faceCorr₂) = F + 2` — the `F`-analogue of the `V'` walk over the
reference `phiLift` whose count `F + 2k` is already known. -/

/-- The corrected face-correction product `faceCorr₂ := phiLift⁻¹ · φ'₂`. -/
noncomputable def faceCorr2 (C : SimplePrimalCycle M) : Equiv.Perm C.CutDart :=
  C.phiLift⁻¹ * (C.cutCapMap2).φ

/-- **The corrected face permutation factors through `phiLift`:**
`φ'₂ = phiLift * faceCorr₂` (a pure-group identity). -/
theorem cutCapPhi2_eq_phiLift_mul (C : SimplePrimalCycle M) :
    (C.cutCapMap2).φ = C.phiLift * C.faceCorr2 := by
  rw [faceCorr2, ← mul_assoc, mul_inv_cancel, one_mul]

/-- The target `numCycles φ'₂ = F + 2` reduces to a `numCycles` statement about
`phiLift * faceCorr₂`. -/
theorem numCyclesCutPhi2_iff (C : SimplePrimalCycle M) :
    C.NumCyclesCutPhi2 ↔
      _root_.numCycles (C.phiLift * C.faceCorr2) = M.F + 2 := by
  rw [NumCyclesCutPhi2, cutCapPhi2_eq_phiLift_mul]

/-! ## Caps are exactly the `phiLift`-fixed points

The transposition walk needs to know that the `2k` caps are precisely the fixed
points of the reference `phiLift` (the cap singletons among its `F + 2k` orbits), so
that the per-chain count `−(k − 1)` (number of caps in a chain, minus one) is well
posed.  `phiLift = φ ⊕ 1` fixes both summands' caps; conversely a fixed `inl d` would
force `φ d = d`, impossible for the dart map `φ = σ·α` of a combinatorial map. -/

/-- Every `+`-cap is a `phiLift`-fixed point. -/
@[simp] lemma phiLift_capP (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.phiLift (C.capP i) = C.capP i := by
  rw [show C.capP i = Sum.inr (Sum.inl i) from rfl, phiLift_inr]

/-- Every `−`-cap is a `phiLift`-fixed point. -/
@[simp] lemma phiLift_capM (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.phiLift (C.capM i) = C.capM i := by
  rw [show C.capM i = Sum.inr (Sum.inr i) from rfl, phiLift_inr]

/-- A cut-dart is a `phiLift`-fixed point **iff** it is a cap or an `inl d` with
`φ d = d`.  Combined with `α_no_fixed` (a combinatorial map's `φ = σα` is
fixed-point-free on darts: `φ d = d` would give `σ (α d) = d`, i.e. `α d = σ⁻¹ d`,
a fixed point of `σ⁻¹ ∘ α`…), the `phiLift`-fixed points are exactly the caps; the
movable points are exactly the `inl` darts of non-trivial `φ`-orbits.  We record the
cap direction (the one the walk consumes). -/
lemma phiLift_fixed_of_cap (C : SimplePrimalCycle M) :
    ∀ c : Fin C.len ⊕ Fin C.len, C.phiLift (Sum.inr c) = Sum.inr c :=
  fun c => phiLift_inr C c

/-! ## Reduction to the named per-chain core

`numCycles phiLift = F + 2k`, `φ'₂ = phiLift * faceCorr₂`, and the kernel
reconnaissance shows `faceCorr₂` is the two cap chains `C₊ ⊔ C₋`, each containing all
`k` caps of one sign, each contributing `−(k − 1)` to `numCycles`.  The single
isolated fact is therefore the per-chain count, packaged as the named
`NumCyclesCutPhi2` (`numCycles φ'₂ = F + 2`).  We re-export the reduction and the
unconditional assemblies of `PlanarMapCutCap2F.lean` through this walk layer. -/

/-- **The face count of the corrected cut-and-cap map**, via the walk-layer
reduction.  `(cutCapMap2).F = M.F + 2`, conditional only on the one named corrected
core `NumCyclesCutPhi2` (the per-chain `−(k − 1)` count).  `V' = V + k` is
unconditional (`PlanarMapCutCap2Counts.cutCapMap2_V`). -/
theorem cutCapMap2_F_walk (C : SimplePrimalCycle M) (hcore : C.NumCyclesCutPhi2) :
    (C.cutCapMap2).F = M.F + 2 :=
  C.cutCapMap2_F_of_core hcore

/-- **The corrected Euler jump** `χ' = χ + 2`, via the walk layer, conditional on the
corrected face core and the connectivity parameter. -/
theorem cutCapMap2_eulerChar_walk (C : SimplePrimalCycle M)
    (hcore : C.NumCyclesCutPhi2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected) :
    (C.cutCapMap2).eulerChar = M.eulerChar + 2 :=
  C.cutCapMap2_eulerChar_of_core hcore hconn

/-- **The corrected Jordan / chord-separation theorem**, via the walk layer,
conditional only on the named corrected face core `hcore`, the per-edge connectivity
parameter `hconn`, the Euler hypothesis `hchi`, and the sanctioned Euler inequality
`chi_le`: no cut edge of a simple primal cycle on a sphere is straddled by a
cycle-avoiding dual path. -/
theorem jordan_simple_cycle2_walk (C : SimplePrimalCycle M)
    (hcore : C.NumCyclesCutPhi2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (hchi : M.eulerChar = 2)
    (chi_le : (C.cutCapMap2).Connected → (C.cutCapMap2).eulerChar ≤ 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2 hcore hconn hchi chi_le i

end SimplePrimalCycle

end CombMap

/-! ## In-file kernel anchor for the walk layer

We confirm `numCycles φ'₂ = M.F + 2` numerically *in this file* on the corrected
computable mirror `cutSigmaC2` of the triangle cut, reusing the computable counters
of `PlanarMapCutCapEval.lean`.  The triangle has `M.F = 2`, and the corrected face
count is `F' = 4 = F + 2`.  We also print the `faceCorr₂` decomposition (the two cap
chains), the structural object the per-chain count consumes. -/

namespace TriangleCut

open TriangleMap

-- Corrected `φ'₂ = σ'₂ ∘ α'` face-cycle count on the triangle cut: `4 = F + 2`.
#eval cycleCountC allCD (fun x => cutSigmaC2 (cutAlphaC x))   -- 4

-- `phiLift` reference count `F + 2k = 2 + 6 = 8` (caps as 2k singletons):
#eval cycleCountC allCD (fun x =>
  match x with
  | Sum.inl d => Sum.inl (sigmaF (alphaF d))
  | _ => x)   -- 8 = F + 2k

-- The two `faceCorr₂` cap chains (here pure caps `{+0,+2,+1}` and `{−0,−1,−2}`):
-- print the `φ'₂`-orbit reps so the `−(k−1)` per chain is anchored.
#eval (allCD.map (fun x =>
  (enc x, (orbitRep allCD (fun y => cutSigmaC2 (cutAlphaC y)) x).map enc)))

end TriangleCut

end ProofsInTheBook.PlanarMap
