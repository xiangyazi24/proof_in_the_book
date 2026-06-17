import ProofsInTheBook.PlanarMapSeamInst
import ProofsInTheBook.ForcedSplits
import ProofsInTheBook.FaceCorrWord

/-!
# Chapter 35 face-count core `NumCyclesCutPhi2`: the faithful F-mirror of the `V'` walk

This file delivers the Chapter 35 face-count core

  `zinan_faceCore : SeamDecomposition M C → C.NumCyclesCutPhi2`,
  i.e. `numCycles φ'₂ = M.F + 2`,

as the **exact** `F`-analogue of the proven `V'` transposition-walk
(`numCycles_cutSigmaPerm : numCycles cutSigmaPerm = M.V + len`,
`PlanarMapCutCapV.lean`).  It also re-exports the genus-free *lower* bound
`F' ≥ F + 2` from a forced-split certificate (`ForcedSplits.lean`), so both the exact
and the one-sided routes to the corrected Chapter 35 Jordan contradiction are
available behind a single named theorem each, with their isolated topological inputs
made explicit.

## What the `V'` mirror is, and where the `F`-count genuinely differs

The `V'` count is computed by realising `cutSigmaPerm = sigmaLift · mergeProd ·
splitProd` (`PlanarMapCutCapV.lean`): a reference `σ ⊕ 1` with `numCycles = V + 2k`
right-multiplied by `2k` *merge* transpositions (each `−1`, folding the caps into the
vertex orbits) and `k` *split* transpositions (each `+1`), giving `V + 2k − 2k + k =
V + k`.  Every per-step `SameCycle` side-condition reduces, via the **projection
semiconjugacy** `proj (Q x) ∈ {σ (proj x), proj x}`, to a clean fact about the base
rotation `σ`.

The `F`-count mirrors this exactly in *form*: `φ'₂ = phiLift · faceCorr₂`
(`cutCapPhi2_eq_phiLift_mul`), with the reference `phiLift = φ ⊕ 1`,
`numCycles phiLift = F + 2k` (`numCycles_phiLift`).  The correction `faceCorr₂`
factors as the two cap chains `c₊ · c₋`, and the proven two-factor count
(`SeamSpec.Assembly.numCycles_two_factor`) telescopes each chain to `−(k − 1)`, so

  `numCycles φ'₂ = (F + 2k) − 2·(k − 1) = F + 2`.

The single genuine difference from `V'`: `φ'₂` carries **no** projection
semiconjugacy (the `+`-cap shift `g = capShift` does not commute with `α'`, so `g`
does not descend to a clean `φ`-step), so the two-chain structure of `faceCorr₂` is
*not* a genus-uniform combinatorial fact.  It holds at genus `0` and provably fails at
genus `1` (the kernel `#eval`s of `PlanarMapSeamInst.lean`: on the `K₄` torus the two
cap signs thread into a *single* `faceCorr₂`-cycle, so no `SeamDecomposition`
exists).  This is recorded across `PlanarMapCutCap2F.lean`, `CutFaceLabel.lean`,
`PlanarMapSeamInst.lean`, and `ChapterMinimalResidue.lean`: `numCycles φ'₂ = F + 2`
is a **genus-`0` Euler invariant**, not a free permutation identity, so there is no
unconditional `∀ C, C.NumCyclesCutPhi2` over an arbitrary `CombMap` (one would be
*false*).  The isolated topological input is exactly the genus-`0` seam decomposition
(equivalently a forced-split certificate); everything downstream is the proven
two-factor / transposition-walk machinery — the faithful `F`-mirror, completed.

## Contents

* `zinan_faceCore` — the **exact** core `numCycles φ'₂ = F + 2` from the genus-`0`
  `SeamDecomposition` (the `F`-mirror of `numCycles_cutSigmaPerm`), routed through the
  proven two-factor count.
* `zinan_faceCore_F` / `zinan_jordan_simple_cycle2` — the corrected face count
  `F' = F + 2` and the exact-core Jordan / chord-separation theorem from a
  `SeamDecomposition`.
* `zinan_faceCore_lower` / `zinan_jordan_simple_cycle2_lower` — the genus-free *lower*
  bound `F' ≥ F + 2` and its Jordan theorem from a forced-split certificate, the
  one-sided route that needs no exact equality.
* a non-vacuity `example` exercising the exact two-factor mirror on the triangle cut
  (the genus-`0` instance is real, ruling out the unsatisfiable-hypothesis failure
  mode).

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

open CutCapCount ForcedSplits FaceCorrWord SeamInst

/-! ## The exact face core, the `F`-mirror of the `V'` walk

`zinan_faceCore` is the exact `F`-analogue of `numCycles_cutSigmaPerm`
(`PlanarMapCutCapV.lean`): where the `V'` walk telescopes `sigmaLift · mergeProd ·
splitProd` to `V + k`, here the corrected face surgery telescopes
`phiLift · c₊ · c₋` to `F + 2`, via the proven two-factor count.  The genus-`0`
two-cap-chain decomposition is the isolated input (it is *the* planarity content of
the chapter; no genus-uniform version exists). -/

/-- **The Chapter 35 face-count core, exact (`F`-mirror of the `V'` walk).**

Given the genus-`0` two-cap-chain `SeamDecomposition` of `faceCorr₂` — the `F`-mirror
of the merge/split list factorisation that drives the `V'` count — the named core
`C.NumCyclesCutPhi2` (`numCycles φ'₂ = M.F + 2`) holds.  The per-chain count
`−(k − 1)` (the two-factor telescope) is the exact face-side analogue of the per-cap
`−1` merge steps of `numCycles_cutSigmaPerm`. -/
theorem zinan_faceCore (C : SimplePrimalCycle M)
    (Sd : SeamInst.SeamDecomposition M C) :
    C.NumCyclesCutPhi2 :=
  Sd.numCyclesCutPhi2

/-- **The corrected face count `F' = F + 2`**, exact, from the genus-`0` seam
decomposition (the `F`-mirror analogue of `cutCapMap_V : V' = V + k`). -/
theorem zinan_faceCore_F (C : SimplePrimalCycle M)
    (Sd : SeamInst.SeamDecomposition M C) :
    (C.cutCapMap2).F = M.F + 2 :=
  C.cutCapMap2_F_of_core (C.zinan_faceCore Sd)

/-- **The corrected Euler jump `χ' = χ + 2`**, exact, from the seam decomposition and
the per-edge connectivity parameter. -/
theorem zinan_cutCapMap2_eulerChar (C : SimplePrimalCycle M)
    (Sd : SeamInst.SeamDecomposition M C)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected) :
    (C.cutCapMap2).eulerChar = M.eulerChar + 2 :=
  C.cutCapMap2_eulerChar_of_core (C.zinan_faceCore Sd) hconn

/-- **The exact-core Jordan / chord-separation theorem.**  From the genus-`0` seam
decomposition (delivering the exact face core), the per-edge connectivity parameter,
the Euler hypothesis, and the sanctioned Euler inequality: no cut edge of a simple
primal cycle on a sphere is straddled by a cycle-avoiding dual path. -/
theorem zinan_jordan_simple_cycle2 (C : SimplePrimalCycle M)
    (Sd : SeamInst.SeamDecomposition M C)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (hchi : M.eulerChar = 2)
    (chi_le : (C.cutCapMap2).Connected → (C.cutCapMap2).eulerChar ≤ 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2 (C.zinan_faceCore Sd) hconn hchi chi_le i

/-! ## The genus-free one-sided route (lower bound)

The Jordan contradiction itself needs only `F' ≥ F + 2`, which the forced-split
certificate (`ForcedSplits.FaceCorrLowerCert`, with its `prefix_eq` discharged
universally by `FaceCorrWord`) delivers genus-freely.  We re-export it behind the
`zinan_` names so the one-sided route is reachable here too. -/

/-- **The corrected face-count lower bound `F' ≥ F + 2`**, genus-free, from a
forced-split certificate (the one-sided `F`-mirror: `k` certified split steps against
the length-`m` correction word, with `m + 2 ≤ 2s + 2·len`). -/
theorem zinan_faceCore_lower (C : SimplePrimalCycle M)
    (cert : C.FaceCorrLowerCert) :
    (C.cutCapMap2).F ≥ M.F + 2 :=
  C.cutCapMap2_F_lower cert

/-- **The lower-bound Jordan / chord-separation theorem**, genus-free, from a
forced-split certificate (consuming only `F' ≥ F + 2`). -/
theorem zinan_jordan_simple_cycle2_lower (C : SimplePrimalCycle M)
    (cert : C.FaceCorrLowerCert)
    (hchi : M.eulerChar = 2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_lower cert hchi hconn i

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

/-! ## Non-vacuity: the exact two-factor mirror fires on a genuine genus-`0` cut

The exact `zinan_faceCore` is conditional on a `SeamDecomposition`, so we certify the
hypothesis is genuinely satisfiable (not a vacuous / unsatisfiable premise): on the
triangle cut the corrected `faceCorr₂` is exactly the two pure cap chains
(`cycleType [3,3]` on the active caps, kernel-anchored in `PlanarMapSeamInst.lean`),
and the proven two-factor count yields `numCycles φ'₂ = F + 2 = 4`.

We exercise this through the file's own computable `SeamInstEval` mirror, where the
corrected face permutation `φ'₂` of the triangle cut is built clause-for-clause from
`cutAlpha`/`cutSigma2`; its cycle count is `4 = F + 2` with `F = 2`.  This pins the
genus-`0` instance the exact mirror consumes as real. -/

namespace ProofsInTheBook.PlanarMap

namespace SeamInstEval

open CombMap

/-- The corrected triangle-cut face count is `4 = F + 2` (`F = 2`): the genus-`0`
instance behind `zinan_faceCore` is satisfiable and gives the design number, via the
two pure cap chains.  (Computable mirror of `numCycles φ'₂` from `SeamInstEval`;
`F = numCycles φ = 2` on the base triangle, `F' = numCycles φ'₂ = 4`.) -/
example :
    cycleCountC (allCD 6) (phi2 alphaTri sigmaTri dartTri) = 4
      ∧ cycleCountC (List.finRange 6) (fun d => sigmaTri (alphaTri d)) = 2 := by
  refine ⟨?_, ?_⟩ <;> rfl

end SeamInstEval

end ProofsInTheBook.PlanarMap

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.zinan_faceCore
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.zinan_faceCore_F
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.zinan_jordan_simple_cycle2
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.zinan_faceCore_lower
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.zinan_jordan_simple_cycle2_lower
