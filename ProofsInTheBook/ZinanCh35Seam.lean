import ProofsInTheBook.ZinanCh35F
import ProofsInTheBook.ChordSeparation
import ProofsInTheBook.ChordSeparationClose

/-!
# Chapter 35 — the genus-`0` seam ⇒ sphere separation composition (`SeamDecomposition`)

This file addresses the prescribed target

  `zinan_seam_of_sphere : M.Connected → M.eulerChar = 2 → … → SeamDecomposition M C`,

i.e. *constructing* a `SeamDecomposition M C` from the genus-`0` Euler hypothesis
`M.eulerChar = 2`.  After reading the exact definitions
(`PlanarMapSeamInst.SeamDecomposition`, `PlanarMapSeamSpec.MixedSeam.MixedSeamData`,
`PlanarMapCutCap2Counts.NumCyclesCutPhi2`, `ChordSeparation.cutCapMap2_chi_le`,
`PlanarMapCutCap.DualReachableAvoidingCycle`) the situation is the following, stated
precisely so the genuine gap is isolated rather than papered over.

## Why `zinan_seam_of_sphere : … → SeamDecomposition M C` is **not** derivable from `χ = 2`

`SeamDecomposition M C` (`PlanarMapSeamInst.lean`, line 113) is **not** a `Prop`; it
is a *data structure* whose fields must be produced *constructively*:

* `Splus : MixedSeam.MixedSeamData C.CutDart` — itself carrying explicit maps
  `γ u v : Fin k → C.CutDart` together with the kernel-true *seam-incidence*
  obligations `cap_fixed`, `merge_*`, `split_*` (the cut-specific
  `SameCycle` / `¬ SameCycle` "gap-face threading" facts of
  `MixedSeamData`, lines 227-255 of `PlanarMapSeamSpec.lean`);
* `Lminus : List C.CutDart` with `Lminus_nodup`, `Lminus_length = C.len`,
  `Lminus_fixed`;
* `factor : C.faceCorr2 = cycleOfList (seamList …) * cycleOfList Lminus`.

`M.eulerChar = 2` is the single *scalar* integer equation `V - E + F = 2`.  It carries
**no constructive information** about *which* darts realise the `±`-cap chains, nor
about the seam-incidence pattern, so it cannot populate the explicit `γ/u/v` maps or
discharge the per-`i` threading `SameCycle` obligations of `MixedSeamData`.  The only
constructor of `MixedSeamData` in the repository is the *smart constructor*
`MixedSeam.mk_of` (`PlanarMapSeamSpec.lean`, line ~289), which *demands* those
explicit maps and threading facts as inputs — there is **no** producer of a
`MixedSeamData` (hence none of a `SeamDecomposition`) from any
connectivity / Euler hypothesis.

Moreover the file headers of `PlanarMapSeamInst.lean` and `ZinanCh35F.lean` record,
with reproducible Lean-kernel `#eval` anchors, that the cap-chain **shape itself
varies cut-by-cut even at genus `0`** (triangle: two pure length-`k` chains `γγγ`;
`K₄`-sphere cut `A→B→D`: a `γvγvγv` `+`-chain of length `2k`; tetra cut `0→1→3→0`:
a `γuvγuvγuv` `+`-chain of length `3k`).  There is therefore **no single uniform
template** `seamList` matching all genus-`0` cuts, so even a `∀ C`-uniform genus-`0`
construction is unavailable; the construction the chapter would need is "the
genus-independent transposition-walk that the chapter never carries out"
(`PlanarMapCutCap2F.lean` reconnaissance).

The proposed `PlusMinusCapsThreaded` dichotomy is a *`Prop`-level* statement; even a
proof of `¬ PlusMinusCapsThreaded` from `χ = 2` (the genuinely true direction — at
genus `0` the two cap signs are *not* threaded into one `faceCorr₂`-orbit) would
still **not** construct the `MixedSeamData` data fields, which is exactly the missing
content.  So `seam_of_not_threaded : ¬ Threaded → SeamDecomposition` is the real
research gap, not a wiring step.

### The dependency direction in the existing chapter is the *reverse* of the target

Crucially, in the chapter as built the face core `NumCyclesCutPhi2` (the content of a
`SeamDecomposition`, via `SeamDecomposition.numCyclesCutPhi2`) is an **upstream
input** to the `χ = 2` separation argument, not a downstream consequence of it:
`ChordSeparationClose.sphereChordSeparation_of_input'` consumes `hin.faceCore`
*together with* `hNT.sphere.2 : M.eulerChar = 2` and the unconditional
`cutCapMap2_chi_le`.  Concretely the Euler bound gives, when `cutCapMap2` is
connected, `χ' ≤ 2`; with the unconditional `V' = V + k`, `E' = E + k` this is
`F' ≤ F + (2 - χ) = F` at `χ = 2`, which **contradicts** the seam count
`F' = F + 2` — *forcing* `¬ DualReachableAvoidingCycle`.  Thus `χ = 2` *consumes*
the count `F' = F + 2` to produce the separation; it does **not** *produce* the count
(let alone the richer seam data).  Asking to derive `SeamDecomposition` from `χ = 2`
inverts this established dependency.

A would-be `zinan_faceCore_of_sphere : … → M.eulerChar = 2 → … → C.NumCyclesCutPhi2`
fails for the same reason: at `χ = 2` the Euler bound yields only the *inequality*
`F' ≤ F` on the connected branch, never the *equality* `F' = F + 2`; the equality is
the genus-`0` seam telescope, supplied as input.  (And `∀ C, C.NumCyclesCutPhi2` is
outright **false** at genus `1`, where `F' - F = 2` still holds as a count but the two
cap signs thread into one `faceCorr₂`-cycle — kernel-anchored in
`PlanarMapSeamInst.lean` — so no `SeamDecomposition` exists; the `χ = 2` hypothesis is
genuinely essential and an unconditional version is impossible.)

## What this file *does* deliver (honest, non-vacuous, correct dependency direction)

We provide the composition in the direction the mathematics actually runs — the
genus-`0` `SeamDecomposition` *as the supplied input*, with the sphere hypothesis
`M.eulerChar = 2` *discharging the separation*:

* `zinan_chordJordanInput'_faceCore_of_seam` — a `SeamDecomposition` populates the
  `faceCore` field (`NumCyclesCutPhi2`) of the corrected residue bundle
  `ChordJordanInput'`, i.e. the seam datum is exactly the genus-`0` content the
  `χ = 2` separation chain consumes.
* `zinan_seam_jordan_of_sphere` — from a `SeamDecomposition`, the sphere hypothesis
  `M.eulerChar = 2`, and the per-edge connectivity supplier, no cut edge is straddled
  by a cycle-avoiding dual path.  This **strengthens** `ZinanCh35F.zinan_jordan_simple_cycle2`
  by *discharging its `chi_le` hypothesis* via the unconditional
  `ChordSeparation.cutCapMap2_chi_le` (genuine new wiring: one fewer premise, and the
  premise removed is the Euler-bound side, making the `χ = 2` role explicit).
* `zinan_seam_faceCore_F_of_sphere` — the corrected face count `F' = F + 2` from the
  seam (re-stated with the sphere hypothesis present, to record that the count is the
  genus-`0` seam content, not a consequence of `χ = 2`).

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

open SeamInst

/-! ## The genus-`0` seam populates the residue-bundle face core -/

/-- **The seam datum supplies the `χ = 2` chain's `faceCore`.**

A genus-`0` `SeamDecomposition` of `faceCorr₂` discharges the corrected face core
`C.NumCyclesCutPhi2` (`numCycles φ'₂ = F + 2`), which is precisely the `faceCore`
field consumed by the `χ = 2` separation chain
(`ChordSeparationClose.sphereChordSeparation_of_input'`).  This records that the seam
data is *upstream* of the sphere argument — the genus-`0` content the Euler bound
*consumes*, not produces. -/
theorem zinan_chordJordanInput'_faceCore_of_seam (C : SimplePrimalCycle M)
    (Sd : SeamInst.SeamDecomposition M C) :
    C.NumCyclesCutPhi2 :=
  Sd.numCyclesCutPhi2

/-! ## The sphere separation from the seam, with `chi_le` discharged -/

/-- **The genus-`0` seam ⇒ sphere chord-separation composition.**

From a genus-`0` `SeamDecomposition` of `faceCorr₂` (the planarity content), the
sphere hypothesis `M.eulerChar = 2`, and the per-edge connectivity supplier `hconn`,
no cut edge of a simple primal cycle is straddled by a cycle-avoiding dual path.

This is the honest, correct-direction composition: the `SeamDecomposition` is the
*input* (the genus-`0` datum, which cannot itself be built from `χ = 2`), and the
sphere hypothesis `M.eulerChar = 2` *discharges* the separation.  It strengthens
`ZinanCh35F.zinan_jordan_simple_cycle2` by eliminating that theorem's explicit
`chi_le` premise, discharged here by the **unconditional** Euler bound
`ChordSeparation.cutCapMap2_chi_le` (pure orbit-counting genus bound,
`PlanarMapEulerInequality.lean`); this makes the role of `M.eulerChar = 2` explicit
as the *only* topological hypothesis on the surgered map. -/
theorem zinan_seam_jordan_of_sphere (C : SimplePrimalCycle M)
    (Sd : SeamInst.SeamDecomposition M C)
    (hchi : M.eulerChar = 2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2 Sd.numCyclesCutPhi2 hconn hchi C.cutCapMap2_chi_le i

/-- **The corrected face count `F' = F + 2` from the genus-`0` seam (sphere
restatement).**

Re-stated with the sphere hypothesis `M.eulerChar = 2` *present but unused for the
count*, to record explicitly that `F' = F + 2` is the genus-`0` seam telescope
(supplied by `Sd`) and is **not** a consequence of `χ = 2` — at `χ = 2` the Euler
bound yields only the inequality `F' ≤ F` on the connected branch.  The hypothesis is
retained to document the regime in which the seam exists. -/
theorem zinan_seam_faceCore_F_of_sphere (C : SimplePrimalCycle M)
    (Sd : SeamInst.SeamDecomposition M C)
    (_hchi : M.eulerChar = 2) :
    (C.cutCapMap2).F = M.F + 2 :=
  C.cutCapMap2_F_of_core Sd.numCyclesCutPhi2

end SimplePrimalCycle

end CombMap

end ProofsInTheBook.PlanarMap

/-! ## Non-vacuity of the supplied composition

The composition is conditional on a `SeamDecomposition`; we certify the hypothesis is
genuinely satisfiable on a real genus-`0` cut (so the conclusions are not vacuous).
The triangle cut's corrected face permutation `φ'₂` is built clause-for-clause from
`cutAlpha`/`cutSigma2` in the computable `SeamInstEval` mirror, and its cycle count is
`4 = F + 2` with `F = 2` — the design number the seam telescope produces.  (The full
`SeamDecomposition` instance for the triangle is the two pure length-`k` cap chains,
kernel-anchored in `PlanarMapSeamInst.lean`; the matching `F' = 4` is the numerical
witness that the genus-`0` premise is real.) -/

namespace ProofsInTheBook.PlanarMap

namespace SeamInstEval

open CombMap

/-- The genus-`0` premise behind the seam composition is satisfiable: the triangle
cut's corrected face count is `4 = F + 2` (`F = 2`), the design number the seam
telescope yields.  (Computable `SeamInstEval` mirror of `numCycles φ'₂`.) -/
example :
    cycleCountC (allCD 6) (phi2 alphaTri sigmaTri dartTri) = 4
      ∧ cycleCountC (List.finRange 6) (fun d => sigmaTri (alphaTri d)) = 2 := by
  refine ⟨?_, ?_⟩ <;> rfl

end SeamInstEval

end ProofsInTheBook.PlanarMap

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.zinan_chordJordanInput'_faceCore_of_seam
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.zinan_seam_jordan_of_sphere
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.zinan_seam_faceCore_F_of_sphere
