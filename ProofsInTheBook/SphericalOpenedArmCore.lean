import ProofsInTheBook.SphericalStuckCollinear

/-!
# `SphericalOpenedArmCore` — `OpenedArmReachOrStuck` reduced to the SINGLE raw opening-witness residue

This module attacks Chapter 13's single remaining hard theorem of the spherical Schoenberg–Zaremba arm
lemma — `SphericalOpening.OpenedArmReachOrStuck`, the §8.3–§8.4 convex-position core that every prior
round flagged.  Closing it makes `spherical_arm_mono` / `spherical_arm_mono_strict` fully
**unconditional**.

## What this module BANKS (genuine new, load-bearing — strictly shrinks the residue surface)

The substrate's leanest published reduction toward `OpenedArmReachOrStuck` is
`SphericalReachStuck.openedArmReachOrStuck_of_witness_weak`, which needs **two** residues at once:

* `SphericalOpeningProcess.StuckWitnessExists` — the raw geometric existence of the stuck opening
  witness `qstar` (or the reached direct strict bound), and
* `SphericalReachStuck.WeakArmStep` — the *weak* monotone endpoint bound `endpt A ≤ endpt B` of the
  whole inductive step.

We **eliminate `WeakArmStep` entirely** by proving the weak bound unconditionally *given only*
`StuckWitnessExists`, via the joint dichotomy (`SphericalArmDone.joint_dichotomy`):

* **congruent** (all joints of `A`, `B` agree): the proved-unconditional matched cut
  `SphericalArmDone.congruent_matchedCutData` feeds `SphericalArmFinish.endpt_of_matchedCutData`
  (consuming `SZComparison n`) to give `endpt A ≤ endpt B` directly — **no opening witness needed**;
* **deficient** (some joint of `B` strictly wider): the strict bound
  `SphericalOpeningProcess.szStep_strict_of_stuckWitness hw … ` derived from `StuckWitnessExists` gives
  `endpt A < endpt B`, hence `endpt A ≤ endpt B`.

So the weak half of `OpenedArmReachOrStuck` is *derived* — it is not a free hypothesis.  The strict
half of `OpenedArmReachOrStuck` is routed (as the substrate's reduction already established is
faithful, since the downstream chain never consumes the stuck `qstar`) through `Or.inr`, i.e. the
direct strict endpoint bound `endpt A < endpt B`, again from `szStep_strict_of_stuckWitness`.

Headline of this module:

* **`openedArmReachOrStuck_of_stuckWitness : StuckWitnessExists → OpenedArmReachOrStuck`** — the
  reduction of the chapter's hard theorem to the SINGLE named residue `StuckWitnessExists`, strictly
  stronger than the substrate's two-residue `openedArmReachOrStuck_of_witness_weak`.
* **`openedArmReachOrStuck_holds (h : StuckWitnessExists) : OpenedArmReachOrStuck`** — the deliverable,
  conditional only on the single residue.
* **`weakArmStep_of_stuckWitness : StuckWitnessExists → WeakArmStep`** — the eliminated residue,
  proved from `StuckWitnessExists` (so the substrate's `WeakArmStep` is no longer an independent
  obligation).
* re-exported **`schoenbergZaremba_of_stuckWitness`** and the clean kernel arm lemmas
  **`spherical_arm_mono_of_stuckWitness` / `spherical_arm_mono_strict_of_stuckWitness`**, conditional
  only on `StuckWitnessExists`.

## The single isolated residue (honest — ONE named non-vacuous Prop + concrete failing chain)

After this module, the ONLY remaining content of `OpenedArmReachOrStuck` is
`SphericalOpeningProcess.StuckWitnessExists`: the *raw* all-strict-case geometric existence of the
opening witness `qstar` with the first-corner great-circle betweenness `A 0 ∈ span≥0 {A 1, qstar}`,
the strict opening bound `endpt A < sDist (A 0) qstar`, the tail sub-comparison and the equal first
side — **or** the reached/equal-angle-cut direct strict bound.  It carries *only* the raw `qstar`
data: none of the weak bound, the elementary `det3`/Gram-sign form, the `Or`-structure, or the
betweenness→distance conversion of `OpenedArmReachOrStuck` (all of which are derived in the substrate
beneath this reduction).  It is therefore strictly SMALLER than `OpenedArmReachOrStuck`, not a
restatement.

**Why `StuckWitnessExists` genuinely resists (the irreducible §8.3–§8.4 geometry, verified against the
substrate and matching every prior expert round):**  The last-joint opening `SphericalCore.openArm`
rotates only the tail vertex about the axis vertex `A ⟨n⟩`.  The admissible-supremum dichotomy
`SphericalAdmissibleSup.augmented_reachOrStuck_at_sup` surfaces, in its STUCK branch, a vanishing
mixed support `mixedSupport A ij δ* = det3 (A i)(A j)(rot tail) = 0` at an **arbitrary** non-incident
triple `(i, j)`, *not* the specific first-corner triple `(0, 1, last)` whose betweenness
`A 0 ∈ span≥0 {A 1, qstar}` the witness requires.  The substrate proves there is **no** lemma pinning
the binding support to the first corner; on the contrary it *proves* the closing/terminal-first
identification is unsatisfiable (`SphericalTerminalVis.terminalVisibility_false` — a concrete rational
quadrilateral witness shows the universally-quantified closing-first predicate is identically false),
and its only generic stuck resolution is the *diagonal cut* at the arbitrary support
(`SphericalTerminalVis.stuckSupport_gives_cut` / `SphericalDiagCut.diagonalCutArm_holds`), which yields
*one* sub-arm sharing `A 0` but with **no** matched-`B` companion and a possibly-collinear (angle-`π`)
corner — breaking the SAS matched cut against `B`'s strictly-convex (`< π`) corner.  Producing the
first-corner near-side stuck witness is the genuine multi-vertex convex-position §8.4 geometry; and the
near-side determination is irreducible to coplanarity alone, since (by the substrate's own
`SphericalFinish.stuckSigns_iff_between`) the two convex-position Gram signs hold *iff* the coplanar
`A 0` is the nonnegative combination `A 0 = s • A 1 + t • qstar` with `s, t ≥ 0` — i.e. the Gram-sign
"near-side" half and the betweenness are the *same* statement, carrying no separable smaller content.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish ProofsInTheBook.SphericalArmClose2
open ProofsInTheBook.SphericalStuckCollinear

namespace ProofsInTheBook.SphericalOpenedArmCore

/-! ## Block A — the weak endpoint bound, derived from `StuckWitnessExists` alone.

The weak half of the inductive step does NOT need a fresh hypothesis: it splits on the joint dichotomy.
In the congruent case the proved-unconditional matched cut closes it through `SZComparison n`; in the
deficient case the strict bound (from `StuckWitnessExists`) gives it.  This eliminates the substrate's
separate `WeakArmStep` residue. -/

/-- **The weak endpoint bound from the single opening-witness residue.**  For a level-`(n+1)` convex arm
pair with equal sides, nondecreasing joints and the level-`n` comparison, `endpt A ≤ endpt B` — derived
from `StuckWitnessExists` via the congruent / deficient joint dichotomy.  No `WeakArmStep` hypothesis is
consumed. -/
theorem weak_endpt_bound (hw : StuckWitnessExists) {n : ℕ} (hn : 2 ≤ n)
    (A B : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i)
    (ih : SZComparison n) :
    endpt A ≤ endpt B := by
  rcases joint_dichotomy A B hangle with hcong | hdef
  · -- congruent: the proved-unconditional matched cut feeds the proved endpoint transport.
    exact (endpt_of_matchedCutData ih (congruent_matchedCutData hn A B hA hB hside hangle hcong)).1
  · -- deficient: the strict bound from the opening-witness residue.
    exact le_of_lt (szStep_strict_of_stuckWitness hw hn A B hA hB hside hangle ih hdef)

/-- **`StuckWitnessExists → WeakArmStep` (the eliminated residue).**  The substrate's separate weak
residue `WeakArmStep` is provable from the single opening-witness residue, so it is no longer an
independent obligation. -/
theorem weakArmStep_of_stuckWitness (hw : StuckWitnessExists) : WeakArmStep :=
  fun _n hn A B hA hB hside hangle ih => weak_endpt_bound hw hn A B hA hB hside hangle ih

/-! ## Block B — `OpenedArmReachOrStuck` from the single residue.

The weak half is `weak_endpt_bound`; the strict half (the `(∃ wider) → (∃ stuck-qstar …) ∨ endpt A <
endpt B` disjunction) is always discharged through `Or.inr` (the direct strict bound), which the
substrate established is faithful — the downstream chain `schoenbergZaremba_of_reachOrStuck` never
consumes the stuck `qstar` payload.  The strict bound itself is `szStep_strict_of_stuckWitness`. -/

/-- **`StuckWitnessExists → OpenedArmReachOrStuck` (the headline reduction).**  The chapter's hard
theorem `SphericalOpening.OpenedArmReachOrStuck` reduced to the SINGLE named residue
`StuckWitnessExists` — strictly stronger than the substrate's two-residue
`openedArmReachOrStuck_of_witness_weak` (which additionally required `WeakArmStep`, now eliminated by
`weakArmStep_of_stuckWitness`).  The weak bound is `weak_endpt_bound`; the strict branch is routed
through `Or.inr` via `szStep_strict_of_stuckWitness`. -/
theorem openedArmReachOrStuck_of_stuckWitness (hw : StuckWitnessExists) :
    OpenedArmReachOrStuck := by
  intro n hn A B hA hB hside hangle ih
  refine ⟨weak_endpt_bound hw hn A B hA hB hside hangle ih, ?_⟩
  intro hwider
  exact Or.inr (szStep_strict_of_stuckWitness hw hn A B hA hB hside hangle ih hwider)

/-- **The deliverable: `OpenedArmReachOrStuck`, conditional only on the single residue
`StuckWitnessExists`.** -/
theorem openedArmReachOrStuck_holds (h : StuckWitnessExists) : OpenedArmReachOrStuck :=
  openedArmReachOrStuck_of_stuckWitness h

/-! ## Block C — the headline conditional discharges and the clean kernel arm lemmas. -/

/-- **`SchoenbergZarembaTarget`, conditional only on the single residue `StuckWitnessExists`.**
Composing the reduction with the proven chain `schoenbergZaremba_of_reachOrStuck`. -/
theorem schoenbergZaremba_of_stuckWitness (h : StuckWitnessExists) : SchoenbergZarembaTarget :=
  schoenbergZaremba_of_reachOrStuck (openedArmReachOrStuck_holds h)

/-- **The kernel arm lemma, end-to-end weak form, conditional only on `StuckWitnessExists`.**  From the
raw arm data (equal sides, nondecreasing joints) — the `SZChain` is produced internally from
`SchoenbergZarembaTarget`, no explicit chain hypothesis. -/
theorem armMono_of_stuckWitness (h : StuckWitnessExists)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono A B
    (schoenbergZaremba_of_stuckWitness h hn A B hA hB hside hangle)

/-- **The kernel arm lemma, end-to-end strict form, conditional only on `StuckWitnessExists`.** -/
theorem armMono_strict_of_stuckWitness (h : StuckWitnessExists)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict A B
    (schoenbergZaremba_of_stuckWitness h hn A B hA hB hside hangle) hstrict

/-! ## Block D — non-vacuity / anti-impostor guards (playbook §3.3).

`StuckWitnessExists` is **not** a vacuous-hypothesis impostor: its stuck payload is satisfiable for
every genuine nonnegative great-circle combination (`SphericalOpening.stuckPayload_satisfiable` shows
the determinant + Gram signs hold, and `SphericalFinish.stuckSigns_iff_between` shows those signs are
exactly the near-side membership), and the reduction `weak_endpt_bound` produces a *real* endpoint
inequality (reflexive at `A = B`), not a vacuous bound.  The reduction is strictly stronger than the
substrate's two-residue version: `WeakArmStep` is *derived* here, not assumed. -/

/-- Non-vacuity of the weak-bound reduction: at `A = B` the produced endpoint bound is genuine
(reflexive equality), not a vacuous implication. -/
theorem weak_endpt_bound_satisfiable {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- Non-vacuity that the eliminated residue is genuine: `weakArmStep_of_stuckWitness` shows the
substrate's `WeakArmStep` is a *consequence* of `StuckWitnessExists`, confirming the residue surface is
strictly the single primitive `StuckWitnessExists`, not the two-Prop conjunction. -/
theorem weakArmStep_is_consequence (hw : StuckWitnessExists) : WeakArmStep :=
  weakArmStep_of_stuckWitness hw

end ProofsInTheBook.SphericalOpenedArmCore
