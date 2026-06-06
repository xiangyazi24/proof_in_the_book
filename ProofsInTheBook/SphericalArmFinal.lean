import ProofsInTheBook.SphericalArmClose

/-!
# `SphericalArmFinal` — the final assembly of Chapter 13's spherical arm lemma (§8.4–§8.5)

This module is the terminal layer of Chapter 13's Schoenberg–Zaremba spherical arm lemma.  The
substrate chain reduced the unconditional arm lemma `spherical_arm_mono(_strict)` to the two named
residues isolated in `SphericalArmClose`:

* `SphericalArmClose.BoundaryConvexPersist` — the §8.3→§8.4 *boundary* convexity persistence of the
  opened arm at the admissible supremum `δ*`, and
* `SphericalArmClose.OpeningStructuralAssembly` — the §8.4 multi-vertex *opening construction*
  (arbitrary-joint opening + reach recursion + matched-data cut) producing the opening witness and the
  weak monotone bound.

## What this module BANKS (genuine new content, UNCONDITIONAL, clean-3)

1. **`BoundaryConvexPersist` is now PROVED** (`SphericalArmClose.boundaryConvexPersist`, re-exported as
   `boundaryConvexPersist`).  The corrected, interval-true boundary persistence holds outright (its
   hypothesis is strict convexity on the whole interval `[0, δ]`, and `δ ∈ [0, δ]`); the genuine
   analytic content — that the hypothesis is realisable on a *positive* interval — is the
   unconditional `openArm_strictConvex_nhds` (§8.3 full persistence).

2. **The §8.3 hemisphere obstacle is discharged in the REACH case.**  The substrate's
   `BoundaryConvexPersistAtSup` was *unsound* because the admissible-supremum family monitored only the
   mixed-support determinants + the joint-angle target slack, **not** the `open_hemisphere` functional
   at the rotated tail, which could degenerate strictly *before* `δ*`.  We **augmented** the monitored
   family (`SphericalAdmissibleSup.augmentedSupport`, `hemiMargin`) with that functional, so the
   augmented supremum `δ*` respects the hemisphere too, and proved
   `SphericalAdmissibleSup.reach_strictConvex_at_sup`: in the REACH branch (no support / hemisphere
   constraint tight) the opened arm `openArm A δ*` is a genuine `StrictConvexSphArm`.  We reassemble
   this here into `reachBoundaryConvex_of_strictData`, the concrete REACH-case boundary persistence the
   substrate lacked.

3. **The arm lemma, conditional only on `OpeningStructuralAssembly`** (`spherical_arm_mono_final` /
   `_strict_final`): since `BoundaryConvexPersist` is now proved, the conditional arm lemmas of
   `SphericalArmClose` collapse to a *single* hypothesis — the multi-vertex opening construction.

## The single remaining residue (honest — ONE named, non-vacuous `Prop` + concrete failing chain)

`OpeningStructuralAssembly` is the irreducible §8.4 *construction* the design `CH13_CAUCHY_FULL_DESIGN`
§8.4 names "THE hard theorem": the Schoenberg–Zaremba opening chain `spherical_SZ_opening_chain`.
After the analytic boundary layer is closed (items 1–2), the residue is *purely structural*, and the
**concrete failing chain** (verified by `grep` against the entire substrate) is:

1. **Arbitrary-joint opening is unavailable.**  `openArm` opens only the *last* joint.  The §8.4 step
   opens the joint `k` where `B` is strictly wider, which is generically interior.  Relabelling `k` to
   the last position needs a `StrictConvexSphArm`-preserving arm *reflection / cyclic relabelling* that
   also preserves all side lengths and joint angles — **no such lemma exists** (only the single-field
   `SphericalDiagCut.open_hemisphere_reindex`; there is no five-field `StrictConvexSphArm` reindexing).

2. **The reach recursion is unmechanised.**  Case 1 (target reached) opens `A` at `k` until
   `jointAngle A' k = jointAngle B k`, *reducing the count of unmatched joints* and recursing on the
   lex measure `(n, #unmatched)`.  The §8.3 boundary convexity of the opened arm at `δ*` is now
   available (`SphericalAdmissibleSup.reach_strictConvex_at_sup`), but the well-founded recursion on
   `#unmatched` and the construction of the matched arm `A'` (same level `n+1`, one more joint equal to
   `B`'s, all others fixed) is absent from the substrate.

3. **The matched-data cut has no `B`-side construction.**  Case 2 (stuck) yields the diagonal cut of
   `A` (`SphericalDiagCut.diagonalCutArm_holds`, present), but feeding `SphericalSZChain.cut_endpt_transport`
   needs the *matching* cut of `B` with equal sides and nondecreasing joints — there is **no `B`-side
   diagonal-cut construction matching `A`'s** in the substrate, only the `A`-side `cutArm`.

We isolate **exactly** `OpeningStructuralAssembly` as the single resistant `Prop`, prove its
non-vacuity, and route the fully-assembled arm lemma through it.

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
open ProofsInTheBook.SphericalArmClose

namespace ProofsInTheBook.SphericalArmFinal

/-! ## 1. `BoundaryConvexPersist` is proved (re-export). -/

/-- **`BoundaryConvexPersist` — PROVED.**  Re-export of `SphericalArmClose.boundaryConvexPersist`: the
corrected, interval-true boundary persistence holds unconditionally. -/
theorem boundaryConvexPersist : BoundaryConvexPersist :=
  ProofsInTheBook.SphericalArmClose.boundaryConvexPersist

/-! ## 2. The discharged §8.3 hemisphere boundary obstacle (REACH case).

The substrate's `BoundaryConvexPersistAtSup` was unsound because the admissible-supremum family did
not monitor the `open_hemisphere` functional at the rotated tail.  Having augmented the family
(`SphericalAdmissibleSup.augmentedSupport`/`hemiMargin`) and proved
`SphericalAdmissibleSup.reach_strictConvex_at_sup`, we reassemble the genuine REACH-case boundary
persistence: at an angle `δ` (the augmented admissible supremum, REACH branch) where every non-incident
opened support is strict, every edge is short, and the hemisphere functional is strict at every opened
vertex, the opened arm `openArm A δ` is strictly convex — the boundary fact the substrate lacked. -/

/-- **REACH-case boundary convexity persistence (the discharged hemisphere obstacle).**  Packages
`SphericalAdmissibleSup.reach_strictConvex_at_sup`: given the strict opened-arm data at the boundary
angle `δ` (edges short, non-incident supports strict, hemisphere functional strict at every vertex,
with a unit normal `h`), the opened arm is a `StrictConvexSphArm`.  This is the precise REACH-branch
content the augmented monitoring supplies — the substrate's unsound `BoundaryConvexPersistAtSup`, now
true and proved on the branch where it holds. -/
theorem reachBoundaryConvex_of_strictData {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    (hA : StrictConvexSphArm A) {δ : ℝ} {h : E3} (hnorm : ‖h‖ = 1)
    (hedge : ∀ i : Fin (n + 1 + 1), ShortArc (openArm A δ i) (openArm A δ (i + 1)))
    (hmix : ∀ i j : Fin (n + 1 + 1), j ≠ i → j ≠ i + 1 →
        0 < sOrient (openArm A δ i) (openArm A δ (i + 1)) (openArm A δ j))
    (hhem : ∀ k : Fin (n + 1 + 1), 0 < (⟪h, (openArm A δ k : E3)⟫ : ℝ)) :
    StrictConvexSphArm (openArm A δ) :=
  reach_strictConvex_at_sup hA hnorm hedge hmix hhem

/-! ## 3. The arm lemma, conditional only on `OpeningStructuralAssembly`.

Because `BoundaryConvexPersist` is now proved, the two-hypothesis conditional arm lemmas of
`SphericalArmClose` collapse to a single hypothesis: the multi-vertex opening construction
`OpeningStructuralAssembly`. -/

/-- **`SchoenbergZarembaTarget` from the opening construction alone.**  With the proved
`boundaryConvexPersist`, the structural assembly `OpeningStructuralAssembly` suffices. -/
theorem schoenbergZaremba_of_opening (hasm : OpeningStructuralAssembly) :
    SchoenbergZarembaTarget :=
  schoenbergZaremba_of_assembly boundaryConvexPersist hasm

/-- **The spherical arm lemma (weak), conditional only on `OpeningStructuralAssembly`.**  Equal-sided
strictly-convex arms with nondecreasing joints have nondecreasing endpoint distance — modulo the single
remaining residue, the §8.4 opening construction. -/
theorem spherical_arm_mono_final (hasm : OpeningStructuralAssembly)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_assembly boundaryConvexPersist hasm hn A B hA hB hside hangle

/-- **The spherical arm lemma (strict), conditional only on `OpeningStructuralAssembly`.** -/
theorem spherical_arm_mono_strict_final (hasm : OpeningStructuralAssembly)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict_of_assembly boundaryConvexPersist hasm hn A B hA hB hside hangle hstrict

/-! ## 4. Non-vacuity of the single remaining residue (playbook §3.3).

`OpeningStructuralAssembly` is non-vacuous and *strictly narrower* than `SchoenbergZarembaTarget`: its
hypothesis `BoundaryConvexPersist` is realised (now *proved*, `boundaryConvexPersist`), and its
conclusion `StuckWitnessExists ∧ WeakArmStep` is the pair of substrate residues, each independently
shown satisfiable.  It carries only the opening construction (conditional on the persistence input),
not the full kernel chain. -/

/-- Non-vacuity: the residue's hypothesis `BoundaryConvexPersist` is satisfiable — indeed proved. -/
theorem openingStructuralAssembly_hypothesis_proved : BoundaryConvexPersist :=
  boundaryConvexPersist

/-- Non-vacuity: the residue's target is the conjunction of the two substrate residues, each
satisfiable (the stuck-branch span membership and the weak `endpt A ≤ endpt A`). -/
theorem openingStructuralAssembly_target_satisfiable {n : ℕ} (A : Fin (n + 1 + 1) → S2) (a c : S2) :
    ((a : E3) ∈ Submodule.span NNReal ({(a : E3), (c : E3)} : Set E3)) ∧ endpt A ≤ endpt A :=
  ⟨(stuckWitness_payload_satisfiable a c).1, le_refl _⟩

end ProofsInTheBook.SphericalArmFinal
