import ProofsInTheBook.SphericalOpeningGeneral
import ProofsInTheBook.SphericalOpeningDichotomy
import ProofsInTheBook.SphericalArmFinish
import ProofsInTheBook.SphericalArmClose2
import ProofsInTheBook.ChordSeparationClose
import ProofsInTheBook.PlanarMapSeamInst
import ProofsInTheBook.PolygonEarExistence
import ProofsInTheBook.PolygonExtremeEar

/-!
# `ChapterMinimalResidue` — consolidation/minimization pass over `ChapterResidueAudit`.

This module DOES NOT prove any new mathematics.  It re-states each of the three open chapters'
headline theorems conditional on the **minimal** genuine-core residue set obtained after
DISCHARGING the dischargeable *secondary* residues the audit flagged.  Every theorem here is a
pure composition of already-committed lemmas; no genuine Jordan/§4 core is attempted.

The four secondary residues examined (per the directive), with the honest verdict for each:

1. **Ch13 `hMain`** (`∀ m, 2 ≤ m → Main m`):  **DISCHARGED** — but only by *route swap*.
   `hMain` cannot be dropped from the `SphericalOpeningDichotomy` route (its STUCK branch is an
   *ear cut* discharged by `interiorStuck_endpt_pair`, which genuinely consumes the `Main` IH at
   strictly smaller dimensions; and `Main` itself closes only from the *separate* residue
   `SZOpeningStep`, not from the three named cores).  The genuinely `hMain`-FREE route is the
   `SphericalArmFinish` `SZComparison`/`unmatchedCount` recursion: its CUT branch produces
   `MatchedCutData A B` (a *same-level* SAS cut), discharged by `endpt_of_matchedCutData` using
   only `SZComparison n` — never `Main m`.  Hence Ch13's headline restates conditional on the
   single bundled per-step atom `DeficientReachStep` (or its strictly-structural refinement
   `DeficientReachStructural`), with NO `hMain`.  See `ch13_*_of_deficientReachStep` /
   `ch13_*_of_structural` below.

2. **Ch13 `LastJointOpeningInterior`** (the §8.4 opening atom):  **NOT DISCHARGED** — genuine core.
   The `by_cases Stuck` dispatch on `augmented_reachOrStuck_at_sup` + `reach_strictConvex_at_sup`
   produces, in the `¬ Stuck` branch, only `StrictConvexSphArm (openTail A K (+δ*))` and the `+δ`
   REACH predicate; but the REACH-datum endpoint bound is the *corrected* `-δ` companion
   `endpt_openTail_interior_mono_neg`.  The two facts live at opposite opening signs and cannot be
   combined into `ReachStepDatum A B` without re-orienting the monitored family from `+δ` to `-δ`.
   That re-orientation is an edit to `SphericalMonitoredSup` (forbidden by the directive), and the
   STUCK boundary additionally needs the separate hard core
   `SphericalOpeningGlue.HemiMarginStrictPosAtSup`.  Exact upstream edit required: see §Ch13 GAP.

3. **Ch35 `faceCore`** (`NumCyclesCutPhi2`):  **NOT eliminated — lateral move only.**
   `PlanarMap.SeamInst.SeamDecomposition.numCyclesCutPhi2` discharges `NumCyclesCutPhi2` *from* a
   `SeamDecomposition M C`, but there is NO unconditional `∀ C, C.NumCyclesCutPhi2` in the
   substrate (`PlanarMapSeamInst`/`CutFaceLabel` headers state the certificate "has no instance"
   for a general `SimplePrimalCycle` — it is the genus-`0` planarity content).  So discharging
   `faceCore` only TRADES the `NumCyclesCutPhi2` residue for a `SeamDecomposition` residue; the
   residue *count* is unchanged.  We record the traded restatement (`ch35_*_of_seam`) for
   completeness and keep the audited Ch35 residue as `gateCompat'` + `faceCore`.

4. **Ch36 `ear` selector**:  **DISCHARGED** (genuine elimination of a parameter).
   `PolygonExtremeEar.extremeEar = extremeVertex` is an unconditional concrete selector
   (`PolygonGeomInput.exists_extreme_vertex`, proved from finiteness).  Instantiating
   `ear := @extremeEar` removes the free `ear` parameter from the Ch36 headline.  The Jordan
   fields `Esup` (`EarCutData.earDeletedExterior`) and `rest` remain — they are now specialised to
   the extreme vertex but are NOT lowered (the genuine core `earDeletedExterior` stays).

No `sorry` / `axiom` / `admit` / `native_decide`.  Every theorem is a pure composition.
-/

set_option autoImplicit false

noncomputable section

namespace ProofsInTheBook.ChapterMinimalResidue

/-! ## Ch13 — headline conditional on the single per-step atom `DeficientReachStep`, NO `hMain`.

The `SphericalArmFinish` `SZComparison`/`unmatchedCount` recursion is fully self-contained: it
recurses on the natural-number measure `unmatchedCount A B` at a *fixed* level, its congruent/CUT
branches producing `MatchedCutData A B` discharged by `endpt_of_matchedCutData` from `SZComparison
n` alone, and its REACH branch recursing on a strictly smaller measure.  No `Main` IH at smaller
dimensions is ever needed — `hMain` is eliminated.

Minimal residue set: `DeficientReachStep` (the single bundled §8.4 opening atom).
-/

open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalArmFinish (DeficientReachStep)
open ProofsInTheBook.SphericalArmClose2 (DeficientReachStructural)

/-- **Ch13 headline (weak), `hMain`-free.**  The spherical arm chord is monotone under joint
widening, conditional on EXACTLY the single per-step atom `DeficientReachStep` — no `Main`
invariant, no separately-exposed cut/strict residues (they are bundled inside the atom).  Direct
re-export of `SphericalArmFinish.spherical_arm_mono_of_deficientReachStep`. -/
theorem ch13_spherical_arm_mono_of_deficientReachStep
    (hstep : DeficientReachStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  ProofsInTheBook.SphericalArmFinish.spherical_arm_mono_of_deficientReachStep
    hstep hn A B hA hB hside hangle

/-- **Ch13 headline (strict), `hMain`-free.**  The spherical arm chord is *strictly* monotone when
some joint is strictly wider, conditional on EXACTLY `DeficientReachStep`. -/
theorem ch13_spherical_arm_mono_strict_of_deficientReachStep
    (hstep : DeficientReachStep)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  ProofsInTheBook.SphericalArmFinish.spherical_arm_mono_strict_of_deficientReachStep
    hstep hn A B hA hB hside hangle hstrict

/-- **Ch13 headline (weak), `hMain`-free, structural refinement.**  Same headline conditional on the
strictly-structural atom `DeficientReachStructural` (the analytic strict-convexity-at-`δ*` half
already banked beneath it; what remains is the structural opening/cut bookkeeping (b1)+(b2)).  Via
`SphericalArmClose2.spherical_arm_mono_of_structural`. -/
theorem ch13_spherical_arm_mono_of_structural
    (hstep : DeficientReachStructural)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  ProofsInTheBook.SphericalArmClose2.spherical_arm_mono_of_structural
    hstep hn A B hA hB hside hangle

/-- **Ch13 headline (strict), `hMain`-free, structural refinement.** -/
theorem ch13_spherical_arm_mono_strict_of_structural
    (hstep : DeficientReachStructural)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  ProofsInTheBook.SphericalArmClose2.spherical_arm_mono_strict_of_structural
    hstep hn A B hA hB hside hangle hstrict

/-! ### Ch13 GAP (residue 2, `LastJointOpeningInterior`): exact upstream edit required.

The §8.4 opening atom `LastJointOpeningInterior` (= `ReachStepDatum A B ∨ InteriorStuckData A B`)
does NOT discharge to the analytic dichotomy pieces without an upstream edit.  Precisely:

* `SphericalReachConstruction.reachDatum_hmix_hhem_from_notStuck` (the `¬ Stuck` REACH branch)
  produces `StrictConvexSphArm (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap))` — i.e. at
  the `+δ` supremum `δ* = monitoredSup …`.
* `SphericalReachConstruction.corrected_endpt_mono` supplies `endpt A ≤ endpt (openTail A K (-δ))`
  — the *corrected* `-δ` orientation (`+δ` gives a *decreasing* endpoint, `EndpointPosMono` false).
* `reachDatum_of_corrected_reach` needs BOTH `hAsharp` and the REACH equality `jointAngle Aσ k =
  jointAngle B k` at the SAME `σ`.  Supplying `hAsharp` at `+δ*` and `hendpt` at `-δ*` is a sign
  mismatch; the REACH predicate `jointAngle (openTail A K (-δ*)) k = jointAngle B k` is only
  attainable in a `-δ`-oriented monitored family.

  **Exact upstream edit (NOT made — directive forbids editing existing files):**
  in `ProofsInTheBook.SphericalMonitoredSup`, re-orient the monitored family `monitoredFamily` /
  `monitoredSup` / `Reach` / `Stuck` (and the closure lemmas `supportConstraint_nonneg_at_sup`,
  `hemiMargin_nonneg_at_sup`, `strict_persistence_at_reach`) from the `+δ` opening
  `openTail A K δ` to the corrected `-δ` opening `openTail A K (-δ)` (equivalently, flip the sign
  of the rotation angle fed to `openTail` throughout the family construction), matching the proved
  endpoint companion `SphericalOpeningGlue.endpt_openTail_interior_mono_neg`.

* Even with that sign fix, the STUCK branch still requires the separate genuine hard core
  `SphericalOpeningGlue.HemiMarginStrictPosAtSup`, and assembling `InteriorStuckData`'s ear
  convexity certificates is part of the genuine §8.4 core.  Hence `LastJointOpeningInterior`
  remains a GENUINE residue (not a mechanical/structural secondary), and is kept.

The audited named-cores route (`SphericalOpeningDichotomy.spherical_arm_mono_of_opening`,
conditional on `FoldedFlatCutTransport` + `InteriorStuckStrict` + `LastJointOpeningInterior` +
`hMain`) is therefore unchanged: in THAT route `hMain` is genuinely required (its STUCK ear cut
consumes the `Main` IH, and `Main` closes only from the separate residue `SZOpeningStep`).  The
`hMain`-free minimization is achieved instead by the `DeficientReachStep` route above.
-/

/-! ## Ch35 — `faceCore` is a lateral move, not an elimination.

`PlanarMap.SeamInst.SeamDecomposition.numCyclesCutPhi2 : SeamDecomposition M C → C.NumCyclesCutPhi2`
discharges `NumCyclesCutPhi2` only from a `SeamDecomposition M C`, and no unconditional
`∀ C, C.NumCyclesCutPhi2` exists (the certificate is the genus-`0` planarity content; the substrate
headers record it "has no instance" for a general cycle).  So the residue is merely TRADED
(`NumCyclesCutPhi2` → `SeamDecomposition`); the count is unchanged.  We record the traded
restatement for completeness; the audited Ch35 residue stays `gateCompat'` + `faceCore`.
-/

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- **Ch35 headline, `faceCore` traded for a seam decomposition (NOT a residue reduction).**  The
chord separates the near-triangulation's region, conditional on the crisp cap-channel kernel
`gateCompat'`, a concrete `SeamDecomposition` of the cut (in place of the abstract `faceCore`), and
the standing chord/cycle data.  The seam decomposition is itself a structural residue with no
unconditional instance, so this restatement does NOT lower the residue count below the audited
`gateCompat'` + `faceCore`. -/
theorem ch35_sphereChordSeparation_of_seam {M : CombMap D} (hNT : NearTriangulation M)
    {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (Sd : ProofsInTheBook.PlanarMap.SeamInst.SeamDecomposition M C)
    (gateCompat' : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h))) :
    hNT.SphereChordSeparation h :=
  hNT.sphereChordSeparation_of_input' h C hsub
    { faceCore := Sd.numCyclesCutPhi2, gateCompat' := gateCompat' } i₀ hleft hright

/-! ## Ch36 — `ear` selector DISCHARGED via the concrete `extremeEar`.

`PolygonExtremeEar.extremeEar` is an unconditional concrete selector (the lexicographically extreme
vertex, `PolygonGeomInput.extremeVertex`, whose existence is proved from finiteness).  Instantiating
`ear := @extremeEar` eliminates the free `ear` parameter from `PolygonEarExistence.artGallery_strict`.

Minimal residue set after this pass: `Esup` (specialised to `extremeEar`, single Jordan field
`EarCutData.earDeletedExterior`) + `rest` (specialised) + `M` (the peel oracle).  The `ear`
parameter is gone; the genuine Jordan core `earDeletedExterior` is unchanged (see the audit's GAP
NOTE — the `RayCrossingAlternation` / `EarLeg1Free` chains do not lower it below `EarCutData`).
-/

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing (ClosedRegion')
open ProofsInTheBook.PolygonEarDelete (EarCutData)
open ProofsInTheBook.PolygonJordan (RemainingResidualData)

/-- **Ch36 headline, `ear` selector discharged.**  Every strict simple polygon with a ray admits
`≤ ⌊n/3⌋` vertex guards covering its closed region, conditional on EXACTLY the ear-cut data supply
`Esup` (single Jordan field `EarCutData.earDeletedExterior`) and the remaining cut data `rest`,
BOTH specialised to the concrete extreme-vertex selector `extremeEar`, plus the peel oracle `M`.
The free `ear` parameter is eliminated by instantiating
`PolygonEarExistence.artGallery_strict` at `ear := @ProofsInTheBook.PolygonExtremeEar.extremeEar`. -/
theorem ch36_artGallery_strict_extremeEar {n : ℕ}
    (Esup : ∀ {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P),
      4 ≤ m → EarCutData P σ (ProofsInTheBook.PolygonExtremeEar.extremeEar P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (ProofsInTheBook.PolygonExtremeEar.extremeEar P))
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonEarExistence.artGallery_strict
    (@ProofsInTheBook.PolygonExtremeEar.extremeEar) Esup rest M P ρ

end ProofsInTheBook.ChapterMinimalResidue

/-! ## Axiom audit — each minimized headline `#print axioms`'d (clean-3 expected:
`propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, no custom axioms). -/

#print axioms ProofsInTheBook.ChapterMinimalResidue.ch13_spherical_arm_mono_of_deficientReachStep
#print axioms ProofsInTheBook.ChapterMinimalResidue.ch13_spherical_arm_mono_strict_of_deficientReachStep
#print axioms ProofsInTheBook.ChapterMinimalResidue.ch13_spherical_arm_mono_of_structural
#print axioms ProofsInTheBook.ChapterMinimalResidue.ch13_spherical_arm_mono_strict_of_structural
#print axioms ProofsInTheBook.ChapterMinimalResidue.ch35_sphereChordSeparation_of_seam
#print axioms ProofsInTheBook.ChapterMinimalResidue.ch36_artGallery_strict_extremeEar
