import ProofsInTheBook.SphericalOpeningGeneral
import ProofsInTheBook.SphericalOpeningDichotomy
import ProofsInTheBook.ChordSeparationClose
import ProofsInTheBook.PolygonEarExistence
import ProofsInTheBook.PolygonWindingBound
import ProofsInTheBook.PolygonEarEscape
import ProofsInTheBook.PolygonEarCornerEscape

/-!
# `ChapterResidueAudit` — integration / audit-readiness verification of the three open
chapters' headline theorems, each wired conditional on EXACTLY its single crisp kernel
(plus any genuinely-irreducible secondary residue).

This module DOES NOT prove any new mathematics.  It only *composes* the committed reduction
lemmas of the three chapters into one audited conditional headline per chapter, and runs
`#print axioms` on each.  The goal is to confirm, mechanically, that each chapter's reduction
chain composes cleanly and to record the EXACT minimal residue set the headline rests on.

The three headlines:

* **Ch13** `spherical_arm_mono` / `spherical_arm_mono_strict`
  ⟸ `FoldedFlatCutTransport` (§4 body/cut transport) + `InteriorStuckStrict` (the single
    strict-bound residue) + `LastJointOpeningInterior` (the §8.4 opening production atom) +
    the weak `Main` invariant.  COMPOSES.

* **Ch35** `SphereChordSeparation`
  ⟸ `gateCompat'` (cap-channel discrete-Jordan, the crisp field of `ChordJordanInput'`) +
    `faceCore` (= `NumCyclesCutPhi2`, kernel-anchored, separately dischargeable) + the chord/
    cycle data.  COMPOSES.

* **Ch36** `artGallery_strict`
  ⟸ `Esup` (the `EarCutData` supply whose single Jordan field is `earDeletedExterior`) +
    `rest` (`RemainingResidualData`) + `M` (the peel oracle).  COMPOSES.
    The further reductions of `earDeletedExterior` to `RayCrossingAlternation`
    (`PolygonWindingBound`) or to `EarLeg1Free` / `EarCornerEscape`
    (`PolygonEarEscape` / `PolygonEarCornerEscape`) reduce the Jordan FIELD's *conclusion* but
    are **structurally conditional on an already-present `EarCutData`** (the residue `Prop`s
    `EarLeg1Free` / `EarCornerEscape` take `EarCutData P ρ i` as a hypothesis, and the only
    `E`-field they project is `E.earOrient`).  Hence they do NOT lower the *headline*'s residue
    below `EarCutData`; the audited Ch36 residue is `Esup` + `rest` + `M`.  See the GAP note in
    §Ch36 below.

No `sorry` / `axiom` / `admit` / `native_decide`.  Every theorem here is a pure composition of
committed lemmas.
-/

set_option autoImplicit false

noncomputable section

namespace ProofsInTheBook.ChapterResidueAudit

/-! ## Ch13 — `spherical_arm_mono(_strict)` conditional on the §4 cut transport + the §8.4
opening atom + the single strict residue + the weak `Main` invariant.

Chain (all committed):
`SphericalOpeningDichotomy.spherical_arm_mono_of_opening` /
`spherical_arm_mono_strict_of_opening`, which compose
`SphericalArmCleanReduction.spherical_arm_mono(_strict)_of_foldedFlat`
(the interior recursion `defStepColInterior_endpt`, with `DeficientReachCollinearInterior`
discharged by `SphericalOpeningDichotomy.deficientReachCollinearInterior_holds` from
`LastJointOpeningInterior`).

Minimal residue set:
* `FoldedFlatCutTransport`     — the §4 body/cut endpoint transport (the design-§4 glue);
* `InteriorStuckStrict`        — the single strict-bound residue (the interior cut exposes only
                                 the weak `≤`; the strict `<` in the wider case is not);
* `LastJointOpeningInterior`   — the §8.4 last-joint opening production atom (REACH ∨ interior
                                 STUCK);
* `hMain : ∀ m, 2 ≤ m → Main m`— the weak `Main` invariant threaded by the inductive harness.
-/

open ProofsInTheBook.SphericalCutTransport (FoldedFlatCutTransport)
open ProofsInTheBook.SphericalArmCleanReduction (InteriorStuckStrict)
open ProofsInTheBook.SphericalOpeningDichotomy (LastJointOpeningInterior)
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction (Main)

/-- **Ch13 headline (weak), audited.**  The spherical arm chord is monotone under joint
widening, conditional on EXACTLY the four residues above. -/
theorem ch13_spherical_arm_mono
    (hcut : FoldedFlatCutTransport)
    (hstr : InteriorStuckStrict)
    (hopen : LastJointOpeningInterior)
    (hMain : ∀ m, 2 ≤ m → Main m)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  ProofsInTheBook.SphericalOpeningDichotomy.spherical_arm_mono_of_opening
    hcut hstr hopen hMain hn A B hA hB hside hangle

/-- **Ch13 headline (strict), audited.**  The spherical arm chord is *strictly* monotone when
some joint is strictly wider, conditional on EXACTLY the four residues above. -/
theorem ch13_spherical_arm_mono_strict
    (hcut : FoldedFlatCutTransport)
    (hstr : InteriorStuckStrict)
    (hopen : LastJointOpeningInterior)
    (hMain : ∀ m, 2 ≤ m → Main m)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  ProofsInTheBook.SphericalOpeningDichotomy.spherical_arm_mono_strict_of_opening
    hcut hstr hopen hMain hn A B hA hB hside hangle hstrict

/-- **Ch13 headline (general-`(i,j)` route variant), audited.**  The same weak bound through the
index-free STUCK route of `SphericalOpeningGeneral`, conditional on `FoldedFlatCutTransport` +
`GeneralStuckStrict` + `DeficientReachGeneral` + `hMain` (the binding-support index-identification
gap eliminated).  Recorded to confirm both committed routes compose. -/
theorem ch13_spherical_arm_mono_general
    (hcut : FoldedFlatCutTransport)
    (hstr : ProofsInTheBook.SphericalOpeningGeneral.GeneralStuckStrict)
    (hstep : ProofsInTheBook.SphericalOpeningGeneral.DeficientReachGeneral)
    (hMain : ∀ m, 2 ≤ m → Main m)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  ProofsInTheBook.SphericalOpeningGeneral.spherical_arm_mono_of_general
    hcut hstr hstep hMain hn A B hA hB hside hangle

/-! ## Ch35 — `SphereChordSeparation` conditional on `gateCompat'` + `faceCore` + chord data.

Chain (all committed):
`ChordSeparationClose.sphereChordSeparation_of_input'`, taking the bundle
`ChordJordanInput'` (fields `faceCore : NumCyclesCutPhi2` and `gateCompat'`, the per-edge
cap-channel discrete-Jordan supplier) and the chord/cycle data, and producing
`SphereChordSeparation`.  We expose the bundle's two fields as separate hypotheses to make the
crisp kernel `gateCompat'` explicit; `faceCore` (= `NumCyclesCutPhi2`) is kernel-anchored and
separately dischargeable (`CutFaceLabel` / `PlanarMapSeamInst.numCyclesCutPhi2`).

Minimal residue set:
* `gateCompat'`  — the single crisp Jordan kernel (cap-channel cross-bank endpoint link +
                   interior triangle gates, per cycle edge);
* `faceCore`     — `NumCyclesCutPhi2` (kernel-anchored, dischargeable);
* the chord/cycle data (`h`, `C`, `hsub`, `i₀`, `hleft`, `hright`) — the standing geometric
  inputs of the chapter statement.
-/

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle (ChordJordanInput')

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- **Ch35 headline, audited.**  The chord separates the near-triangulation's region,
conditional on EXACTLY the crisp cap-channel kernel `gateCompat'`, the kernel-anchored
`faceCore`, and the standing chord/cycle data.  Composes the two `ChordJordanInput'` fields
back into the bundle and runs `sphereChordSeparation_of_input'`. -/
theorem ch35_sphereChordSeparation {M : CombMap D} (hNT : NearTriangulation M)
    {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (faceCore : C.NumCyclesCutPhi2)
    (gateCompat' : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h))) :
    hNT.SphereChordSeparation h :=
  hNT.sphereChordSeparation_of_input' h C hsub
    { faceCore := faceCore, gateCompat' := gateCompat' } i₀ hleft hright

/-! ## Ch36 — `artGallery_strict` conditional on the ear-cut data (Jordan field
`earDeletedExterior`) + the remaining cut data + the peel oracle `M`.

Chain (all committed):
`PolygonEarExistence.artGallery_strict`, which composes
`isConvexVertex'_holds` (the `n = 3` base discharged internally via
`triangle_isConvexVertex'`, the `4 ≤ m` step via `PolygonEarDelete.isConvexVertex'_of_earCutData`)
with `PolygonGeomInput.artGallery_strict_of_residue` over the peel oracle `M`.

Minimal residue set:
* `Esup` — the `EarCutData` supply.  Its ONLY genuine planar field is the Jordan kernel
           `EarCutData.earDeletedExterior` (a strict-interior ear point lies outside the
           ear-deleted `(n-1)`-gon); the other fields are the standard cut data
           (`hdiag`/`lax`/`rax`/`leftRayEq`/`rightRayEq`/`earOrient`).
* `rest` — `RemainingResidualData` (transversality, axioms, sub-rays, disjointness, boundary,
           intersection — the standard combinatorial cut data).
* `M`    — `PolygonLast.DiagonalAttachInput` over the proved base-triangle facts (the
           ear-deletion induction driver / peel oracle).
* `ear`  — the ear selector.

### GAP NOTE (honest, per the directive): the `RayCrossingAlternation` / `EarLeg1Free` chains
do NOT lower the headline residue below `EarCutData`.

The task hypothesised the Ch36 headline could be wired conditional on `RayCrossingAlternation`
(via `PolygonWindingBound`/`PolygonEarEscape`/`PolygonEarCornerEscape`) or `EarLeg1Free`, with
`earDeletedExterior` reduced to it.  Verification finds this does NOT compose into the *headline*:

1. `PolygonWindingBound.earDeleted_exterior_of_bound` (the `RayCrossingAlternation` route)
   produces the `¬ ClosedRegion'` conclusion only from `windCross P ρ x = 1` (inside the parent)
   AND `windCross (buildLeftPoly …) σL x = 1` (inside the left ear) as *extra* inputs — neither
   is supplied by the ear-cut data nor by `RayCrossingAlternation`.  So this route discharges the
   bound `windCross ∈ {-1,0,1}`, not the headline's Jordan field.

2. `PolygonEarCornerEscape.earDeletedExterior_of_leg1Free` (the `EarLeg1Free` route) and
   `PolygonEarEscape.earDeletedExterior_of_cornerEscape` (the `EarCornerEscape` route) DO produce
   the `earDeletedExterior` *conclusion*, but BOTH take a full `EarCutData P ρ i` as a hypothesis
   (the residue `Prop`s `EarLeg1Free` / `EarCornerEscape` are themselves quantified over
   `EarCutData P ρ i`).  No committed lemma builds a full `EarCutData` from `EarLeg1Free` +
   the non-Jordan fields; the chain only projects `E.earOrient`.  Hence these reductions are
   structurally CIRCULAR for the headline: they replace the conclusion of the Jordan field given
   the bundle, but cannot remove `EarCutData` from the residue set.

We RECORD both reductions below as their committed (bundle-conditional) forms, to certify they
compose *as stated* (each is `EarCutData → … → ¬ ClosedRegion'`), and keep the audited headline
on the genuine residue `Esup` + `rest` + `M`.
-/

open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing (ClosedRegion' IsDiagonal')
open ProofsInTheBook.PolygonCutOracle (RightStrictAxioms buildRightPoly)
open ProofsInTheBook.PolygonEarDelete (EarCutData)
open ProofsInTheBook.PolygonJordan (RemainingResidualData)

/-- **Ch36 headline, audited.**  Every strict simple polygon with a ray admits `≤ ⌊n/3⌋`
vertex guards covering its closed region, conditional on EXACTLY the ear-cut data supply `Esup`
(single Jordan field `EarCutData.earDeletedExterior`), the remaining cut data `rest`, and the
peel oracle `M`.  Direct re-export of `PolygonEarExistence.artGallery_strict`. -/
theorem ch36_artGallery_strict {n : ℕ}
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esup : ∀ {m : ℕ} (P : StrictSimplePolygon m) (σ : RayDirection P),
      4 ≤ m → EarCutData P σ (ear P))
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (ear P))
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
          ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
          ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonEarExistence.artGallery_strict ear Esup rest M P ρ

/-- **Ch36 Jordan-field reduction (escape route), as committed.**  The `earDeletedExterior`
conclusion from the LOCAL `EarLeg1Free` kernel — but conditional on a full `EarCutData E`
(the structural circularity documented in the GAP NOTE).  Re-export of
`PolygonEarCornerEscape.earDeletedExterior_of_leg1Free`. -/
theorem ch36_earDeletedExterior_of_leg1Free
    (L : ProofsInTheBook.PolygonEarCornerEscape.EarLeg1Free)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (i : Fin m)
    (hm : 4 ≤ m) (E : EarCutData P ρ i)
    {x : Pt} {w0 w1 w2 : ℝ}
    (hoff : ¬ OnBoundary P x)
    (hw0 : 0 < w0) (hw1 : 0 < w1) (hw2 : 0 < w2) (hsum : w0 + w1 + w2 = 1)
    (hx : x = w0 • P.q (cyclicPrev i) + w1 • P.q i + w2 • P.q (cyclicNext i))
    (hdiag : IsDiagonal' P ρ (cyclicPrev i) (cyclicNext i))
    (rax : RightStrictAxioms P (cyclicPrev i) (cyclicNext i))
    (σR : RayDirection (ProofsInTheBook.PolygonCutOracle.buildRightPoly hdiag rax))
    (hRr : σR.r = ρ.r) :
    ¬ ClosedRegion' (ProofsInTheBook.PolygonCutOracle.buildRightPoly hdiag rax) σR x :=
  ProofsInTheBook.PolygonEarCornerEscape.earDeletedExterior_of_leg1Free
    L P ρ i hm E hoff hw0 hw1 hw2 hsum hx hdiag rax σR hRr

/-- **Ch36 winding bound (alternation route), as committed.**  The CORE planar-Jordan winding
bound `windCross ∈ {-1,0,1}` from the single Jordan kernel `RayCrossingAlternation`.  This is the
genuine integer-valued Jordan content the alternation kernel discharges; note it is the *bound*,
not the headline's `earDeletedExterior` field (see GAP NOTE).  Re-export of
`PolygonWindingBound.oWind_mem_neg_one_zero_one`. -/
theorem ch36_windCross_bound {n : ℕ} (P : StrictSimplePolygon n)
    (ρ : RayDirection P) (x : Pt) (hx : ¬ OnBoundary P x)
    (halt : ProofsInTheBook.PolygonWindingBound.RayCrossingAlternation P ρ x) :
    ProofsInTheBook.PolygonWinding.windCross P ρ x = 0 ∨
      ProofsInTheBook.PolygonWinding.windCross P ρ x = 1 ∨
      ProofsInTheBook.PolygonWinding.windCross P ρ x = -1 :=
  ProofsInTheBook.PolygonWindingBound.oWind_mem_neg_one_zero_one P ρ x hx halt

end ProofsInTheBook.ChapterResidueAudit

/-! ## Axiom audit — each audited headline `#print axioms`'d (clean-3 expected:
`propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`, no custom axioms). -/

#print axioms ProofsInTheBook.ChapterResidueAudit.ch13_spherical_arm_mono
#print axioms ProofsInTheBook.ChapterResidueAudit.ch13_spherical_arm_mono_strict
#print axioms ProofsInTheBook.ChapterResidueAudit.ch13_spherical_arm_mono_general
#print axioms ProofsInTheBook.ChapterResidueAudit.ch35_sphereChordSeparation
#print axioms ProofsInTheBook.ChapterResidueAudit.ch36_artGallery_strict
#print axioms ProofsInTheBook.ChapterResidueAudit.ch36_earDeletedExterior_of_leg1Free
#print axioms ProofsInTheBook.ChapterResidueAudit.ch36_windCross_bound
