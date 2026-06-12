import ProofsInTheBook.ZinanCh36Assembly
import ProofsInTheBook.PolygonJordan

/-!
# Ch36 ear-base split supply

This file isolates the exact non-circular data needed to discharge the
`ZinanCh36Assembly.EarValueSplitData` input.

The landed substrate does not prove an unconditional Meisters/two-ears theorem.  What it does
provide is a precise ear-removal interface (`PolygonJordan.EarInductionInput`) and the remaining
cut data (`PolygonJordan.RemainingResidualData`).  The only part of the ear input used here is the
ear-base diagonal, not the exterior/even-parity kernel.  The strict child axioms and same-ray child
directions come from the remaining residual data.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36Ears

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonJordan
open ProofsInTheBook.ZinanCh36Assembly

noncomputable section

/-- The exact non-circular ear-base diagonal supply needed by `EarValueSplitData`.

It contains only an ear selector and the assertion that the ear base
`cyclicPrev (ear P) → cyclicNext (ear P)` is a corrected diagonal.  It deliberately does not carry
the `EarCutData.earDeletedExterior` field. -/
structure EarDiagonalSupply : Type where
  ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m
  hdiag : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
    4 ≤ m → IsDiagonal' P ρ (cyclicPrev (ear P)) (cyclicNext (ear P))

/-- The ear selector carried by an `EarDiagonalSupply`. -/
def earChoice (S : EarDiagonalSupply) : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m :=
  S.ear

/-- Remaining per-cut data keyed to the chosen ear selector. -/
abbrev RestFor (S : EarDiagonalSupply) : Type :=
  ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
    RemainingResidualData P ρ ((earChoice S) P)

/-- A `PolygonJordan.EarInductionInput` contains an ear-base diagonal supply.

The exterior/even-parity field of `EarInductionInput` is not used by the adapter below; this
projection records only the selector and diagonal field. -/
def earDiagonalSupply_of_earInput (E : EarInductionInput) : EarDiagonalSupply where
  ear := E.ear
  hdiag := E.earDiagonal

/-- Build the non-circular `EarValueSplitData` package from an ear-base diagonal supply plus the
remaining cut data.

The diagonal comes from `S`; the left/right strict axioms and same-ray child directions come from
`rest`. -/
def earValueSplitData_of_supply
    (S : EarDiagonalSupply) (rest : RestFor S)
    {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P) (hm : 4 ≤ m) :
    EarValueSplitData P ρ ((earChoice S) P) := by
  let hdiag := S.hdiag P ρ hm
  let R := rest P ρ
  exact
    { hdiag := hdiag
      lax := R.leftAxioms hdiag
      rax := R.rightAxioms hdiag
      σL := R.leftRay hdiag
      σR := R.rightRay hdiag
      hLr := (R.commonRay hdiag).1
      hRr := (R.commonRay hdiag).2 }

/-- The `Esplit` input required by `ZinanCh36Assembly.artGallery_strict_mod_M`, produced from the
honest ear-base diagonal supply and the existing remaining cut data. -/
def esplit_holds
    (S : EarDiagonalSupply) (rest : RestFor S) :
    ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ ((earChoice S) P) := by
  intro m P ρ hm
  exact earValueSplitData_of_supply S rest P ρ hm

/-- Specialization of `esplit_holds` to the existing `PolygonJordan.EarInductionInput` interface. -/
def esplit_holds_of_earInput
    (E : EarInductionInput)
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (E.ear P)) :
    ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ (E.ear P) := by
  intro m P ρ hm
  exact earValueSplitData_of_supply (earDiagonalSupply_of_earInput E) rest P ρ hm

/-- Adapter from full `EarCutData` to the non-circular value-split package.

This is provided only as a compatibility adapter: unlike `earValueSplitData_of_supply`, it starts
from a full `EarCutData`, whose exterior field is stronger than the split package needs. -/
def earValueSplitData_of_earCutData
    {m : ℕ} {P : StrictSimplePolygon m} {ρ : RayDirection P} {i : Fin m}
    (E : ProofsInTheBook.PolygonEarDelete.EarCutData P ρ i) :
    EarValueSplitData P ρ i where
  hdiag := E.hdiag
  lax := E.lax
  rax := E.rax
  σL := Classical.choose E.leftRayEq
  σR := Classical.choose E.rightRayEq
  hLr := Classical.choose_spec E.leftRayEq
  hRr := Classical.choose_spec E.rightRayEq

/-- A uniform full `EarCutData` supply also yields the `Esplit` input. -/
def esplit_holds_of_earCutData
    (ear : ∀ {m : ℕ} (_P : StrictSimplePolygon m), Fin m)
    (Esup : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → ProofsInTheBook.PolygonEarDelete.EarCutData P ρ (ear P)) :
    ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      4 ≤ m → EarValueSplitData P ρ (ear P) := by
  intro m P ρ hm
  exact earValueSplitData_of_earCutData (Esup P ρ hm)

/-- The base facts package used by the Ch36 geometric art-gallery headline. -/
abbrev Ch36BaseFacts :=
  ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
    (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms
      ProofsInTheBook.PolygonTriangleConvex.triangleConvexLeaf_holds
      ProofsInTheBook.PolygonDegenerateWall.triangleExteriorEven_unconditional)

/-- The remaining diagonal-attach input in the Ch36 headline. -/
abbrev Ch36AttachInput :=
  ProofsInTheBook.PolygonLast.DiagonalAttachInput Ch36BaseFacts

/-- `artGallery_strict_mod_M` with `Esplit` discharged from an honest ear-base diagonal supply.

The remaining inputs are exactly `S` (the ear-base diagonal supply), `rest`, and the peel oracle
`M`. -/
theorem artGallery_strict_mod_M_from_supply
    {n : ℕ} (S : EarDiagonalSupply) (rest : RestFor S) (M : Ch36AttachInput)
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  ProofsInTheBook.ZinanCh36Assembly.artGallery_strict_mod_M
    (earChoice S) (esplit_holds S rest) rest M P ρ

/-- `artGallery_strict_mod_M` with `Esplit` discharged from `PolygonJordan.EarInductionInput`. -/
theorem artGallery_strict_mod_M_of_earInput
    {n : ℕ} (E : EarInductionInput)
    (rest : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
      RemainingResidualData P ρ (E.ear P))
    (M : Ch36AttachInput)
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  ProofsInTheBook.ZinanCh36Assembly.artGallery_strict_mod_M
    E.ear (esplit_holds_of_earInput E rest) rest M P ρ

end

end ProofsInTheBook.ZinanCh36Ears

#print axioms ProofsInTheBook.ZinanCh36Ears.earValueSplitData_of_supply
#print axioms ProofsInTheBook.ZinanCh36Ears.esplit_holds
#print axioms ProofsInTheBook.ZinanCh36Ears.esplit_holds_of_earInput
#print axioms ProofsInTheBook.ZinanCh36Ears.earValueSplitData_of_earCutData
#print axioms ProofsInTheBook.ZinanCh36Ears.artGallery_strict_mod_M_from_supply
#print axioms ProofsInTheBook.ZinanCh36Ears.artGallery_strict_mod_M_of_earInput
