import ProofsInTheBook.SphericalOpenedArmCore
import ProofsInTheBook.ZinanFFCT111
import ProofsInTheBook.ZinanFFCT113

/-!
# `ZinanFFCT112` — wiring the REAL arm lemma into the Cauchy fixed-chord contradiction.

Audit finding (2026-06-14): `Chapter13.CauchyArmOpeningObstruction` POSITS the arm lemma's conclusion
as a structure field `arm_conclusion : chord < newChord ∨ (∀ i, angles i = newAngles i)`, and its
`.contradiction` is a trivial 3-line unpacking — the genuine spherical arm lemma is never used
(Chapter13.lean does not even import the arm-lemma development).

This file supplies the GENUINE fixed-chord arm contradiction, derived from the real strict arm lemma
`SphericalOpenedArmCore.armMono_strict_of_stuckWitness`, conditional only on the single geometric
residue `StuckWitnessExists` (the §8.4 opening-witness existence; being discharged separately in
`ZinanFFCT113`).  When that residue lands, `cauchy_arm_fixed_chord_contradiction` is UNCONDITIONAL and
is the honest replacement for the posited `arm_conclusion`.

The unconditional `≤` arm lemma `ZinanFFCT111.spherical_arm_mono_final_ch13 : SphericalArmMonotone`
(closed 2026-06-13) discharges the weak half on its own; the strict half needs `StuckWitnessExists`.
-/

namespace ProofsInTheBook.ZinanFFCT112

open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalOpenedArmCore
open ProofsInTheBook.SphericalOpeningProcess (StuckWitnessExists)

/-- **The genuine fixed-chord arm contradiction.**  Two strictly convex spherical arms `A`, `B` with
equal side lengths and nondecreasing joints, where SOME joint of `B` is strictly wider, cannot have an
equal endpoint chord: the strict arm lemma forces `sDist (A 0)(A last) < sDist (B 0)(B last)`,
contradicting equality.  This is exactly the content the Cauchy 0/2-sign-change vertex link supplies —
DERIVED from `armMono_strict_of_stuckWitness`, not posited.  Conditional only on `StuckWitnessExists`. -/
theorem cauchy_arm_fixed_chord_contradiction (h : StuckWitnessExists)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i)
    (hchord : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n))) :
    False :=
  absurd hchord (ne_of_lt (armMono_strict_of_stuckWitness h hn A B hA hB hside hangle hstrict))

/-- **The strict arm lemma, surfaced as a clean top-level statement** (conditional on the single
residue).  Companion to the unconditional `≤` headline `spherical_arm_mono_final_ch13`. -/
theorem spherical_arm_mono_strict_of_residue (h : StuckWitnessExists)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  armMono_strict_of_stuckWitness h hn A B hA hB hside hangle hstrict

/-! ## Unconditional forms — the residue `StuckWitnessExists` is discharged in `ZinanFFCT113`.

`ZinanFFCT113.stuckWitnessExists_holds : StuckWitnessExists` (clean-3, via the tiny-opening bootstrap
off the unconditional weak lemma `spherical_arm_mono_final_ch13`) removes the last hypothesis.  The
strict spherical arm lemma and the genuine Cauchy fixed-chord contradiction are therefore
UNCONDITIONAL. -/

/-- **The strict spherical arm lemma — UNCONDITIONAL.**  Equal-sided strictly convex spherical arms
with nondecreasing joints and SOME joint strictly wider have a strictly longer endpoint chord.
Companion to the unconditional `≤` headline `spherical_arm_mono_final_ch13`. -/
theorem spherical_arm_mono_strict_uncond
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict_of_residue ProofsInTheBook.ZinanFFCT113.stuckWitnessExists_holds
    hn A B hA hB hside hangle hstrict

/-- **The genuine fixed-chord arm contradiction — UNCONDITIONAL.**  This is the honest, derived
replacement for `Chapter13.CauchyArmOpeningObstruction.arm_conclusion` (which posited it). -/
theorem cauchy_arm_fixed_chord_contradiction_uncond
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i)
    (hchord : sDist (A 0) (A (Fin.last n)) = sDist (B 0) (B (Fin.last n))) :
    False :=
  cauchy_arm_fixed_chord_contradiction ProofsInTheBook.ZinanFFCT113.stuckWitnessExists_holds
    hn A B hA hB hside hangle hstrict hchord

end ProofsInTheBook.ZinanFFCT112

#print axioms ProofsInTheBook.ZinanFFCT112.spherical_arm_mono_strict_uncond
#print axioms ProofsInTheBook.ZinanFFCT112.cauchy_arm_fixed_chord_contradiction_uncond
