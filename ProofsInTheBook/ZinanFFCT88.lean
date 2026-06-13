import ProofsInTheBook.ZinanFFCT87

/-!
# `ZinanFFCT88` -- the simplicity residue isolated

This file records the part of the requested Chapter 13 simplicity route that
is available in the landed library without adding any unsafe assumptions.

The full target

```
WeakConvexSphArm P -> PositiveJoints P -> NoNonadjacentRepeat P
```

is left as the explicit residue `WeakPositiveSimplicity`: the current formal
`PositiveJoints` predicate supplies only `0 < jointAngle`, while the existing
flat-joint contradiction lemmas need the additional non-flat upper bound
`jointAngle < pi` to rule out the `pi` branch.  The digon base case does close
from positivity alone, and the final Ch13 headline closes immediately from the
remaining residue.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT17
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT87

namespace ProofsInTheBook.ZinanFFCT88

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## The base case of the simplicity route. -/

/-- A weakly convex arm with positive interior joints cannot have the digon
repeat `P r = P (r+2)`.  The repeated endpoints make the joint at `r+1`
literally `0`, contradicting `PositiveJoints`.

This is the base case named in the handoff. -/
theorem weakConvex_positiveJoints_no_gap_two_repeat
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P)
    {r : ℕ} (hr2 : r + 2 < n + 1) :
    P ⟨r, by omega⟩ ≠ P ⟨r + 2, hr2⟩ := by
  intro hrep
  have hjoint_pos : 0 < jointAngle P ⟨r, by omega⟩ := hpos ⟨r, by omega⟩
  have hedge : ShortArc (P ⟨r, by omega⟩) (P ⟨r + 1, by omega⟩) := by
    have h := hweak.closed_convex.edge_short ⟨r, by omega⟩
    have hsucc :
        ((⟨r, by omega⟩ : Fin (n + 1)) + 1) =
          (⟨r + 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (by omega)]
    rwa [hsucc] at h
  have hangle_zero : jointAngle P ⟨r, by omega⟩ = 0 := by
    rw [jointAngle]
    rw [← hrep]
    exact sphAngle_self_zero hedge.symm
  rw [hangle_zero] at hjoint_pos
  exact lt_irrefl 0 hjoint_pos

/-- Nat-indexed restatement of the digon base case in the `NoNonadjacentRepeat`
calling convention. -/
theorem weakConvex_positiveJoints_noNonadjacentRepeat_gap_two
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P)
    {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1)
    (hrs : r + 2 = s) :
    P ⟨r, hr⟩ ≠ P ⟨s, hs⟩ := by
  subst s
  exact weakConvex_positiveJoints_no_gap_two_repeat hweak hpos hs

/-! ## The exact remaining residue and its Ch13 consequence. -/

/-- The full weak-positive simplicity theorem requested by the handoff, kept as
the precise remaining residue rather than introduced as an unsafe assumption. -/
def WeakPositiveSimplicity : Prop :=
  ∀ {n : ℕ} {P : Fin (n + 1) → S2},
    WeakConvexSphArm P → PositiveJoints P → NoNonadjacentRepeat P

/-- The opened WBS arm has no nonadjacent repeats once the remaining
weak-positive simplicity residue is supplied. -/
theorem openedWBS_noNonadjacentRepeat_of_weakPositiveSimplicity
    (hsimp : WeakPositiveSimplicity)
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (_hside : SameSides A B) (_hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k)
    (_hstuck : SupportStuckWBS A B k) :
    NoNonadjacentRepeat (openedWBS A B k) := by
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hwrapArc :
      ShortArc (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0) :=
    openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
  have hPweak : WeakConvexSphArm (openedWBS A B k) := by
    unfold openedWBS
    exact supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrapArc
  have hPpos : PositiveJoints (openedWBS A B k) := by
    intro r
    unfold openedWBS
    exact (openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef r).1
  exact hsimp hPweak hPpos

/-- The collision endpoint residue is vacuous once weak-positive simplicity is
available for the opened WBS arm. -/
theorem crossPieceCollisionEndpointAtSup_of_weakPositiveSimplicity
    (hsimp : WeakPositiveSimplicity) :
    CrossPieceCollisionEndpointAtSup := by
  intro n A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs hcoll
  have hnr : NoNonadjacentRepeat (openedWBS A B k) :=
    openedWBS_noNonadjacentRepeat_of_weakPositiveSimplicity hsimp A B
      hA hB hside hangle k hkdef hstuck
  exact False.elim (hnr r s hr hs hrs hcoll)

/-- Conditional Chapter 13 headline from the exact remaining simplicity
residue.  This is the requested final composition with the residue kept honest. -/
theorem spherical_arm_mono_ch13_of_weakPositiveSimplicity
    (hsimp : WeakPositiveSimplicity) :
    SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v11
    (crossPieceCollisionEndpointAtSup_of_weakPositiveSimplicity hsimp)

/-! ## Guards. -/

#print axioms weakConvex_positiveJoints_no_gap_two_repeat
#print axioms weakConvex_positiveJoints_noNonadjacentRepeat_gap_two
#print axioms openedWBS_noNonadjacentRepeat_of_weakPositiveSimplicity
#print axioms crossPieceCollisionEndpointAtSup_of_weakPositiveSimplicity
#print axioms spherical_arm_mono_ch13_of_weakPositiveSimplicity

end ProofsInTheBook.ZinanFFCT88
