import ProofsInTheBook.ZinanFFCT88

/-!
# `ZinanFFCT89` -- bounded-joint simplicity interface

This file lands the parts of the bounded-joint Chapter 13 route that are
available from the current library without adding an unsafe assumption:

* a direct bounded-joint flat-consecutive-triple contradiction;
* the WBS opened arm's upper joint bound `jointAngle < pi`;
* the collision/headline composition from the exact bounded simplicity
  statement, kept as an explicit residue.

The global theorem

```
WeakConvexSphArm P -> PositiveJoints P ->
  (forall i, jointAngle P i < pi) -> NoNonadjacentRepeat P
```

still needs the face-run propagation from an arbitrary nonadjacent repeat to a
consecutive vanishing determinant.  The current landed library contains the
local flat-joint kill and WBS joint bounds, but not that global propagation.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT88

namespace ProofsInTheBook.ZinanFFCT89

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## Local bounded-joint flat-triple contradiction. -/

/-- A consecutive vanishing determinant at an interior vertex is incompatible
with weak convexity, positive joints, and the direct upper bound
`jointAngle < pi`.

This is the local contradiction used at the end of the bounded simplicity
route: `sphAngle_eq_zero_or_pi_of_det3_zero` gives `0` or `pi`; positivity
kills the `0` branch and `hlt` kills the `pi` branch. -/
theorem weakConvex_boundedJoints_no_consecutive_det3_zero
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hlt : ∀ i : Fin (n - 1), jointAngle P i < Real.pi)
    {r : ℕ} (hr2 : r + 2 < n + 1)
    (hdet :
      det3 (P ⟨r, by omega⟩ : E3)
        (P ⟨r + 1, by omega⟩ : E3)
        (P ⟨r + 2, hr2⟩ : E3) = 0) :
    False := by
  have hsau : ShortArc (P ⟨r + 1, by omega⟩) (P ⟨r, by omega⟩) := by
    have hedge := hweak.closed_convex.edge_short ⟨r, by omega⟩
    have hsucc :
        ((⟨r, by omega⟩ : Fin (n + 1)) + 1) =
          (⟨r + 1, by omega⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (by omega)]
    have hforward : ShortArc (P ⟨r, by omega⟩) (P ⟨r + 1, by omega⟩) := by
      simpa [hsucc] using hedge
    exact hforward.symm
  have hsav : ShortArc (P ⟨r + 1, by omega⟩) (P ⟨r + 2, hr2⟩) := by
    have hedge := hweak.closed_convex.edge_short ⟨r + 1, by omega⟩
    have hsucc :
        ((⟨r + 1, by omega⟩ : Fin (n + 1)) + 1) =
          (⟨r + 2, hr2⟩ : Fin (n + 1)) := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (by omega)]
    simpa [hsucc] using hedge
  have hbridge := sphAngle_eq_zero_or_pi_of_det3_zero
    (u := P ⟨r, by omega⟩) (v := P ⟨r + 1, by omega⟩)
    (w := P ⟨r + 2, hr2⟩) hsau hsav hdet
  have hposJoint : 0 < jointAngle P ⟨r, by omega⟩ :=
    hpos ⟨r, by omega⟩
  have hltJoint : jointAngle P ⟨r, by omega⟩ < Real.pi :=
    hlt ⟨r, by omega⟩
  have hjoint_eq : jointAngle P ⟨r, by omega⟩ =
      sphAngle (P ⟨r, by omega⟩) (P ⟨r + 1, by omega⟩) (P ⟨r + 2, hr2⟩) := by
    rw [jointAngle]
  rcases hbridge with hzero | hpi
  · rw [hjoint_eq, hzero] at hposJoint
    exact lt_irrefl 0 hposJoint
  · rw [hjoint_eq, hpi] at hltJoint
    exact lt_irrefl Real.pi hltJoint

/-! ## The exact bounded simplicity residue. -/

/-- The bounded weak-positive simplicity theorem still needed for the
unconditional collision branch.  This is a `Prop`, not an assumed theorem. -/
def BoundedWeakPositiveSimplicity : Prop :=
  ∀ {n : ℕ} {P : Fin (n + 1) → S2},
    WeakConvexSphArm P →
    PositiveJoints P →
    (∀ i : Fin (n - 1), jointAngle P i < Real.pi) →
      NoNonadjacentRepeat P

/-! ## WBS opened arm joint upper bounds. -/

/-- At a WBS support-stuck supremum, the opened arm's joints are bounded above
by the corresponding joints of the strict comparison arm. -/
theorem openedWBS_jointLe_at_sup
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    (hA : StrictConvexSphArm A) (_hB : StrictConvexSphArm B)
    (hangle : JointLe A B) (hkdef : jointAngle A k < jointAngle B k) :
    JointLe (openedWBS A B k) B := by
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hjointk : jointAngle (openedWBS A B k) k =
      openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) := by
    unfold openedWBS
    exact jointAngle_openTail_eq_openedInterior A k (-(monitoredSupWBS A B k))
  have hslack : openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) ≤ jointAngle B k :=
    openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
  intro r
  by_cases hrk : r = k
  · rw [hrk, hjointk]
    exact hslack
  · unfold openedWBS
    rw [jointAngle_openTail_eq_of_ne A k (-(monitoredSupWBS A B k)) hrk]
    exact hangle r

/-- The opened WBS arm has all interior joints strictly below `pi`.

The proof is just `JointLe (openedWBS A B k) B` plus strict convexity of `B`.
The support-stuck hypothesis is included to match the Chapter 13 call site;
the strict upper bound itself only uses the supremum joint slack. -/
theorem openedWBS_jointAngle_lt_pi
    {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    (_hstuck : SupportStuckWBS A B k)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hangle : JointLe A B) (hkdef : jointAngle A k < jointAngle B k) :
    ∀ i : Fin (n - 1), jointAngle (openedWBS A B k) i < Real.pi := by
  intro i
  exact lt_of_le_of_lt
    (openedWBS_jointLe_at_sup A B k hA hB hangle hkdef i)
    (strict_jointAngle_lt_pi hB i)

/-! ## Conditional collision/headline composition from bounded simplicity. -/

/-- The opened WBS arm has no nonadjacent repeats once the bounded simplicity
residue is supplied. -/
theorem openedWBS_noNonadjacentRepeat_of_boundedWeakPositiveSimplicity
    (hsimp : BoundedWeakPositiveSimplicity)
    {n : ℕ} (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k) :
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
  have hPlt : ∀ i : Fin (n - 1), jointAngle (openedWBS A B k) i < Real.pi :=
    openedWBS_jointAngle_lt_pi A B k hstuck hA hB hangle hkdef
  exact hsimp hPweak hPpos hPlt

/-- The collision endpoint residue follows from the bounded weak-positive
simplicity theorem. -/
theorem crossPieceCollisionEndpointAtSup_of_boundedWeakPositiveSimplicity
    (hsimp : BoundedWeakPositiveSimplicity) :
    CrossPieceCollisionEndpointAtSup := by
  intro n A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs hcoll
  have hnr : NoNonadjacentRepeat (openedWBS A B k) :=
    openedWBS_noNonadjacentRepeat_of_boundedWeakPositiveSimplicity hsimp
      A B hA hB hangle k hkdef hstuck
  exact False.elim (hnr r s hr hs hrs hcoll)

/-- Conditional Chapter 13 headline from the exact bounded simplicity residue. -/
theorem spherical_arm_mono_ch13_of_boundedWeakPositiveSimplicity
    (hsimp : BoundedWeakPositiveSimplicity) :
    SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v11
    (crossPieceCollisionEndpointAtSup_of_boundedWeakPositiveSimplicity hsimp)

/-! ## Guards. -/

#print axioms weakConvex_boundedJoints_no_consecutive_det3_zero
#print axioms openedWBS_jointLe_at_sup
#print axioms openedWBS_jointAngle_lt_pi
#print axioms openedWBS_noNonadjacentRepeat_of_boundedWeakPositiveSimplicity
#print axioms crossPieceCollisionEndpointAtSup_of_boundedWeakPositiveSimplicity
#print axioms spherical_arm_mono_ch13_of_boundedWeakPositiveSimplicity

end ProofsInTheBook.ZinanFFCT89
