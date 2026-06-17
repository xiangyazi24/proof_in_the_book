import ProofsInTheBook.ZinanFFCT89

/-!
# `ZinanFFCT90` -- face-run propagation interface for bounded simplicity

This file records the non-circular part of the final Chapter 13 no-repeat
route over the current library.

The requested unconditional theorem

```
WeakConvexSphArm P -> PositiveJoints P ->
  (forall i, jointAngle P i < pi) -> NoNonadjacentRepeat P
```

still needs the global face-run propagation step: an arbitrary nonadjacent
repeat must force a consecutive flat triple.  The library already contains the
digon base case (`ZinanFFCT88`) and the consecutive-flat contradiction
(`ZinanFFCT89`).  Here we add the checked first support-zero seed from a repeat
and package the remaining propagation as a single named `Prop`; supplying that
`Prop` closes the bounded simplicity theorem and the Chapter 13 headline.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT88
open ProofsInTheBook.ZinanFFCT89

namespace ProofsInTheBook.ZinanFFCT90

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## The support-zero seed forced by a repeat. -/

/-- If a repeated vertex `P r = P s` is followed by a non-wrapping edge
`(s,s+1)`, then the two weak supports of edges `(r,r+1)` and `(s,s+1)` force
the successor `P (s+1)` onto the support great circle of `(r,r+1)`.

This is the first determinant-zero seed of the face-run route. -/
theorem repeat_support_zero_next
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P)
    {r s : ℕ} (hr : r < n + 1) (hr1 : r + 1 < n + 1)
    (hs : s < n + 1) (hs1 : s + 1 < n + 1)
    (hrep : P ⟨r, hr⟩ = P ⟨s, hs⟩) :
    det3 (P ⟨r, hr⟩ : E3) (P ⟨r + 1, hr1⟩ : E3)
      (P ⟨s + 1, hs1⟩ : E3) = 0 := by
  have hsuccr :
      ((⟨r, hr⟩ : Fin (n + 1)) + 1) =
        (⟨r + 1, hr1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (by omega)]
  have hsuccs :
      ((⟨s, hs⟩ : Fin (n + 1)) + 1) =
        (⟨s + 1, hs1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (by omega)]
  have hsupp_r :
      0 ≤ det3 (P ⟨r, hr⟩ : E3) (P ⟨r + 1, hr1⟩ : E3)
        (P ⟨s + 1, hs1⟩ : E3) := by
    have h := hweak.closed_convex.edge_support
      (⟨r, hr⟩ : Fin (n + 1)) (⟨s + 1, hs1⟩ : Fin (n + 1))
    simpa [sOrient, hsuccr] using h
  have hsupp_s :
      0 ≤ det3 (P ⟨s, hs⟩ : E3) (P ⟨s + 1, hs1⟩ : E3)
        (P ⟨r + 1, hr1⟩ : E3) := by
    have h := hweak.closed_convex.edge_support
      (⟨s, hs⟩ : Fin (n + 1)) (⟨r + 1, hr1⟩ : Fin (n + 1))
    simpa [sOrient, hsuccs] using h
  rw [← hrep] at hsupp_s
  have hswap :
      det3 (P ⟨r, hr⟩ : E3) (P ⟨s + 1, hs1⟩ : E3)
          (P ⟨r + 1, hr1⟩ : E3)
        =
      - det3 (P ⟨r, hr⟩ : E3) (P ⟨r + 1, hr1⟩ : E3)
          (P ⟨s + 1, hs1⟩ : E3) := by
    simp only [det3]
    ring
  rw [hswap] at hsupp_s
  linarith

/-- The wrapping variant of `repeat_support_zero_next`: if `P r = P n`, then
the closing edge `(n,0)` supplies the opposite support and forces `P 0` onto
the support great circle of `(r,r+1)`. -/
theorem repeat_support_zero_wrap
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P)
    {r : ℕ} (hr : r < n + 1) (hr1 : r + 1 < n + 1)
    (hrep : P ⟨r, hr⟩ = P (Fin.last n)) :
    det3 (P ⟨r, hr⟩ : E3) (P ⟨r + 1, hr1⟩ : E3) (P 0 : E3) = 0 := by
  have hsuccr :
      ((⟨r, hr⟩ : Fin (n + 1)) + 1) =
        (⟨r + 1, hr1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (by omega)]
  have hsuccn : (Fin.last n + 1 : Fin (n + 1)) = 0 := by
    apply Fin.ext
    simp
  have hsupp_r :
      0 ≤ det3 (P ⟨r, hr⟩ : E3) (P ⟨r + 1, hr1⟩ : E3) (P 0 : E3) := by
    have h := hweak.closed_convex.edge_support
      (⟨r, hr⟩ : Fin (n + 1)) (0 : Fin (n + 1))
    simpa [sOrient, hsuccr] using h
  have hsupp_n :
      0 ≤ det3 (P (Fin.last n) : E3) (P 0 : E3)
        (P ⟨r + 1, hr1⟩ : E3) := by
    have h := hweak.closed_convex.edge_support
      (Fin.last n : Fin (n + 1)) (⟨r + 1, hr1⟩ : Fin (n + 1))
    simpa [sOrient, hsuccn] using h
  rw [← hrep] at hsupp_n
  have hswap :
      det3 (P ⟨r, hr⟩ : E3) (P 0 : E3) (P ⟨r + 1, hr1⟩ : E3)
        =
      - det3 (P ⟨r, hr⟩ : E3) (P ⟨r + 1, hr1⟩ : E3) (P 0 : E3) := by
    simp only [det3]
    ring
  rw [hswap] at hsupp_n
  linarith

/-! ## The exact remaining propagation surface. -/

/-- The remaining face-run propagation needed for bounded weak-positive
simplicity.

For every repeated nonadjacent pair beyond the digon case (`r+3 ≤ s`), the
closed face-run must contain a consecutive flat triple.  FFCT88 handles the
digon case; FFCT89 consumes the consecutive flat triple. -/
def BoundedFaceRunPropagation : Prop :=
  ∀ {n : ℕ} {P : Fin (n + 1) → S2},
    WeakConvexSphArm P →
    PositiveJoints P →
    (∀ i : Fin (n - 1), jointAngle P i < Real.pi) →
    ∀ {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1),
      r + 3 ≤ s →
      P ⟨r, hr⟩ = P ⟨s, hs⟩ →
        ∃ t : ℕ, ∃ ht2 : t + 2 < n + 1,
          det3 (P ⟨t, by omega⟩ : E3)
            (P ⟨t + 1, by omega⟩ : E3)
            (P ⟨t + 2, by omega⟩ : E3) = 0

/-- The bounded no-repeat theorem follows immediately once the face-run
propagation surface is supplied. -/
theorem weakConvex_boundedJoints_noNonadjacentRepeat_of_faceRunPropagation
    (hprop : BoundedFaceRunPropagation)
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hlt : ∀ i : Fin (n - 1), jointAngle P i < Real.pi) :
    NoNonadjacentRepeat P := by
  intro r s hr hs hrs hrep
  by_cases hgap2 : r + 2 = s
  · exact (weakConvex_positiveJoints_noNonadjacentRepeat_gap_two
      hweak hpos hr hs hgap2) hrep
  · have hgap3 : r + 3 ≤ s := by omega
    obtain ⟨t, ht2, hdet⟩ := hprop hweak hpos hlt hr hs hgap3 hrep
    exact False.elim
      (weakConvex_boundedJoints_no_consecutive_det3_zero
        hweak hpos hlt ht2 hdet)

/-- The FFCT89 bounded-simplicity residue is exactly supplied by the
face-run propagation surface. -/
theorem boundedWeakPositiveSimplicity_of_faceRunPropagation
    (hprop : BoundedFaceRunPropagation) :
    BoundedWeakPositiveSimplicity := by
  intro n P hweak hpos hlt
  exact weakConvex_boundedJoints_noNonadjacentRepeat_of_faceRunPropagation
    hprop hweak hpos hlt

/-! ## Conditional Chapter 13 composition. -/

/-- The collision endpoint branch closes once face-run propagation is supplied. -/
theorem crossPieceCollisionEndpointAtSup_of_faceRunPropagation
    (hprop : BoundedFaceRunPropagation) :
    CrossPieceCollisionEndpointAtSup :=
  crossPieceCollisionEndpointAtSup_of_boundedWeakPositiveSimplicity
    (boundedWeakPositiveSimplicity_of_faceRunPropagation hprop)

/-- Conditional Chapter 13 headline from the single remaining face-run
propagation surface. -/
theorem spherical_arm_mono_ch13_of_faceRunPropagation
    (hprop : BoundedFaceRunPropagation) :
    SphericalArmMonotone :=
  spherical_arm_mono_ch13_of_boundedWeakPositiveSimplicity
    (boundedWeakPositiveSimplicity_of_faceRunPropagation hprop)

/-! ## Guards. -/

#print axioms repeat_support_zero_next
#print axioms repeat_support_zero_wrap
#print axioms weakConvex_boundedJoints_noNonadjacentRepeat_of_faceRunPropagation
#print axioms boundedWeakPositiveSimplicity_of_faceRunPropagation
#print axioms crossPieceCollisionEndpointAtSup_of_faceRunPropagation
#print axioms spherical_arm_mono_ch13_of_faceRunPropagation

end ProofsInTheBook.ZinanFFCT90
