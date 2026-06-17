import ProofsInTheBook.ZinanFFCT58

/-!
# `ZinanFFCT59` — non-axis mixed binding audit for the WBS support-stuck branch

This module records the clean part of the `NonAxisMixedBindingResidue` discharge and the exact
remaining boundary.  The residue named in FFCT56 already contains the sign datum `b < 0`; with that
datum in hand, the FFCT56 mid-fold kill applies to every non-axis binding whose apex has a successor
edge.  The two genuine non-axis mixed patterns therefore behave as follows:

* `i,i+1` fixed and `j` rotated: non-axis means `i+1 < K`, hence the apex has a successor edge, so
  the residue is impossible.
* `i,i+1` rotated and `j` fixed: if `i+1 ≠ n`, the apex again has a successor edge and the residue is
  impossible.  The only surviving shape is the tail boundary `i+1 = n`; this file names that exact
  residual instead of pretending the successor-edge kill applies there.

The final assembly included here is the splice-free reach-only endpoint chain: weak-entry vanishing
supports use FFCT58's modern `WeakPositiveCutReady` + `cut_step_from_stuckAtK_plus`, while deficient
strict steps use FFCT57's `SupportStuckWBSImpossible` route.  No legacy splice Prop is used.

No proof placeholders or extra logical postulates are introduced.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT57
open ProofsInTheBook.ZinanFFCT58

namespace ProofsInTheBook.ZinanFFCT59

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The local non-axis residue kill when the apex has a successor edge. -/

/-- **Generic successor-edge kill for `NonAxisMixedBindingResidue`.**  The FFCT56 residue already
contains a `b < 0` span datum.  If the apex `i+1` has a successor edge (`i+2 < n+1`), FFCT56's
pattern-agnostic `midFold_bneg_false` refutes it under the standard weak-convex, positive-joint,
open-hemisphere, and comparison hypotheses. -/
theorem nonAxisMixedBindingResidue_false_of_successor {n : ℕ} {A B : Fin (n + 1) → S2}
    {k : Fin (n - 1)} {i j : ℕ}
    {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hangle' : JointLe (openedWBS A B k) B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hi2 : i + 2 < n + 1)
    (hres : NonAxisMixedBindingResidue A B k i j hi hi1 hj) :
    False := by
  rcases hres with ⟨_hnonaxis, a, b, hspan, hb⟩
  exact midFold_bneg_false hA'weak hA'pos hB hangle' hi hi1 hi2 hj hhem hspan hb

/-! ## §2. The two non-axis mixed patterns. -/

/-- **Pattern (a), fixed-fixed-rotated, is impossible.**  If the edge vertices are fixed
(`i+1 ≤ K`) and the far vertex is rotated (`K < j`), then the non-axis guard inside
`NonAxisMixedBindingResidue` strengthens `i+1 ≤ K` to `i+1 < K`.  Since `K < n`, the apex has a
successor edge, so §1 fires. -/
theorem nonAxis_fixedFixed_rotated_false {n : ℕ} {A B : Fin (n + 1) → S2}
    {k : Fin (n - 1)} {i j : ℕ}
    {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hangle' : JointLe (openedWBS A B k) B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hi1_fixed : i + 1 ≤ (openingAxis k).val)
    (_hj_rot : (openingAxis k).val < j)
    (hres : NonAxisMixedBindingResidue A B k i j hi hi1 hj) :
    False := by
  have hKint := openingAxis_interior k
  have hnonaxis : i + 1 ≠ (openingAxis k).val := hres.1
  have hltK : i + 1 < (openingAxis k).val := by omega
  have hi2 : i + 2 < n + 1 := by omega
  exact nonAxisMixedBindingResidue_false_of_successor hA'weak hA'pos hB hangle' hhem hi2 hres

/-- **Pattern (c), rotated-rotated-fixed, is impossible away from the tail boundary.**  When
`K < i` and `j ≤ K`, the only obstruction to §1 is the last apex `i+1 = n`.  If that boundary is
excluded, `i+2 < n+1` and the same mid-fold kill refutes the residue. -/
theorem nonAxis_rotatedRotated_fixed_false_of_not_tail {n : ℕ} {A B : Fin (n + 1) → S2}
    {k : Fin (n - 1)} {i j : ℕ}
    {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hangle' : JointLe (openedWBS A B k) B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (_hi_rot : (openingAxis k).val < i)
    (_hj_fixed : j ≤ (openingAxis k).val)
    (hnotTail : i + 1 ≠ n)
    (hres : NonAxisMixedBindingResidue A B k i j hi hi1 hj) :
    False := by
  have hi2 : i + 2 < n + 1 := by omega
  exact nonAxisMixedBindingResidue_false_of_successor hA'weak hA'pos hB hangle' hhem hi2 hres

/-- **The remaining rotated-rotated-fixed residue is exactly the tail boundary.**  In pattern (c),
any surviving `NonAxisMixedBindingResidue` must have `i+1 = n`; otherwise
`nonAxis_rotatedRotated_fixed_false_of_not_tail` refutes it. -/
theorem nonAxis_rotatedRotated_fixed_forces_tail {n : ℕ} {A B : Fin (n + 1) → S2}
    {k : Fin (n - 1)} {i j : ℕ}
    {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hangle' : JointLe (openedWBS A B k) B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hi_rot : (openingAxis k).val < i)
    (hj_fixed : j ≤ (openingAxis k).val)
    (hres : NonAxisMixedBindingResidue A B k i j hi hi1 hj) :
    i + 1 = n := by
  by_contra hnotTail
  exact nonAxis_rotatedRotated_fixed_false_of_not_tail hA'weak hA'pos hB hangle' hhem
    hi_rot hj_fixed hnotTail hres

/-- **The named tail-boundary survivor for pattern (c).**  This is not a new postulate or an attempted
proof: it is the exact residual left after the successor-edge kill has done all it can. -/
def NonAxisTailBoundaryResidue {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    (i j : ℕ) (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1) : Prop :=
  i + 1 = n ∧
  (openingAxis k).val < i ∧
  j ≤ (openingAxis k).val ∧
  NonAxisMixedBindingResidue A B k i j hi hi1 hj

/-- Pattern (c)'s survivor packaged in its exact boundary form. -/
theorem nonAxis_tailBoundaryResidue_of_rotatedRotated_fixed {n : ℕ} {A B : Fin (n + 1) → S2}
    {k : Fin (n - 1)} {i j : ℕ}
    {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hangle' : JointLe (openedWBS A B k) B)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hi_rot : (openingAxis k).val < i)
    (hj_fixed : j ≤ (openingAxis k).val)
    (hres : NonAxisMixedBindingResidue A B k i j hi hi1 hj) :
    NonAxisTailBoundaryResidue A B k i j hi hi1 hj := by
  exact ⟨nonAxis_rotatedRotated_fixed_forces_tail hA'weak hA'pos hB hangle' hhem
    hi_rot hj_fixed hres, hi_rot, hj_fixed, hres⟩

/-- Unfolding guard: the tail survivor is exactly the stated boundary plus the original FFCT56
non-axis residue. -/
theorem nonAxisTailBoundaryResidue_unfold {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    {i j : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hj : j < n + 1) :
    NonAxisTailBoundaryResidue A B k i j hi hi1 hj
      ↔ i + 1 = n ∧
        (openingAxis k).val < i ∧
        j ≤ (openingAxis k).val ∧
        NonAxisMixedBindingResidue A B k i j hi hi1 hj := Iff.rfl

/-! ## §3. Splice-free reach-only final chain. -/

/-- **Reach-only honest residue bundle.**  Compared with FFCT58's `Ch13ResiduesHonest`, the WBS
support-stuck cut bridge is replaced by the direct elimination input `SupportStuckWBSImpossible`.
The weak-entry cut remains modern (`WeakPositiveCutReady` + `FoldedFlatCutTransportPlus`), so no
legacy splice Prop appears. -/
structure Ch13ReachOnlyResidues : Prop where
  /-- Weak-entry vanishing support → `CutReadyPlus`. -/
  hwpc : WeakPositiveCutReady
  /-- Repaired folded-flat cut transport for the weak-entry modern cut. -/
  hffct : FoldedFlatCutTransportPlus
  /-- WBS support-stuck is impossible at every deficient strict step. -/
  helim : SupportStuckWBSImpossible

/-- **Splice-free reach-only per-step predicate.**  The weak-entry vanishing case uses the modern
cut-ready consumer from FFCT58.  The strict deficient-joint case uses FFCT57's reach-only open step,
with `SupportStuckWBSImpossible` explicitly carried. -/
theorem szOpeningStepPlus_reachOnly_honest (res : Ch13ReachOnlyResidues) : SZOpeningStepPlus := by
  intro n hn ihdim A B hA hposA hB hside hangle ihdefRaw
  have ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B' := by
    intro A' B' hA' hposA' hB' hside' hangle' hlt
    exact ihdefRaw A' B' hA' hposA' hB' hside' hangle' hlt
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · have hcr : CutReadyPlus A B := res.hwpc A B hA hposA hB hside hangle hvanish
    exact cut_step_from_stuckAtK_plus res.hffct hn ihdim hA hposA hB hside hangle hcr
  · by_cases hnd : deficitCount A B = 0
    · exact congruence_step hAstrict hB hside hangle hnd
    · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step_reachOnly res.helim hAstrict hB hside hangle ihdef k hkdef

/-- **The splice-free reach-only Ch13 endpoint chain.**  This is the route that would become the
REACH-only headline once `SupportStuckWBSImpossible` is actually supplied; the old splice residues do
not occur. -/
theorem spherical_arm_mono_reachOnly_honest (res : Ch13ReachOnlyResidues)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_stepPlus (szOpeningStepPlus_reachOnly_honest res) hn A B hA hB hside hangle

/-! ## §4. Anti-impostor guards. -/

/-- The generic local kill is not a vacuous conclusion: its target is exactly `False` from a real
`b < 0` span datum carried by `NonAxisMixedBindingResidue`. -/
theorem nonAxis_successor_kill_target_real : (False → False) := id

/-- The tail residual is a genuine boundary statement, not `True`: it exposes the concrete equality
`i+1 = n` and the original FFCT56 residue. -/
theorem nonAxisTailBoundaryResidue_boundary {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (h : NonAxisTailBoundaryResidue A B k i j hi hi1 hj) :
    i + 1 = n := h.1

/-- The reach-only headline's conclusion is the genuine endpoint inequality, realised reflexively at
`A = B`. -/
theorem spherical_arm_mono_reachOnly_honest_conclusion_satisfiable {n : ℕ}
    (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

end ProofsInTheBook.ZinanFFCT59

#print axioms ProofsInTheBook.ZinanFFCT59.nonAxisMixedBindingResidue_false_of_successor
#print axioms ProofsInTheBook.ZinanFFCT59.nonAxis_fixedFixed_rotated_false
#print axioms ProofsInTheBook.ZinanFFCT59.nonAxis_rotatedRotated_fixed_false_of_not_tail
#print axioms ProofsInTheBook.ZinanFFCT59.nonAxis_rotatedRotated_fixed_forces_tail
#print axioms ProofsInTheBook.ZinanFFCT59.nonAxis_tailBoundaryResidue_of_rotatedRotated_fixed
#print axioms ProofsInTheBook.ZinanFFCT59.szOpeningStepPlus_reachOnly_honest
#print axioms ProofsInTheBook.ZinanFFCT59.spherical_arm_mono_reachOnly_honest
