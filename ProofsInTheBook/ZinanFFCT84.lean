import ProofsInTheBook.ZinanFFCT83

/-!
# `ZinanFFCT84` -- signed-tail stall as normalized progress

This layer closes the live `b > 0, a < 0, j = n` tail-corner residue without
the missing cone re-extraction semantic.  The first backward edge `(n-1,n)`
already forces the predecessor into the span of the two tail anchors; in the
non-adjacent case this is exactly a no-tail normalized support zero with far
probe `n-1`.  The adjacent case is the checked FFCT83 consecutive-cone
contradiction.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83

namespace ProofsInTheBook.ZinanFFCT84

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## First-step tail progress. -/

/-- In the non-adjacent signed-tail cone, the first backward edge `(n-1,n)`
forces a no-tail normalized support zero on the original edge `(i,i+1)` with
far probe `n-1`. -/
theorem normalizedStrictInteriorSupportZero_of_tail_firstStep
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P)
    {i : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1)
    (hnonadj : i + 2 < n)
    (hcone : OpenCone (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨n, hn⟩)) :
    NormalizedStrictInteriorSupportZero P := by
  have hprev : n - 1 < n + 1 := by omega
  have hsucc :
      (⟨n - 1, hprev⟩ + 1 : Fin (n + 1)) = ⟨n, hn⟩ := by
    apply Fin.ext
    rw [Fin.val_add, Fin.val_mk]
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [hone, Nat.mod_eq_of_lt (show n - 1 + 1 < n + 1 by omega)]
    change n - 1 + 1 = n
    omega
  have hYP :
      0 ≤ sOrient (P ⟨n - 1, hprev⟩) (P ⟨n, hn⟩) (P ⟨i, hi⟩) := by
    have h := hP.closed_convex.edge_support ⟨n - 1, hprev⟩ ⟨i, hi⟩
    simpa [hsucc] using h
  have hYQ :
      0 ≤ sOrient (P ⟨n - 1, hprev⟩) (P ⟨n, hn⟩) (P ⟨i + 1, hi1⟩) := by
    have h := hP.closed_convex.edge_support ⟨n - 1, hprev⟩ ⟨i + 1, hi1⟩
    simpa [hsucc] using h
  have hplane :
      sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨n - 1, hprev⟩) = 0 :=
    edgeAnchor_prev_plane_of_next_openCone hcone hYP hYQ
  refine ⟨i, n - 1, hi, hi1, hprev, ?_, ?_, hplane⟩ <;> omega

/-- The live signed-tail residue closes directly: the adjacent tail is
impossible, and every non-adjacent tail yields a no-tail normalized support
zero consumed by FFCT81's stratified endpoint dispatcher. -/
theorem bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero :
    BPosANegTailCornerResidueV9 := by
  intro n P B hP hpos hB hside hangle hnr hhem ihdim i hitail hi hi1 hn a b hspan hb ha
  by_cases hnonadj : i + 2 < n
  · have hcone : OpenCone (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨n, hn⟩) :=
      openCone_tail_of_aneg_bpos hi hi1 hn hspan hb ha
    have hnorm : NormalizedStrictInteriorSupportZero P :=
      normalizedStrictInteriorSupportZero_of_tail_firstStep hP hi hi1 hn hnonadj hcone
    exact endpoint_of_normalizedInteriorZero_noTail hP hpos hnr hB
      hside hangle hhem ihdim hnorm
  · have htight : i + 2 = n := by omega
    exact False.elim
      (bpos_aneg_tail_adjacent_forbidden hP hpos hB hangle hi hi1 hn
        htight hspan hb ha)

/-! ## Final wrapper with the remaining wrap-propagation input. -/

/-- After the signed-tail residue is closed, a general wrap propagation theorem
is the only remaining non-cross boundary input needed by the checked v10
assembly. -/
theorem spherical_arm_mono_final_ch13_v10_of_hcross_wrapGeneral_ffct84
    (hcross : CrossPieceNoCollisionAtSup)
    (hwrap : WrapPlanePropagationGeneral) :
    SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v10_of_hcross_wrap_and_tail hcross hwrap
    bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero

/-! ## Guards. -/

#print axioms normalizedStrictInteriorSupportZero_of_tail_firstStep
#print axioms bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero
#print axioms spherical_arm_mono_final_ch13_v10_of_hcross_wrapGeneral_ffct84

end ProofsInTheBook.ZinanFFCT84
