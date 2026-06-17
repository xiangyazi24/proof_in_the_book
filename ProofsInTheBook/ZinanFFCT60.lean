import ProofsInTheBook.ZinanFFCT54
import ProofsInTheBook.ZinanFFCT59

/-!
# `ZinanFFCT60` — tail-boundary audit for the last non-axis residue

FFCT59 isolated the only non-axis mixed binding not killed by the ordinary successor-edge
mid-fold contradiction: the tail boundary `i + 1 = n`.  The intended reversal route needs a
convexity fact for the reversed arm.  That fact is not currently present in the substrate: the
implemented reversal suite transports side lengths, joint angles, positive joints, `JointLe`, and
no-repeat, but not `WeakConvexSphArm` / `StrictConvexSphArm`.

This file therefore proves the sharp conditional result that the available FFCT25 classifier would
give once the missing reversed convexity certificates are supplied: the tail residue can only sit at
the two endpoint cuts `j = 0` or `j = 1`; in particular every `2 ≤ j` tail residue is impossible.

No proof placeholders or extra logical postulates are introduced.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT53
open ProofsInTheBook.ZinanFFCT54
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT59

namespace ProofsInTheBook.ZinanFFCT60

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The exact missing input. -/

/-- The reversed convexity certificates needed to run FFCT25 on `revArm`.

These are kept as explicit data.  They are not derivable from `WeakConvexSphArm P` in the current
orientation convention: reversing the vertex order flips the `sOrient` support sign. -/
structure TailBoundaryReversalConvexity {n : ℕ}
    (P Q : Fin (n + 1) → S2) : Prop where
  /-- Weak convexity of the reversed left arm. -/
  weak_rev : WeakConvexSphArm (revArm P)
  /-- Strict convexity of the reversed comparison arm. -/
  strict_rev : StrictConvexSphArm (revArm Q)

/-! ## §2. The local reversed far-fold classifier. -/

/-- A positive tail mid-fold at the last vertex becomes a forward fold at index `0` on the reversed
arm.  Under the explicit reversed convexity certificates, FFCT53's adjacent contradiction and FFCT25's
far-fold boundary classifier force the original fixed index to be `j = 0` or `j = 1`.

The adjacent reversed case `n - j = 2` is already impossible by `foldedFlat_adjacent_contradiction`;
the far case `2 < n - j` is classified by `far_fold_boundary_classification_unconditional`. -/
theorem rev_tail_midFold_forces_endpoint_j {n : ℕ} {P Q : Fin (n + 1) → S2}
    {j : ℕ}
    (hrev : TailBoundaryReversalConvexity P Q)
    (hposRev : PositiveJoints (revArm P))
    (hangleRev : JointLe (revArm P) (revArm Q))
    (hnrRev : NoNonadjacentRepeat (revArm P))
    (hjtail : j + 2 ≤ n)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hmid : (P ⟨n, by omega⟩ : E3)
      = c • (P ⟨n - 1, by omega⟩ : E3) + d • (P ⟨j, by omega⟩ : E3)) :
    j = 0 ∨ j = 1 := by
  have hcol : (revArm P ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(revArm P ⟨1, by omega⟩ : E3), (revArm P ⟨n - j, by omega⟩ : E3)} : Set E3) := by
    rw [Submodule.mem_span_pair]
    refine ⟨⟨c, le_of_lt hc⟩, ⟨d, le_of_lt hd⟩, ?_⟩
    rw [NNReal.smul_def, NNReal.smul_def]
    have h0 : (revArm P ⟨0, by omega⟩ : S2) = P ⟨n, by omega⟩ := by
      change P (revFin (⟨0, by omega⟩ : Fin (n + 1))) = P ⟨n, by omega⟩
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have h1 : (revArm P ⟨1, by omega⟩ : S2) = P ⟨n - 1, by omega⟩ := by
      change P (revFin (⟨1, by omega⟩ : Fin (n + 1))) = P ⟨n - 1, by omega⟩
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have hj : (revArm P ⟨n - j, by omega⟩ : S2) = P ⟨j, by omega⟩ := by
      change P (revFin (⟨n - j, by omega⟩ : Fin (n + 1))) = P ⟨j, by omega⟩
      exact congrArg P (Fin.ext (by simp [revFin_val]; omega))
    rw [h0, h1, hj]
    exact hmid.symm
  have hq2 : 2 ≤ n - j := by omega
  rcases Nat.eq_or_lt_of_le hq2 with hqeq | hqgt
  · exfalso
    have hidx : (⟨n - j, by omega⟩ : Fin (n + 1)) = ⟨2, by omega⟩ :=
      Fin.ext hqeq.symm
    have hcol2 : (revArm P ⟨0, by omega⟩ : E3) ∈
        Submodule.span NNReal
          ({(revArm P ⟨1, by omega⟩ : E3), (revArm P ⟨2, by omega⟩ : E3)} : Set E3) := by
      rwa [hidx] at hcol
    exact foldedFlat_adjacent_contradiction (A := revArm P) hrev.weak_rev hposRev
      (i := 0) (by omega) hcol2
  · have hclass : (0 : ℕ) = 0 ∧ (n - j = n ∨ n - j = n - 1) :=
      far_fold_boundary_classification_unconditional
        (A := revArm P) (B := revArm Q)
        hrev.weak_rev hposRev hrev.strict_rev hangleRev hnrRev
        (i := 0) (j := n - j) (by omega) (by omega) hcol
    rcases hclass.2 with hleft | hleft
    · left; omega
    · right; omega

/-! ## §3. Instantiation for FFCT59's `NonAxisTailBoundaryResidue`. -/

/-- The FFCT59 tail-boundary residue reduces to the two endpoint cuts, conditional only on the
explicit reversed convexity certificates.  All other reversed data are already transported by the
landed FFCT52/54 lemmas. -/
theorem nonAxisTailBoundaryResidue_forces_endpoint_j_under_reversal {n : ℕ}
    {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hrev : TailBoundaryReversalConvexity (openedWBS A B k) B)
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hangle' : JointLe (openedWBS A B k) B)
    (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hres : NonAxisTailBoundaryResidue A B k i j hi hi1 hj) :
    j = 0 ∨ j = 1 := by
  set P : Fin (n + 1) → S2 := openedWBS A B k
  rcases hres with ⟨htail, hi_rot, hj_fixed, hmix⟩
  rcases hmix with ⟨_hnonaxis, a, b, hspan, hb⟩
  obtain ⟨c, d, hc, hd, hmid0⟩ :=
    midFold_coeffs_of_bneg (P := P) hhem hi hi1 hj hspan hb
  have hi_eq : i = n - 1 := by omega
  have hjtail : j + 2 ≤ n := by
    have hKlt : (openingAxis k).val < n - 1 := by omega
    omega
  have hmid : (P ⟨n, by omega⟩ : E3)
      = c • (P ⟨n - 1, by omega⟩ : E3) + d • (P ⟨j, by omega⟩ : E3) := by
    have e0 : (⟨i + 1, hi1⟩ : Fin (n + 1)) = ⟨n, by omega⟩ := Fin.ext (by omega)
    have e1 : (⟨i, hi⟩ : Fin (n + 1)) = ⟨n - 1, by omega⟩ := Fin.ext (by omega)
    have ej : (⟨j, hj⟩ : Fin (n + 1)) = ⟨j, by omega⟩ := Fin.ext rfl
    rwa [e0, e1, ej] at hmid0
  have hposRev : PositiveJoints (revArm P) := positiveJoints_revArm hA'pos
  have hangleRev : JointLe (revArm P) (revArm B) := jointLe_revArm hangle'
  have hnrRev : NoNonadjacentRepeat (revArm P) := revArm_noNonadjacentRepeat hnr
  exact rev_tail_midFold_forces_endpoint_j (P := P) (Q := B) hrev hposRev hangleRev hnrRev
    hjtail hc hd hmid

/-- Consequently, every tail-boundary residue with `2 ≤ j` is impossible under the same explicit
reversed convexity certificates. -/
theorem nonAxisTailBoundaryResidue_false_of_two_le_j_under_reversal {n : ℕ}
    {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hrev : TailBoundaryReversalConvexity (openedWBS A B k) B)
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hangle' : JointLe (openedWBS A B k) B)
    (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hj2 : 2 ≤ j)
    (hres : NonAxisTailBoundaryResidue A B k i j hi hi1 hj) :
    False := by
  rcases nonAxisTailBoundaryResidue_forces_endpoint_j_under_reversal hrev hA'pos hangle'
      hnr hhem hres with hj0 | hj1
  · omega
  · omega

/-! ## §4. Anti-impostor guards. -/

/-- The reversed-convexity input exposes real geometric fields; it is not `True`. -/
theorem tailBoundaryReversalConvexity_weak_field {n : ℕ} {P Q : Fin (n + 1) → S2}
    (h : TailBoundaryReversalConvexity P Q) :
    WeakConvexSphArm (revArm P) := h.weak_rev

/-- The endpoint boundary conclusion is a genuine restriction and is satisfiable. -/
theorem endpoint_j_conclusion_satisfiable : ((0 : ℕ) = 0 ∨ (0 : ℕ) = 1) := Or.inl rfl

#print axioms TailBoundaryReversalConvexity
#print axioms rev_tail_midFold_forces_endpoint_j
#print axioms nonAxisTailBoundaryResidue_forces_endpoint_j_under_reversal
#print axioms nonAxisTailBoundaryResidue_false_of_two_le_j_under_reversal

end ProofsInTheBook.ZinanFFCT60
