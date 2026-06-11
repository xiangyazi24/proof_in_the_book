import ProofsInTheBook.ZinanFFCT74

/-!
# `ZinanFFCT75` -- corner audit for the FFCT74 surface

This layer records the verifiable reductions found when trying to remove the
three non-cross fields of `Ch13FinalSurface74`.

The requested `{hcross}`-only surface is not introduced here: the remaining
wrap-base and signed tail corner need a genuine cyclic boundary-propagation
argument not present in the current substrate.  The lemmas below are the
noncontroversial pieces of that audit, kept kernel-checked so the report can
refer to concrete facts rather than informal reconstruction.

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74

namespace ProofsInTheBook.ZinanFFCT75

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Signed tail corner: the immediate zero-support consequence. -/

/-- The `b > 0, a < 0, j = n` tail-corner span always puts the last vertex on the
supporting great circle of the edge `(i, i+1)`.  This is the easy part of the
tail residue; turning this boundary zero into an endpoint comparison is exactly
the missing cyclic-propagation step. -/
theorem bpos_aneg_tail_span_forces_zero {n : ℕ} {P : Fin (n + 1) → S2}
    {i : ℕ} (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨n, hn⟩ : E3)) :
    sOrient (P ⟨i, hi⟩) (P ⟨i + 1, hi1⟩) (P ⟨n, hn⟩) = 0 :=
  ProofsInTheBook.ZinanFFCT72.sOrient_zero_of_span_coeff hspan

/-! ## Wrap support: exact index shape. -/

/-- A raw weak-entry wrap seed has base index `n`. -/
theorem weak_wrap_base_is_last {n : ℕ} {a : Fin (n + 1)}
    (hwrap : ¬ a.val + 1 < n + 1) :
    a.val = n := by
  have ha := a.isLt
  omega

/-- On a wrap base, the Fin successor is the head vertex. -/
theorem weak_wrap_successor_is_zero {n : ℕ} {a : Fin (n + 1)}
    (hwrap : ¬ a.val + 1 < n + 1) :
    a + 1 = (0 : Fin (n + 1)) := by
  apply Fin.ext
  have ha : a.val = n := weak_wrap_base_is_last hwrap
  have hval : ((a + 1 : Fin (n + 1)) : ℕ) = (a.val + 1) % (n + 1) := by
    rw [Fin.add_def]
    simp
  rw [hval, ha, Nat.mod_self]
  simp

/-- The probed vertex of a genuine wrap seed is an interior vertex: neither `0`
nor `n`. -/
theorem weak_wrap_probe_interior {n : ℕ} {a b : Fin (n + 1)}
    (hne : b ≠ a) (hne1 : b ≠ a + 1)
    (hwrap : ¬ a.val + 1 < n + 1) :
    0 < b.val ∧ b.val < n := by
  have ha : a.val = n := weak_wrap_base_is_last hwrap
  have hsucc : a + 1 = (0 : Fin (n + 1)) := weak_wrap_successor_is_zero hwrap
  constructor
  · by_contra h0
    have hb0 : b.val = 0 := by omega
    apply hne1
    have hbFin : b = (0 : Fin (n + 1)) := Fin.ext hb0
    exact hbFin.trans hsucc.symm
  · have hbne : b.val ≠ n := by
      intro hb
      apply hne
      have hbFin : b = ⟨n, by omega⟩ := Fin.ext hb
      have haFin : a = ⟨n, by omega⟩ := Fin.ext ha
      exact hbFin.trans haFin.symm
    have hb := b.isLt
    omega

/-! ## Final surface status. -/

/-- The FFCT74 theorem remains the strongest kernel-checked final surface in this
branch: it still needs the three non-cross corner inputs. -/
theorem spherical_arm_mono_final_ch13_v8_reexport (res : Ch13FinalSurface74)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_final_ch13_v8 res hn A B hA hB hside hangle

#print axioms bpos_aneg_tail_span_forces_zero
#print axioms weak_wrap_base_is_last
#print axioms weak_wrap_probe_interior
#print axioms spherical_arm_mono_final_ch13_v8_reexport

end ProofsInTheBook.ZinanFFCT75
