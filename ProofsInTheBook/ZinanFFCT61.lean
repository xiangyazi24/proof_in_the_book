import ProofsInTheBook.ZinanFFCT60
import ProofsInTheBook.SphericalRotation

/-!
# `ZinanFFCT61` — mirror reversal for the tail-boundary residue

This file adds the orientation-reversing reflection missing from the raw `revArm` route.  Reversal
alone flips spherical supports; composing it with one ambient coordinate reflection flips the sign
back while preserving all metric data.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.ZinanFFCT12
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
open ProofsInTheBook.ZinanFFCT60

namespace ProofsInTheBook.ZinanFFCT61

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The coordinate reflection. -/

/-- Reflection in the `z = 0` coordinate plane: `(x,y,z) ↦ (x,y,-z)`. -/
def reflectZ (v : E3) : E3 := !₂[v 0, v 1, -v 2]

@[simp] theorem reflectZ_apply_zero (v : E3) : reflectZ v 0 = v 0 := rfl
@[simp] theorem reflectZ_apply_one (v : E3) : reflectZ v 1 = v 1 := rfl
@[simp] theorem reflectZ_apply_two (v : E3) : reflectZ v 2 = -v 2 := rfl

theorem reflectZ_involutive (v : E3) : reflectZ (reflectZ v) = v := by
  apply ext_coord <;> simp [reflectZ]

theorem reflectZ_injective : Function.Injective reflectZ := by
  intro x y h
  have h' := congrArg reflectZ h
  simpa [reflectZ_involutive] using h'

theorem reflectZ_neg (v : E3) : reflectZ (-v) = -reflectZ v := by
  apply ext_coord <;> simp [reflectZ]

theorem reflectZ_add (u v : E3) : reflectZ (u + v) = reflectZ u + reflectZ v := by
  apply ext_coord
  · simp [reflectZ]
  · simp [reflectZ]
  · simp [reflectZ]; ring_nf

theorem reflectZ_sub (u v : E3) : reflectZ (u - v) = reflectZ u - reflectZ v := by
  apply ext_coord
  · simp [reflectZ]
  · simp [reflectZ]
  · simp [reflectZ]; ring_nf

theorem reflectZ_smul (a : ℝ) (v : E3) : reflectZ (a • v) = a • reflectZ v := by
  apply ext_coord <;> simp [reflectZ]

theorem inner_reflectZ_reflectZ (u v : E3) :
    (⟪reflectZ u, reflectZ v⟫ : ℝ) = ⟪u, v⟫ := by
  rw [inner_eq_coord, inner_eq_coord]
  simp [reflectZ]

theorem norm_reflectZ (v : E3) : ‖reflectZ v‖ = ‖v‖ := by
  have hsq : ‖reflectZ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_reflectZ_reflectZ]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · have hn1 : (0 : ℝ) ≤ ‖reflectZ v‖ := norm_nonneg _
    have hn2 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
    linarith

theorem det3_reflectZ (x y z : E3) :
    det3 (reflectZ x) (reflectZ y) (reflectZ z) = -det3 x y z := by
  simp only [det3, reflectZ_apply_zero, reflectZ_apply_one, reflectZ_apply_two]
  ring

/-- The induced reflection of `S²`. -/
def mirrorS2 (p : S2) : S2 :=
  ⟨reflectZ (p : E3), by rw [norm_reflectZ, p.2]⟩

@[simp] theorem mirrorS2_coe (p : S2) : (mirrorS2 p : E3) = reflectZ (p : E3) := rfl

theorem mirrorS2_injective : Function.Injective mirrorS2 := by
  intro p q h
  apply S2.ext
  apply reflectZ_injective
  exact congrArg (fun r : S2 => (r : E3)) h

theorem mirrorS2_involutive (p : S2) : mirrorS2 (mirrorS2 p) = p := by
  apply S2.ext
  simp [mirrorS2, reflectZ_involutive]

theorem sInner_mirrorS2 (p q : S2) :
    sInner (mirrorS2 p) (mirrorS2 q) = sInner p q := by
  simp [sInner, inner_reflectZ_reflectZ]

theorem sDist_mirrorS2 (p q : S2) :
    sDist (mirrorS2 p) (mirrorS2 q) = sDist p q := by
  simp [sDist, sInner_mirrorS2]

theorem shortArc_mirrorS2 {p q : S2} (h : ShortArc p q) :
    ShortArc (mirrorS2 p) (mirrorS2 q) := by
  refine ⟨?_, ?_⟩
  · intro heq
    exact h.1 (mirrorS2_injective heq)
  · intro hanti
    apply h.2
    apply reflectZ_injective
    rw [reflectZ_neg]
    exact hanti

theorem angle_reflectZ (u v : E3) :
    InnerProductGeometry.angle (reflectZ u) (reflectZ v) =
      InnerProductGeometry.angle u v := by
  simp [InnerProductGeometry.angle, inner_reflectZ_reflectZ, norm_reflectZ]

theorem tangentTo_mirrorS2 (p q : S2) :
    tangentTo (mirrorS2 p) (mirrorS2 q) = reflectZ (tangentTo p q) := by
  rw [tangentTo_eq, tangentTo_eq]
  show (mirrorS2 q : E3) - sInner (mirrorS2 q) (mirrorS2 p) • (mirrorS2 p : E3)
    = reflectZ ((q : E3) - sInner q p • (p : E3))
  rw [mirrorS2_coe, mirrorS2_coe, sInner_mirrorS2, reflectZ_sub, reflectZ_smul]

theorem sphAngle_mirrorS2 (u v w : S2) :
    sphAngle (mirrorS2 u) (mirrorS2 v) (mirrorS2 w) = sphAngle u v w := by
  rw [sphAngle, sphAngle, tangentTo_mirrorS2, tangentTo_mirrorS2, angle_reflectZ]

theorem sOrient_mirrorS2 (a b c : S2) :
    sOrient (mirrorS2 a) (mirrorS2 b) (mirrorS2 c) = -sOrient a b c := by
  simp [sOrient, det3_reflectZ]

/-! ## §2. The mirror-reversed arm. -/

/-- The corrected tail arm: reverse the index order and then reflect in one coordinate. -/
def mirrorArm {n : ℕ} (P : Fin (n + 1) → S2) : Fin (n + 1) → S2 :=
  fun m => mirrorS2 (revArm P m)

@[simp] theorem mirrorArm_apply {n : ℕ} (P : Fin (n + 1) → S2) (m : Fin (n + 1)) :
    mirrorArm P m = mirrorS2 (revArm P m) := rfl

theorem sideLen_mirrorArm {n : ℕ} (P : Fin (n + 1) → S2) (i : Fin n) :
    sideLen (mirrorArm P) i = sideLen P ⟨n - 1 - i.val, by have := i.isLt; omega⟩ := by
  rw [show sideLen (mirrorArm P) i = sideLen (revArm P) i by
    unfold sideLen mirrorArm
    rw [sDist_mirrorS2]]
  exact revArm_sideLen P i

theorem jointAngle_mirrorArm {n : ℕ} (P : Fin (n + 1) → S2) (i : Fin (n - 1)) :
    jointAngle (mirrorArm P) i = jointAngle P ⟨n - 2 - i.val, by have := i.isLt; omega⟩ := by
  rw [show jointAngle (mirrorArm P) i = jointAngle (revArm P) i by
    unfold jointAngle mirrorArm
    rw [sphAngle_mirrorS2]]
  exact revArm_jointAngle P i

theorem endpt_mirrorArm {n : ℕ} (P : Fin (n + 1) → S2) :
    endpt (mirrorArm P) = endpt P := by
  rw [show endpt (mirrorArm P) = endpt (revArm P) by
    unfold endpt mirrorArm
    rw [sDist_mirrorS2]]
  exact endpt_revArm P

theorem sameSides_mirrorArm {n : ℕ} {A B : Fin (n + 1) → S2} (h : SameSides A B) :
    SameSides (mirrorArm A) (mirrorArm B) := by
  intro i
  rw [sideLen_mirrorArm, sideLen_mirrorArm]
  exact h _

theorem jointLe_mirrorArm {n : ℕ} {A B : Fin (n + 1) → S2} (h : JointLe A B) :
    JointLe (mirrorArm A) (mirrorArm B) := by
  intro i
  rw [jointAngle_mirrorArm, jointAngle_mirrorArm]
  exact h _

theorem positiveJoints_mirrorArm {n : ℕ} {A : Fin (n + 1) → S2} (h : PositiveJoints A) :
    PositiveJoints (mirrorArm A) := by
  intro i
  rw [jointAngle_mirrorArm]
  exact h _

theorem noNonadjacentRepeat_mirrorArm {n : ℕ} {A : Fin (n + 1) → S2}
    (h : NoNonadjacentRepeat A) : NoNonadjacentRepeat (mirrorArm A) := by
  intro r s hr hs hrs he
  have hrev : revArm A ⟨r, hr⟩ = revArm A ⟨s, hs⟩ := mirrorS2_injective he
  exact revArm_noNonadjacentRepeat h r s hr hs hrs hrev

theorem neg_sOrient_eq_swap12 (a b c : S2) :
    -sOrient a b c = sOrient b a c := by
  rw [sOrient, sOrient, det3_swap12 (b : E3) (a : E3) (c : E3)]

theorem mirrorArm_edge_short {n : ℕ} {P : Fin (n + 1) → S2}
    (hshort : ∀ i : Fin (n + 1), ShortArc (P i) (P (i + 1))) :
    ∀ i : Fin (n + 1), ShortArc (mirrorArm P i) (mirrorArm P (i + 1)) := by
  intro i
  by_cases hi : i.val < n
  · have hsucc_i : (i + 1 : Fin (n + 1)) = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def]
      omega
    have hsucc_e : (⟨n - i.val - 1, by omega⟩ + 1 : Fin (n + 1))
        = ⟨n - i.val, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_eq_of_lt (show n - i.val - 1 + 1 < n + 1 by omega)]
      omega
    have hbase := hshort ⟨n - i.val - 1, by omega⟩
    rw [hsucc_e] at hbase
    have ri : revArm P i = P ⟨n - i.val, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have ris : revArm P (i + 1) = P ⟨n - i.val - 1, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (⟨i.val + 1, by omega⟩ : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]; omega))
    rw [mirrorArm_apply, mirrorArm_apply, ri, ris]
    exact shortArc_mirrorS2 hbase.symm
  · have hin : i.val = n := by omega
    have hsucc_i : (i + 1 : Fin (n + 1)) = 0 := by
      apply Fin.ext
      simp [Fin.add_def, hin, Nat.mod_self]
    have hwrap : (⟨n, by omega⟩ + 1 : Fin (n + 1)) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_self]
    have hbase := hshort ⟨n, by omega⟩
    rw [hwrap] at hbase
    have ri : revArm P i = P ⟨0, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val, hin]))
    have ris : revArm P (i + 1) = P ⟨n, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (0 : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    rw [mirrorArm_apply, mirrorArm_apply, ri, ris]
    exact shortArc_mirrorS2 hbase.symm

theorem mirrorArm_edge_support {n : ℕ} {P : Fin (n + 1) → S2}
    (hsupp : ∀ i j : Fin (n + 1), 0 ≤ sOrient (P i) (P (i + 1)) (P j)) :
    ∀ i j : Fin (n + 1),
      0 ≤ sOrient (mirrorArm P i) (mirrorArm P (i + 1)) (mirrorArm P j) := by
  intro i j
  by_cases hi : i.val < n
  · have hsucc_i : (i + 1 : Fin (n + 1)) = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def]
      omega
    have hsucc_e : (⟨n - i.val - 1, by omega⟩ + 1 : Fin (n + 1))
        = ⟨n - i.val, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_eq_of_lt (show n - i.val - 1 + 1 < n + 1 by omega)]
      omega
    have hbase := hsupp ⟨n - i.val - 1, by omega⟩ ⟨n - j.val, by omega⟩
    rw [hsucc_e] at hbase
    have ri : revArm P i = P ⟨n - i.val, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have ris : revArm P (i + 1) = P ⟨n - i.val - 1, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (⟨i.val + 1, by omega⟩ : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]; omega))
    have rj : revArm P j = P ⟨n - j.val, by omega⟩ := by
      change P (revFin j) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have heq : sOrient (mirrorArm P i) (mirrorArm P (i + 1)) (mirrorArm P j)
        = sOrient (P ⟨n - i.val - 1, by omega⟩) (P ⟨n - i.val, by omega⟩)
            (P ⟨n - j.val, by omega⟩) := by
      rw [mirrorArm_apply, mirrorArm_apply, mirrorArm_apply, ri, ris, rj,
        sOrient_mirrorS2, neg_sOrient_eq_swap12]
    rw [heq]
    exact hbase
  · have hin : i.val = n := by omega
    have hsucc_i : (i + 1 : Fin (n + 1)) = 0 := by
      apply Fin.ext
      simp [Fin.add_def, hin, Nat.mod_self]
    have hwrap : (⟨n, by omega⟩ + 1 : Fin (n + 1)) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_self]
    have hbase := hsupp ⟨n, by omega⟩ ⟨n - j.val, by omega⟩
    rw [hwrap] at hbase
    have ri : revArm P i = P ⟨0, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val, hin]))
    have ris : revArm P (i + 1) = P ⟨n, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (0 : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have rj : revArm P j = P ⟨n - j.val, by omega⟩ := by
      change P (revFin j) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have heq : sOrient (mirrorArm P i) (mirrorArm P (i + 1)) (mirrorArm P j)
        = sOrient (P ⟨n, by omega⟩) (P ⟨0, by omega⟩)
            (P ⟨n - j.val, by omega⟩) := by
      rw [mirrorArm_apply, mirrorArm_apply, mirrorArm_apply, ri, ris, rj,
        sOrient_mirrorS2, neg_sOrient_eq_swap12]
    rw [heq]
    exact hbase

theorem weakConvex_mirrorArm {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P) : WeakConvexSphArm (mirrorArm P) := by
  refine ⟨hP.two_le, ?_⟩
  refine
    { three_le := hP.closed_convex.three_le
      edge_short := mirrorArm_edge_short hP.closed_convex.edge_short
      edge_support := mirrorArm_edge_support hP.closed_convex.edge_support
      open_hemisphere := ?_ }
  obtain ⟨h, hnorm, hhem⟩ := hP.closed_convex.open_hemisphere
  refine ⟨reflectZ h, by rw [norm_reflectZ, hnorm], ?_⟩
  intro r
  rw [mirrorArm_apply, mirrorS2_coe, inner_reflectZ_reflectZ]
  exact hhem (revFin r)

theorem strictConvex_mirrorArm {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : StrictConvexSphArm P) : StrictConvexSphArm (mirrorArm P) := by
  have hweak : WeakConvexSphArm (mirrorArm P) :=
    weakConvex_mirrorArm (strictConvexSphArm_toWeak hP)
  refine ⟨hP.two_le, ?_⟩
  refine
    { three_le := hweak.closed_convex.three_le
      edge_short := hweak.closed_convex.edge_short
      edge_support := hweak.closed_convex.edge_support
      strict_nonincident := ?_
      open_hemisphere := hweak.closed_convex.open_hemisphere }
  intro i j hji hji1
  by_cases hi : i.val < n
  · have hsucc_i : (i + 1 : Fin (n + 1)) = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def]
      omega
    have hsucc_e : (⟨n - i.val - 1, by omega⟩ + 1 : Fin (n + 1))
        = ⟨n - i.val, by omega⟩ := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_eq_of_lt (show n - i.val - 1 + 1 < n + 1 by omega)]
      omega
    have hv_ne_e : (⟨n - j.val, by omega⟩ : Fin (n + 1))
        ≠ ⟨n - i.val - 1, by omega⟩ := by
      intro hv
      apply hji1
      apply Fin.ext
      have hsval : ((i + 1 : Fin (n + 1)) : ℕ) = i.val + 1 := by
        rw [hsucc_i]
      rw [hsval]
      have hvval : n - j.val = n - i.val - 1 := congrArg Fin.val hv
      have hjlt := j.isLt
      have hilt := i.isLt
      omega
    have hv_ne_succ : (⟨n - j.val, by omega⟩ : Fin (n + 1))
        ≠ (⟨n - i.val - 1, by omega⟩ : Fin (n + 1)) + 1 := by
      rw [hsucc_e]
      intro hv
      apply hji
      apply Fin.ext
      have hvval : n - j.val = n - i.val := congrArg Fin.val hv
      omega
    have hbase := hP.closed_convex.strict_nonincident
      ⟨n - i.val - 1, by omega⟩ ⟨n - j.val, by omega⟩ hv_ne_e hv_ne_succ
    rw [hsucc_e] at hbase
    have ri : revArm P i = P ⟨n - i.val, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have ris : revArm P (i + 1) = P ⟨n - i.val - 1, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (⟨i.val + 1, by omega⟩ : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]; omega))
    have rj : revArm P j = P ⟨n - j.val, by omega⟩ := by
      change P (revFin j) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have heq : sOrient (mirrorArm P i) (mirrorArm P (i + 1)) (mirrorArm P j)
        = sOrient (P ⟨n - i.val - 1, by omega⟩) (P ⟨n - i.val, by omega⟩)
            (P ⟨n - j.val, by omega⟩) := by
      rw [mirrorArm_apply, mirrorArm_apply, mirrorArm_apply, ri, ris, rj,
        sOrient_mirrorS2, neg_sOrient_eq_swap12]
    rw [heq]
    exact hbase
  · have hin : i.val = n := by omega
    have hsucc_i : (i + 1 : Fin (n + 1)) = 0 := by
      apply Fin.ext
      simp [Fin.add_def, hin, Nat.mod_self]
    have hwrap : (⟨n, by omega⟩ + 1 : Fin (n + 1)) = (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp [Fin.add_def, Nat.mod_self]
    have hv_ne_e : (⟨n - j.val, by omega⟩ : Fin (n + 1))
        ≠ ⟨n, by omega⟩ := by
      intro hv
      apply hji1
      apply Fin.ext
      have hsval : ((i + 1 : Fin (n + 1)) : ℕ) = 0 := by
        rw [hsucc_i]
        simp
      rw [hsval]
      have hvval : n - j.val = n := congrArg Fin.val hv
      have hjlt := j.isLt
      omega
    have hv_ne_succ : (⟨n - j.val, by omega⟩ : Fin (n + 1))
        ≠ (⟨n, by omega⟩ : Fin (n + 1)) + 1 := by
      rw [hwrap]
      intro hv
      apply hji
      apply Fin.ext
      have hvval : n - j.val = 0 := congrArg Fin.val hv
      omega
    have hbase := hP.closed_convex.strict_nonincident
      ⟨n, by omega⟩ ⟨n - j.val, by omega⟩ hv_ne_e hv_ne_succ
    rw [hwrap] at hbase
    have ri : revArm P i = P ⟨0, by omega⟩ := by
      change P (revFin i) = _
      exact congrArg P (Fin.ext (by simp [revFin_val, hin]))
    have ris : revArm P (i + 1) = P ⟨n, by omega⟩ := by
      rw [hsucc_i]
      change P (revFin (0 : Fin (n + 1))) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have rj : revArm P j = P ⟨n - j.val, by omega⟩ := by
      change P (revFin j) = _
      exact congrArg P (Fin.ext (by simp [revFin_val]))
    have heq : sOrient (mirrorArm P i) (mirrorArm P (i + 1)) (mirrorArm P j)
        = sOrient (P ⟨n, by omega⟩) (P ⟨0, by omega⟩)
            (P ⟨n - j.val, by omega⟩) := by
      rw [mirrorArm_apply, mirrorArm_apply, mirrorArm_apply, ri, ris, rj,
        sOrient_mirrorS2, neg_sOrient_eq_swap12]
    rw [heq]
    exact hbase

/-! ## §3. Tail-boundary classification through the mirror arm. -/

theorem mirror_tail_midFold_forces_endpoint_j {n : ℕ} {P Q : Fin (n + 1) → S2}
    {j : ℕ}
    (hP : WeakConvexSphArm P)
    (hpos : PositiveJoints P)
    (hQ : StrictConvexSphArm Q)
    (hangle : JointLe P Q)
    (hnr : NoNonadjacentRepeat P)
    (hjtail : j + 2 ≤ n)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hmid : (P ⟨n, by omega⟩ : E3)
      = c • (P ⟨n - 1, by omega⟩ : E3) + d • (P ⟨j, by omega⟩ : E3)) :
    j = 0 ∨ j = 1 := by
  have hcol : (mirrorArm P ⟨0, by omega⟩ : E3) ∈
      Submodule.span NNReal
        ({(mirrorArm P ⟨1, by omega⟩ : E3),
          (mirrorArm P ⟨n - j, by omega⟩ : E3)} : Set E3) := by
    rw [Submodule.mem_span_pair]
    refine ⟨⟨c, le_of_lt hc⟩, ⟨d, le_of_lt hd⟩, ?_⟩
    rw [NNReal.smul_def, NNReal.smul_def]
    have h0 : (mirrorArm P ⟨0, by omega⟩ : S2) = mirrorS2 (P ⟨n, by omega⟩) := by
      change mirrorS2 (P (revFin (⟨0, by omega⟩ : Fin (n + 1)))) = _
      exact congrArg mirrorS2 (congrArg P (Fin.ext (by simp [revFin_val])))
    have h1 : (mirrorArm P ⟨1, by omega⟩ : S2) = mirrorS2 (P ⟨n - 1, by omega⟩) := by
      change mirrorS2 (P (revFin (⟨1, by omega⟩ : Fin (n + 1)))) = _
      exact congrArg mirrorS2 (congrArg P (Fin.ext (by simp [revFin_val])))
    have hj : (mirrorArm P ⟨n - j, by omega⟩ : S2) = mirrorS2 (P ⟨j, by omega⟩) := by
      change mirrorS2 (P (revFin (⟨n - j, by omega⟩ : Fin (n + 1)))) = _
      congr 1
      exact congrArg P (Fin.ext (by simp [revFin_val]; omega))
    rw [h0, h1, hj, mirrorS2_coe, mirrorS2_coe, mirrorS2_coe]
    have hR := congrArg reflectZ hmid
    rw [reflectZ_add, reflectZ_smul, reflectZ_smul] at hR
    exact hR.symm
  have hq2 : 2 ≤ n - j := by omega
  have hPmirror : WeakConvexSphArm (mirrorArm P) := weakConvex_mirrorArm hP
  have hposMirror : PositiveJoints (mirrorArm P) := positiveJoints_mirrorArm hpos
  have hQmirror : StrictConvexSphArm (mirrorArm Q) := strictConvex_mirrorArm hQ
  have hangleMirror : JointLe (mirrorArm P) (mirrorArm Q) := jointLe_mirrorArm hangle
  have hnrMirror : NoNonadjacentRepeat (mirrorArm P) := noNonadjacentRepeat_mirrorArm hnr
  rcases Nat.eq_or_lt_of_le hq2 with hqeq | hqgt
  · exfalso
    have hidx : (⟨n - j, by omega⟩ : Fin (n + 1)) = ⟨2, by omega⟩ :=
      Fin.ext hqeq.symm
    have hcol2 : (mirrorArm P ⟨0, by omega⟩ : E3) ∈
        Submodule.span NNReal
          ({(mirrorArm P ⟨1, by omega⟩ : E3), (mirrorArm P ⟨2, by omega⟩ : E3)} : Set E3) := by
      rwa [hidx] at hcol
    exact foldedFlat_adjacent_contradiction (A := mirrorArm P) hPmirror hposMirror
      (i := 0) (by omega) hcol2
  · have hclass : (0 : ℕ) = 0 ∧ (n - j = n ∨ n - j = n - 1) :=
      far_fold_boundary_classification_unconditional
        (A := mirrorArm P) (B := mirrorArm Q)
        hPmirror hposMirror hQmirror hangleMirror hnrMirror
        (i := 0) (j := n - j) (by omega) (by omega) hcol
    rcases hclass.2 with hleft | hleft
    · left; omega
    · right; omega

theorem nonAxisTailBoundaryResidue_forces_endpoint_j_mirror {n : ℕ}
    {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
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
  exact mirror_tail_midFold_forces_endpoint_j (P := P) (Q := B)
    hA'weak hA'pos hB hangle' hnr hjtail hc hd hmid

theorem nonAxisTailBoundaryResidue_false_of_two_le_j_mirror {n : ℕ}
    {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    {i j : ℕ} {hi : i < n + 1} {hi1 : i + 1 < n + 1} {hj : j < n + 1}
    (hA'weak : WeakConvexSphArm (openedWBS A B k))
    (hA'pos : PositiveJoints (openedWBS A B k))
    (hB : StrictConvexSphArm B)
    (hangle' : JointLe (openedWBS A B k) B)
    (hnr : NoNonadjacentRepeat (openedWBS A B k))
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ))
    (hj2 : 2 ≤ j)
    (hres : NonAxisTailBoundaryResidue A B k i j hi hi1 hj) :
    False := by
  rcases nonAxisTailBoundaryResidue_forces_endpoint_j_mirror hA'weak hA'pos hB hangle'
      hnr hhem hres with hj0 | hj1
  · omega
  · omega

/-! ## §4. Anti-impostor guards and axiom audit. -/

theorem mirror_tail_endpoint_conclusion_satisfiable : ((0 : ℕ) = 0 ∨ (0 : ℕ) = 1) :=
  Or.inl rfl

#print axioms reflectZ
#print axioms weakConvex_mirrorArm
#print axioms strictConvex_mirrorArm
#print axioms mirror_tail_midFold_forces_endpoint_j
#print axioms nonAxisTailBoundaryResidue_forces_endpoint_j_mirror
#print axioms nonAxisTailBoundaryResidue_false_of_two_le_j_mirror

end ProofsInTheBook.ZinanFFCT61
