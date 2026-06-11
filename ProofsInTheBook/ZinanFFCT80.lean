import ProofsInTheBook.ZinanFFCT79

/-!
# `ZinanFFCT80` -- sign-carrying wrap-state bricks

This file starts the sign-carrying wrap-propagation layer requested after
`ZinanFFCT79`.  It lands only kernel-checked worker bricks: the coefficient
state, its determinant consequence, the same-sign one-step propagation, and
the real-span extraction from a wrap-boundary zero.

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
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79

namespace ProofsInTheBook.ZinanFFCT80

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## Sign-carrying wrap state. -/

/-- A vertex `k` lies in the positive real cone spanned by the wrap anchor
`A n` and the probe vertex `A j`. -/
structure WrapPlaneState {n : ℕ} (A : Fin (n + 1) → S2)
    (j : Fin (n + 1)) (k : ℕ) where
  hk : k < n + 1
  c : ℝ
  d : ℝ
  rep :
    (A ⟨k, hk⟩ : E3) =
      (c : ℝ) • (A (Fin.last n) : E3) + (d : ℝ) • (A j : E3)
  hc_pos : 0 < c
  hd_pos : 0 < d

/-- The coefficient state implies the swept vertex is coplanar with the two
wrap anchors. -/
theorem WrapPlaneState.sOrient_zero
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)} {k : ℕ}
    (S : WrapPlaneState A j k) :
    sOrient (A (Fin.last n)) (A j) (A ⟨k, S.hk⟩) = 0 := by
  rw [sOrient, S.rep]
  simp only [det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Same-sign propagation across one ordinary edge, specialized to a
`WrapPlaneState`.  The geometric nonincidence bookkeeping is deliberately left
to the caller as the two weak-support hypotheses. -/
theorem wrapPlaneState_step_sameSign
    {n : ℕ} {A : Fin (n + 1) → S2}
    {j : Fin (n + 1)} {k : ℕ}
    (S : WrapPlaneState A j k)
    (hk1 : k + 1 < n + 1)
    (hLast :
      0 ≤ sOrient (A ⟨k, by omega⟩)
        (A ⟨k + 1, by omega⟩) (A (Fin.last n)))
    (hprobe :
      0 ≤ sOrient (A ⟨k, by omega⟩)
        (A ⟨k + 1, by omega⟩) (A j)) :
    sOrient (A (Fin.last n)) (A j)
      (A ⟨k + 1, by omega⟩) = 0 := by
  have hrep :
      (A ⟨k, by omega⟩ : E3) =
        S.c • (A (Fin.last n) : E3) + S.d • (A j : E3) := by
    have hidx : (⟨k, by omega⟩ : Fin (n + 1)) = ⟨k, S.hk⟩ := Fin.ext rfl
    simpa [hidx] using S.rep
  exact boundaryPlane_step_sameSign (A := A)
    (U := A (Fin.last n)) (V := A j) (k := k)
    hk1 hrep (ne_of_gt S.hc_pos) (ne_of_gt S.hd_pos)
    (mul_pos S.hc_pos S.hd_pos) hLast hprobe

/-- After a same-sign step, the next vertex again lies in the real span of the
same wrap anchors.  This is the re-extraction half; the signs of the new
coefficients remain a separate trichotomy. -/
theorem wrap_next_real_span_of_sameSign
    {n : ℕ} {A : Fin (n + 1) → S2}
    {j : Fin (n + 1)} {k : ℕ}
    (hdist : A (Fin.last n) ≠ A j)
    (hanti : (A (Fin.last n) : E3) ≠ -(A j : E3))
    (S : WrapPlaneState A j k)
    (hk1 : k + 1 < n + 1)
    (hLast :
      0 ≤ sOrient (A ⟨k, by omega⟩)
        (A ⟨k + 1, by omega⟩) (A (Fin.last n)))
    (hprobe :
      0 ≤ sOrient (A ⟨k, by omega⟩)
        (A ⟨k + 1, by omega⟩) (A j)) :
    ∃ c d : ℝ,
      (A ⟨k + 1, by omega⟩ : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3) := by
  have hzero :=
    wrapPlaneState_step_sameSign S hk1 hLast hprobe
  rw [sOrient] at hzero
  exact lin_indep_span_of_det3_zero
    (A (Fin.last n)).2 (A j).2
    (fun heq => hdist (S2.ext heq)) hanti hzero

/-! ## Initial real-span extraction. -/

/-- A wrap-boundary zero places the head vertex `A 0` in the real span of the
two anchors `A n` and `A j`, provided those anchors are not equal or antipodal.
The signs of these coefficients are exactly the missing trichotomy data for the
full propagation theorem. -/
theorem wrap_zero_real_span
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hdist : A (Fin.last n) ≠ A j)
    (hanti : (A (Fin.last n) : E3) ≠ -(A j : E3))
    (hzero : sOrient (A (Fin.last n)) (A 0) (A j) = 0) :
    ∃ c d : ℝ,
      (A 0 : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3) := by
  have hdet :
      det3 (A (Fin.last n) : E3) (A j : E3) (A 0 : E3) = 0 := by
    rw [sOrient] at hzero
    rw [ProofsInTheBook.ZinanFFCT5.det3_swap23
      (A (Fin.last n) : E3) (A 0 : E3) (A j : E3)]
    simp [hzero]
  exact lin_indep_span_of_det3_zero
    (A (Fin.last n)).2 (A j).2
    (fun heq => hdist (S2.ext heq)) hanti hdet

/-- The open-hemisphere certificate supplies the non-antipodal half of the
anchor nondegeneracy needed for `wrap_zero_real_span`. -/
theorem wrap_anchor_nonAntipodal_of_hemisphere
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ)) :
    (A (Fin.last n) : E3) ≠ -(A j : E3) := by
  obtain ⟨_, _, hpos⟩ := hhem
  exact hemisphere_nonAntipodal hpos (Fin.last n) j

/-- The last vertex is distinct from any probe index different from `Fin.last`.
For far probes this is `NoNonadjacentRepeat`; for the predecessor probe it is
the ordinary short edge `(n-1,n)`. -/
theorem wrap_anchor_distinct_of_noRepeat
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hA : WeakConvexSphArm A)
    (hnr : NoNonadjacentRepeat A)
    (hj_ne_last : j ≠ Fin.last n) :
    A (Fin.last n) ≠ A j := by
  intro heq
  have hjlt : j.val < n := by
    have hjn : j.val ≠ n := by
      intro hjn
      apply hj_ne_last
      exact Fin.ext (by simpa using hjn)
    omega
  by_cases hfar : j.val + 2 ≤ n
  · have hbad :
        A ⟨j.val, j.isLt⟩ ≠ A ⟨n, by omega⟩ :=
      hnr j.val n j.isLt (by omega) hfar
    apply hbad
    have hjidx : (⟨j.val, j.isLt⟩ : Fin (n + 1)) = j := Fin.ext rfl
    have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
    simpa [hjidx, hlast] using heq.symm
  · have hjpred : j.val + 1 = n := by omega
    have hedge : ShortArc (A j) (A (j + 1)) :=
      hA.closed_convex.edge_short j
    have hsucc : j + 1 = Fin.last n := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by have hn := hA.two_le; omega)
      rw [Fin.val_add, hone, Nat.mod_eq_of_lt (show j.val + 1 < n + 1 by omega)]
      exact hjpred
    have hneq : A j ≠ A (Fin.last n) := by
      simpa [hsucc] using hedge.1
    exact hneq heq.symm

/-- Contextual form of the initial real-span extraction. -/
theorem wrap_zero_real_span_of_context
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hA : WeakConvexSphArm A)
    (hnr : NoNonadjacentRepeat A)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    (hj_ne_last : j ≠ Fin.last n)
    (hzero : sOrient (A (Fin.last n)) (A 0) (A j) = 0) :
    ∃ c d : ℝ,
      (A 0 : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3) :=
  wrap_zero_real_span
    (wrap_anchor_distinct_of_noRepeat hA hnr hj_ne_last)
    (wrap_anchor_nonAntipodal_of_hemisphere hhem)
    hzero

/-- Contextual form of same-sign re-extraction. -/
theorem wrap_next_real_span_of_sameSign_context
    {n : ℕ} {A : Fin (n + 1) → S2}
    {j : Fin (n + 1)} {k : ℕ}
    (hA : WeakConvexSphArm A)
    (hnr : NoNonadjacentRepeat A)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    (hj_ne_last : j ≠ Fin.last n)
    (S : WrapPlaneState A j k)
    (hk1 : k + 1 < n + 1)
    (hLast :
      0 ≤ sOrient (A ⟨k, by omega⟩)
        (A ⟨k + 1, by omega⟩) (A (Fin.last n)))
    (hprobe :
      0 ≤ sOrient (A ⟨k, by omega⟩)
        (A ⟨k + 1, by omega⟩) (A j)) :
    ∃ c d : ℝ,
      (A ⟨k + 1, by omega⟩ : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3) :=
  wrap_next_real_span_of_sameSign
    (wrap_anchor_distinct_of_noRepeat hA hnr hj_ne_last)
    (wrap_anchor_nonAntipodal_of_hemisphere hhem)
    S hk1 hLast hprobe

/-! ## Zero-coefficient routing. -/

/-- A real scalar multiple of one sphere point equal to another sphere point is
equality when both vertices lie in the same strict open hemisphere. -/
theorem s2_eq_of_real_smul_with_positive_inner
    {x y : S2} {h : E3} {a : ℝ}
    (hx : 0 < (⟪h, (x : E3)⟫ : ℝ))
    (hy : 0 < (⟪h, (y : E3)⟫ : ℝ))
    (hxy : (x : E3) = a • (y : E3)) :
    x = y := by
  have hinner :
      (⟪h, (x : E3)⟫ : ℝ) = a * (⟪h, (y : E3)⟫ : ℝ) := by
    rw [hxy, inner_smul_right]
  have ha : 0 < a := by nlinarith [hinner, hx, hy]
  have hnorm := congrArg (fun v : E3 => ‖v‖) hxy
  simp only [norm_smul, Real.norm_eq_abs] at hnorm
  rw [x.2, y.2, mul_one] at hnorm
  have ha1 : a = 1 := by
    rw [abs_of_pos ha] at hnorm
    linarith
  exact S2.ext (by rw [hxy, ha1, one_smul])

/-- The head vertex is distinct from any nonzero probe.  The adjacent case is
the first short edge; the remaining cases are `NoNonadjacentRepeat`. -/
theorem wrap_head_distinct_of_noRepeat
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hA : WeakConvexSphArm A)
    (hnr : NoNonadjacentRepeat A)
    (hj_ne_zero : j ≠ 0) :
    A 0 ≠ A j := by
  intro heq
  have hjpos : 0 < j.val := by
    have hj0 : j.val ≠ 0 := by
      intro hj0
      apply hj_ne_zero
      exact Fin.ext (by simpa using hj0)
    omega
  by_cases hjone : j.val = 1
  · have hedge : ShortArc (A (0 : Fin (n + 1))) (A ((0 : Fin (n + 1)) + 1)) :=
      hA.closed_convex.edge_short 0
    have hsucc : ((0 : Fin (n + 1)) + 1) = j := by
      apply Fin.ext
      have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by have hn := hA.two_le; omega)
      simp [Nat.mod_eq_of_lt (show 1 < n + 1 by have hn := hA.two_le; omega), hjone]
    have hneq : A 0 ≠ A j := by
      simpa [hsucc] using hedge.1
    exact hneq heq
  · have hfar : 0 + 2 ≤ j.val := by omega
    have hbad : A ⟨0, by omega⟩ ≠ A ⟨j.val, j.isLt⟩ :=
      hnr 0 j.val (by omega) j.isLt hfar
    apply hbad
    have hzero : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
    have hjidx : (⟨j.val, j.isLt⟩ : Fin (n + 1)) = j := Fin.ext rfl
    simpa [hzero, hjidx] using heq

/-- The closing short edge separates the last vertex from the head vertex. -/
theorem wrap_last_head_distinct_of_weak
    {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) :
    A (Fin.last n) ≠ A 0 := by
  have hedge : ShortArc (A (Fin.last n)) (A (Fin.last n + 1)) :=
    hA.closed_convex.edge_short (Fin.last n)
  have hwrap : ¬ (Fin.last n).val + 1 < n + 1 := by simp
  have hsucc : (Fin.last n + 1 : Fin (n + 1)) = 0 :=
    weak_wrap_successor_is_zero (a := Fin.last n) hwrap
  simpa [hsucc] using hedge.1

/-- In the initial wrap span, the probe coefficient cannot be the only
surviving coefficient. -/
theorem wrap_initial_last_coeff_zero_absurd
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hA : WeakConvexSphArm A)
    (hnr : NoNonadjacentRepeat A)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    (hj_ne_zero : j ≠ 0)
    {c d : ℝ}
    (hspan :
      (A 0 : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3))
    (hc0 : c = 0) :
    False := by
  obtain ⟨h, _, hpos⟩ := hhem
  have hscalar : (A 0 : E3) = d • (A j : E3) := by
    rw [hspan, hc0, zero_smul, zero_add]
  have heq : A 0 = A j :=
    s2_eq_of_real_smul_with_positive_inner (hpos 0) (hpos j) hscalar
  exact (wrap_head_distinct_of_noRepeat hA hnr hj_ne_zero) heq

/-- In the initial wrap span, the last-anchor coefficient cannot be the only
surviving coefficient. -/
theorem wrap_initial_probe_coeff_zero_absurd
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hA : WeakConvexSphArm A)
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {c d : ℝ}
    (hspan :
      (A 0 : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3))
    (hd0 : d = 0) :
    False := by
  obtain ⟨h, _, hpos⟩ := hhem
  have hscalar : (A 0 : E3) = c • (A (Fin.last n) : E3) := by
    rw [hspan, hd0, zero_smul, add_zero]
  have heq : A 0 = A (Fin.last n) :=
    s2_eq_of_real_smul_with_positive_inner (hpos 0) (hpos (Fin.last n)) hscalar
  exact (wrap_last_head_distinct_of_weak hA) heq.symm

/-- The initial wrap span cannot have both coefficients negative, because all
vertices lie in a strict open hemisphere. -/
theorem wrap_initial_both_negative_absurd
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {c d : ℝ}
    (hspan :
      (A 0 : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3))
    (hc : c < 0) (hd : d < 0) :
    False := by
  obtain ⟨h, _, hpos⟩ := hhem
  have hinner :
      (⟪h, (A 0 : E3)⟫ : ℝ) =
        c * (⟪h, (A (Fin.last n) : E3)⟫ : ℝ) +
          d * (⟪h, (A j : E3)⟫ : ℝ) := by
    rw [hspan, inner_add_right, inner_smul_right, inner_smul_right]
  have h0 := hpos 0
  have hn := hpos (Fin.last n)
  have hj := hpos j
  nlinarith [hinner, h0, hn, hj, hc, hd]

/-- The same-sign initial branch produces the first positive cone state. -/
def wrap_initial_state_of_sameSign
    {n : ℕ} {A : Fin (n + 1) → S2} {j : Fin (n + 1)}
    (hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (A r : E3)⟫ : ℝ))
    {c d : ℝ}
    (hspan :
      (A 0 : E3) =
        c • (A (Fin.last n) : E3) + d • (A j : E3))
    (hprod : 0 < c * d) :
    WrapPlaneState A j 0 := by
  by_cases hcpos : 0 < c
  · have hdpos : 0 < d := by nlinarith [hprod, hcpos]
    refine ⟨by omega, c, d, ?_, hcpos, hdpos⟩
    have hidx : (⟨0, by omega⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
    simpa [hidx] using hspan
  · have hcne : c ≠ 0 := by
      intro hc0
      rw [hc0, zero_mul] at hprod
      exact lt_irrefl 0 hprod
    have hcle : c ≤ 0 := le_of_not_gt hcpos
    have hcneg : c < 0 := lt_of_le_of_ne hcle hcne
    have hdneg : d < 0 := by nlinarith [hprod, hcneg]
    exact False.elim
      (wrap_initial_both_negative_absurd hhem hspan hcneg hdneg)

/-! ## Tail branch routed to a wrap zero. -/

/-- In the signed tail branch, the wrap edge supports force a wrap-boundary
zero at the successor of the local edge.  This is the non-circular direction:
it produces a wrap zero, not an endpoint conclusion by the v9 tail consumer. -/
theorem bpos_aneg_tail_span_forces_wrap_zero
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hP : WeakConvexSphArm P)
    {i : ℕ}
    (hi : i < n + 1) (hi1 : i + 1 < n + 1) (hn : n < n + 1)
    {a b : ℝ}
    (hspan : (P ⟨i, hi⟩ : E3) =
      a • (P ⟨i + 1, hi1⟩ : E3) + b • (P ⟨n, hn⟩ : E3))
    (ha : a < 0) :
    sOrient (P ⟨n, hn⟩) (P 0) (P ⟨i + 1, hi1⟩) = 0 := by
  have hlast : (⟨n, hn⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
  have hwrap : ¬ (Fin.last n).val + 1 < n + 1 := by simp
  have hsucc : (Fin.last n + 1 : Fin (n + 1)) = 0 :=
    weak_wrap_successor_is_zero (a := Fin.last n) hwrap
  have hsupp_i :
      0 ≤ sOrient (P ⟨n, hn⟩) (P 0) (P ⟨i, hi⟩) := by
    have h := hP.closed_convex.edge_support (Fin.last n) ⟨i, hi⟩
    simpa [hlast, hsucc] using h
  have hsupp_next :
      0 ≤ sOrient (P ⟨n, hn⟩) (P 0) (P ⟨i + 1, hi1⟩) := by
    have h := hP.closed_convex.edge_support (Fin.last n) ⟨i + 1, hi1⟩
    simpa [hlast, hsucc] using h
  rw [sOrient] at hsupp_i hsupp_next ⊢
  set D : ℝ := det3 (P ⟨n, hn⟩ : E3) (P 0 : E3) (P ⟨i + 1, hi1⟩ : E3)
  have hid :
      det3 (P ⟨n, hn⟩ : E3) (P 0 : E3) (P ⟨i, hi⟩ : E3) = a * D := by
    rw [hspan]
    simp only [D, det3, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  have hD0 : D = 0 := by
    have hread : 0 ≤ a * D := by simpa [hid] using hsupp_i
    nlinarith [hread, hsupp_next, ha]
  simpa [D] using hD0

/-! ## Conditional wrapper audit. -/

/-- If the general wrap propagation theorem is supplied, the weak-entry v9
wrap residue follows by the landed wrap-index normalizations. -/
theorem weakWrapSeed_v9_of_wrapPropagationGeneral
    (hwrap : WrapPlanePropagationGeneral) :
    WeakVanishingWrapSeedResidueV9 := by
  intro n P B hP hpos hnr hB hside hangle a b hne hne1 hwrapBase hsupp
  left
  have ha_val : a.val = n := weak_wrap_base_is_last hwrapBase
  have ha : a = Fin.last n := Fin.ext (by simpa using ha_val)
  have hsucc : a + 1 = (0 : Fin (n + 1)) :=
    weak_wrap_successor_is_zero hwrapBase
  have hb_ne_last : b ≠ Fin.last n := by
    intro hb
    exact hne (hb.trans ha.symm)
  have hb_ne_zero : b ≠ 0 := by
    intro hb
    exact hne1 (hb.trans hsucc.symm)
  have hzero :
      sOrient (P (Fin.last n)) (P 0) (P b) = 0 := by
    simpa [ha, hsucc] using hsupp
  exact hwrap hP.two_le hP hpos hB hside hangle hnr
    hP.closed_convex.open_hemisphere hb_ne_last hb_ne_zero hzero

/-- With the cross-piece no-collision input available, the general wrap
propagation theorem also supplies the WBS support-stuck wrap residue. -/
theorem supportStuckWBSWrapSeed_v9_of_wrapPropagationGeneral
    (hcross : CrossPieceNoCollisionAtSup)
    (hwrap : WrapPlanePropagationGeneral) :
    SupportStuckWBSWrapSeedResidueV9 := by
  intro n A B hA hB hside hangle k hkdef hstuck a b hne hne1 hwrapBase hsupp
  left
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
  have hedge := openedEdges_short_at_supWBS_of_wrap (A := A) (B := B) hA hwrapArc
  have hjopen := openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef
  have hhem0 := openHemisphere_at_WBS_sup hA hka hkt hkdef hedge hjopen
  have hhem : ∃ h : E3, ‖h‖ = 1 ∧
      ∀ r : Fin (n + 1), 0 < (⟪h, (openedWBS A B k r : E3)⟫ : ℝ) := by
    simpa [openedWBS] using hhem0
  have hside' : SameSides (openedWBS A B k) B := by
    intro r
    unfold openedWBS
    rw [openTail_preserves_sides A (openingAxis k) (-(monitoredSupWBS A B k)) r]
    exact hside r
  have hjointk : jointAngle (openedWBS A B k) k =
      openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) := by
    unfold openedWBS
    exact jointAngle_openTail_eq_openedInterior A k (-(monitoredSupWBS A B k))
  have hslack : openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) ≤ jointAngle B k :=
    openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
  have hangle' : JointLe (openedWBS A B k) B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]
      exact hslack
    · unfold openedWBS
      rw [jointAngle_openTail_eq_of_ne A k (-(monitoredSupWBS A B k)) hrk]
      exact hangle r
  have hnr : NoNonadjacentRepeat (openedWBS A B k) :=
    openedWBS_noNonadjacentRepeat_of_crossPiece hcross A B hA hB hside hangle k hkdef hstuck
  have ha_val : a.val = n := weak_wrap_base_is_last hwrapBase
  have ha : a = Fin.last n := Fin.ext (by simpa using ha_val)
  have hsucc : a + 1 = (0 : Fin (n + 1)) :=
    weak_wrap_successor_is_zero hwrapBase
  have hb_ne_last : b ≠ Fin.last n := by
    intro hb
    exact hne (hb.trans ha.symm)
  have hb_ne_zero : b ≠ 0 := by
    intro hb
    exact hne1 (hb.trans hsucc.symm)
  have hzero :
      sOrient (openedWBS A B k (Fin.last n)) (openedWBS A B k 0)
        (openedWBS A B k b) = 0 := by
    simpa [ha, hsucc] using hsupp
  exact hwrap hPweak.two_le hPweak hPpos hB hside' hangle' hnr hhem
    hb_ne_last hb_ne_zero hzero

/-- Assembly audit: after the general wrap propagation theorem, the only
remaining non-cross boundary input is the live signed tail endpoint residue. -/
theorem spherical_arm_mono_final_ch13_v10_of_hcross_wrap_and_tail
    (hcross : CrossPieceNoCollisionAtSup)
    (hwrap : WrapPlanePropagationGeneral)
    (htail : BPosANegTailCornerResidueV9) :
    SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v10_of_hcross_and_boundaryResidues hcross
    { hweakWrapSeed := weakWrapSeed_v9_of_wrapPropagationGeneral hwrap
      hwrapSeed := supportStuckWBSWrapSeed_v9_of_wrapPropagationGeneral hcross hwrap
      hbpos_aneg_tail := htail }

#print axioms WrapPlaneState.sOrient_zero
#print axioms wrapPlaneState_step_sameSign
#print axioms wrap_next_real_span_of_sameSign
#print axioms wrap_next_real_span_of_sameSign_context
#print axioms wrap_zero_real_span
#print axioms wrap_anchor_nonAntipodal_of_hemisphere
#print axioms wrap_anchor_distinct_of_noRepeat
#print axioms wrap_zero_real_span_of_context
#print axioms s2_eq_of_real_smul_with_positive_inner
#print axioms wrap_head_distinct_of_noRepeat
#print axioms wrap_last_head_distinct_of_weak
#print axioms wrap_initial_last_coeff_zero_absurd
#print axioms wrap_initial_probe_coeff_zero_absurd
#print axioms wrap_initial_both_negative_absurd
#print axioms wrap_initial_state_of_sameSign
#print axioms bpos_aneg_tail_span_forces_wrap_zero
#print axioms weakWrapSeed_v9_of_wrapPropagationGeneral
#print axioms supportStuckWBSWrapSeed_v9_of_wrapPropagationGeneral
#print axioms spherical_arm_mono_final_ch13_v10_of_hcross_wrap_and_tail

end ProofsInTheBook.ZinanFFCT80
