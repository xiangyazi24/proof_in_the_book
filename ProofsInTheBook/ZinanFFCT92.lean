import ProofsInTheBook.ZinanFFCT8
import ProofsInTheBook.ZinanFFCT89

/-!
# `ZinanFFCT92` -- gnomonic surface for bounded weak simplicity

This file follows the non-circular part of the gnomonic route for the bounded
no-repeat problem.  It does **not** use `ZinanFFCT91.FaceContiguityPropagation`.

What is proved here:

* gnomonic projection is injective on a fixed open hemisphere;
* weak cyclic edge supports transport to weak planar edge supports;
* `PositiveJoints` plus `jointAngle < pi` makes every interior gnomonic turn
  strictly positive;
* the Chapter 13 bounded no-repeat theorem follows from one explicit planar
  closed-chain no-repeat core.

The remaining core is stated as a planar proposition, not introduced through
any unsafe declaration.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.ZinanFFCT8
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT21
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT89

namespace ProofsInTheBook.ZinanFFCT92

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## Pointwise gnomonic facts. -/

/-- Gnomonic projection is injective on the open hemisphere where
`0 < ⟪h, p⟫`. -/
theorem gproj_eq_imp_eq {h : E3} {p q : S2}
    (hp : (0 : ℝ) < ⟪h, (p : E3)⟫)
    (hq : (0 : ℝ) < ⟪h, (q : E3)⟫)
    (heq : gproj h p = gproj h q) :
    p = q := by
  set a : ℝ := ⟪h, (p : E3)⟫ with ha_def
  set b : ℝ := ⟪h, (q : E3)⟫ with hb_def
  have ha_pos : 0 < a := by simpa [ha_def] using hp
  have hb_pos : 0 < b := by simpa [hb_def] using hq
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hscale : (p : E3) = (a / b) • (q : E3) := by
    have hmul := congrArg (fun x : E3 => a • x) heq
    rw [gproj, gproj] at hmul
    simp only [ha_def] at hmul
    rw [smul_smul, mul_inv_cancel₀ ha_ne, one_smul, smul_smul] at hmul
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hnonneg : 0 ≤ a / b := le_of_lt (div_pos ha_pos hb_pos)
  exact (nnreal_smul_unit_eq_unit (p := p) (v := q) hnonneg hscale).2

/-- Gnomonic projection reflects equality on a fixed open hemisphere. -/
theorem gproj_eq_iff_eq {h : E3} {p q : S2}
    (hp : (0 : ℝ) < ⟪h, (p : E3)⟫)
    (hq : (0 : ℝ) < ⟪h, (q : E3)⟫) :
    gproj h p = gproj h q ↔ p = q := by
  constructor
  · exact gproj_eq_imp_eq hp hq
  · intro hpq
    rw [hpq]

/-- A short spherical edge projects to a nonzero planar edge. -/
theorem gproj_ne_of_short {h : E3} {p q : S2}
    (hp : (0 : ℝ) < ⟪h, (p : E3)⟫)
    (hq : (0 : ℝ) < ⟪h, (q : E3)⟫)
    (hshort : ShortArc p q) :
    gproj h p ≠ gproj h q := by
  intro heq
  exact hshort.1 (gproj_eq_imp_eq hp hq heq)

/-! ## The planar no-repeat core isolated from the gnomonic reduction. -/

/-- The remaining purely planar closed-chain no-repeat core.

It is stated directly for the gnomonic image: all vertices lie in one affine
plane, every cyclic directed edge weakly supports every vertex, every cyclic
edge is nonzero, and every non-wrapping interior turn is strict.  Under those
planar hypotheses the chain has no nonadjacent repeated vertices.
-/
def PlanarClosedWeakStrictNoRepeat : Prop :=
  ∀ {n : ℕ} (hn : 2 ≤ n) (h : E3) (f : Fin (n + 1) → E3),
    (∀ i : Fin (n + 1), (⟪h, f i⟫ : ℝ) = 1) →
    (∀ i j : Fin (n + 1), 0 ≤ det3 (f i) (f (i + 1)) (f j)) →
    (∀ i : Fin (n + 1), f i ≠ f (i + 1)) →
    (∀ r : ℕ, ∀ (hr2 : r + 2 < n + 1),
      0 < det3 (f ⟨r, by omega⟩) (f ⟨r + 1, by omega⟩) (f ⟨r + 2, hr2⟩)) →
    ∀ r s : ℕ, ∀ (hr : r < n + 1) (hs : s < n + 1), r + 2 ≤ s →
      f ⟨r, hr⟩ ≠ f ⟨s, hs⟩

/-! ## Gnomonic data produced by the spherical hypotheses. -/

/-- Consecutive interior triples have positive spherical orientation under
weak convexity, positive joints, and the upper bound `jointAngle < pi`. -/
theorem consecutive_sOrient_pos
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hlt : ∀ i : Fin (n - 1), jointAngle P i < Real.pi)
    {r : ℕ} (hr2 : r + 2 < n + 1) :
    0 < sOrient (P ⟨r, by omega⟩) (P ⟨r + 1, by omega⟩)
      (P ⟨r + 2, hr2⟩) := by
  have hr : r < n + 1 := by omega
  have hr1 : r + 1 < n + 1 := by omega
  have hsucc :
      ((⟨r, hr⟩ : Fin (n + 1)) + 1) =
        (⟨r + 1, hr1⟩ : Fin (n + 1)) := by
    apply Fin.ext
    have hone : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, Fin.val_mk, hone, Nat.mod_eq_of_lt (by omega)]
  have hnonneg :
      0 ≤ sOrient (P ⟨r, hr⟩) (P ⟨r + 1, hr1⟩) (P ⟨r + 2, hr2⟩) := by
    have h := hweak.closed_convex.edge_support
      (⟨r, hr⟩ : Fin (n + 1)) (⟨r + 2, hr2⟩ : Fin (n + 1))
    simpa [hsucc] using h
  have hne :
      sOrient (P ⟨r, hr⟩) (P ⟨r + 1, hr1⟩) (P ⟨r + 2, hr2⟩) ≠ 0 := by
    intro hzero
    have hdet :
        det3 (P ⟨r, by omega⟩ : E3)
          (P ⟨r + 1, by omega⟩ : E3)
          (P ⟨r + 2, hr2⟩ : E3) = 0 := by
      simpa [sOrient] using hzero
    exact weakConvex_boundedJoints_no_consecutive_det3_zero hweak hpos hlt hr2 hdet
  exact lt_of_le_of_ne hnonneg hne.symm

/-- Consecutive interior triples of the gnomonic image have positive planar
orientation. -/
theorem gnomonic_consecutive_turn_pos
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hlt : ∀ i : Fin (n - 1), jointAngle P i < Real.pi)
    {h : E3} (hhem : ∀ i : Fin (n + 1), (0 : ℝ) < ⟪h, (P i : E3)⟫)
    {r : ℕ} (hr2 : r + 2 < n + 1) :
    0 < det3 (gproj h (P ⟨r, by omega⟩))
      (gproj h (P ⟨r + 1, by omega⟩))
      (gproj h (P ⟨r + 2, hr2⟩)) := by
  have hspos := consecutive_sOrient_pos hweak hpos hlt hr2
  have hbridge := sOrient_pos_iff_planar_pos h
    (P ⟨r, by omega⟩) (P ⟨r + 1, by omega⟩) (P ⟨r + 2, hr2⟩)
    (hhem ⟨r, by omega⟩) (hhem ⟨r + 1, by omega⟩) (hhem ⟨r + 2, hr2⟩)
  exact hbridge.mp hspos

/-- The gnomonic image of a bounded weak-positive arm satisfies the planar
closed-chain hypotheses of `PlanarClosedWeakStrictNoRepeat`. -/
theorem weakConvex_boundedJoints_noNonadjacentRepeat_of_planarClosed
    (hplanar : PlanarClosedWeakStrictNoRepeat)
    {n : ℕ} {P : Fin (n + 1) → S2}
    (hweak : WeakConvexSphArm P) (hpos : PositiveJoints P)
    (hlt : ∀ i : Fin (n - 1), jointAngle P i < Real.pi) :
    NoNonadjacentRepeat P := by
  obtain ⟨h, _hnorm, hhem⟩ := hweak.closed_convex.open_hemisphere
  set Q : Fin (n + 1) → E3 := fun i => gproj h (P i) with hQ
  have hplane : ∀ i : Fin (n + 1), (⟪h, Q i⟫ : ℝ) = 1 := by
    intro i
    rw [hQ]
    exact inner_gproj (ne_of_gt (hhem i))
  have hsupport : ∀ i j : Fin (n + 1), 0 ≤ det3 (Q i) (Q (i + 1)) (Q j) := by
    intro i j
    change 0 ≤ det3 (gproj h (P i)) (gproj h (P (i + 1))) (gproj h (P j))
    exact gnomonic_edge_support_nonneg hweak.closed_convex hhem i j
  have hedge_ne : ∀ i : Fin (n + 1), Q i ≠ Q (i + 1) := by
    intro i
    change gproj h (P i) ≠ gproj h (P (i + 1))
    exact gproj_ne_of_short (hhem i) (hhem (i + 1)) (hweak.closed_convex.edge_short i)
  have hturn : ∀ r : ℕ, ∀ (hr2 : r + 2 < n + 1),
      0 < det3 (Q ⟨r, by omega⟩) (Q ⟨r + 1, by omega⟩) (Q ⟨r + 2, hr2⟩) := by
    intro r hr2
    change 0 < det3 (gproj h (P ⟨r, by omega⟩))
      (gproj h (P ⟨r + 1, by omega⟩)) (gproj h (P ⟨r + 2, hr2⟩))
    exact gnomonic_consecutive_turn_pos hweak hpos hlt hhem hr2
  intro r s hr hs hrs hrep
  have hQnr := hplanar hweak.two_le h Q hplane hsupport hedge_ne hturn r s hr hs hrs
  exact hQnr (by simp [hQ, hrep])

/-! ## Downstream Chapter 13 wrappers from the planar core. -/

/-- FFCT89's bounded-simplicity residue follows from the planar gnomonic
closed-chain core. -/
theorem boundedWeakPositiveSimplicity_of_planarClosed
    (hplanar : PlanarClosedWeakStrictNoRepeat) :
    BoundedWeakPositiveSimplicity := by
  intro n P hweak hpos hlt
  exact weakConvex_boundedJoints_noNonadjacentRepeat_of_planarClosed
    hplanar hweak hpos hlt

/-- The collision endpoint branch closes from the planar gnomonic core. -/
theorem crossPieceCollisionEndpointAtSup_of_planarClosed
    (hplanar : PlanarClosedWeakStrictNoRepeat) :
    CrossPieceCollisionEndpointAtSup :=
  crossPieceCollisionEndpointAtSup_of_boundedWeakPositiveSimplicity
    (boundedWeakPositiveSimplicity_of_planarClosed hplanar)

/-- Conditional Chapter 13 headline from the planar gnomonic core. -/
theorem spherical_arm_mono_ch13_of_planarClosed
    (hplanar : PlanarClosedWeakStrictNoRepeat) :
    SphericalArmMonotone :=
  spherical_arm_mono_ch13_of_boundedWeakPositiveSimplicity
    (boundedWeakPositiveSimplicity_of_planarClosed hplanar)

/-! ## Guards. -/

#check gproj_eq_imp_eq
#check gproj_eq_iff_eq
#check consecutive_sOrient_pos
#check gnomonic_consecutive_turn_pos
#check weakConvex_boundedJoints_noNonadjacentRepeat_of_planarClosed
#check boundedWeakPositiveSimplicity_of_planarClosed
#check crossPieceCollisionEndpointAtSup_of_planarClosed
#check spherical_arm_mono_ch13_of_planarClosed

end ProofsInTheBook.ZinanFFCT92
