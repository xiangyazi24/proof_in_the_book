import ProofsInTheBook.ZinanFFCT100

/-!
# `ZinanFFCT111` -- DIRECT subarm-induction route for cross-piece no-collision

This file rebuilds the FFCT86 WBS support-stuck dispatch / recursion / headline as a
`v12` family that DROPS the cross-piece collision residue `CrossPieceCollisionEndpointAtSup`.
The collision branch of the dispatch is proven INLINE using the induction hypothesis
`ihdim : ∀ m < n → MainPlusNR m`, by a direct subarm argument:

* **full closure** `r = 0 ∧ s = n`: `endpt (openedWBS) = sDist self = 0 ≤ endpt B`;
* **`δ = 0`**: `openedWBS = A`, so the collision is a nonadjacent repeat of `A` — refuted;
* **`r = K` (`δ > 0`)**: the opened tail is a rigid rotation about `A K`; the `sDist_rotS2`
  isometry turns the collision into `A K = A s`, a nonadjacent repeat — refuted;
* **`r < K` (`δ > 0`)**: the genuine subarm-induction case — isolated as `SubarmIHContra`,
  which takes `ihdim` and is the single remaining residue (the weak-target / limit core).

Composing the `v12` recursion gives the Chapter-13 headline `SphericalArmMonotone` with the
`hcollision` residue replaced by the sharper `SubarmIHContra`.

## Route status (numerically verified TRUE; two false routes killed — see HANDOFF notes)
The cap route (`endpt_openTail_interior_mono_neg`) is DEAD: the subarm base angle exceeds the
full base angle (155497/155497), so the subarm cap `δ + sphAngle(A_r,A_K,A_s) ≤ π` is false —
the collision is a genuine over-opening.  The TRUE route is subarm-IH + weak-target via a limit
from below (`endpt A_sub ≤ endpt O_τ` for `τ < δ`, continuity sends `endpt O_τ → 0`).

No proof placeholders or unsafe declarations.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
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
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalDiagCut
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT12
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT22
open ProofsInTheBook.ZinanFFCT23
open ProofsInTheBook.ZinanFFCT24
open ProofsInTheBook.ZinanFFCT25
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT52
open ProofsInTheBook.ZinanFFCT56
open ProofsInTheBook.ZinanFFCT61
open ProofsInTheBook.ZinanFFCT64
open ProofsInTheBook.ZinanFFCT65
open ProofsInTheBook.ZinanFFCT66
open ProofsInTheBook.ZinanFFCT68
open ProofsInTheBook.ZinanFFCT69
open ProofsInTheBook.ZinanFFCT70
open ProofsInTheBook.ZinanFFCT71
open ProofsInTheBook.ZinanFFCT74
open ProofsInTheBook.ZinanFFCT75
open ProofsInTheBook.ZinanFFCT76
open ProofsInTheBook.ZinanFFCT77
open ProofsInTheBook.ZinanFFCT78
open ProofsInTheBook.ZinanFFCT79
open ProofsInTheBook.ZinanFFCT80
open ProofsInTheBook.ZinanFFCT81
open ProofsInTheBook.ZinanFFCT82
open ProofsInTheBook.ZinanFFCT83
open ProofsInTheBook.ZinanFFCT84
open ProofsInTheBook.ZinanFFCT85
open ProofsInTheBook.ZinanFFCT86
open ProofsInTheBook.ZinanFFCT100

namespace ProofsInTheBook.ZinanFFCT111

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## Subarm strict convexity (general start index, including `r = 0`). -/

/-- Strict interval wrap data for `A[a..a+m]`, for an arbitrary start `a` (not just `a ≥ 1`).
Mirrors `intervalWrapDataStrict_of_cyclicTriple` but is valid at `a = 0` too. -/
theorem wrapDataStrict_general {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {a m : ℕ} (hm : 2 ≤ m) (hb : a + m ≤ n) :
    IntervalWrapDataStrict A a m hb := by
  have hcyc : CyclicTriplePos (n := n + 1) A := cyclicTriplePos_unconditional hA.closed_convex
  obtain ⟨h, _hnorm, hhem⟩ := hA.closed_convex.open_hemisphere
  have hbase : NoNonadjacentRepeat A := strictConvex_noNonadjacentRepeat hA
  refine { toWeak := { wrap_short := ?_, wrap_support := ?_ }, wrap_strict := ?_ }
  · refine ⟨?_, hemisphere_nonAntipodal hhem ⟨a + m, by omega⟩ ⟨a, by omega⟩⟩
    intro heq
    exact hbase a (a + m) (by omega) (by omega) (by omega) heq.symm
  · intro v hv
    by_cases hv0 : v = 0
    · subst hv0
      have : sOrient (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + 0, by omega⟩) = 0 := by
        simp only [sOrient, det3]; ring
      rw [this]
    · by_cases hvm : v = m
      · have hav : a + v = a + m := by omega
        have hidx : (⟨a + v, by omega⟩ : Fin (n + 1)) = ⟨a + m, by omega⟩ := Fin.ext hav
        rw [hidx]
        have : sOrient (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + m, by omega⟩) = 0 := by
          simp only [sOrient, det3]; ring
        rw [this]
      · have hpos : 0 < sOrient (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩) (A ⟨a + m, by omega⟩) :=
          hcyc ⟨a, by omega⟩ ⟨a + v, by omega⟩ ⟨a + m, by omega⟩
            (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
        rw [sOrient_cyclic (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩)]
        exact le_of_lt hpos
  · intro v hv hvm hv0
    have hpos : 0 < sOrient (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩) (A ⟨a + m, by omega⟩) :=
      hcyc ⟨a, by omega⟩ ⟨a + v, by omega⟩ ⟨a + m, by omega⟩
        (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
    rw [sOrient_cyclic (A ⟨a + m, by omega⟩) (A ⟨a, by omega⟩) (A ⟨a + v, by omega⟩)]
    exact hpos

/-- The subarm `A[a..a+m]` of a strictly convex arm is strictly convex (for `2 ≤ m`). -/
theorem strictConvex_subarm {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {a m : ℕ} (hm : 2 ≤ m) (hb : a + m ≤ n) :
    StrictConvexSphArm (intervalArm A a m hb) :=
  strictConvex_intervalArm_of_wrap hA hm hb (wrapDataStrict_general hA hm hb)

/-! ## General tangent-plane sin formulas (port of FFCT37 to an arbitrary triple).

`joint_orientedDatum_eq` / `support_openNeg_eq_sin` are stated for the joint triple
`(jointPrev, A K, jointNext)`.  We re-prove them verbatim for an arbitrary triple `(a0, axis, tail)`
with the convex orientation `0 ≤ sOrient a0 axis tail`. -/

/-- General oriented tangent datum: for the convex orientation `0 ≤ sOrient a0 axis tail`, the signed
tangent support equals `‖u‖‖w‖ sin (sphAngle a0 axis tail)` (the `+` branch). -/
theorem orientedDatum_sin_general {axis a0 tail : S2}
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsupp : 0 ≤ sOrient a0 axis tail) :
    (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ)
      = ‖tangentTo axis a0‖ * ‖tangentTo axis tail‖ * Real.sin (sphAngle a0 axis tail) := by
  set u : E3 := tangentTo axis a0 with hu
  set w : E3 := tangentTo axis tail with hw
  set c : ℝ := ⟪u, w⟫ with hc
  set s : ℝ := ⟪u, cross (axis : E3) w⟫ with hs
  set N : ℝ := ‖u‖ * ‖w‖ with hN
  set γ : ℝ := sphAngle a0 axis tail with hγ
  have hunz : u ≠ 0 := (tangentTo_ne_zero_iff axis a0).2 hka
  have hwnz : w ≠ 0 := (tangentTo_ne_zero_iff axis tail).2 hkt
  have hup : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwnz
  have hNp : (0 : ℝ) < N := mul_pos hup hwp
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact sphAngle_nonneg _ _ _
  have hγπ : γ ≤ Real.pi := by rw [hγ]; exact sphAngle_le_pi _ _ _
  have hcEq : c = N * Real.cos γ := by
    have hcos : Real.cos γ = c / N := by
      rw [hγ, sphAngle, InnerProductGeometry.cos_angle]
    rw [hcos]; field_simp
  have hpyth : c ^ 2 + s ^ 2 = N ^ 2 := by
    have := tangentPlane_pythag (k := (axis : E3)) (u := u) (w := w) axis.2
      (tangentTo_orthogonal axis a0) (tangentTo_orthogonal axis tail)
    rw [hc, hs, hN]; rw [mul_pow]; linear_combination this
  have hsinγ : 0 ≤ Real.sin γ := Real.sin_nonneg_of_nonneg_of_le_pi hγ0 hγπ
  have hssq : s ^ 2 = (N * Real.sin γ) ^ 2 := by
    have hsincos : Real.sin γ ^ 2 = 1 - Real.cos γ ^ 2 := by
      have := Real.sin_sq_add_cos_sq γ; linarith
    have hsc : s ^ 2 = N ^ 2 - c ^ 2 := by linarith [hpyth]
    rw [hsc, hcEq]
    linear_combination (-(N ^ 2)) * hsincos
  have hsnn : 0 ≤ s := by
    have hbridge : s = -sOrient axis a0 tail := by
      rw [hs, hu, hw, inner_tangent_cross_eq_neg_sOrient]
    have hswap : sOrient axis a0 tail = -sOrient a0 axis tail := by
      simp only [sOrient, det3]; ring
    rw [hbridge, hswap]; linarith
  have hge : 0 ≤ N * Real.sin γ := mul_nonneg (le_of_lt hNp) hsinγ
  have hsEq : s = N * Real.sin γ := by
    nlinarith [hssq, hsnn, hge, sq_nonneg (s - N * Real.sin γ)]
  rw [hs] at hsEq ⊢
  rw [hsEq, hN]

/-- General signed support of the opened (by `-θ`) triple: `N sin (sphAngle a0 axis tail + θ)`.  Port of
`support_openNeg_eq_sin` for an arbitrary convex-oriented triple. -/
theorem support_openNeg_sin_general {axis a0 tail : S2}
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsupp : 0 ≤ sOrient a0 axis tail) (θ : ℝ) :
    sOrient a0 axis (rotS2 axis (-θ) tail)
      = ‖tangentTo axis a0‖ * ‖tangentTo axis tail‖
          * Real.sin (sphAngle a0 axis tail + θ) := by
  set u : E3 := tangentTo axis a0 with hu
  set w : E3 := tangentTo axis tail with hw
  have hq' : tangentTo axis (rotS2 axis (-θ) tail) = rot (axis : E3) (-θ) w := by
    rw [hw]; exact tangentTo_axis_rotS2 axis tail (-θ)
  have hbridge : sOrient a0 axis (rotS2 axis (-θ) tail)
      = (⟪u, cross (axis : E3) (tangentTo axis (rotS2 axis (-θ) tail))⟫ : ℝ) := by
    have h := inner_tangent_cross_eq_neg_sOrient axis a0 (rotS2 axis (-θ) tail)
    have hswap : sOrient a0 axis (rotS2 axis (-θ) tail)
        = - sOrient axis a0 (rotS2 axis (-θ) tail) := by
      simp only [sOrient, det3]; ring
    rw [hswap, ← h, hu]
  rw [hbridge, hq']
  have hcomm : cross (axis : E3) (rot (axis : E3) (-θ) w)
      = rot (axis : E3) (-θ) (cross (axis : E3) w) := by
    rw [rot_cross axis.2 (-θ) (axis : E3) w, rot_axis axis.2]
  rw [hcomm]
  have horthcw : (⟪cross (axis : E3) w, (axis : E3)⟫ : ℝ) = 0 := inner_cross_left (axis : E3) w
  rw [inner_rot_tangent (axis : E3) (-θ) horthcw]
  have hsval : (⟪u, cross (axis : E3) w⟫ : ℝ)
      = ‖u‖ * ‖w‖ * Real.sin (sphAngle a0 axis tail) := by
    rw [hu, hw]; exact orientedDatum_sin_general hka hkt hsupp
  have haa : (⟪(axis : E3), w⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact tangentTo_orthogonal axis tail
  have haa1 : (⟪(axis : E3), (axis : E3)⟫ : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, axis.2]; norm_num
  have hcc : cross (axis : E3) (cross (axis : E3) w) = -w := by
    rw [cross_cross, haa, haa1]; simp
  have hcval : (⟪u, cross (axis : E3) (cross (axis : E3) w)⟫ : ℝ)
      = -(‖u‖ * ‖w‖ * Real.cos (sphAngle a0 axis tail)) := by
    rw [hcc, inner_neg_right]
    have hcosγ : (⟪u, w⟫ : ℝ) = ‖u‖ * ‖w‖ * Real.cos (sphAngle a0 axis tail) := by
      have hγeq : sphAngle a0 axis tail = InnerProductGeometry.angle u w := by
        rw [hu, hw, sphAngle]
      have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm u w
      rw [← hγeq] at h; linear_combination -h
    rw [hcosγ]
  rw [hsval, hcval, Real.cos_neg, Real.sin_neg]
  rw [Real.sin_add]; ring

/-- **The angle cap from a nonnegative rotated support.**  If the original triple is strictly oriented
(`0 < sOrient a0 axis tail`) and the opened-by-`-θ` triple is weakly oriented
(`0 ≤ sOrient a0 axis (rotS2 axis (-θ) tail)`), with `0 ≤ θ ≤ π`, then `θ + sphAngle a0 axis tail ≤ π`.
Tangent-plane: the rotated support is `N sin (α + θ)` (`support_openNeg_sin_general`), so its
nonnegativity forces `sin (α + θ) ≥ 0`; with `α ∈ (0,π)` and `θ ∈ [0,π]` this gives `α + θ ≤ π`. -/
theorem angle_cap_of_rotated_support_nonneg {axis a0 tail : S2}
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hstrict : 0 < sOrient a0 axis tail)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi)
    (hrot : 0 ≤ sOrient a0 axis (rotS2 axis (-θ) tail)) :
    θ + sphAngle a0 axis tail ≤ Real.pi := by
  set α := sphAngle a0 axis tail with hα
  have hunz : tangentTo axis a0 ≠ 0 := (tangentTo_ne_zero_iff axis a0).2 hka
  have hwnz : tangentTo axis tail ≠ 0 := (tangentTo_ne_zero_iff axis tail).2 hkt
  have hNp : 0 < ‖tangentTo axis a0‖ * ‖tangentTo axis tail‖ :=
    mul_pos (norm_pos_iff.2 hunz) (norm_pos_iff.2 hwnz)
  have hsin : sOrient a0 axis (rotS2 axis (-θ) tail)
      = ‖tangentTo axis a0‖ * ‖tangentTo axis tail‖ * Real.sin (α + θ) := by
    rw [hα]; exact support_openNeg_sin_general hka hkt (le_of_lt hstrict) θ
  rw [hsin] at hrot
  have hsinnn : 0 ≤ Real.sin (α + θ) := by
    by_contra h; push_neg at h
    have := mul_neg_of_pos_of_neg hNp h
    linarith [hrot]
  have hdet : det3 (a0 : E3) (axis : E3) (tail : E3) ≠ 0 := ne_of_gt hstrict
  have hα0 : 0 < α := by rw [hα]; exact sphAngle_pos_of_det3_ne a0 axis tail hdet
  have hαπ : α < Real.pi := by rw [hα]; exact sphAngle_lt_pi_of_det3_ne a0 axis tail hdet
  by_contra hcon
  push_neg at hcon
  have h1 : 0 < α + θ - Real.pi := by linarith
  have h2 : α + θ - Real.pi < Real.pi := by linarith
  have hpos : 0 < Real.sin (α + θ - Real.pi) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  have heq : Real.sin (α + θ - Real.pi) = - Real.sin (α + θ) := by
    rw [Real.sin_sub, Real.sin_pi, Real.cos_pi]; ring
  linarith [heq, hpos, hsinnn]

/-! ## The subarm angle cap, via the apex tangent-cone + adjacent opened edge support.

The cap `δ* + sphAngle (A r)(A K)(A s) ≤ π` for a proper subarm (`r < K < s`) is sourced **without** any
weak diagonal of the opened arm (the unqualified weak planar diagonal is FALSE — doubled-triangle).  It
splits into two genuinely true facts:

* **Lemma A** (`strictConvex_apex_angle_le_joint`): on the original *strict* arm, the chord seen from an
  interior vertex `A K` lies inside the tangent cone spanned by the adjacent directions `A (K-1)`, `A (K+1)`,
  so `sphAngle (A r)(A K)(A s) ≤ sphAngle (A (K-1))(A K)(A (K+1))`.  No opening, no weak supports.
* **Lemma B** (`joint_cap_of_opened_adjacent_support`): the *adjacent* opened triple `(K-1, K, K+1)` is a
  genuine **edge** support of the opened arm (`edge_support (K-1) (K+1)`, not a diagonal), and
  `angle_cap_of_rotated_support_nonneg` turns its nonnegativity into `δ* + sphAngle (A (K-1))(A K)(A (K+1)) ≤ π`.

Together (`linarith`) they give the cap. -/

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1800000 in
/-- **2D Plücker / sine-addition identity in the tangent plane.**
For `axis` unit and three vectors `p, x, n` with `x ⊥ axis`:
`⟪x,x⟫ ⟪p, axis×n⟫ = ⟪p, axis×x⟫ ⟪x,n⟫ + ⟪p,x⟫ ⟪x, axis×n⟫`.
(This is `sin(β+γ) = sinβ cosγ + cosβ sinγ` over constant norms.) -/
theorem plucker_sine_add {axis p x n : E3} (hxa : (⟪x, axis⟫ : ℝ) = 0) :
    (⟪x, x⟫ : ℝ) * (⟪p, cross axis n⟫ : ℝ)
      = (⟪p, cross axis x⟫ : ℝ) * (⟪x, n⟫ : ℝ)
        + (⟪p, x⟫ : ℝ) * (⟪x, cross axis n⟫ : ℝ) := by
  rw [inner_eq_coord x x, inner_eq_coord p (cross axis n), inner_eq_coord p (cross axis x),
    inner_eq_coord x n, inner_eq_coord p x, inner_eq_coord x (cross axis n)]
  simp only [cross_apply_zero, cross_apply_one, cross_apply_two]
  rw [inner_eq_coord] at hxa
  linear_combination
    (n 0 * p 1 * x 2 - n 0 * p 2 * x 1 - n 1 * p 0 * x 2 + n 1 * p 2 * x 0
      + n 2 * p 0 * x 1 - n 2 * p 1 * x 0) * hxa

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1800000 in
/-- **Planar resolution of `n` in the orthogonal basis `{x, axis×x}`** (for `x, n ⊥ axis`, `axis`
unit).  `⟪x,x⟫ • n = ⟪x,n⟫ • x + ⟪axis×x, n⟫ • (axis×x)`. -/
theorem planar_decompose {axis x n : E3} (haxis : ‖axis‖ = 1)
    (hxa : (⟪x, axis⟫ : ℝ) = 0) (hna : (⟪n, axis⟫ : ℝ) = 0) :
    (⟪x, x⟫ : ℝ) • n
      = (⟪x, n⟫ : ℝ) • x + (⟪cross axis x, n⟫ : ℝ) • cross axis x := by
  have haa : (axis 0) ^ 2 + (axis 1) ^ 2 + (axis 2) ^ 2 = 1 := by
    have := real_inner_self_eq_norm_sq axis
    rw [inner_eq_coord, haxis] at this; nlinarith [this]
  rw [inner_eq_coord] at hxa hna
  apply ext_coord
  · simp only [smul_apply, add_apply, cross_apply_zero, cross_apply_one, cross_apply_two,
      inner_eq_coord]
    linear_combination
      (-axis 0 * n 0 * x 0 - axis 0 * n 1 * x 1 - axis 0 * n 2 * x 2 + axis 1 * n 0 * x 1
        - axis 1 * n 1 * x 0 + axis 2 * n 0 * x 2 - axis 2 * n 2 * x 0) * hxa
      + (axis 0 * x 0 ^ 2 + axis 0 * x 1 ^ 2 + axis 0 * x 2 ^ 2) * hna
      + (-n 0 * x 1 ^ 2 - n 0 * x 2 ^ 2 + n 1 * x 0 * x 1 + n 2 * x 0 * x 2) * haa
  · simp only [smul_apply, add_apply, cross_apply_zero, cross_apply_one, cross_apply_two,
      inner_eq_coord]
    linear_combination
      (-axis 0 * n 0 * x 1 + axis 0 * n 1 * x 0 - axis 1 * n 0 * x 0 - axis 1 * n 1 * x 1
        - axis 1 * n 2 * x 2 + axis 2 * n 1 * x 2 - axis 2 * n 2 * x 1) * hxa
      + (axis 1 * x 0 ^ 2 + axis 1 * x 1 ^ 2 + axis 1 * x 2 ^ 2) * hna
      + (n 0 * x 0 * x 1 - n 1 * x 0 ^ 2 - n 1 * x 2 ^ 2 + n 2 * x 1 * x 2) * haa
  · simp only [smul_apply, add_apply, cross_apply_zero, cross_apply_one, cross_apply_two,
      inner_eq_coord]
    linear_combination
      (axis 0 * n 2 * x 0 + axis 1 * n 2 * x 1 - axis 2 * n 0 * x 0 - axis 2 * n 1 * x 1) * hxa
      + (-axis 0 * x 0 * x 2 - axis 1 * x 1 * x 2 + axis 2 * x 0 ^ 2 + axis 2 * x 1 ^ 2) * hna
      + (n 0 * x 0 * x 2 + n 1 * x 1 * x 2 - n 2 * x 0 ^ 2 - n 2 * x 1 ^ 2) * haa

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1800000 in
/-- **2D Plücker / cosine-addition identity in the tangent plane.**
For `axis` unit and three vectors `p, x, n` all orthogonal to `axis`:
`⟪x,x⟫ ⟪p, n⟫ = ⟪p,x⟫ ⟪x,n⟫ - ⟪p, axis×x⟫ ⟪x, axis×n⟫`.
(This is `cos(β+γ) = cosβ cosγ - sinβ sinγ` over constant norms.)  Derived from `planar_decompose`. -/
theorem plucker_cos_add {axis p x n : E3} (haxis : ‖axis‖ = 1)
    (hxa : (⟪x, axis⟫ : ℝ) = 0) (hna : (⟪n, axis⟫ : ℝ) = 0) :
    (⟪x, x⟫ : ℝ) * (⟪p, n⟫ : ℝ)
      = (⟪p, x⟫ : ℝ) * (⟪x, n⟫ : ℝ)
        - (⟪p, cross axis x⟫ : ℝ) * (⟪x, cross axis n⟫ : ℝ) := by
  have hdec := planar_decompose haxis hxa hna
  have h := congrArg (fun v => (⟪p, v⟫ : ℝ)) hdec
  simp only [inner_smul_right, inner_add_right] at h
  have hswap : (⟪cross axis x, n⟫ : ℝ) = -(⟪x, cross axis n⟫ : ℝ) := by
    rw [inner_eq_coord (cross axis x) n, inner_eq_coord x (cross axis n)]
    simp only [cross_apply_zero, cross_apply_one, cross_apply_two]; ring
  rw [hswap] at h
  rw [h]; ring

/-- The signed support datum equals `sOrient a axis b`. -/
theorem datum_eq_sOrient (axis a b : S2) :
    (⟪tangentTo axis a, cross (axis : E3) (tangentTo axis b)⟫ : ℝ) = sOrient a axis b := by
  rw [inner_tangent_cross_eq_neg_sOrient]
  simp only [sOrient, det3]; ring

/-- The cosine datum: `⟪t a, t b⟫ = ‖t a‖‖t b‖ cos (sphAngle a axis b)`. -/
theorem cos_datum (axis a b : S2) :
    (⟪tangentTo axis a, tangentTo axis b⟫ : ℝ)
      = ‖tangentTo axis a‖ * ‖tangentTo axis b‖ * Real.cos (sphAngle a axis b) := by
  have h := InnerProductGeometry.cos_angle_mul_norm_mul_norm (tangentTo axis a) (tangentTo axis b)
  rw [sphAngle]; linarith [h]

/-- The signed datum in sine form, valid for the convex orientation `0 ≤ sOrient a axis b`. -/
theorem sin_datum {axis a b : S2} (hka : ShortArc axis a) (hkb : ShortArc axis b)
    (hsupp : 0 ≤ sOrient a axis b) :
    sOrient a axis b
      = ‖tangentTo axis a‖ * ‖tangentTo axis b‖ * Real.sin (sphAngle a axis b) := by
  rw [← datum_eq_sOrient]; exact orientedDatum_sin_general hka hkb hsupp

set_option maxHeartbeats 1800000 in
/-- **Angle additivity.**  If `z` lies in the convex wedge (`0 ≤ sOrient prev axis z` and
`0 ≤ sOrient z axis next`), the strictly-oriented joint angle splits:
`sphAngle prev axis z + sphAngle z axis next = sphAngle prev axis next`. -/
theorem sphAngle_add_of_wedge {prev axis next z : S2}
    (hprev : ShortArc axis prev) (hnext : ShortArc axis next) (hz : ShortArc axis z)
    (hpos : 0 < sOrient prev axis next)
    (hzw1 : 0 ≤ sOrient prev axis z) (hzw2 : 0 ≤ sOrient z axis next) :
    sphAngle prev axis z + sphAngle z axis next = sphAngle prev axis next := by
  set tp := tangentTo axis prev with htp
  set tz := tangentTo axis z with htz
  set tn := tangentTo axis next with htn
  have hpnz : tp ≠ 0 := (tangentTo_ne_zero_iff axis prev).2 hprev
  have hznz : tz ≠ 0 := (tangentTo_ne_zero_iff axis z).2 hz
  have hnnz : tn ≠ 0 := (tangentTo_ne_zero_iff axis next).2 hnext
  have hpp : (0:ℝ) < ‖tp‖ := norm_pos_iff.2 hpnz
  have hzp : (0:ℝ) < ‖tz‖ := norm_pos_iff.2 hznz
  have hnp : (0:ℝ) < ‖tn‖ := norm_pos_iff.2 hnnz
  set α := sphAngle prev axis next with hαdef
  set β := sphAngle prev axis z with hβdef
  set γ := sphAngle z axis next with hγdef
  have hα0 : 0 < α := by
    rw [hαdef]; exact sphAngle_pos_of_det3_ne prev axis next (ne_of_gt hpos)
  have hαπ : α < Real.pi := by
    rw [hαdef]; exact sphAngle_lt_pi_of_det3_ne prev axis next (ne_of_gt hpos)
  have hβ0 : 0 ≤ β := sphAngle_nonneg _ _ _
  have hβπ : β ≤ Real.pi := sphAngle_le_pi _ _ _
  have hγ0 : 0 ≤ γ := sphAngle_nonneg _ _ _
  have hγπ : γ ≤ Real.pi := sphAngle_le_pi _ _ _
  have hpa : (⟪tp, (axis:E3)⟫ : ℝ) = 0 := tangentTo_orthogonal axis prev
  have hza : (⟪tz, (axis:E3)⟫ : ℝ) = 0 := tangentTo_orthogonal axis z
  have hna : (⟪tn, (axis:E3)⟫ : ℝ) = 0 := tangentTo_orthogonal axis next
  have hSpn : sOrient prev axis next
      = ‖tp‖ * ‖tn‖ * Real.sin α := sin_datum hprev hnext (le_of_lt hpos)
  have hCpn : (⟪tp, tn⟫ : ℝ) = ‖tp‖ * ‖tn‖ * Real.cos α := cos_datum axis prev next
  have hSpz : sOrient prev axis z
      = ‖tp‖ * ‖tz‖ * Real.sin β := sin_datum hprev hz hzw1
  have hCpz : (⟪tp, tz⟫ : ℝ) = ‖tp‖ * ‖tz‖ * Real.cos β := cos_datum axis prev z
  have hSzn : sOrient z axis next
      = ‖tz‖ * ‖tn‖ * Real.sin γ := sin_datum hz hnext hzw2
  have hCzn : (⟪tz, tn⟫ : ℝ) = ‖tz‖ * ‖tn‖ * Real.cos γ := cos_datum axis z next
  have hDpn : (⟪tp, cross (axis:E3) tn⟫ : ℝ) = sOrient prev axis next := datum_eq_sOrient axis prev next
  have hDpz : (⟪tp, cross (axis:E3) tz⟫ : ℝ) = sOrient prev axis z := datum_eq_sOrient axis prev z
  have hDzn : (⟪tz, cross (axis:E3) tn⟫ : ℝ) = sOrient z axis next := datum_eq_sOrient axis z next
  have hzz : (⟪tz, tz⟫ : ℝ) = ‖tz‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  have hsine := plucker_sine_add (axis := (axis:E3)) (p := tp) (x := tz) (n := tn) hza
  have hcosine := plucker_cos_add (axis := (axis:E3)) (p := tp) (x := tz) (n := tn) axis.2 hza hna
  rw [hDpn, hDpz, hDzn, hSpn, hSpz, hSzn, hzz, hCpz, hCzn] at hsine
  rw [hDpz, hDzn, hCpn, hCpz, hCzn, hzz] at hcosine
  have hPZN : (0:ℝ) < ‖tp‖ * ‖tz‖ ^ 2 * ‖tn‖ := by positivity
  have hsinα : Real.sin α = Real.sin (β + γ) := by
    rw [Real.sin_add]
    have : ‖tp‖ * ‖tz‖ ^ 2 * ‖tn‖ * Real.sin α
        = ‖tp‖ * ‖tz‖ ^ 2 * ‖tn‖ * (Real.sin β * Real.cos γ + Real.cos β * Real.sin γ) := by
      nlinarith [hsine]
    have h2 := mul_left_cancel₀ (ne_of_gt hPZN) this
    linarith [h2]
  have hcosα : Real.cos α = Real.cos (β + γ) := by
    rw [Real.cos_add]
    have : ‖tp‖ * ‖tz‖ ^ 2 * ‖tn‖ * Real.cos α
        = ‖tp‖ * ‖tz‖ ^ 2 * ‖tn‖ * (Real.cos β * Real.cos γ - Real.sin β * Real.sin γ) := by
      nlinarith [hcosine]
    have h2 := mul_left_cancel₀ (ne_of_gt hPZN) this
    linarith [h2]
  have hcosdiff : Real.cos (α - (β + γ)) = 1 := by
    rw [Real.cos_sub, hcosα, hsinα]
    have := Real.sin_sq_add_cos_sq (β + γ); nlinarith [this]
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hlo : -(2 * Real.pi) < α - (β + γ) := by nlinarith [hα0, hαπ, hβ0, hγ0, hβπ, hγπ, hpi]
  have hhi : α - (β + γ) < 2 * Real.pi := by nlinarith [hα0, hαπ, hβ0, hγ0, hβπ, hγπ, hpi]
  have hzero : α - (β + γ) = 0 := (Real.cos_eq_one_iff_of_lt_of_lt hlo hhi).1 hcosdiff
  linarith [hzero]

set_option maxHeartbeats 1800000 in
/-- **Cosine of the subtended angle.**  For `x, y` on the same (nonnegative) side of `prev` at the
apex (`0 ≤ sOrient prev axis x`, `0 ≤ sOrient prev axis y`), with `prev` a short arc, the cosine of
`sphAngle x axis y` equals `cos (β_x - β_y)`, where `β_z = sphAngle prev axis z`. -/
theorem cos_sphAngle_sub {prev axis x y : S2}
    (hprev : ShortArc axis prev) (hx : ShortArc axis x) (hy : ShortArc axis y)
    (hxw1 : 0 ≤ sOrient prev axis x) (hyw1 : 0 ≤ sOrient prev axis y) :
    Real.cos (sphAngle x axis y)
      = Real.cos (sphAngle prev axis x - sphAngle prev axis y) := by
  set tp := tangentTo axis prev with htp
  set tx := tangentTo axis x with htx
  set ty := tangentTo axis y with hty
  have hpnz : tp ≠ 0 := (tangentTo_ne_zero_iff axis prev).2 hprev
  have hxnz : tx ≠ 0 := (tangentTo_ne_zero_iff axis x).2 hx
  have hynz : ty ≠ 0 := (tangentTo_ne_zero_iff axis y).2 hy
  have hpp : (0:ℝ) < ‖tp‖ := norm_pos_iff.2 hpnz
  have hxp : (0:ℝ) < ‖tx‖ := norm_pos_iff.2 hxnz
  have hyp : (0:ℝ) < ‖ty‖ := norm_pos_iff.2 hynz
  set βx := sphAngle prev axis x with hβx
  set βy := sphAngle prev axis y with hβy
  have hpa : (⟪tp, (axis:E3)⟫ : ℝ) = 0 := tangentTo_orthogonal axis prev
  have hcosine := plucker_cos_add (axis := (axis:E3)) (p := tx) (x := tp) (n := ty) axis.2 hpa
    (tangentTo_orthogonal axis y)
  have hpp2 : (⟪tp, tp⟫ : ℝ) = ‖tp‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  have hCxp : (⟪tx, tp⟫ : ℝ) = ‖tx‖ * ‖tp‖ * Real.cos βx := by
    rw [cos_datum axis x prev, hβx, sphAngle_comm prev axis x]
  have hCpy : (⟪tp, ty⟫ : ℝ) = ‖tp‖ * ‖ty‖ * Real.cos βy := by
    rw [cos_datum axis prev y, hβy]
  have hCxy : (⟪tx, ty⟫ : ℝ) = ‖tx‖ * ‖ty‖ * Real.cos (sphAngle x axis y) := cos_datum axis x y
  have hSxp : (⟪tx, cross (axis:E3) tp⟫ : ℝ) = -(‖tp‖ * ‖tx‖ * Real.sin βx) := by
    rw [datum_eq_sOrient axis x prev]
    have hswap : sOrient x axis prev = -sOrient prev axis x := by
      simp only [sOrient, det3]; ring
    rw [hswap, sin_datum hprev hx hxw1, hβx]
  have hSpy : (⟪tp, cross (axis:E3) ty⟫ : ℝ) = ‖tp‖ * ‖ty‖ * Real.sin βy := by
    rw [datum_eq_sOrient axis prev y, sin_datum hprev hy hyw1, hβy]
  rw [hpp2, hCxp, hCpy, hCxy, hSxp, hSpy] at hcosine
  rw [Real.cos_sub]
  have hP : (0:ℝ) < ‖tp‖ ^ 2 * (‖tx‖ * ‖ty‖) := by positivity
  have : ‖tp‖ ^ 2 * (‖tx‖ * ‖ty‖) * Real.cos (sphAngle x axis y)
      = ‖tp‖ ^ 2 * (‖tx‖ * ‖ty‖) * (Real.cos βx * Real.cos βy + Real.sin βx * Real.sin βy) := by
    nlinarith [hcosine]
  exact mul_left_cancel₀ (ne_of_gt hP) this

set_option maxHeartbeats 1800000 in
/-- **The apex-wedge angle cap (hard core).**  If `prev, axis, next` is a strictly-oriented joint
(`0 < sOrient prev axis next`, opening `α = sphAngle prev axis next ∈ (0,π)`), and `x, y` both lie in
the convex wedge between `prev` and `next` at the apex `axis`, then the subtended angle is at most the
opening: `sphAngle x axis y ≤ sphAngle prev axis next`. -/
theorem sphAngle_le_of_in_apex_wedge {prev axis next x y : S2}
    (hprev : ShortArc axis prev) (hnext : ShortArc axis next)
    (hx : ShortArc axis x) (hy : ShortArc axis y)
    (hpos : 0 < sOrient prev axis next)
    (hxw1 : 0 ≤ sOrient prev axis x) (hxw2 : 0 ≤ sOrient x axis next)
    (hyw1 : 0 ≤ sOrient prev axis y) (hyw2 : 0 ≤ sOrient y axis next) :
    sphAngle x axis y ≤ sphAngle prev axis next := by
  set α := sphAngle prev axis next with hαdef
  have hxadd := sphAngle_add_of_wedge hprev hnext hx hpos hxw1 hxw2
  have hyadd := sphAngle_add_of_wedge hprev hnext hy hpos hyw1 hyw2
  set βx := sphAngle prev axis x with hβx
  set βy := sphAngle prev axis y with hβy
  set γx := sphAngle x axis next with hγx
  set γy := sphAngle y axis next with hγy
  have hα0 : 0 < α := by
    rw [hαdef]; exact sphAngle_pos_of_det3_ne prev axis next (ne_of_gt hpos)
  have hαπ : α < Real.pi := by
    rw [hαdef]; exact sphAngle_lt_pi_of_det3_ne prev axis next (ne_of_gt hpos)
  have hβx0 : 0 ≤ βx := sphAngle_nonneg _ _ _
  have hβy0 : 0 ≤ βy := sphAngle_nonneg _ _ _
  have hγx0 : 0 ≤ γx := sphAngle_nonneg _ _ _
  have hγy0 : 0 ≤ γy := sphAngle_nonneg _ _ _
  have hβxα : βx ≤ α := by have := hxadd; rw [← hαdef] at this; linarith
  have hβyα : βy ≤ α := by have := hyadd; rw [← hαdef] at this; linarith
  have hcoseq : Real.cos (sphAngle x axis y) = Real.cos (βx - βy) :=
    cos_sphAngle_sub hprev hx hy hxw1 hyw1
  have hcoslb : Real.cos α ≤ Real.cos (βx - βy) := by
    by_cases hcase : βy ≤ βx
    · have h1 : 0 ≤ βx - βy := by linarith
      have h2 : βx - βy ≤ α := by linarith
      exact Real.cos_le_cos_of_nonneg_of_le_pi h1 (le_of_lt hαπ) h2
    · push_neg at hcase
      have h1 : 0 ≤ βy - βx := by linarith
      have h2 : βy - βx ≤ α := by linarith
      have hk := Real.cos_le_cos_of_nonneg_of_le_pi h1 (le_of_lt hαπ) h2
      rw [show βx - βy = -(βy - βx) from by ring, Real.cos_neg]; exact hk
  have hxyπ : sphAngle x axis y ≤ Real.pi := sphAngle_le_pi _ _ _
  have hcoslb2 : Real.cos α ≤ Real.cos (sphAngle x axis y) := by rw [hcoseq]; exact hcoslb
  by_contra hcon
  push_neg at hcon
  have hlt : Real.cos (sphAngle x axis y) < Real.cos α :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hα0) hxyπ hcon
  linarith [hcoslb2, hlt]

/-- For a strict convex arm, `A i = A j` (`i ≠ j`) is impossible. -/
theorem arm_index_ne {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {i j : Fin (n + 1)} (hij : i ≠ j) : A i ≠ A j := by
  have hcyc : ProofsInTheBook.SphericalCyclicTriple.CyclicTriplePos (n := n + 1) A :=
    ProofsInTheBook.PlanarConvexDiag.cyclicTriplePos_unconditional hA.closed_convex
  have hn2 : 2 ≤ n := hA.two_le
  intro heq
  obtain ⟨k, hki, hkj⟩ : ∃ k : Fin (n + 1), k ≠ i ∧ k ≠ j := by
    by_contra h; push_neg at h
    have hsub : (Finset.univ : Finset (Fin (n + 1))) ⊆ {i, j} := by
      intro m _; simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hm : m = i
      · exact Or.inl hm
      · exact Or.inr (h m hm)
    have hcard : (Finset.univ : Finset (Fin (n + 1))).card ≤ 2 :=
      (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))
    rw [Finset.card_univ, Fintype.card_fin] at hcard; omega
  have key : ∀ a b c : Fin (n + 1), a < b → b < c → A a = A b ∨ A a = A c ∨ A b = A c → False := by
    intro a b c hab hbc hrep
    have hp := hcyc a b c hab hbc
    have hz : sOrient (A a) (A b) (A c) = 0 := by
      rcases hrep with h | h | h <;> · simp only [sOrient, det3, h]; ring
    linarith [hp, hz]
  rcases lt_trichotomy i j with hij1 | hij1 | hij1
  · rcases lt_trichotomy k i with hk1 | hk1 | hk1
    · exact key k i j hk1 hij1 (Or.inr (Or.inr heq))
    · exact hki hk1
    · rcases lt_trichotomy k j with hk2 | hk2 | hk2
      · exact key i k j hk1 hk2 (Or.inr (Or.inl heq))
      · exact hkj hk2
      · exact key i j k hij1 hk2 (Or.inl heq)
  · exact hij hij1
  · rcases lt_trichotomy k j with hk1 | hk1 | hk1
    · exact key k j i hk1 hij1 (Or.inr (Or.inr heq.symm))
    · exact hkj hk1
    · rcases lt_trichotomy k i with hk2 | hk2 | hk2
      · exact key j k i hk1 hk2 (Or.inr (Or.inl heq.symm))
      · exact hki hk2
      · exact key j i k hij1 hk2 (Or.inl heq.symm)

/-- Any two distinct-index vertices of a strict convex arm form a short arc. -/
theorem arm_shortArc {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {i j : Fin (n + 1)} (hij : i ≠ j) : ShortArc (A i) (A j) := by
  obtain ⟨_hvec, _hnorm, hhem⟩ := hA.closed_convex.open_hemisphere
  exact ⟨arm_index_ne hA hij, hemisphere_nonAntipodal hhem i j⟩

/-- **Lemma A — apex tangent-cone monotonicity (strict arm).**  On a strictly convex spherical arm `A`,
for `r < K < s` the chord `A r — A s` is seen from the interior vertex `A K` under an angle no larger than
the local joint angle at `A K`: `sphAngle (A r)(A K)(A s) ≤ sphAngle (A (K-1))(A K)(A (K+1))`.  Pure
original-arm fact: `A r`, `A s` both lie in the apex wedge spanned by `A (K-1)`, `A (K+1)` (four direct
edge supports of `A`), and the unoriented angle subtended within a wedge of opening `< π` is at most the
wedge opening. -/
theorem strictConvex_apex_angle_le_joint {n : ℕ} {A : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {K r s : ℕ}
    (hK0 : 1 ≤ K) (hKn : K < n) (hrK : r < K) (hKs : K < s) (hsn : s < n + 1) :
    sphAngle (A ⟨r, by omega⟩) (A ⟨K, by omega⟩) (A ⟨s, hsn⟩)
      ≤ sphAngle (A ⟨K - 1, by omega⟩) (A ⟨K, by omega⟩) (A ⟨K + 1, by omega⟩) := by
  set Km : Fin (n + 1) := ⟨K-1, by omega⟩ with hKm
  set Ka : Fin (n + 1) := ⟨K, by omega⟩ with hKa
  set Kp : Fin (n + 1) := ⟨K+1, by omega⟩ with hKp
  set R : Fin (n + 1) := ⟨r, by omega⟩ with hR
  set S : Fin (n + 1) := ⟨s, hsn⟩ with hS
  have h1v : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    simp only [Fin.val_one']; rw [Nat.mod_eq_of_lt (by omega)]
  have add_one : ∀ m : ℕ, (hm : m + 1 < n + 1) →
      ((⟨m, by omega⟩ : Fin (n + 1)) + 1) = (⟨m + 1, hm⟩ : Fin (n + 1)) := by
    intro m hm; apply Fin.ext
    rw [Fin.val_add, h1v, Fin.val_mk, Nat.mod_eq_of_lt hm]
  have hpos : 0 < sOrient (A Km) (A Ka) (A Kp) := by
    have hlt0 : Km < Ka := Fin.mk_lt_mk.mpr (by omega)
    have hlt1 : Ka < Kp := Fin.mk_lt_mk.mpr (by omega)
    exact cut_diagonal_supports hA.closed_convex hlt0 hlt1
  have hneKm : Ka ≠ Km := by rw [hKa, hKm, Ne, Fin.mk.injEq]; omega
  have hneKp : Ka ≠ Kp := by rw [hKa, hKp, Ne, Fin.mk.injEq]; omega
  have hneR : Ka ≠ R := by rw [hKa, hR, Ne, Fin.mk.injEq]; omega
  have hneS : Ka ≠ S := by rw [hKa, hS, Ne, Fin.mk.injEq]; omega
  have hprev : ShortArc (A Ka) (A Km) := arm_shortArc hA hneKm
  have hnext : ShortArc (A Ka) (A Kp) := arm_shortArc hA hneKp
  have hx : ShortArc (A Ka) (A R) := arm_shortArc hA hneR
  have hy : ShortArc (A Ka) (A S) := arm_shortArc hA hneS
  have hKmKa : (Km + 1 : Fin (n + 1)) = Ka := by
    rw [hKm, add_one (K-1) (by omega), hKa, Fin.mk.injEq]; omega
  have hKaKp : (Ka + 1 : Fin (n + 1)) = Kp := by rw [hKa, add_one K (by omega)]
  have hxw1 : 0 ≤ sOrient (A Km) (A Ka) (A R) := by
    have := hA.closed_convex.edge_support Km R; rw [hKmKa] at this; exact this
  have hxw2 : 0 ≤ sOrient (A R) (A Ka) (A Kp) := by
    have h := hA.closed_convex.edge_support Ka R; rw [hKaKp] at h
    rw [sOrient_cyclic (A R) (A Ka) (A Kp)]; exact h
  have hyw1 : 0 ≤ sOrient (A Km) (A Ka) (A S) := by
    have := hA.closed_convex.edge_support Km S; rw [hKmKa] at this; exact this
  have hyw2 : 0 ≤ sOrient (A S) (A Ka) (A Kp) := by
    have h := hA.closed_convex.edge_support Ka S; rw [hKaKp] at h
    rw [sOrient_cyclic (A S) (A Ka) (A Kp)]; exact h
  exact sphAngle_le_of_in_apex_wedge hprev hnext hx hy hpos hxw1 hxw2 hyw1 hyw2

/-- **Lemma B — the adjacent opened edge support caps the joint.**  At the WBS opening supremum the opened
adjacent triple `(K-1, K, K+1)` is a genuine edge support of the opened arm
(`0 ≤ sOrient (P (K-1))(P K)(P (K+1))` with `P (K-1) = A (K-1)`, `P K = A K`,
`P (K+1) = rotS2 (A K)(-δ*)(A (K+1))`), so by `angle_cap_of_rotated_support_nonneg`
`δ* + sphAngle (A (K-1))(A K)(A (K+1)) ≤ π`. -/
theorem joint_cap_of_opened_adjacent_support {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B) (k : Fin (n - 1))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k
        + sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) ≤ Real.pi := by
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have hk := k.isLt
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  set K : Fin (n + 1) := openingAxis k with hKdef
  set δ : ℝ := monitoredSupWBS A B k with hδdef
  have hKval : K.val = k.val + 1 := by rw [hKdef]; rfl
  -- strict consecutive support 0 < sOrient(jointPrev, A K, jointNext) (defeq to the A⟨·⟩ form)
  have hlt0 : (⟨k.val, by omega⟩ : Fin (n + 1)) < ⟨k.val + 1, by omega⟩ :=
    Fin.mk_lt_mk.mpr (by omega)
  have hlt1 : (⟨k.val + 1, by omega⟩ : Fin (n + 1)) < ⟨k.val + 2, by omega⟩ :=
    Fin.mk_lt_mk.mpr (by omega)
  have hstrict : 0 < sOrient (jointPrev A k) (A K) (jointNext A k) :=
    cut_diagonal_supports hA.closed_convex hlt0 hlt1
  -- weak convexity of opened arm; the adjacent edge support
  have hwrapArc : ShortArc (openTail A K (-δ) (Fin.last n)) (openTail A K (-δ) 0) :=
    openedWrapShortArc_at_supWBS hA hB hka hkt hkdef
  have hPweak : WeakConvexSphArm (openTail A K (-δ)) :=
    supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrapArc
  have hidx : (⟨k.val, by omega⟩ : Fin (n + 1)) + 1 = K := by
    rw [hKdef]; ext; simp [Fin.add_def, openingAxis]; omega
  have hwc0 := hPweak.closed_convex.edge_support ⟨k.val, by omega⟩ ⟨k.val + 2, by omega⟩
  rw [hidx] at hwc0
  have hkle : k.val ≤ K.val := by omega
  have hklt : K.val < k.val + 2 := by omega
  have hPprev : openTail A K (-δ) ⟨k.val, by omega⟩ = A ⟨k.val, by omega⟩ :=
    openTail_fixed A K (-δ) (r := ⟨k.val, by omega⟩) hkle
  have hPK : openTail A K (-δ) K = A K := openTail_fixed A K (-δ) (r := K) (le_refl K.val)
  have hPnext : openTail A K (-δ) ⟨k.val + 2, by omega⟩
      = rotS2 (A K) (-δ) (A ⟨k.val + 2, by omega⟩) :=
    openTail_rot A K (-δ) (r := ⟨k.val + 2, by omega⟩) hklt
  rw [hPprev, hPK, hPnext] at hwc0
  have hδ0 : 0 ≤ δ := (monitoredSupWBS_mem_Icc hA hka hkt hkdef).1
  have hδπ : δ ≤ Real.pi := le_of_lt (monitoredSupWBS_lt_pi hA hB hka hkt hkdef)
  exact angle_cap_of_rotated_support_nonneg hka hkt hstrict hδ0 hδπ hwc0

/-- **The subarm angle cap.**  At the WBS opening supremum, the subarm base angle `sphAngle (A r)(A K)(A s)`
(`r < K < s`) together with the opening `δ* = monitoredSupWBS` satisfies `δ* + sphAngle (A r)(A K)(A s) ≤ π`.
This is the cap `endpt_openTail_interior_mono` needs on the strict subarm.  Proof: Lemma A bounds the subarm
base angle by the local joint angle `sphAngle (A (K-1))(A K)(A (K+1))` (pure strict-arm tangent cone), and
Lemma B caps `δ* +` that joint angle by `π` (the adjacent opened *edge* support); combine by `linarith`.
This avoids the false weak planar diagonal entirely. -/
theorem openedWBS_subarm_angle_cap {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B) (k : Fin (n - 1))
    (hkdef : jointAngle A k < jointAngle B k)
    {r s : ℕ} (hr : r < n + 1) (hs : s < n + 1)
    (hrK : r < (openingAxis k).val) (hKs : (openingAxis k).val < s) :
    monitoredSupWBS A B k
        + sphAngle (A ⟨r, hr⟩) (A (openingAxis k)) (A ⟨s, hs⟩) ≤ Real.pi := by
  have hk := k.isLt
  have hKval : (openingAxis k).val = k.val + 1 := rfl
  have hKn : k.val + 1 < n := by omega
  -- Lemma B: the joint cap.
  have hjoint := joint_cap_of_opened_adjacent_support hA hB k hkdef
  -- Lemma A: subarm base angle ≤ local joint angle (defeq to the jointPrev/openingAxis/jointNext form).
  have hangle :
      sphAngle (A ⟨r, hr⟩) (A (openingAxis k)) (A ⟨s, hs⟩)
        ≤ sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) :=
    strictConvex_apex_angle_le_joint hA (K := k.val + 1) (r := r) (s := s)
      (by omega) hKn hrK hKs hs
  linarith [hangle, hjoint]

/-! ## The isolated subarm-induction residue (`r < K`, `δ > 0`). -/

/-- The genuine subarm-induction residue: with the IH `MainPlusNR` for all smaller dimensions,
a proper cross collision whose opening axis is strictly interior to the pair (`r < K < s`) and
with positive opening (`0 < δ*`) is impossible.  This is the weak-target / limit core. -/
def SubarmIHContra : Prop :=
  ∀ {n : ℕ}, (∀ m : ℕ, m < n → MainPlusNR m) →
    ∀ (A B : Fin (n + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
      ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k → SupportStuckWBS A B k →
        ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
          r + 2 ≤ s →
          r < (openingAxis k).val → (openingAxis k).val < s →
          (0 < r ∨ s < n) →
          0 < monitoredSupWBS A B k →
          openedWBS A B k ⟨r, hr⟩ = openedWBS A B k ⟨s, hs⟩ → False

/-- **The subarm-induction residue is discharged (limit-free, no IH).**  A proper cross collision with
strictly interior axis (`r < K < s`) and positive opening is impossible: the strict subarm `A[r..s]`
opened at its interior axis `K-r` by `-δ*` has, by `endpt_openTail_interior_mono` (cap from
`openedWBS_subarm_angle_cap`), endpoint `≥ sDist (A r)(A s) > 0` (strict no-repeat, `r + 2 ≤ s`); but the
collision makes the opened subarm endpoints coincide (`openedWBS r = openedWBS s`), forcing endpoint `0`.
Contradiction.  Note the IH `ihdim` is not used. -/
theorem subarmIHContra_holds : SubarmIHContra := by
  intro n _ihdim A B hA hB hside hangle k hkdef hstuck r s hr hs hrs hrK hKs _hproper hδpos heq
  set K : Fin (n + 1) := openingAxis k with hKdef
  set δ : ℝ := monitoredSupWBS A B k with hδdef
  have hsn : s ≤ n := by omega
  set m : ℕ := s - r with hm
  have hm2 : 2 ≤ m := by omega
  have hbnd : r + m ≤ n := by omega
  set Aint : Fin (m + 1) → S2 := intervalArm A r m hbnd with hAint_def
  have hAint : StrictConvexSphArm Aint := strictConvex_subarm hA hm2 hbnd
  set Kint : Fin (m + 1) := ⟨K.val - r, by omega⟩ with hKint_def
  have hKint0 : 1 ≤ Kint.val := by simp only [hKint_def]; omega
  have hKintm : Kint.val < m := by simp only [hKint_def]; omega
  -- vertex identifications
  have eAint0 : Aint 0 = A ⟨r, hr⟩ := by
    simp only [hAint_def, intervalArm]
    exact congrArg A (Fin.ext (by simp))
  have eAintK : Aint Kint = A K := by
    simp only [hAint_def, intervalArm]
    exact congrArg A (Fin.ext (by simp only [hKint_def]; omega))
  have eAintLast : Aint (Fin.last m) = A ⟨s, hs⟩ := by
    simp only [hAint_def, intervalArm]
    exact congrArg A (Fin.ext (by simp only [Fin.val_last]; omega))
  -- the cap on the subarm
  have hcap : δ + sphAngle (Aint 0) (Aint Kint) (Aint (Fin.last m)) ≤ Real.pi := by
    rw [eAint0, eAintK, eAintLast]
    exact openedWBS_subarm_angle_cap hA hB k hkdef hr hs hrK hKs
  -- interior-axis endpoint monotonicity on the strict subarm
  have hmono : endpt Aint ≤ endpt (openTail Aint Kint (-δ)) :=
    endpt_openTail_interior_mono hAint hKint0 hKintm (le_of_lt hδpos) hcap
  -- the opened subarm endpoints are the colliding `openedWBS` vertices
  have hopen0 : openTail Aint Kint (-δ) 0 = openedWBS A B k ⟨r, hr⟩ := by
    rw [openTail_fixed Aint Kint (-δ) (r := 0) (Nat.zero_le _), eAint0]
    simp only [openedWBS, ← hδdef, ← hKdef]
    exact (openTail_fixed A K (-δ) (r := ⟨r, hr⟩) (le_of_lt hrK)).symm
  have hopenLast : openTail Aint Kint (-δ) (Fin.last m) = openedWBS A B k ⟨s, hs⟩ := by
    rw [openTail_rot Aint Kint (-δ) (r := Fin.last m) (by simp only [Fin.val_last]; exact hKintm),
      eAintK, eAintLast]
    simp only [openedWBS, ← hδdef, ← hKdef]
    exact (openTail_rot A K (-δ) (r := ⟨s, hs⟩) hKs).symm
  have htarget0 : endpt (openTail Aint Kint (-δ)) = 0 := by
    unfold endpt
    rw [hopen0, hopenLast, heq, sDist_eq_zero_iff]
  have hsource_pos : 0 < endpt Aint := by
    unfold endpt
    rw [eAint0, eAintLast]
    exact sDist_pos_of_ne (strictConvex_noNonadjacentRepeat hA r s hr hs (by omega))
  rw [htarget0] at hmono
  linarith [hsource_pos]

/-! ## v12 dispatch (collision branch proven inline via the IH). -/

/-- WBS support-stuck endpoint dispatch with the cross-piece collision residue removed.
Collision-free branches reconstruct opened no-repeat locally (verbatim from v11); collision
branches are discharged inline (full closure / `δ = 0` / `r = K`), with the `r < K` case routed
to the subarm-induction residue `SubarmIHContra`. -/
theorem supportStuckWBS_endpoint_dispatch_at_level_nr_v12
    (hSub : SubarmIHContra)
    {n : ℕ} (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k)
    (hstuck : SupportStuckWBS A B k) :
    endpt (openedWBS A B k) ≤ endpt B := by
  by_cases hnocross :
      ∀ (r s : ℕ) (hr : r < n + 1) (hs : s < n + 1),
        r + 2 ≤ s →
        r ≤ (openingAxis k).val → (openingAxis k).val < s →
          openedWBS A B k ⟨r, hr⟩ ≠ openedWBS A B k ⟨s, hs⟩
  · obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
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
      openedWBS_noNonadjacentRepeat_of_localNoCross A B hA hB hside hangle
        k hkdef hstuck hnocross
    have hprog : MirrorBoundaryZeroProgress (openedWBS A B k) B :=
      supportStuckWBS_boundaryProgress_of_noRepeat_firstStep A B hA hB hside hangle
        k hkdef hstuck hPweak hnr hhem
    exact endpoint_of_mirrorBoundaryZeroProgress_at_level_nr
      bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero
      hPweak hPpos hnr hB hside' hangle' hhem ihdim hprog
  · push Not at hnocross
    obtain ⟨r, s, hr, hs, hrs, hrK, hKs, heq⟩ := hnocross
    have hbase : NoNonadjacentRepeat A := strictConvex_noNonadjacentRepeat hA
    by_cases hfull : r = 0 ∧ s = n
    · -- full-arm closure: `endpt (openedWBS) = sDist self = 0 ≤ endpt B`.
      obtain ⟨hr0, hsn⟩ := hfull
      have e0 : (0 : Fin (n + 1)) = ⟨r, hr⟩ := Fin.ext (by simp [hr0])
      have en : (Fin.last n) = ⟨s, hs⟩ := Fin.ext (by simp [hsn])
      have hzero : endpt (openedWBS A B k) = 0 := by
        unfold endpt
        rw [e0, en, heq]
        unfold sDist sInner
        rw [S2.inner_self]
        exact Real.arccos_one
      rw [hzero]
      unfold endpt
      exact sDist_nonneg _ _
    · -- proper collision: derive `False`.
      exfalso
      have hproper : 0 < r ∨ s < n := by
        rcases Nat.eq_zero_or_pos r with hr0 | hrpos
        · refine Or.inr ?_
          rcases Nat.lt_or_ge s n with hlt | hge
          · exact hlt
          · exact absurd ⟨hr0, le_antisymm (by omega) hge⟩ hfull
        · exact Or.inl hrpos
      set δ : ℝ := monitoredSupWBS A B k with hδdef
      by_cases hδ0 : δ = 0
      · have hO : openedWBS A B k = A := by
          simp only [openedWBS, ← hδdef, hδ0, neg_zero]
          exact openTail_zero_angle A (openingAxis k)
        rw [hO] at heq
        exact hbase r s hr hs hrs heq
      · have hδpos : 0 < δ := lt_of_le_of_ne (hδdef ▸ (monitoredSupWBS_mem_Icc hA
          (shortArcs_of_strict hA k).1 (shortArcs_of_strict hA k).2 hkdef).1) (Ne.symm hδ0)
        by_cases hrKeq : r = (openingAxis k).val
        · -- `r = K`: rigid rotation about `A K`; `heq` becomes `A K = A s`.
          have hrleK : r ≤ (openingAxis k).val := le_of_eq hrKeq
          have hrw_r : openedWBS A B k ⟨r, hr⟩ = A (openingAxis k) := by
            have h1 : openedWBS A B k ⟨r, hr⟩ = A ⟨r, hr⟩ := by
              simp only [openedWBS, ← hδdef]
              exact openTail_fixed A (openingAxis k) (-δ) hrleK
            rw [h1]
            congr 1
            exact Fin.ext (by simp [hrKeq])
          have hrw_s : openedWBS A B k ⟨s, hs⟩ = rotS2 (A (openingAxis k)) (-δ) (A ⟨s, hs⟩) := by
            simp only [openedWBS, ← hδdef]
            exact openTail_rot A (openingAxis k) (-δ) hKs
          rw [hrw_r, hrw_s] at heq
          have hzero : sDist (A (openingAxis k)) (A ⟨s, hs⟩) = 0 := by
            have hiso : sDist (A (openingAxis k)) (A ⟨s, hs⟩)
                = sDist (rotS2 (A (openingAxis k)) (-δ) (A (openingAxis k)))
                    (rotS2 (A (openingAxis k)) (-δ) (A ⟨s, hs⟩)) :=
              (sDist_rotS2 (A (openingAxis k)) (-δ) (A (openingAxis k)) (A ⟨s, hs⟩)).symm
            rw [hiso, rotS2_axis_fixed, ← heq, sDist_eq_zero_iff]
          have hKs2 : A (openingAxis k) = A ⟨s, hs⟩ := sDist_eq_zero_iff.mp hzero
          have hKlt : (openingAxis k).val + 2 ≤ s := by omega
          refine hbase (openingAxis k).val s (openingAxis k).isLt hs hKlt ?_
          rw [← hKs2]
        · -- `r < K`: the genuine subarm-induction residue.
          have hrK_lt : r < (openingAxis k).val := lt_of_le_of_ne hrK hrKeq
          exact hSub ihdim A B hA hB hside hangle k hkdef hstuck
            r s hr hs hrs hrK_lt hKs hproper hδpos heq

/-! ## v12 recursion and headline (mirroring FFCT86 v11, dropping `hcollision`). -/

theorem open_step_wbs_nr_v12
    (hSub : SubarmIHContra)
    {n : ℕ} (_hn : 2 ≤ n) (ihdim : ∀ m : ℕ, m < n → MainPlusNR m)
    {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' → NoNonadjacentRepeat A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B')
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k) :
    endpt A ≤ endpt B := by
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupWBS A B k with hδ
  set A' : Fin (n + 1) → S2 := openTail A K (-δ) with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hjointk : jointAngle A' k = openedInteriorJointAngle A k (-δ) := by
    rw [hA']; exact jointAngle_openTail_eq_openedInterior A k (-δ)
  have hslack : openedInteriorJointAngle A k (-δ) ≤ jointAngle B k :=
    openedInteriorJoint_le_at_supWBS hA hka hkt hkdef
  have hside' : SameSides A' B := by
    intro i; rw [hA', openTail_preserves_sides A K (-δ) i]; exact hside i
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hjointk]; exact hslack
    · rw [hA', jointAngle_openTail_eq_of_ne A k (-δ) hrk]; exact hangle r
  have hmono : endpt A ≤ endpt A' := glueWBS_clause_i hA hka hkt hkdef
  by_cases hstuck : SupportStuckWBS A B k
  · have hAB0 : endpt (openedWBS A B k) ≤ endpt B :=
      supportStuckWBS_endpoint_dispatch_at_level_nr_v12 hSub ihdim
        A B hA hB hside hangle k hkdef hstuck
    have hAB : endpt A' ≤ endpt B := by
      rw [hA']
      exact hAB0
    exact le_trans hmono hAB
  · have hreach : ReachWBS A B k := by
      rcases glueWBS_clause_ii hA hB hka hkt hkdef hstuck with hr | hbase
      · exact hr
      · rcases BaseStuckProgressWBS_holds n A B hA hB k hkdef hbase with hr | hvan
        · exact hr
        · exfalso
          obtain ⟨i, j, hji, hji1, heq⟩ := hvan
          exact hstuck ⟨⟨(i, j), ⟨hji, hji1⟩⟩, by rw [supportConstraint_apply]; exact heq⟩
    have hstrict : StrictConvexSphArm A' := by
      rw [hA']; exact reachWBS_strictConvex hA hB hka hkt hkdef hstuck
    have hreach_k : jointAngle A' k = jointAngle B k := by rw [hjointk]; exact hreach
    have hdrop : deficitCount A' B < deficitCount A B := by
      rw [hA']; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
    have hAB : endpt A' ≤ endpt B :=
      ihdef A' B (strictConvexSphArm_toWeak hstrict)
        (strictConvexSphArm_positiveJoints hstrict) (strictConvex_noNonadjacentRepeat hstrict)
        hB hside' hangle' hdrop
    exact le_trans hmono hAB

theorem szOpeningStepPlusNR_v12
    (hSub : SubarmIHContra) :
    SZOpeningStepPlusNR := by
  intro n hn ihdim A B hA hposA hnrA hB hside hangle ihdef
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · exact weakPositiveCutReadyNR_v9_holds weakWrapSeed_v9_of_firstStep
      bpos_aneg_tailCornerResidueV9_of_firstStepInteriorZero
      hA hposA hnrA hB hside hangle ihdim hvanish
  · by_cases hnd : deficitCount A B = 0
    · exact congruence_step hAstrict hB hside hangle hnd
    · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step_wbs_nr_v12 hSub hn ihdim hAstrict hB hside hangle ihdef k hkdef

theorem mainPlusNR_at_level_v12
    (hSub : SubarmIHContra)
    {n : ℕ} (hn : 2 ≤ n)
    (ihdim : ∀ m : ℕ, m < n → MainPlusNR m) : MainPlusNR n := by
  intro A B hA hposA hnrA hB hside hangle
  let hstep := szOpeningStepPlusNR_v12 hSub
  have hrec :
      ∀ d : ℕ, ∀ A B : Fin (n + 1) → S2,
        WeakConvexSphArm A → PositiveJoints A → NoNonadjacentRepeat A →
        StrictConvexSphArm B → SameSides A B → JointLe A B →
        deficitCount A B = d → endpt A ≤ endpt B := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d IH =>
      intro A B hA hposA hnrA hB hside hangle hdef
      refine hstep n hn ihdim A B hA hposA hnrA hB hside hangle ?_
      intro A' B' hA' hposA' hnrA' hB' hside' hangle' hlt
      exact IH (deficitCount A' B') (hdef ▸ hlt) A' B' hA' hposA' hnrA'
        hB' hside' hangle' rfl
  exact hrec (deficitCount A B) A B hA hposA hnrA hB hside hangle rfl

theorem mainPlusNR_all_v12
    (hSub : SubarmIHContra) :
    ∀ n : ℕ, 2 ≤ n → MainPlusNR n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn A B hA hposA hnrA hB hside hangle
    have ihdim : ∀ m : ℕ, m < n → MainPlusNR m := by
      intro m hm
      rcases Nat.lt_or_ge m 2 with h2 | h2
      · exact mainPlusNR_of_lt_two h2
      · exact IH m hm h2
    exact mainPlusNR_at_level_v12 hSub hn ihdim
      A B hA hposA hnrA hB hside hangle

/-- Chapter-13 strict-arm monotonicity, with the cross-piece collision residue replaced by the
genuine subarm-induction residue `SubarmIHContra`. -/
theorem spherical_arm_mono_final_ch13_v12
    (hSub : SubarmIHContra) :
    SphericalArmMonotone := by
  intro n hn A B hA hB hside hangle
  exact (mainPlusNR_all_v12 hSub n hn) A B
    (strictConvexSphArm_toWeak hA) (strictConvexSphArm_positiveJoints hA)
    (strictConvex_noNonadjacentRepeat hA) hB hside hangle

/-- **Chapter-13 strict-arm monotonicity, UNCONDITIONAL.**  The subarm-induction residue `SubarmIHContra`
is discharged by `subarmIHContra_holds`, so the `v12` headline becomes unconditional: Chapter 13 closed. -/
theorem spherical_arm_mono_final_ch13 : SphericalArmMonotone :=
  spherical_arm_mono_final_ch13_v12 subarmIHContra_holds

/-! ## Guards. -/

#print axioms subarmIHContra_holds
#print axioms spherical_arm_mono_final_ch13
#print axioms supportStuckWBS_endpoint_dispatch_at_level_nr_v12
#print axioms mainPlusNR_all_v12
#print axioms spherical_arm_mono_final_ch13_v12

end ProofsInTheBook.ZinanFFCT111
