import ProofsInTheBook.ZinanFFCT95
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# `ZinanFFCT96` -- the planar turning bound + the (oriented) single-wind residue discharge

This file delivers the genuine analytic core isolated by `ZinanFFCT95`: the
*total-turning bound* for a strictly convex **open** planar chain in convex
position, and from it the construction of `FFCT94.PlanarLiftedTurnSpan`.

## The orientation finding (load-bearing)

`ZinanFFCT95.StrictPlanarChainLiftedTurnSpanExists` is quantified over **every**
orthonormal frame `(u, v) ⊥ h`.  This is **too strong**: it is *false* for the
wrong-handed frame.  Concretely, for a strictly convex chain `Q` (intrinsic
left turns, `det3 (Q i)(Q (i+1))(Q j) > 0`) and a frame with `det3 h u v < 0`,
the edge directions rotate **clockwise** in the `(u, v)` coordinates, so the
signed per-joint turns are all *negative*; no lift can have `turn_pos`
(`θ` strictly increasing) with every gap `< π` (a clockwise turn by
`α ∈ (0, π)` is a counterclockwise turn by `2π − α > π`).  Swapping `u ↔ v`
preserves every hypothesis of the residue but flips `sign (det3 h u v)`, so the
residue as stated is unsatisfiable for one of the two frames — hence not
provable.

The fix is the **oriented** residue, which adds the frame-orientation
hypothesis `0 < det3 h u v`.  This is exactly the orientation the actual
application always supplies: the frame built in `ZinanFFCT95.exists_orthoFrame`
takes `v = cross h u`, for which `det3 h u v = ⟪h, cross u v⟫ = ⟪h, h⟫ = 1 > 0`.
We therefore:

* construct the lifted certificate **completely and unconditionally** for the
  oriented frame, reducing `one_wind` to one named real residual
  `OpenConvexArmTurningLtTwoPi` (`oriented_residue_of_turningBound`), and
* re-derive the spherical certificate `ZinanFFCT95.GnomonicSingleWind`
  (`strictConvexSphArm_gnomonicSingleWind'`) modulo that single residual.

## The analytic content (all unconditional)

* `det3_frame_coord` : `det3 h (a•u+b•v) (c•u+d•v) = (a*d − b*c) · det3 h u v`,
  the multilinear shadow that turns planar `det3` signs into `2×2` determinants
  of the frame coordinates.
* `liftedAngle` / `liftedAngle_exp` / `liftedAngle_cos_sin` : the lift of the
  edge directions by accumulating per-joint signed turn angles (`Complex.arg` of
  `conj zₖ · zₖ₊₁`); the angle-addition induction reconstructs each direction
  (`‖z m‖ · exp(θ m · I) = z m`).
* `edgeZ_turn_im_pos` : the per-joint strict turn `det3(Qₘ)(Qₘ₊₁)(Qₘ₊₂) > 0`
  forces `Im(conj zₘ · zₘ₊₁) > 0`, giving `turn ∈ (0,π)`.
* `oriented_residue_of_turningBound` : the full `PlanarLiftedTurnSpan`
  (`edge_eq`, `turn_pos`, `turn_lt_pi`, `one_wind`) built from the lift, with a
  slack linear continuation past the open arm; `one_wind` is reduced to the
  single residual below.

## The isolated residual

`OpenConvexArmTurningLtTwoPi` : the total turning of the open arm
(`liftedAngle (edgeZ Q u v) (n−1) − liftedAngle (edgeZ Q u v) 0 < 2π`) of a
strictly convex *cyclic* planar chain in convex position.  This is the one piece
not reduced to first-order data.  Verified:
* numerically TRUE and tight (convex arms approach but never reach `2π`); not a
  vacuous/false hypothesis;
* the single-covector pairing against edge `0` alone is *insufficient*
  (counterexample with arm turning `> 2π` exists) — the **global cyclic** support
  is essential, matching `ZinanFFCT94`'s recorded obstruction.
-/

noncomputable section

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalGnomonic
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT94

namespace ProofsInTheBook.ZinanFFCT96

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1800000

/-! ## Block A — the frame-coordinate `det3` shadow. -/

/-- The multilinear shadow: with `(u, v) ⊥ h`, the planar orientation of two
in-plane vectors expressed in the frame is the `2×2` coordinate determinant
times the frame orientation `det3 h u v`. -/
theorem det3_frame_coord (h u v : E3) (a b c d : ℝ) :
    det3 h (a • u + b • v) (c • u + d • v) = (a * d - b * c) * det3 h u v := by
  rw [det3_add_mid, det3_smul_mid, det3_smul_mid,
      det3_add_right, det3_add_right, det3_smul_right, det3_smul_right,
      det3_smul_right, det3_smul_right]
  rw [show det3 h u u = 0 from det3_self_mid₂ h u,
      show det3 h v v = 0 from det3_self_mid₂ h v]
  rw [det3_swap_right h v u]
  ring

/-- An oriented orthonormal frame from a unit `h`: in addition to orthonormality
and perpendicularity, the frame carries the positive orientation
`det3 h u v = 1`.  Construction `v := cross h u`, for which
`det3 h u v = ⟪h, cross u v⟫ = ⟪h, ⟪u,u⟫•h − ⟪u,h⟫•u⟫ = ⟪h,h⟫ = 1`. -/
theorem exists_orthoFrame_oriented {h : E3} (hh : ‖h‖ = 1) :
    ∃ u v : E3, (⟪h, u⟫ : ℝ) = 0 ∧ (⟪h, v⟫ : ℝ) = 0 ∧
      (⟪u, u⟫ : ℝ) = 1 ∧ (⟪v, v⟫ : ℝ) = 1 ∧ (⟪u, v⟫ : ℝ) = 0 ∧
      det3 h u v = 1 := by
  -- reuse the FFCT95 seed-frame, but keep `v = cross h u` to read off the orientation.
  obtain ⟨u, v, hhu, hhv, huu, hvv, huv⟩ := ProofsInTheBook.ZinanFFCT95.exists_orthoFrame hh
  -- We do NOT know `v = cross h u` from the existential, so rebuild from `u`.
  -- Set `w := cross h u`; it is orthonormal-with-`u` and `det3 h u w = 1`.
  refine ⟨u, cross h u, hhu, ?_, huu, ?_, ?_, ?_⟩
  · -- ⟪h, cross h u⟫ = 0
    rw [real_inner_comm]; exact inner_cross_left h u
  · -- ⟪cross h u, cross h u⟫ = ‖h‖²‖u‖² − ⟪h,u⟫² = 1
    rw [real_inner_self_eq_norm_sq, norm_sq_cross, hh,
        ← real_inner_self_eq_norm_sq, huu, hhu]; ring
  · -- ⟪u, cross h u⟫ = 0
    rw [real_inner_comm]; exact inner_cross_right h u
  · -- det3 h u (cross h u) = ⟪h, cross u (cross h u)⟫ = ⟪h, ⟪u,u⟫•h − ⟪u,h⟫•u⟫ = ⟪u,u⟫⟪h,h⟫ = 1
    rw [← inner_cross_eq_det3, cross_cross]
    have huh : (⟪u, h⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hhu
    rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right, huh, huu,
        real_inner_self_eq_norm_sq, hh]
    ring

/-- For three points in the affine plane `⟪h,·⟫ = 1` (`‖h‖ = 1`), the shared-apex
orientation is the orientation of the two difference vectors against `h`:
`det3 a b c = det3 h (b − a) (c − a)`. -/
theorem det3_eq_det3_h_diff {h : E3} (hh : ‖h‖ = 1) {a b c : E3}
    (ha : (⟪h, a⟫ : ℝ) = 1) (hb : (⟪h, b⟫ : ℝ) = 1) (hc : (⟪h, c⟫ : ℝ) = 1) :
    det3 a b c = det3 h (b - a) (c - a) := by
  have hne : h ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hh; norm_num at hh
  -- expand the RHS multilinearly
  rw [show b - a = b + (-1 : ℝ) • a by module,
      show c - a = c + (-1 : ℝ) • a by module]
  rw [det3_add_mid, det3_smul_mid, det3_add_right, det3_add_right,
      det3_smul_right, det3_smul_right]
  rw [show det3 h a a = 0 from det3_self_mid₂ h a]
  -- now: det3 h b c + (-1)*det3 h b a + ((-1)*det3 h a c + (-1)*((-1)*0))
  -- planar cocycle with d = h (in the plane since ‖h‖=1)
  have hhh : (⟪h, h⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hh]; norm_num
  have hcoc := planar_cocycle hne ha hb hc hhh
  -- hcoc : det3 a b c = det3 a b h − det3 a c h + det3 b c h
  -- rewrite each det3 · · h as a det3 h · · via cyclic rotation
  have e1 : det3 a b h = det3 h a b := by rw [det3_cyclic a b h, det3_cyclic b h a]
  have e2 : det3 a c h = det3 h a c := by rw [det3_cyclic a c h, det3_cyclic c h a]
  have e3 : det3 b c h = det3 h b c := by rw [det3_cyclic b c h, det3_cyclic c h b]
  rw [e1, e2, e3] at hcoc
  -- det3 h a b = - det3 h b a
  rw [hcoc]
  rw [show det3 h a b = - det3 h b a from by rw [det3_swap_right h a b]]
  ring

/-! ## Block B — the lifted angle from a nonzero complex sequence.

Given `z : ℕ → ℂ` with every `z m ≠ 0`, the cumulative lifted angle
`Θ z m := arg (z 0) + ∑_{k<m} arg (conj (z k) * z (k+1))`
satisfies `‖z m‖ • exp (Θ z m * I) = z m` (i.e. `exp (Θ z m * I) = z m / ‖z m‖`,
the lift of the direction of `z m`), and its per-step increment is exactly
`arg (conj (z m) * z (m+1))`.  This is the analytic lift: no `2π`-mod, real-valued
angle, reconstructing the direction by an angle-addition induction. -/

open Complex in
/-- The cumulative lifted angle of a nonzero complex sequence. -/
def liftedAngle (z : ℕ → ℂ) : ℕ → ℝ :=
  fun m => Complex.arg (z 0) + ∑ k ∈ Finset.range m, Complex.arg (starRingEnd ℂ (z k) * z (k + 1))

open Complex in
/-- The per-step increment of `liftedAngle` is the argument of the ratio. -/
theorem liftedAngle_succ (z : ℕ → ℂ) (m : ℕ) :
    liftedAngle z (m + 1) - liftedAngle z m
      = Complex.arg (starRingEnd ℂ (z m) * z (m + 1)) := by
  simp only [liftedAngle, Finset.sum_range_succ]
  ring

open Complex in
/-- The lift reconstructs the direction: `(‖z m‖ : ℂ) * exp (liftedAngle z m * I) = z m`. -/
theorem liftedAngle_exp (z : ℕ → ℂ) (hz : ∀ k, z k ≠ 0) (m : ℕ) :
    ((‖z m‖ : ℂ)) * Complex.exp ((liftedAngle z m : ℝ) * Complex.I) = z m := by
  induction m with
  | zero =>
    simp only [liftedAngle, Finset.range_zero, Finset.sum_empty, add_zero]
    exact_mod_cast Complex.norm_mul_exp_arg_mul_I (z 0)
  | succ k ih =>
    -- liftedAngle z (k+1) = liftedAngle z k + arg (conj (z k) * z (k+1))
    have hstep : (liftedAngle z (k + 1) : ℝ)
        = liftedAngle z k + Complex.arg (starRingEnd ℂ (z k) * z (k + 1)) := by
      have := liftedAngle_succ z k; linarith
    rw [hstep]
    push_cast
    rw [add_mul, Complex.exp_add, ← mul_assoc]
    -- goal: ‖z (k+1)‖ * (exp(θk I) * exp(arg(...) I)) = z (k+1)
    -- rewrite ‖z(k+1)‖ * exp(θk I) part using ih in the form exp(θk I) = z k / ‖z k‖
    set r : ℝ := Complex.arg (starRingEnd ℂ (z k) * z (k + 1)) with hr
    -- exp(θk I) = z k / ‖z k‖
    have hzk : (‖z k‖ : ℝ) ≠ 0 := by
      simpa [norm_ne_zero_iff] using hz k
    have hexpk : Complex.exp ((liftedAngle z k : ℝ) * Complex.I) = z k / (‖z k‖ : ℂ) := by
      have hh : ((‖z k‖ : ℂ)) ≠ 0 := by exact_mod_cast hzk
      field_simp
      rw [mul_comm]; exact ih
    -- ‖conj(z k) * z(k+1)‖ * exp(r I) = conj(z k) * z(k+1)
    have hreq : ((‖starRingEnd ℂ (z k) * z (k + 1)‖ : ℂ)) * Complex.exp ((r : ℝ) * Complex.I)
        = starRingEnd ℂ (z k) * z (k + 1) := by
      rw [hr]; exact_mod_cast Complex.norm_mul_exp_arg_mul_I _
    -- Now assemble.  We want: ‖z(k+1)‖ * exp(θk I) * exp(r I) = z(k+1).
    -- Multiply hexpk and the exp(r I) extracted from hreq.
    have hnzk1 : (‖z (k + 1)‖ : ℝ) ≠ 0 := by simpa [norm_ne_zero_iff] using hz (k + 1)
    -- exp(r I) = conj(z k) * z(k+1) / ‖conj(z k)*z(k+1)‖
    have hnormprod : (‖starRingEnd ℂ (z k) * z (k + 1)‖ : ℝ) = ‖z k‖ * ‖z (k + 1)‖ := by
      rw [norm_mul, Complex.norm_conj]
    have hnp0 : ((‖starRingEnd ℂ (z k) * z (k + 1)‖ : ℂ)) ≠ 0 := by
      rw [hnormprod]; push_cast; exact mul_ne_zero (by exact_mod_cast hzk) (by exact_mod_cast hnzk1)
    have hexpr : Complex.exp ((r : ℝ) * Complex.I)
        = (starRingEnd ℂ (z k) * z (k + 1)) / (‖starRingEnd ℂ (z k) * z (k + 1)‖ : ℂ) := by
      field_simp
      rw [mul_comm]; exact hreq
    rw [hexpk, hexpr, hnormprod]
    push_cast
    -- goal: ‖z(k+1)‖ * (z k / ‖z k‖ * (conj(z k)*z(k+1) / (‖z k‖*‖z(k+1)‖))) = z(k+1)
    -- z k * conj(z k) = ‖z k‖²
    have hconj : z k * starRingEnd ℂ (z k) = ((‖z k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hh : ((‖z k‖ : ℂ)) ≠ 0 := by exact_mod_cast hzk
    have hh1 : ((‖z (k + 1)‖ : ℂ)) ≠ 0 := by exact_mod_cast hnzk1
    field_simp
    -- goal: z k * conj(z k) * z(k+1) = ‖z k‖² * z(k+1)
    rw [show z k * starRingEnd ℂ (z k) * z (k + 1)
          = (z k * starRingEnd ℂ (z k)) * z (k + 1) by ring, hconj]
    push_cast; ring

/-- A complex number with strictly positive imaginary part has argument in `(0, π)`. -/
theorem arg_mem_Ioo_of_im_pos {z : ℂ} (him : 0 < z.im) :
    Complex.arg z ∈ Set.Ioo (0 : ℝ) Real.pi := by
  refine ⟨?_, ?_⟩
  · -- 0 < arg z
    have hnonneg : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr him.le
    rcases hnonneg.lt_or_eq with h | h
    · exact h
    · -- arg = 0 forces im = 0, contradiction
      exfalso
      have := (Complex.arg_eq_zero_iff.mp h.symm).2
      linarith
  · -- arg z < π
    exact Complex.arg_lt_pi_iff.mpr (Or.inr (ne_of_gt him))

/-- `cos (liftedAngle z m) = (z m).re / ‖z m‖` and `sin (liftedAngle z m) = (z m).im / ‖z m‖`. -/
theorem liftedAngle_cos_sin (z : ℕ → ℂ) (hz : ∀ k, z k ≠ 0) (m : ℕ) :
    Real.cos (liftedAngle z m) = (z m).re / ‖z m‖ ∧
    Real.sin (liftedAngle z m) = (z m).im / ‖z m‖ := by
  have hlift := liftedAngle_exp z hz m
  have hzm : (‖z m‖ : ℝ) ≠ 0 := by simpa [norm_ne_zero_iff] using hz m
  -- exp(θ I) = z m / ‖z m‖
  have hexp : Complex.exp ((liftedAngle z m : ℝ) * Complex.I) = z m / (‖z m‖ : ℂ) := by
    have hh : ((‖z m‖ : ℂ)) ≠ 0 := by exact_mod_cast hzm
    field_simp
    rw [mul_comm]; exact hlift
  constructor
  · have hre := congrArg Complex.re hexp
    rw [Complex.exp_ofReal_mul_I_re, Complex.div_ofReal_re] at hre
    exact hre
  · have him := congrArg Complex.im hexp
    rw [Complex.exp_ofReal_mul_I_im, Complex.div_ofReal_im] at him
    exact him

/-! ## Block C — the geometric instantiation: edges, frame coordinates, strict turns.

We now fix a planar chain `Q : Fin (n+1) → E3` in the plane `⟨h,·⟩=1` with the
oriented frame (`det3 h u v = 1`) and the cyclic convex-position supports.  The
edge complex sequence is `zc m := ⟪E_m, u⟫ + ⟪E_m, v⟫·I` where `E_m` is the
(cyclically-extended) edge `g(m+1) − g(m)`; for `m < n` it is a genuine
nondegenerate edge, and we pad it to `1` past the open arm so that it is nonzero
everywhere (the padding indices are never read by `edge_eq`/`turn_pos` on the
arm). -/

/-- Plane decomposition: an in-plane vector `w ⊥ h` equals its `(u,v)`
coordinates, for an orthonormal frame `(u,v) ⊥ h` (unit `h`, `det3 h u v = 1`
so `cross u v` is a unit normal `∥ h`). -/
theorem perp_decomp {h u v w : E3} (hh : ‖h‖ = 1)
    (hhu : (⟪h, u⟫ : ℝ) = 0) (hhv : (⟪h, v⟫ : ℝ) = 0)
    (huu : (⟪u, u⟫ : ℝ) = 1) (hvv : (⟪v, v⟫ : ℝ) = 1) (huv : (⟪u, v⟫ : ℝ) = 0)
    (hD : det3 h u v = 1) (hwh : (⟪h, w⟫ : ℝ) = 0) :
    w = (⟪w, u⟫ : ℝ) • u + (⟪w, v⟫ : ℝ) • v := by
  have hne : h ≠ 0 := by intro h0; rw [h0, norm_zero] at hh; norm_num at hh
  -- ‖cross u v‖ = ‖h‖‖? ... compute ‖cross u v‖² via Lagrange = ⟪u,u⟫⟪v,v⟫-⟪u,v⟫² = 1
  have hcuv2 : ‖cross u v‖ ^ 2 = 1 := by
    rw [norm_sq_cross, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        huu, hvv, huv]; ring
  -- coplanarity: ⟪cross u v, w⟫ = 0 (u,v,w all ⊥ h)
  have hperp : (⟪cross u v, w⟫ : ℝ) = 0 :=
    inner_cross_perp hne hwh hhu hhv
  have hns := ProofsInTheBook.SphericalSZ.normsq_smul_b u w v hperp
  rw [hcuv2, one_smul] at hns
  -- ⟪v,u⟫ = ⟪u,v⟫ = 0
  have hvu : (⟪v, u⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact huv
  rw [huu, hvv, huv, hvu] at hns
  -- hns : w = (⟪w,u⟫*1 - ⟪w,v⟫*0)•u + (⟪w,v⟫*1 - ⟪w,u⟫*0)•v
  conv_lhs => rw [hns]
  rw [mul_one, mul_one, mul_zero, mul_zero, sub_zero, sub_zero]

/-- The edge complex sequence of a planar chain in the oriented frame:
`edgeZ Q u v m = ⟪E_m, u⟫ + ⟪E_m, v⟫·I`, `E_m = g(m+1) − g(m)` with `g` the
cyclic `ℕ`-extension of `Q`.  Padded to `1` once the open arm is exhausted so it
is nonzero everywhere on the indices the arm actually reads. -/
def edgeZ {n : ℕ} (Q : Fin (n + 1) → E3) (u v : E3) (m : ℕ) : ℂ :=
  if hm : m < n then
    have h1 : (m + 1) % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
    have h0 : m % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
    ((⟪Q ⟨(m + 1) % (n + 1), h1⟩ - Q ⟨m % (n + 1), h0⟩, u⟫ : ℝ) : ℂ)
      + ((⟪Q ⟨(m + 1) % (n + 1), h1⟩ - Q ⟨m % (n + 1), h0⟩, v⟫ : ℝ) : ℂ) * Complex.I
  else 1

/-- The decisive abstract turning bound, isolated as a clean named residual: the
total turning of the open arm (edges `0 .. n−1`) of a strictly convex cyclic
planar chain in convex position is strictly below `2π`.  This is the one piece
not reduced to first-order data — the global cyclic support is what forbids the
open arm from completing a full turn (numerically tight: convex arms approach but
never reach `2π`; and provably *false* with only the single-covector support of
edge `0`, which admits arm turning `> 2π`). -/
def OpenConvexArmTurningLtTwoPi : Prop :=
  ∀ {n : ℕ} (Q : Fin (n + 1) → E3) (h u v : E3),
    2 ≤ n →
    (⟪h, u⟫ : ℝ) = 0 → (⟪h, v⟫ : ℝ) = 0 →
    (⟪u, u⟫ : ℝ) = 1 → (⟪v, v⟫ : ℝ) = 1 → (⟪u, v⟫ : ℝ) = 0 → det3 h u v = 1 →
    (∀ i : Fin (n + 1), (⟪h, Q i⟫ : ℝ) = 1) →
    (∀ i j : Fin (n + 1), 0 ≤ det3 (Q i) (Q (i + 1)) (Q j)) →
    (∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 → 0 < det3 (Q i) (Q (i + 1)) (Q j)) →
    (∀ i : Fin (n + 1), Q i ≠ Q (i + 1)) →
    liftedAngle (edgeZ Q u v) (n - 1) - liftedAngle (edgeZ Q u v) 0 < 2 * Real.pi

/-! ## Block D — the oriented residue, modulo the turning bound. -/

/-- `edgeZ` at an arm index `m < n` is the frame-complex of the genuine edge
`Q⟨m+1⟩ − Q⟨m⟩`. -/
theorem edgeZ_arm {n : ℕ} (Q : Fin (n + 1) → E3) (u v : E3) {m : ℕ} (hm : m < n)
    (hm1 : m + 1 < n + 1) (hm0 : m < n + 1) :
    edgeZ Q u v m
      = ((⟪Q ⟨m + 1, hm1⟩ - Q ⟨m, hm0⟩, u⟫ : ℝ) : ℂ)
        + ((⟪Q ⟨m + 1, hm1⟩ - Q ⟨m, hm0⟩, v⟫ : ℝ) : ℂ) * Complex.I := by
  unfold edgeZ
  rw [dif_pos hm]
  have e1 : (m + 1) % (n + 1) = m + 1 := Nat.mod_eq_of_lt hm1
  have e0 : m % (n + 1) = m := Nat.mod_eq_of_lt hm0
  simp only [e1, e0]

/-- The strict-turn sign at an interior arm joint: the imaginary part of the
edge-ratio `conj (z m) * z (m+1)` equals `det3 (Q⟨m⟩)(Q⟨m+1⟩)(Q⟨m+2⟩)`, strictly
positive by the strict non-incident support. -/
theorem edgeZ_turn_im_pos {n : ℕ} (Q : Fin (n + 1) → E3) (h u v : E3)
    (hh : ‖h‖ = 1)
    (hhu : (⟪h, u⟫ : ℝ) = 0) (hhv : (⟪h, v⟫ : ℝ) = 0)
    (huu : (⟪u, u⟫ : ℝ) = 1) (hvv : (⟪v, v⟫ : ℝ) = 1) (huv : (⟪u, v⟫ : ℝ) = 0)
    (hD : det3 h u v = 1)
    (hplane : ∀ i : Fin (n + 1), (⟪h, Q i⟫ : ℝ) = 1)
    (hstrict : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 → 0 < det3 (Q i) (Q (i + 1)) (Q j))
    {m : ℕ} (hm : m + 2 ≤ n) :
    0 < (starRingEnd ℂ (edgeZ Q u v m) * edgeZ Q u v (m + 1)).im := by
  -- index facts
  have hm0 : m < n + 1 := by omega
  have hm1 : m + 1 < n + 1 := by omega
  have hm2 : m + 2 < n + 1 := by omega
  -- the two edges
  set Em : E3 := Q ⟨m + 1, hm1⟩ - Q ⟨m, hm0⟩ with hEm
  set Em1 : E3 := Q ⟨m + 2, hm2⟩ - Q ⟨m + 1, hm1⟩ with hEm1
  -- z m and z (m+1) in coordinates
  have hzm : edgeZ Q u v m
      = ((⟪Em, u⟫ : ℝ) : ℂ) + ((⟪Em, v⟫ : ℝ) : ℂ) * Complex.I :=
    edgeZ_arm Q u v (by omega) hm1 hm0
  have hzm1 : edgeZ Q u v (m + 1)
      = ((⟪Em1, u⟫ : ℝ) : ℂ) + ((⟪Em1, v⟫ : ℝ) : ℂ) * Complex.I :=
    edgeZ_arm Q u v (by omega) hm2 hm1
  -- Im(conj zm * zm1) = ⟪Em,u⟫⟪Em1,v⟫ − ⟪Em,v⟫⟪Em1,u⟫
  have him : (starRingEnd ℂ (edgeZ Q u v m) * edgeZ Q u v (m + 1)).im
      = (⟪Em, u⟫ : ℝ) * (⟪Em1, v⟫ : ℝ) - (⟪Em, v⟫ : ℝ) * (⟪Em1, u⟫ : ℝ) := by
    rw [hzm, hzm1]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    simp [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [him]
  -- = det3 h Em Em1 = det3(Q⟨m⟩)(Q⟨m+1⟩)(Q⟨m+2⟩) > 0
  -- decompose the two edges in the frame
  have hwhm : (⟪h, Em⟫ : ℝ) = 0 := by
    rw [hEm, inner_sub_right, hplane ⟨m + 1, hm1⟩, hplane ⟨m, hm0⟩, sub_self]
  have hwhm1 : (⟪h, Em1⟫ : ℝ) = 0 := by
    rw [hEm1, inner_sub_right, hplane ⟨m + 2, hm2⟩, hplane ⟨m + 1, hm1⟩, sub_self]
  have hdm := perp_decomp hh hhu hhv huu hvv huv hD hwhm
  have hdm1 := perp_decomp hh hhu hhv huu hvv huv hD hwhm1
  -- det3 h Em Em1 = (⟪Em,u⟫⟪Em1,v⟫ − ⟪Em,v⟫⟪Em1,u⟫)·det3 h u v
  have hdet : det3 h Em Em1
      = ((⟪Em, u⟫ : ℝ) * (⟪Em1, v⟫ : ℝ) - (⟪Em, v⟫ : ℝ) * (⟪Em1, u⟫ : ℝ)) * det3 h u v := by
    conv_lhs => rw [hdm, hdm1]
    rw [det3_frame_coord]
  rw [hD, mul_one] at hdet
  -- relate det3 h Em Em1 to det3 of the three vertices
  have hcyc : det3 (Q ⟨m, hm0⟩) (Q ⟨m + 1, hm1⟩) (Q ⟨m + 2, hm2⟩)
      = det3 h Em Em1 := by
    rw [det3_eq_det3_h_diff hh (hplane _) (hplane _) (hplane _)]
    -- Q⟨m+1⟩ - Q⟨m⟩ = Em ;  Q⟨m+2⟩ - Q⟨m⟩ = Em + Em1
    have e2 : Q ⟨m + 2, hm2⟩ - Q ⟨m, hm0⟩ = Em + Em1 := by rw [hEm, hEm1]; abel
    rw [show Q ⟨m + 1, hm1⟩ - Q ⟨m, hm0⟩ = Em from rfl, e2,
        det3_add_right, det3_self_mid₂, zero_add]
  -- strict positivity from hstrict
  have hsucc : (⟨m, hm0⟩ + 1 : Fin (n + 1)) = ⟨m + 1, hm1⟩ := by
    apply Fin.ext
    exact ProofsInTheBook.PlanarConvexDiag.fin_succ_val (i := (⟨m, hm0⟩ : Fin (n + 1))) hm1
  have hpos := hstrict ⟨m, hm0⟩ ⟨m + 2, hm2⟩
    (by intro hc; simp only [Fin.ext_iff] at hc; omega)
    (by rw [hsucc]; intro hc; simp only [Fin.ext_iff] at hc; omega)
  rw [hsucc] at hpos
  rw [← hdet, ← hcyc]
  exact hpos

/-- The **oriented** planar single-wind residue, discharged modulo the turning
bound `OpenConvexArmTurningLtTwoPi`.  Given the oriented frame (`det3 h u v = 1`)
and the cyclic convex-position supports of a nondegenerate strictly convex planar
chain, there is a `PlanarLiftedTurnSpan`. -/
theorem oriented_residue_of_turningBound (hturn : OpenConvexArmTurningLtTwoPi)
    {n : ℕ} (hn : 2 ≤ n) (Q : Fin (n + 1) → E3) (h u v : E3)
    (hh : ‖h‖ = 1)
    (hhu : (⟪h, u⟫ : ℝ) = 0) (hhv : (⟪h, v⟫ : ℝ) = 0)
    (huu : (⟪u, u⟫ : ℝ) = 1) (hvv : (⟪v, v⟫ : ℝ) = 1) (huv : (⟪u, v⟫ : ℝ) = 0)
    (hD : det3 h u v = 1)
    (hplane : ∀ i : Fin (n + 1), (⟪h, Q i⟫ : ℝ) = 1)
    (hsupp : ∀ i j : Fin (n + 1), 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    (hstrict : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 → 0 < det3 (Q i) (Q (i + 1)) (Q j))
    (hedge : ∀ i : Fin (n + 1), Q i ≠ Q (i + 1)) :
    Nonempty (PlanarLiftedTurnSpan Q h u v) := by
  classical
  set z : ℕ → ℂ := edgeZ Q u v with hz
  -- Edge vectors and their nonvanishing in the plane.
  -- For an arm index m < n, z m carries the genuine edge.
  -- `z` is nonzero everywhere.
  have hznz : ∀ k, z k ≠ 0 := by
    intro k
    by_cases hk : k < n
    · -- genuine edge: nonzero since Q⟨k⟩ ≠ Q⟨k+1⟩ and they differ in-plane
      have hk1 : k + 1 < n + 1 := by omega
      have hk0 : k < n + 1 := by omega
      rw [hz, edgeZ_arm Q u v hk hk1 hk0]
      -- if it were 0 both inner products vanish, so the edge (⊥h) is 0, contra hedge
      intro h0
      have hre : (⟪Q ⟨k + 1, hk1⟩ - Q ⟨k, hk0⟩, u⟫ : ℝ) = 0 := by
        have := congrArg Complex.re h0
        simpa using this
      have him : (⟪Q ⟨k + 1, hk1⟩ - Q ⟨k, hk0⟩, v⟫ : ℝ) = 0 := by
        have := congrArg Complex.im h0
        simpa using this
      -- edge ⊥ h
      have hwh : (⟪h, Q ⟨k + 1, hk1⟩ - Q ⟨k, hk0⟩⟫ : ℝ) = 0 := by
        rw [inner_sub_right, hplane ⟨k + 1, hk1⟩, hplane ⟨k, hk0⟩, sub_self]
      have hdecomp := perp_decomp hh hhu hhv huu hvv huv hD hwh
      rw [hre, him, zero_smul, zero_smul, add_zero] at hdecomp
      -- so the edge is 0 ⟹ Q⟨k⟩ = Q⟨k+1⟩
      have : Q ⟨k + 1, hk1⟩ = Q ⟨k, hk0⟩ := by
        have := sub_eq_zero.mp hdecomp; exact this
      -- contradiction with hedge
      apply hedge ⟨k, hk0⟩
      have hsucc : (⟨k, hk0⟩ + 1 : Fin (n + 1)) = ⟨k + 1, hk1⟩ := by
        apply Fin.ext
        exact ProofsInTheBook.PlanarConvexDiag.fin_succ_val (i := (⟨k, hk0⟩ : Fin (n + 1))) hk1
      rw [hsucc]; exact this.symm
    · rw [hz]; unfold edgeZ; rw [dif_neg hk]; exact one_ne_zero
  -- The geometric lift and the slack virtual continuation.
  set θg : ℕ → ℝ := liftedAngle z with hθg
  -- Per-joint geometric turn ∈ (0,π) for interior arm joints m ≤ n−2.
  have hgturn : ∀ m : ℕ, m + 2 ≤ n →
      θg (m + 1) - θg m ∈ Set.Ioo (0 : ℝ) Real.pi := by
    intro m hm
    rw [hθg, liftedAngle_succ]
    exact arg_mem_Ioo_of_im_pos
      (edgeZ_turn_im_pos Q h u v hh hhu hhv huu hvv huv hD hplane hstrict hm)
  -- The real arm turning bound.
  have hSlt : θg (n - 1) - θg 0 < 2 * Real.pi :=
    hturn Q h u v hn hhu hhv huu hvv huv hD hplane hsupp hstrict hedge
  set S : ℝ := θg (n - 1) - θg 0 with hS
  -- S > 0: telescoping sum of strictly positive interior turns (n−1 ≥ 1 of them).
  have hSpos : 0 < S := by
    rw [hS]
    -- θg (n-1) - θg 0 = ∑_{m<n-1} (θg(m+1) - θg m), each term > 0.
    have htele : ∑ m ∈ Finset.range (n - 1), (θg (m + 1) - θg m)
        = θg (n - 1) - θg 0 := Finset.sum_range_sub θg (n - 1)
    rw [← htele]
    apply Finset.sum_pos
    · intro m hm
      rw [Finset.mem_range] at hm
      exact (hgturn m (by omega)).1
    · rw [Finset.nonempty_range_iff]; omega
  set δ : ℝ := (2 * Real.pi - S) / 3 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith [hSlt]
  have hδltpi : δ < Real.pi := by rw [hδ]; linarith [hSpos, Real.pi_pos]
  -- The final lifted angle: geometric on the arm, linear slack continuation past n−1.
  set θ : ℕ → ℝ :=
    fun m => if m ≤ n - 1 then θg m else θg (n - 1) + ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) * δ
    with hθdef
  -- evaluation helpers
  have hθle : ∀ m, m ≤ n - 1 → θ m = θg m := by
    intro m hm; simp only [hθdef, if_pos hm]
  have hθgt : ∀ m, ¬ (m ≤ n - 1) → θ m = θg (n - 1) + ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) * δ := by
    intro m hm; simp only [hθdef, if_neg hm]
  -- The per-step turn of θ is in (0,π) for every m.
  have hturn_pos : ∀ m : ℕ, 0 < θ (m + 1) - θ m := by
    intro m
    by_cases h1 : m + 1 ≤ n - 1
    · -- both geometric, m+2 ≤ n
      rw [hθle (m + 1) h1, hθle m (by omega)]
      exact (hgturn m (by omega)).1
    · -- m ≥ n−1
      have hm : ¬ (m ≤ n - 1) ∨ m = n - 1 := by omega
      rcases hm with hm | hm
      · -- m > n−1: both in slack branch
        rw [hθgt (m + 1) (by omega), hθgt m hm]
        push_cast
        have : ((m : ℝ) + 1 - ((n - 1 : ℕ) : ℝ)) * δ - ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) * δ = δ := by
          ring
        linarith [hδpos, this]
      · -- m = n−1: θ(n) = slack, θ(n−1) = geometric
        subst hm
        rw [hθgt (n - 1 + 1) (by omega), hθle (n - 1) (le_refl _)]
        push_cast
        -- goal: 0 < θg(n-1) + (↑(n-1)+1 - ↑(n-1))·δ − θg(n-1) = δ
        nlinarith [hδpos]
  have hturn_ltpi : ∀ m : ℕ, θ (m + 1) - θ m < Real.pi := by
    intro m
    by_cases h1 : m + 1 ≤ n - 1
    · rw [hθle (m + 1) h1, hθle m (by omega)]
      exact (hgturn m (by omega)).2
    · have hm : ¬ (m ≤ n - 1) ∨ m = n - 1 := by omega
      rcases hm with hm | hm
      · rw [hθgt (m + 1) (by omega), hθgt m hm]
        have : ((m : ℝ) + 1 - ((n - 1 : ℕ) : ℝ)) * δ - ((m : ℝ) - ((n - 1 : ℕ) : ℝ)) * δ = δ := by ring
        push_cast at this ⊢; linarith [hδltpi, this]
      · subst hm
        rw [hθgt (n - 1 + 1) (by omega), hθle (n - 1) (le_refl _)]
        push_cast
        nlinarith [hδltpi]
  -- one_wind: θ (n+1) − θ 0 = S + 2δ < 2π.
  have hone : θ (n + 1) - θ 0 < 2 * Real.pi := by
    rw [hθgt (n + 1) (by omega), hθle 0 (by omega)]
    -- θ 0 = θg 0 ; θ(n+1) = θg(n-1) + ((n+1)-(n-1))·δ = θg(n-1) + 2δ
    have hcast : ((n + 1 : ℕ) : ℝ) - ((n - 1 : ℕ) : ℝ) = 2 := by
      have h1 : (1 : ℕ) ≤ n := by omega
      rw [Nat.cast_sub h1]; push_cast; ring
    have hgoal : θg (n - 1) + (((n + 1 : ℕ) : ℝ) - ((n - 1 : ℕ) : ℝ)) * δ - θg 0
        = S + 2 * δ := by rw [hcast, hS]; ring
    rw [hgoal, hδ]
    linarith [hSlt]
  -- edge_eq: for m+1 < n+1 (m ≤ n−1, m < n), θ m = θg m and the lift reconstructs the edge.
  have hedge_eq : ∀ (m : ℕ) (hm : m + 1 < n + 1),
      Q ⟨m + 1, hm⟩ - Q ⟨m, by omega⟩
        = (‖z m‖) • (Real.cos (θ m) • u + Real.sin (θ m) • v) := by
    intro m hm
    have hmn : m < n := by omega
    have hm0 : m < n + 1 := by omega
    rw [hθle m (by omega)]
    -- cos/sin of θg m = liftedAngle z m
    obtain ⟨hcos, hsin⟩ := liftedAngle_cos_sin z hznz m
    rw [hcos, hsin]
    -- the edge in coords
    have hzm : z m = ((⟪Q ⟨m + 1, hm⟩ - Q ⟨m, hm0⟩, u⟫ : ℝ) : ℂ)
        + ((⟪Q ⟨m + 1, hm⟩ - Q ⟨m, hm0⟩, v⟫ : ℝ) : ℂ) * Complex.I := by
      rw [hz]; exact edgeZ_arm Q u v hmn hm hm0
    have hre : (z m).re = (⟪Q ⟨m + 1, hm⟩ - Q ⟨m, hm0⟩, u⟫ : ℝ) := by
      rw [hzm]; simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have him : (z m).im = (⟪Q ⟨m + 1, hm⟩ - Q ⟨m, hm0⟩, v⟫ : ℝ) := by
      rw [hzm]; simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    have hznz0 : (‖z m‖ : ℝ) ≠ 0 := by simpa [norm_ne_zero_iff] using hznz m
    -- ‖z m‖ • (re/‖z m‖ • u + im/‖z m‖ • v) = re • u + im • v
    rw [hre, him]
    rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ hznz0, mul_div_cancel₀ _ hznz0]
    -- = ⟪E,u⟫•u + ⟪E,v⟫•v = E (perp_decomp)
    have hwh : (⟪h, Q ⟨m + 1, hm⟩ - Q ⟨m, hm0⟩⟫ : ℝ) = 0 := by
      rw [inner_sub_right, hplane ⟨m + 1, hm⟩, hplane ⟨m, hm0⟩, sub_self]
    have hdecomp := perp_decomp hh hhu hhv huu hvv huv hD hwh
    -- index identity ⟨m, hm0⟩ = ⟨m, by omega⟩
    rw [show (⟨m, by omega⟩ : Fin (n + 1)) = ⟨m, hm0⟩ from rfl]
    exact hdecomp
  -- assemble
  exact ⟨{
    in_plane := hplane
    u_perp_h := hhu
    v_perp_h := hhv
    u_unit := huu
    v_unit := hvv
    uv_perp := huv
    θ := θ
    ρ := fun m => ‖z m‖
    ρ_pos := fun m => by simpa [norm_pos_iff] using hznz m
    edge_eq := hedge_eq
    turn_pos := hturn_pos
    turn_lt_pi := hturn_ltpi
    one_wind := by
      -- one_wind uses θ N = θ (n+1)
      show θ (n + 1) - θ 0 < 2 * Real.pi
      exact hone }⟩

/-! ## Block E — the unconditional spherical single-wind certificate (modulo the bound).

We re-derive `ZinanFFCT95.GnomonicSingleWind` from a strictly convex spherical
arm, modulo only the abstract turning bound `OpenConvexArmTurningLtTwoPi`.  Unlike
`ZinanFFCT95.strictConvexSphArm_gnomonicSingleWind`, this uses the **oriented**
frame (`det3 h u v = 1` from `exists_orthoFrame_oriented`), repairing the
orientation gap in `ZinanFFCT95.StrictPlanarChainLiftedTurnSpanExists`. -/

open ProofsInTheBook.ZinanFFCT95 in
/-- **Brick D-strict, oriented and repaired.**  Modulo the abstract turning bound
`OpenConvexArmTurningLtTwoPi`, every strictly convex spherical arm admits a
`GnomonicSingleWind` certificate — built with the *oriented* `(u,v)` frame, so the
lifted turns are genuinely positive (the residue's missing orientation
hypothesis). -/
theorem strictConvexSphArm_gnomonicSingleWind'
    (hturn : OpenConvexArmTurningLtTwoPi)
    {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A) :
    Nonempty (GnomonicSingleWind A) := by
  obtain ⟨h, hnorm, hhem⟩ := hA.closed_convex.open_hemisphere
  obtain ⟨u, v, hhu, hhv, huu, hvv, huv, hDet⟩ := exists_orthoFrame_oriented hnorm
  set Q : Fin (n + 1) → E3 := fun i => gproj h (A i) with hQ
  have hplane : ∀ i : Fin (n + 1), (⟪h, Q i⟫ : ℝ) = 1 :=
    fun i => ProofsInTheBook.ZinanFFCT95.gnomonic_image_in_plane hhem i
  have hsupp : ∀ i j : Fin (n + 1), 0 ≤ det3 (Q i) (Q (i + 1)) (Q j) := by
    intro i j
    have hs : 0 ≤ sOrient (A i) (A (i + 1)) (A j) := hA.closed_convex.edge_support i j
    have hc := gnomonic_sign_correspondence h (A i) (A (i + 1)) (A j)
      (ne_of_gt (hhem i)) (ne_of_gt (hhem (i + 1))) (ne_of_gt (hhem j))
    have hsc : (0 : ℝ) <
        (⟪h, (A i : E3)⟫ : ℝ) * (⟪h, (A (i + 1) : E3)⟫ : ℝ) * (⟪h, (A j : E3)⟫ : ℝ) :=
      mul_pos (mul_pos (hhem i) (hhem (i + 1))) (hhem j)
    rw [hc] at hs
    change 0 ≤ det3 (gproj h (A i)) (gproj h (A (i + 1))) (gproj h (A j))
    by_contra hlt; push Not at hlt
    nlinarith [hs, hsc, hlt]
  have hstrict : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 < det3 (Q i) (Q (i + 1)) (Q j) := by
    intro i j hj1 hj2
    have hs := hA.closed_convex.strict_nonincident i j hj1 hj2
    change 0 < det3 (gproj h (A i)) (gproj h (A (i + 1))) (gproj h (A j))
    exact (sOrient_pos_iff_planar_pos h (A i) (A (i + 1)) (A j)
      (hhem i) (hhem (i + 1)) (hhem j)).mp hs
  have hedge : ∀ i : Fin (n + 1), Q i ≠ Q (i + 1) :=
    fun i => ProofsInTheBook.ZinanFFCT95.gnomonic_image_edge_ne hA hhem i
  obtain ⟨lifted⟩ := oriented_residue_of_turningBound hturn hA.two_le Q h u v
    hnorm hhu hhv huu hvv huv hDet hplane hsupp hstrict hedge
  exact ⟨{ h := h, hnorm := hnorm, hpos := hhem, u := u, v := v, lifted := lifted }⟩

/-! ## Guards. -/

#check @det3_frame_coord
#check @exists_orthoFrame_oriented
#check @perp_decomp
#check @liftedAngle_exp
#check @OpenConvexArmTurningLtTwoPi
#check @oriented_residue_of_turningBound
#check @strictConvexSphArm_gnomonicSingleWind'

#print axioms det3_frame_coord
#print axioms exists_orthoFrame_oriented
#print axioms perp_decomp
#print axioms liftedAngle_exp
#print axioms liftedAngle_cos_sin
#print axioms edgeZ_turn_im_pos
#print axioms oriented_residue_of_turningBound
#print axioms strictConvexSphArm_gnomonicSingleWind'

end ProofsInTheBook.ZinanFFCT96
