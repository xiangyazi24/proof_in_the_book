import ProofsInTheBook.ZinanFFCT8
import ProofsInTheBook.SphericalRotation

/-!
# `ZinanFFCT9` — the LOCAL oriented-angle branch cut for the Ch13 planar kernel

`ZinanFFCT8` isolated the Ch13 kernel as the purely-planar `det3` predicate
`PlanarWeakNoflatStrictEdge`.  Prior routes (syzygy / gnomonic / supporting-line) all stalled on the
*circular* gap-1 bootstrap, whose only escape is a monotone polar-angle ordering — which the syzygy
and the integer turning-number routes both needed and the substrate genuinely lacked.

This file builds that ordering through a **single local branch, with NO integer turning-number lift**,
and proves it unconditionally.  Fix the apex `a = f i` and the base direction `b = f (i+1) − f i`.
Every vertex, viewed from `a`, lies in the closed half-plane `det3 (f i)(f (i+1))(f m) ≥ 0` (the weak
edge support of the base edge).  That single `≥ 0` side pins the polar angle
`theta b ρ := arccos (⟪b, ρ⟫ / (‖b‖ ‖ρ‖))` to the branch `[0, π]` — where `arccos` is a genuine
total order with no `2π` ambiguity, so no winding lift is needed.

## What is proved here UNCONDITIONALLY (axioms `{propext, Classical.choice, Quot.sound}`)

* **§0** — the planar area-form algebra natively on the kernel `det3` and the `E3` inner product:
  `det3_apex_transport`, `det3h_sq` (the `sin²+cos²` identity), `det3_areaform_sub`, `cos_add_id`
  (cosine addition), `sin_add_id` (sine addition).
* **§1** — `mono_abstract`, the route's crux, the pure identity
  `(cp − cq)(1 + cpq) = spq (sp + sq)`, and its geometric instances `mono_ncos`, **`mono_theta`**:
  the polar angle is monotone along the weak-supported arm when the consecutive turn is not antipodal.
  This is the single ingredient the circular bootstrap lacked, and it carries NO integer lift.
* **§2–§4** — the branch-cut squeeze and its strict-support consequence: `branch_squeeze_theta_ne_zero`
  (a vanishing forward support would return the monotone angle to the base ray, contradicting the
  no-flat joint), `det3_pos_of_theta_mem` (strict support from `theta ∈ (0, π)`).
* **§5** — `forward_strict_support`: strict edge support for the forward chain, assembled from the
  squeeze and the angle ordering, **modulo the single antipodal care-point** `theta b ρ ≠ π`.

## The precise remaining blocker (premise-respecting, isolated, NOT faked)

The angle ordering provides `theta ≠ 0` (the collinear-forward case) *unconditionally*.  The one
residual care-point is `theta b ρ ≠ π`: a non-incident vertex antipodal to the base ray (`f i`
strictly between `f (i+1)` and `f j` on a line).  On the sphere this is excluded by the
*one-open-hemisphere* / *short-arc* data the Cauchy vertex link carries; the **purely planar**
predicate `PlanarWeakNoflatStrictEdge` (weak convexity + no-flat only) does not carry that datum, so
the antipodal exclusion is not derivable inside the abstract predicate as stated.  It is therefore
isolated, exactly, as the hypotheses `hcons` (consecutive non-antipodal) and `hnotanti`
(`theta ≠ π`) of `forward_strict_support` — one named, non-vacuous, purely-planar care-point, not
faked.  (The full cyclic strict-support assembly of `PlanarWeakNoflatStrictEdge` then needs, in
addition, the symmetric backward chain and the arm-wrap index bookkeeping, all driven by the same
proven `mono_theta`.)

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section
open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalConeMembership
open ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.ZinanFFCT8

namespace ProofsInTheBook.ZinanFFCT9

set_option maxHeartbeats 1600000

/-! ## §0. Cross-product / `det3` plane algebra (the 2D area-form identities, native on `E3`). -/

/-- `det3 a b c = ⟪a, b ×₃ c⟫`. -/
theorem det3_eq_inner_cross (a u v : E3) : det3 a u v = (⟪a, cross u v⟫ : ℝ) :=
  (inner_cross_eq_det3 a u v).symm

theorem cross_sub_right' (a b c : E3) : cross a (b - c) = cross a b - cross a c := by
  rw [sub_eq_add_neg, cross_add_right, sub_eq_add_neg]
  congr 1
  rw [show (-c) = (-1:ℝ) • c by module, cross_smul_right]; module

/-- For `u, v ⊥ h`, the cross product `u ×₃ v` is parallel to `h`: `h ×₃ (u ×₃ v) = 0`. -/
theorem cross_h_cross {h u v : E3} (hu : (⟪h, u⟫ : ℝ) = 0) (hv : (⟪h, v⟫ : ℝ) = 0) :
    cross h (cross u v) = 0 := by
  rw [cross_cross, hu, hv]; simp

/-- `⟪a, u×v⟫ • h = ⟪a, h⟫ • (u×v)` for `u, v ⊥ h`: the parallelism `u×v ∥ h`, scalarised. -/
theorem apex_parallel {h u v a : E3} (hu : (⟪h, u⟫ : ℝ) = 0) (hv : (⟪h, v⟫ : ℝ) = 0) :
    (⟪a, cross u v⟫ : ℝ) • h = (⟪a, h⟫ : ℝ) • cross u v := by
  have h0 : cross h (cross u v) = 0 := cross_h_cross hu hv
  have key : cross a (cross h (cross u v)) = (⟪a, cross u v⟫ : ℝ) • h - (⟪a, h⟫ : ℝ) • cross u v :=
    cross_cross a h (cross u v)
  rw [h0] at key
  rw [show cross a (0:E3) = 0 from by
    have := cross_smul_right 0 a (0:E3); simpa using this] at key
  linear_combination (norm := module) -key

/-- **Apex transport.**  `det3 a u v · ‖h‖² = ⟪a, h⟫ · det3 h u v` for `u, v ⊥ h`.  This carries the
sign of the planar `det3` (apex `a`) to the fixed-normal area form `det3 h ··`. -/
theorem det3_apex_transport {h u v a : E3} (hu : (⟪h, u⟫ : ℝ) = 0) (hv : (⟪h, v⟫ : ℝ) = 0) :
    det3 a u v * ‖h‖^2 = (⟪a, h⟫ : ℝ) * det3 h u v := by
  have hp := apex_parallel (h := h) (u := u) (v := v) (a := a) hu hv
  have hc := congrArg (fun w => (⟪h, w⟫ : ℝ)) hp
  simp only [inner_smul_right] at hc
  rw [real_inner_self_eq_norm_sq] at hc
  rw [← inner_cross_eq_det3, ← inner_cross_eq_det3]; exact hc

/-- Lagrange: `‖u×v‖² = ‖u‖²‖v‖² − ⟪u,v⟫²`. -/
theorem norm_cross_sq (u v : E3) :
    (⟪cross u v, cross u v⟫ : ℝ) = ‖u‖^2 * ‖v‖^2 - (⟪u, v⟫:ℝ)^2 := by
  rw [inner_cross_cross, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm v u]; ring

/-- **`sin² + cos²` (area form).**  `(det3 h u v)² = ‖h‖²(‖u‖²‖v‖² − ⟪u,v⟫²)` for `u, v ⊥ h`. -/
theorem det3h_sq {h u v : E3} (hu : (⟪h, u⟫ : ℝ) = 0) (hv : (⟪h, v⟫ : ℝ) = 0) :
    (det3 h u v)^2 = ‖h‖^2 * (‖u‖^2 * ‖v‖^2 - (⟪u, v⟫:ℝ)^2) := by
  have hp := apex_parallel (h := h) (u := u) (v := v) (a := h) hu hv
  rw [real_inner_self_eq_norm_sq, inner_cross_eq_det3] at hp
  have hn := congrArg (fun w => (⟪w, w⟫ : ℝ)) hp
  simp only [inner_smul_left, inner_smul_right, conj_trivial] at hn
  rw [real_inner_self_eq_norm_sq, norm_cross_sq] at hn
  rcases eq_or_lt_of_le (sq_nonneg ‖h‖) with he | hpos
  · have hh0 : h = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg h])
    subst hh0; simp [det3]
  · nlinarith [hn, hpos]

/-- **Decomposition identity (areaform-sub).**  `⟪b,p⟫·det3 h b q − det3 h b p·⟪b,q⟫ = ‖b‖²·det3 h p q`
for `b ⊥ h`. -/
theorem det3_areaform_sub {h b p q : E3} (hb : (⟪h,b⟫:ℝ)=0) :
    (⟪b,p⟫:ℝ) * det3 h b q - det3 h b p * (⟪b,q⟫:ℝ) = ‖b‖^2 * det3 h p q := by
  have vecid : (⟪b,q⟫:ℝ) • cross b p - (⟪b,p⟫:ℝ) • cross b q
      = (⟪b, cross p q⟫:ℝ) • b - (‖b‖^2:ℝ) • cross p q := by
    have e1 : cross b (cross p q) = (⟪b,q⟫:ℝ) • p - (⟪b,p⟫:ℝ) • q := cross_cross b p q
    have e2 := SphericalRotation.cross_cross b b (cross p q)
    rw [real_inner_self_eq_norm_sq] at e2
    have e3 : cross b ((⟪b,q⟫:ℝ) • p - (⟪b,p⟫:ℝ) • q)
        = (⟪b,q⟫:ℝ) • cross b p - (⟪b,p⟫:ℝ) • cross b q := by
      rw [cross_sub_right', cross_smul_right, cross_smul_right]
    rw [← e1] at e3; rw [e3] at e2; exact e2
  have hkey := congrArg (fun w => (⟪h, w⟫ : ℝ)) vecid
  simp only [inner_sub_right, inner_smul_right] at hkey
  rw [inner_cross_eq_det3, inner_cross_eq_det3, inner_cross_eq_det3] at hkey
  rw [hb, mul_zero, zero_sub, inner_cross_eq_det3] at hkey
  linarith [hkey]

/-- `⟪w, p×q⟫ · ‖h‖² = ⟪h, p×q⟫ · ⟪w, h⟫` for `p, q ⊥ h`. -/
theorem inner_cross_pq {h p q w : E3} (hp : (⟪h,p⟫:ℝ)=0) (hq : (⟪h,q⟫:ℝ)=0) :
    (⟪w, cross p q⟫:ℝ) * ‖h‖^2 = (⟪h, cross p q⟫:ℝ) * (⟪w, h⟫:ℝ) := by
  have hp2 := apex_parallel (h:=h) (u:=p) (v:=q) (a:=w) hp hq
  have hc := congrArg (fun z => (⟪z, h⟫ : ℝ)) hp2
  simp only [inner_smul_left, conj_trivial] at hc
  rw [real_inner_self_eq_norm_sq] at hc
  have hcc : (⟪cross p q, h⟫:ℝ) = (⟪h, cross p q⟫:ℝ) := real_inner_comm _ _
  rw [hcc] at hc; linarith [hc]

/-- **Cosine-addition identity.**  `⟪b,q⟫·‖p‖²·‖h‖² = ⟪b,p⟫·⟪p,q⟫·‖h‖² − det3 h b p·det3 h p q`
for `p, q ⊥ h`.  (The `cos` of the sum equals `cos cos − sin sin`.) -/
theorem cos_add_id {h b p q : E3} (hp : (⟪h,p⟫:ℝ)=0) (hq : (⟪h,q⟫:ℝ)=0) :
    (⟪b,q⟫:ℝ) * ‖p‖^2 * ‖h‖^2
      = (⟪b,p⟫:ℝ) * (⟪p,q⟫:ℝ) * ‖h‖^2 - det3 h b p * det3 h p q := by
  have hbc := inner_cross_cross b p p q
  rw [real_inner_self_eq_norm_sq] at hbc
  have hpar := inner_cross_pq (h:=h) (p:=p) (q:=q) (w := cross b p) hp hq
  rw [hbc] at hpar
  have e1 : (⟪h, cross p q⟫:ℝ) = det3 h p q := inner_cross_eq_det3 h p q
  have e2 : (⟪cross b p, h⟫:ℝ) = det3 h b p := by
    have hcm : (⟪cross b p, h⟫:ℝ) = (⟪h, cross b p⟫:ℝ) := real_inner_comm _ _
    rw [hcm]; exact inner_cross_eq_det3 h b p
  rw [e1, e2] at hpar
  nlinarith [hpar]

/-- **Sine-addition identity.**  `‖p‖²·det3 h b q = ⟪b,p⟫·det3 h p q + det3 h b p·⟪p,q⟫`
for `p ⊥ h`.  (The `sin` of the sum equals `sin cos + cos sin`.) -/
theorem sin_add_id {h b p q : E3} (hp : (⟪h,p⟫:ℝ)=0) :
    ‖p‖^2 * det3 h b q = (⟪b,p⟫:ℝ) * det3 h p q + det3 h b p * (⟪p,q⟫:ℝ) := by
  have hI2 := det3_areaform_sub (h:=h) (b:=p) (p:=b) (q:=q) hp
  -- hI2 : ⟪p,b⟫·det3 h p q − det3 h p b·⟪p,q⟫ = ‖p‖²·det3 h b q
  rw [det3_swap_right h p b] at hI2
  have hcm : (⟪p,b⟫:ℝ) = (⟪b,p⟫:ℝ) := real_inner_comm _ _
  rw [hcm] at hI2
  linarith [hI2]


/-! ## §1. The polar-angle layer (apex-local branch cut). -/

/-- Normalised cosine of the angle from `b` to `p` (at the apex). -/
def ncos (b p : E3) : ℝ := (⟪b,p⟫:ℝ) / (‖b‖ * ‖p‖)

/-- Normalised sine, oriented by `h` (`≥ 0` on the weak-support side). -/
def nsin (h b p : E3) : ℝ := det3 h b p / (‖b‖ * ‖p‖ * ‖h‖)

/-- The polar angle, valued in `[0, π]` (the single branch). -/
def theta (b p : E3) : ℝ := Real.arccos (ncos b p)

theorem ncos_mem {b p : E3} (hb : b ≠ 0) (hp : p ≠ 0) : ncos b p ∈ Set.Icc (-1:ℝ) 1 := by
  have hbp : |(⟪b,p⟫:ℝ)| ≤ ‖b‖ * ‖p‖ := abs_real_inner_le_norm b p
  have hbpos : 0 < ‖b‖ * ‖p‖ := mul_pos (norm_pos_iff.mpr hb) (norm_pos_iff.mpr hp)
  rw [abs_le] at hbp
  refine ⟨?_, ?_⟩
  · rw [ncos, le_div_iff₀ hbpos]; linarith [hbp.1]
  · rw [ncos, div_le_iff₀ hbpos]; linarith [hbp.2]

theorem cos_theta {b p : E3} (hb : b ≠ 0) (hp : p ≠ 0) :
    Real.cos (theta b p) = ncos b p := by
  rw [theta, Real.cos_arccos (ncos_mem hb hp).1 (ncos_mem hb hp).2]

/-- `nsin ≥ 0` from the weak support `det3 h b p ≥ 0`. -/
theorem nsin_nonneg {h b p : E3} (hb : b ≠ 0) (hp : p ≠ 0) (hh : h ≠ 0)
    (hsupp : 0 ≤ det3 h b p) : 0 ≤ nsin h b p := by
  rw [nsin]
  apply div_nonneg hsupp
  positivity

/-- `ncos² + nsin² = 1` (the branch identity), for `b,p ⊥ h` nonzero, `h ≠ 0`. -/
theorem ncos_sq_add_nsin_sq {h b p : E3} (hb0 : (⟪h,b⟫:ℝ)=0) (hp0 : (⟪h,p⟫:ℝ)=0)
    (hb : b ≠ 0) (hp : p ≠ 0) (hh : h ≠ 0) :
    (ncos b p)^2 + (nsin h b p)^2 = 1 := by
  have hbn : (0:ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hpn : (0:ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  have hhn : (0:ℝ) < ‖h‖ := norm_pos_iff.mpr hh
  have hsq := det3h_sq (h:=h) (u:=b) (v:=p) hb0 hp0
  rw [ncos, nsin, div_pow, div_pow, hsq]
  rw [div_add_div _ _ (by positivity) (by positivity)]
  rw [div_eq_one_iff_eq (by positivity)]
  ring

/-- **Abstract angle-addition monotonicity.**  With all three sines `≥ 0` and the consecutive turn
not antipodal (`-1 < cpq`), `cos` of the sum is `≤ cos` of the first angle.  This is the route's
single branch-cut crux, proved through the pure identity
`(cp − cq)(1 + cpq) = spq (sp + sq)`. -/
theorem mono_abstract
    (cp sp cpq spq cq sq : ℝ)
    (hsp : 0 ≤ sp) (hspq : 0 ≤ spq) (hsq : 0 ≤ sq)
    (hpq1 : cpq^2 + spq^2 = 1)
    (hC : cq = cp*cpq - sp*spq) (hS : sq = sp*cpq + cp*spq)
    (hnotanti : -1 < cpq) :
    cq ≤ cp := by
  have hkey : (cp - cq) * (1 + cpq) = spq * (sp + sq) := by
    rw [hC, hS]; linear_combination (-cp) * hpq1
  have h1 : 0 < 1 + cpq := by linarith
  have h2 : 0 ≤ spq * (sp + sq) := mul_nonneg hspq (by linarith)
  nlinarith [hkey, h1, h2]

/-- (C) in normalised form: `ncos b q = ncos b p · ncos p q − nsin h b p · nsin h p q`. -/
theorem ncos_add {h b p q : E3} (hp0 : (⟪h,p⟫:ℝ)=0) (hq0 : (⟪h,q⟫:ℝ)=0)
    (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0) :
    ncos b q = ncos b p * ncos p q - nsin h b p * nsin h p q := by
  have hbn : (0:ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hpn : (0:ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  have hqn : (0:ℝ) < ‖q‖ := norm_pos_iff.mpr hq
  have hhn : (0:ℝ) < ‖h‖ := norm_pos_iff.mpr hh
  have hid := cos_add_id (h:=h) (b:=b) (p:=p) (q:=q) hp0 hq0
  rw [ncos, ncos, ncos, nsin, nsin]
  field_simp
  nlinarith [hid]

/-- (S) in normalised form: `nsin h b q = nsin h b p · ncos p q + ncos b p · nsin h p q`. -/
theorem nsin_add {h b p q : E3} (hp0 : (⟪h,p⟫:ℝ)=0)
    (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0) :
    nsin h b q = nsin h b p * ncos p q + ncos b p * nsin h p q := by
  have hbn : (0:ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hpn : (0:ℝ) < ‖p‖ := norm_pos_iff.mpr hp
  have hqn : (0:ℝ) < ‖q‖ := norm_pos_iff.mpr hq
  have hhn : (0:ℝ) < ‖h‖ := norm_pos_iff.mpr hh
  have hid := sin_add_id (h:=h) (b:=b) (p:=p) (q:=q) hp0
  rw [ncos, ncos, nsin, nsin, nsin]
  field_simp
  nlinarith [hid]

/-- **Monotone angle (cos form).**  For `b,p,q ⊥ h` nonzero, `h ≠ 0`, with weak supports
`det3 h b p ≥ 0`, `det3 h b q ≥ 0`, `det3 h p q ≥ 0`, and the consecutive turn `p→q` not antipodal
(`-1 < ncos p q`), the cosine is non-increasing: `ncos b q ≤ ncos b p`. -/
theorem mono_ncos {h b p q : E3} (hb0 : (⟪h,b⟫:ℝ)=0) (hp0 : (⟪h,p⟫:ℝ)=0) (hq0 : (⟪h,q⟫:ℝ)=0)
    (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (sbp : 0 ≤ det3 h b p) (sbq : 0 ≤ det3 h b q) (spq : 0 ≤ det3 h p q)
    (hnotanti : -1 < ncos p q) :
    ncos b q ≤ ncos b p := by
  refine mono_abstract (ncos b p) (nsin h b p) (ncos p q) (nsin h p q) (ncos b q) (nsin h b q)
    (nsin_nonneg hb hp hh sbp) (nsin_nonneg hp hq hh spq) (nsin_nonneg hb hq hh sbq)
    (ncos_sq_add_nsin_sq hp0 hq0 hp hq hh)
    (ncos_add hp0 hq0 hb hp hq hh)
    (nsin_add hp0 hb hp hq hh)
    hnotanti

/-- **Monotone angle (θ form).**  Under the same hypotheses, `theta b p ≤ theta b q`. -/
theorem mono_theta {h b p q : E3} (hb0 : (⟪h,b⟫:ℝ)=0) (hp0 : (⟪h,p⟫:ℝ)=0) (hq0 : (⟪h,q⟫:ℝ)=0)
    (hb : b ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0) (hh : h ≠ 0)
    (sbp : 0 ≤ det3 h b p) (sbq : 0 ≤ det3 h b q) (spq : 0 ≤ det3 h p q)
    (hnotanti : -1 < ncos p q) :
    theta b p ≤ theta b q := by
  rw [theta, theta]
  exact Real.arccos_le_arccos (mono_ncos hb0 hp0 hq0 hb hp hq hh sbp sbq spq hnotanti)



/-! ## §2. Transport to the apex, and the vanishing-support squeeze. -/

/-- The planar `det3` at apex `a` (in the plane `⟪h,a⟫ = 1`) equals the fixed-normal area form of the
apex differences, up to the fixed positive scalar `1/‖h‖²`:
`det3 a u w · ‖h‖² = det3 h (u−a) (w−a)` when `a, u, w` are coplanar in `⟪h,·⟫ = 1`. -/
theorem det3_plane_eq {h a u w : E3} (ha : (⟪h,a⟫:ℝ)=1) (hu : (⟪h,u⟫:ℝ)=1) (hw : (⟪h,w⟫:ℝ)=1) :
    det3 a u w * ‖h‖^2 = det3 h (u - a) (w - a) := by
  have hreduce : det3 a u w = det3 a (u - a) (w - a) := by
    simp only [det3, PiLp.sub_apply]; ring
  have hua : (⟪h, u - a⟫:ℝ) = 0 := by rw [inner_sub_right, hu, ha]; ring
  have hwa : (⟪h, w - a⟫:ℝ) = 0 := by rw [inner_sub_right, hw, ha]; ring
  have htr := det3_apex_transport (h:=h) (u:=u-a) (v:=w-a) (a:=a) hua hwa
  rw [hreduce, htr]
  have hah : (⟪a, h⟫:ℝ) = 1 := by rw [real_inner_comm]; exact ha
  rw [hah, one_mul]

/-- `theta b p = 0 → nsin h b p = 0`, i.e. a degenerate (collinear, same-ray) angle has zero oriented
sine, hence zero area form `det3 h b p = 0`. -/
theorem nsin_eq_zero_of_theta_zero {h b p : E3} (hb0 : (⟪h,b⟫:ℝ)=0) (hp0 : (⟪h,p⟫:ℝ)=0)
    (hb : b ≠ 0) (hp : p ≠ 0) (hh : h ≠ 0) (hθ : theta b p = 0) :
    nsin h b p = 0 := by
  have hcos : ncos b p = 1 := by
    have := cos_theta hb hp; rw [hθ, Real.cos_zero] at this; linarith [this]
  have hpyth := ncos_sq_add_nsin_sq hb0 hp0 hb hp hh
  rw [hcos] at hpyth
  nlinarith [hpyth, sq_nonneg (nsin h b p)]

/-- The oriented sine vanishes iff the area form vanishes (positive denominators). -/
theorem det3_eq_zero_of_nsin_zero {h b p : E3} (hb : b ≠ 0) (hp : p ≠ 0) (hh : h ≠ 0)
    (hns : nsin h b p = 0) : det3 h b p = 0 := by
  have hd : (‖b‖ * ‖p‖ * ‖h‖) ≠ 0 := by positivity
  rw [nsin, div_eq_zero_iff] at hns
  rcases hns with h1 | h2
  · exact h1
  · exact absurd h2 hd




/-! ## §3. The branch-cut squeeze: a vanishing forward support forces a flat joint. -/

/-- **Branch-cut squeeze (the operative lemma).**  Apex differences `ρs : ℕ → E3` of a forward chain
(`ρs 0 = b` the base direction).  Assuming every `ρs t ⊥ h` nonzero, every base support
`det3 h b (ρs t) ≥ 0`, every consecutive turn weak-supported and non-antipodal, and the *first joint*
strict (`0 < det3 h b (ρs 1)`, the no-flat at the apex's successor), every forward angle is nonzero:
`theta b (ρs k) ≠ 0` for `1 ≤ k ≤ N`.  (The monotone polar angle, pinned to `[0,π]`, cannot return to
the base ray.) -/
theorem branch_squeeze_theta_ne_zero {h b : E3} (ρs : ℕ → E3) (N : ℕ)
    (hb0 : (⟪h,b⟫:ℝ)=0) (hh : h ≠ 0) (hb : b ≠ 0)
    (hperp : ∀ t, t ≤ N → (⟪h, ρs t⟫:ℝ) = 0)
    (hne : ∀ t, t ≤ N → ρs t ≠ 0)
    (hsupp : ∀ t, t ≤ N → 0 ≤ det3 h b (ρs t))
    (hturn : ∀ t, t + 1 ≤ N → 0 ≤ det3 h (ρs t) (ρs (t+1)))
    (hcons : ∀ t, t + 1 ≤ N → -1 < ncos (ρs t) (ρs (t+1)))
    (hnoflat : 0 < det3 h b (ρs 1)) (hN : 1 ≤ N) :
    ∀ k, 1 ≤ k → k ≤ N → theta b (ρs k) ≠ 0 := by
  have hmono : ∀ t, t + 1 ≤ N → theta b (ρs t) ≤ theta b (ρs (t+1)) := by
    intro t ht
    exact mono_theta hb0 (hperp t (by omega)) (hperp (t+1) (by omega)) hb
      (hne t (by omega)) (hne (t+1) (by omega)) hh
      (hsupp t (by omega)) (hsupp (t+1) (by omega)) (hturn t ht) (hcons t ht)
  have hchain : ∀ a c, a ≤ c → c ≤ N → theta b (ρs a) ≤ theta b (ρs c) := by
    intro a c hac hcN
    induction c with
    | zero => simp_all
    | succ d IH =>
      rcases Nat.lt_or_ge a (d+1) with hlt | hge
      · have h1 : theta b (ρs a) ≤ theta b (ρs d) := IH (by omega) (by omega)
        have h2 : theta b (ρs d) ≤ theta b (ρs (d+1)) := hmono d (by omega)
        linarith
      · have hae : a = d + 1 := by omega
        rw [hae]
  intro k hk1 hkN hcontra
  -- theta b (ρs 1) ≤ theta b (ρs k) = 0, and theta ≥ 0, so theta b (ρs 1) = 0
  have h1k : theta b (ρs 1) ≤ theta b (ρs k) := hchain 1 k hk1 hkN
  have hθ1 : theta b (ρs 1) = 0 := by
    rw [hcontra] at h1k
    have hnn : 0 ≤ theta b (ρs 1) := by rw [theta]; exact Real.arccos_nonneg _
    linarith
  have hns : nsin h b (ρs 1) = 0 :=
    nsin_eq_zero_of_theta_zero hb0 (hperp 1 hN) hb (hne 1 hN) hh hθ1
  have hd0 : det3 h b (ρs 1) = 0 :=
    det3_eq_zero_of_nsin_zero hb (hne 1 hN) hh hns
  linarith [hnoflat, hd0]


/-! ## §4. From the squeeze to strict support. -/

/-- The oriented sine equals `Real.sin (theta …)`, given the weak support `det3 h b p ≥ 0` (both are
then `≥ 0` and have equal square `1 − ncos²`). -/
theorem nsin_eq_sin_theta {h b p : E3} (hb0 : (⟪h,b⟫:ℝ)=0) (hp0 : (⟪h,p⟫:ℝ)=0)
    (hb : b ≠ 0) (hp : p ≠ 0) (hh : h ≠ 0) (hsupp : 0 ≤ det3 h b p) :
    nsin h b p = Real.sin (theta b p) := by
  have hpyth := ncos_sq_add_nsin_sq hb0 hp0 hb hp hh
  have hcos : Real.cos (theta b p) = ncos b p := cos_theta hb hp
  have hsin_nonneg : 0 ≤ Real.sin (theta b p) := by
    rw [theta, Real.sin_arccos]; exact Real.sqrt_nonneg _
  have hns_nonneg : 0 ≤ nsin h b p := nsin_nonneg hb hp hh hsupp
  have hsq : Real.sin (theta b p) ^ 2 = nsin h b p ^ 2 := by
    have hs2 : Real.sin (theta b p) ^ 2 = 1 - Real.cos (theta b p) ^ 2 := by
      have := Real.sin_sq_add_cos_sq (theta b p); nlinarith [this]
    rw [hs2, hcos]; nlinarith [hpyth]
  nlinarith [hsq, hns_nonneg, hsin_nonneg, sq_nonneg (nsin h b p - Real.sin (theta b p))]

/-- **Strict support from a non-degenerate angle.**  Weak support plus `theta ∈ (0, π)` gives strict
support `0 < det3 h b p`. -/
theorem det3_pos_of_theta_mem {h b p : E3} (hb0 : (⟪h,b⟫:ℝ)=0) (hp0 : (⟪h,p⟫:ℝ)=0)
    (hb : b ≠ 0) (hp : p ≠ 0) (hh : h ≠ 0) (hsupp : 0 ≤ det3 h b p)
    (hθ0 : theta b p ≠ 0) (hθπ : theta b p ≠ Real.pi) :
    0 < det3 h b p := by
  have hnn : 0 ≤ theta b p := by rw [theta]; exact Real.arccos_nonneg _
  have hle : theta b p ≤ Real.pi := by rw [theta]; exact Real.arccos_le_pi _
  have hsinpos : 0 < Real.sin (theta b p) :=
    Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_ne hnn (Ne.symm hθ0))
      (lt_of_le_of_ne hle hθπ)
  have hns : nsin h b p = Real.sin (theta b p) := nsin_eq_sin_theta hb0 hp0 hb hp hh hsupp
  have hnspos : 0 < nsin h b p := by rw [hns]; exact hsinpos
  rw [nsin] at hnspos
  have hden : (0:ℝ) < ‖b‖ * ‖p‖ * ‖h‖ := by positivity
  rw [lt_div_iff₀ hden] at hnspos
  linarith [hnspos]

/-! ## §5. Headline (forward): strict edge support from the branch-cut, modulo non-antipodality.

Packaging §3 + §4: for a forward chain of apex differences `ρs` (with `ρs 0 = b` the base direction),
all weak-supported with weak, non-antipodal consecutive turns and a strict first joint, every forward
support `det3 h b (ρs k)` (`1 ≤ k ≤ N`) is strictly positive **provided** the far vertex is not
antipodal to the base (`theta b (ρs k) ≠ π`).

The angle ordering (the genuine new content, `branch_squeeze_theta_ne_zero`) supplies `theta ≠ 0`
unconditionally; the only residual care-point is `theta ≠ π`, the antipodal vertex — exactly the
degenerate case the route flagged, which on the sphere is excluded by the one-open-hemisphere /
short-arc data that the *purely planar* predicate `PlanarWeakNoflatStrictEdge` does not carry. -/

/-- **Forward strict edge support (branch-cut), modulo non-antipodality.** -/
theorem forward_strict_support {h b : E3} (ρs : ℕ → E3) (N : ℕ)
    (hb0 : (⟪h,b⟫:ℝ)=0) (hh : h ≠ 0) (hb : b ≠ 0)
    (hperp : ∀ t, t ≤ N → (⟪h, ρs t⟫:ℝ) = 0)
    (hne : ∀ t, t ≤ N → ρs t ≠ 0)
    (hsupp : ∀ t, t ≤ N → 0 ≤ det3 h b (ρs t))
    (hturn : ∀ t, t + 1 ≤ N → 0 ≤ det3 h (ρs t) (ρs (t+1)))
    (hcons : ∀ t, t + 1 ≤ N → -1 < ncos (ρs t) (ρs (t+1)))
    (hnoflat : 0 < det3 h b (ρs 1)) (hN : 1 ≤ N)
    (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (hnotanti : theta b (ρs k) ≠ Real.pi) :
    0 < det3 h b (ρs k) := by
  have hθ0 : theta b (ρs k) ≠ 0 :=
    branch_squeeze_theta_ne_zero ρs N hb0 hh hb hperp hne hsupp hturn hcons hnoflat hN k hk1 hkN
  exact det3_pos_of_theta_mem hb0 (hperp k hkN) hb (hne k hkN) hh (hsupp k hkN) hθ0 hnotanti

end ProofsInTheBook.ZinanFFCT9
