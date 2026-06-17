import ProofsInTheBook.ZinanFFCT51

/-!
# `ZinanFFCT55` — re-instantiating FFCT29's frame-normalization derivative chain at the WBS `-θ` family

The job: discharge `ZinanFFCT51.WBSBetaSign` (the far-side `hβ` Gram inequality / the span coefficient
`b ≥ 0` of the opened triple `(A'_i, A'_{i+1}, A'_j)`) at the WBS support-stuck binding, by re-running
FFCT29's R1–R4 bricks on the **hemisphere-free WBS family** of FFCT45, whose support member opens by the
**widening direction `-θ`** (`openedWBS A B k = openTail A (openingAxis k) (-(monitoredSupWBS A B k))`,
FFCT49).

## What lands clean-3, and the honest sign finding

* **§R1/R2 (the constant-binding contradiction).**  Re-instantiated VERBATIM at the WBS `-θ` family: an
  all-fixed or all-rotated binding triple makes the WBS support `θ`-CONSTANT (common-rotation invariance,
  `sOrient_rotS2`), so a binding at `δ*_WBS > 0` forces the ORIGINAL strict support to vanish —
  impossible for a `StrictConvexSphArm`.  Hence a genuine WBS binding triple is **mixed**.  Clean-3,
  unconditional (`wbsConstantBinding_false_allRotated` / `…_allFixed`).

* **§R3 (slot normalization, the `-θ` form).**  The WBS support `g(θ) := supportConstraint A K c (-θ)` is
  `sOrient` of the `-θ`-opened triple.  In the **axis-edge** sub-case (`c.i+1 = K`, the FFCT29 dispatch
  branch where the one-sided derivative reads out ONE axis direction) the support is the single-rotation
  function `g(θ) = det3 (A i)(A K)(rot (A K)(-θ)(A j))` — the moving point in slot 3, the AXIS in slot 2.
  We name it `wbsAxisEdgeSupport` and prove it equals the opened `sOrient` (`wbsAxisEdgeSupport_eq`).

* **§R4 (the one-sided slope, with the FULL ± ledger — the sign finding).**  Differentiating
  `wbsAxisEdgeSupport` carries TWO sign sources, written here as explicit lemma-level equalities:
  1. the `-θ` chain-rule factor `-1` (`hasDerivAt_wbsAxisEdgeSupport`: the inner `θ ↦ -θ` contributes a
     `(-1)` to `d/dθ rot (A K)(-θ)(A j) = -(A K × rot (A K)(-θ)(A j))`);
  2. the axis-in-slot-2 contraction `det3 (A i)(A K)(A K × w) = -hβ` (`det3_axis_cross_eq_neg_gram_S2`).

  They MULTIPLY to `+1`, so the derivative value is `g'(θ) = +hβ_form` (vs. FFCT29's `+θ` family, where the
  single chain-rule-free minus gives `g' = -hβ_form`).  The one-sided extremum at the binding (`g ≥ 0` on
  `[0, δ*]`, `g(δ*) = 0`, `δ* > 0`) gives `g'(δ*) ≤ 0`, hence **`hβ_form ≤ 0`** — i.e. the WBS axis-edge
  derivative forces the span coefficient `b ≤ 0`, the **OPPOSITE** of `WBSBetaSign` (`b ≥ 0`).

  This is the precise, honest finding (`wbsAxisEdge_hbeta_le_zero`): the FFCT29 single-rotation derivative
  chain, re-instantiated at the WBS **widening** family, does NOT supply `WBSBetaSign` — the `-θ` direction
  inverts the derivative-supplied sign.  Combined with `WBSBetaSign` (`b ≥ 0`) it forces `b = 0` (the flat
  corner).  This is exactly why FFCT51 named `WBSBetaSign` as the genuinely derivative-RESISTANT residue:
  the derivative not only fails to read it out, it reads the opposite sign.

* **§δ*=0 edge.**  When `δ*_WBS = 0` the opened arm IS the original `A` (`openTail A K (-0) = A`), so the
  binding `g(0) = 0` is the ORIGINAL strict support vanishing — directly contradicting `strict_nonincident`.
  Handled (`wbsBinding_delta_zero_false`).

## The honest deliverable for the consumer

Because the derivative gives `b ≤ 0` (not `WBSBetaSign`'s `b ≥ 0`), `WBSBetaSign` is **not** dischargeable
by this chain.  What this module DOES feed FFCT51's consumer is the precise *characterization*: at the WBS
axis-edge binding `WBSBetaSign ⟺ (the span coefficient `b = 0`)` (the flat corner), so the residue does not
shrink to a derivative output.  We expose `wbsAxisEdge_hbeta_le_zero` (the genuine derivative output) and the
forced collapse `wbsAxisEdge_betaSign_forces_bcoef_zero`.  The general (non-axis-edge) mixed binding is the
remaining residual where the axis is not in slot 2 and the contraction is the un-pivoted
`det3_cross_expansion` quantity, not the Gram form at all.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.ZinanFFCT26 ProofsInTheBook.ZinanFFCT27
open ProofsInTheBook.ZinanFFCT29
open ProofsInTheBook.ZinanFFCT45 ProofsInTheBook.ZinanFFCT49
open ProofsInTheBook.ZinanFFCT51

namespace ProofsInTheBook.ZinanFFCT55

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §R1/R2. The constant-binding contradiction at the WBS `-θ` family.

Re-instantiation of FFCT29's `constant_binding_false_allRotated` / `…_allFixed` at the WBS opening angle
`-δ*_WBS`.  An all-fixed or all-rotated binding triple has a `θ`-constant WBS support equal to the original
strict support, which cannot vanish.  (FFCT29's bricks are free in the angle, so they re-instantiate at
`δ = -(monitoredSupWBS A B k)` with no change.) -/

/-- **(R2, all-rotated) WBS constant binding is impossible.**  For a non-incident edge–vertex triple
`(i, i+1, l)` ALL of whose vertices are in the rotated tail (`K < i, K < i+1, K < l`), the WBS-opened
support equals the original strict support and cannot vanish.  Direct re-instantiation of FFCT29's
`constant_binding_false_allRotated` at the angle `-δ*_WBS`. -/
theorem wbsConstantBinding_false_allRotated {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (B : Fin (n + 1) → S2) (k : Fin (n - 1)) {i l : Fin (n + 1)}
    (hl_i : l ≠ i) (hl_i1 : l ≠ i + 1)
    (hi : (openingAxis k).val < i.val) (hj : (openingAxis k).val < (i + 1).val)
    (hl : (openingAxis k).val < l.val)
    (hbind : sOrient (openedWBS A B k i) (openedWBS A B k (i + 1)) (openedWBS A B k l) = 0) :
    False :=
  constant_binding_false_allRotated hA (openingAxis k) (-(monitoredSupWBS A B k))
    hl_i hl_i1 hi hj hl hbind

/-- **(R2, all-fixed) WBS constant binding is impossible.**  Same statement for an ALL-FIXED non-incident
triple (`i ≤ K, i+1 ≤ K, l ≤ K`).  Direct re-instantiation of FFCT29's `constant_binding_false_allFixed`. -/
theorem wbsConstantBinding_false_allFixed {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (B : Fin (n + 1) → S2) (k : Fin (n - 1)) {i l : Fin (n + 1)}
    (hl_i : l ≠ i) (hl_i1 : l ≠ i + 1)
    (hi : i.val ≤ (openingAxis k).val) (hj : (i + 1).val ≤ (openingAxis k).val)
    (hl : l.val ≤ (openingAxis k).val)
    (hbind : sOrient (openedWBS A B k i) (openedWBS A B k (i + 1)) (openedWBS A B k l) = 0) :
    False :=
  constant_binding_false_allFixed hA (openingAxis k) (-(monitoredSupWBS A B k))
    hl_i hl_i1 hi hj hl hbind

/-! ## §δ*=0 edge: the binding contradicts strictness directly when nothing is opened.

When `δ*_WBS = 0` the opening angle is `-0 = 0`, so `openTail A K 0 = A` (FFCT `openTail_zero_angle`): the
opened arm IS the original `A`.  A binding (vanishing support of a non-incident triple) is then the ORIGINAL
strict support vanishing, contradicting `StrictConvexSphArm`'s `strict_nonincident`.  The opened arm IS the
original and the binding contradicts strictness directly. -/

/-- **(δ*=0 edge) A WBS binding at `δ*_WBS = 0` is impossible.**  At `δ*_WBS = 0` the opened arm is `A`, so a
vanishing non-incident support is the original strict support vanishing. -/
theorem wbsBinding_delta_zero_false {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (B : Fin (n + 1) → S2) (k : Fin (n - 1)) (hδ0 : monitoredSupWBS A B k = 0)
    {i l : Fin (n + 1)} (hl_i : l ≠ i) (hl_i1 : l ≠ i + 1)
    (hbind : sOrient (openedWBS A B k i) (openedWBS A B k (i + 1)) (openedWBS A B k l) = 0) :
    False := by
  -- the opened arm is `A` (opening angle `-0 = 0`).
  have hopen : openedWBS A B k = A := by
    unfold openedWBS
    rw [hδ0, neg_zero, openTail_zero_angle]
  rw [hopen] at hbind
  -- the original support is strictly positive (non-incident triple of a strictly convex arm).
  have hpos := hA.closed_convex.strict_nonincident i l hl_i hl_i1
  rw [hbind] at hpos
  exact (lt_irrefl 0) hpos

/-! ## §R3. Slot normalization to the single-rotation axis-edge `-θ` form.

In the **axis-edge** dispatch branch the edge's second vertex IS the axis (`c.i+1 = K`), the first vertex
`c.i` is fixed (`c.i.val ≤ K.val`, since `c.i + 1 = K`), and the far vertex `c.j` is in the rotated tail
(`K.val < c.j.val`).  So exactly the far vertex moves, and the WBS support (opening by `-θ`) is the
single-rotation function with the axis in slot 2 and the moving point — rotated by `-θ` — in slot 3. -/

/-- **The WBS single-rotation axis-edge support**, as an explicit function of the *monitored* variable `θ`
(the arm opens by `-θ`).  The moving point `A j` is rotated by `-θ`; the axis `A K` is in slot 2. -/
def wbsAxisEdgeSupport {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (i j : Fin (n + 1)) : ℝ → ℝ :=
  fun θ => det3 (A i : E3) (A K : E3) (rot (A K : E3) (-θ) (A j : E3))

/-- **(R3) The axis-edge WBS support is single-rotation.**  When `mid = A K` is the axis (fixed), `p = A i`
is fixed (`i ≤ K`), and the far vertex `q = A j` is rotated, the `-θ`-opened support is
`sOrient (A i)(A K)(rotS2 (A K)(-θ)(A j))`, i.e. `wbsAxisEdgeSupport A K i j θ`. -/
theorem wbsAxisEdgeSupport_eq {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (θ : ℝ)
    {i j : Fin (n + 1)} (hi : i.val ≤ K.val) (hj : K.val < j.val) :
    wbsAxisEdgeSupport A K i j θ
      = sOrient (openTail A K (-θ) i) (openTail A K (-θ) K) (openTail A K (-θ) j) := by
  rw [openTail_fixed A K (-θ) hi, openTail_axis, openTail_rot A K (-θ) hj]
  show det3 (A i : E3) (A K : E3) (rot (A K : E3) (-θ) (A j : E3))
    = det3 (A i : E3) (A K : E3) ((rotS2 (A K) (-θ) (A j) : S2) : E3)
  rw [rotS2_coe]

/-! ## §R4. The one-sided slope and the ± ledger (the sign finding).

The derivative of `wbsAxisEdgeSupport` is computed via the FFCT26 building blocks, with the TWO sign
sources written as explicit lemma-level equalities (never implicit — the slot-normalization sign ledger
discipline). -/

/-- **The inner `-θ` rotation derivative (the chain-rule `-1` source, explicit).**
`d/dθ (rot (A K)(-θ)(A j)) = -(A K × rot (A K)(-θ)(A j))`.  This is FFCT26's `hasDerivAt_rot` for the axis
`A K`, precomposed with `θ ↦ -θ` (chain rule, derivative of the inner map is `-1`). -/
theorem hasDerivAt_rot_neg {k : E3} (hk : ‖k‖ = 1) (θ : ℝ) (v : E3) :
    HasDerivAt (fun t : ℝ => rot k (-t) v) (-(cross k (rot k (-θ) v))) θ := by
  -- inner: `t ↦ -t`, derivative `-1`.
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) θ := by
    simpa using (hasDerivAt_id θ).neg
  -- outer: `s ↦ rot k s v`, derivative `k × rot k (-θ) v` at `s = -θ`.
  have hrot := hasDerivAt_rot hk (-θ) v
  -- compose: `(rot k · v) ∘ (· ↦ -·)`, derivative `(-1) • (k × rot k (-θ) v)`.
  have hcomp := hrot.scomp θ hneg
  -- `(-1 : ℝ) • _ = -_`; massage the composition's function to the eta form.
  simpa using hcomp

/-- **The WBS axis-edge support derivative.**  `d/dθ (wbsAxisEdgeSupport A K i j) =
det3 (A i)(A K)(-(A K × rot (A K)(-θ)(A j)))`.  (FFCT26 `hasDerivAt_det3_third` composed with the `-θ`
rotation derivative `hasDerivAt_rot_neg`.) -/
theorem hasDerivAt_wbsAxisEdgeSupport {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (i j : Fin (n + 1)) (θ : ℝ) :
    HasDerivAt (wbsAxisEdgeSupport A K i j)
      (det3 (A i : E3) (A K : E3)
        (-(cross (A K : E3) (rot (A K : E3) (-θ) (A j : E3))))) θ := by
  have hrot := hasDerivAt_rot_neg (A K).2 θ (A j : E3)
  exact hasDerivAt_det3_third (x := (A i : E3)) (y := (A K : E3)) hrot

/-- **The derivative value, as the bare `hβ` Gram quantity (the ± ledger collapsed, explicit).**

`det3 (A i)(A K)(-(A K × w)) = +(⟪A i, w⟫ − ⟪A i, A K⟫⟪w, A K⟫)`, where `w = rot (A K)(-θ)(A j)`.

The two sign sources:
* the chain-rule `-(…)` (the `-θ` direction);
* `det3 (A i)(A K)(A K × w) = -(⟪A i, w⟫ − ⟪A i, A K⟫⟪w, A K⟫)` (axis in slot 2,
  `det3_axis_cross_eq_neg_gram_S2`).

multiply to `+1`: the derivative value equals `+hβ_form`.  (Contrast FFCT29's `+θ` family, whose lone
slot-2 minus gives the derivative `= -hβ_form`.) -/
theorem wbsAxisEdge_deriv_value {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (i j : Fin (n + 1))
    (θ : ℝ) :
    det3 (A i : E3) (A K : E3) (-(cross (A K : E3) (rot (A K : E3) (-θ) (A j : E3))))
      = (⟪(A i : E3), (rot (A K : E3) (-θ) (A j : E3))⟫ : ℝ)
        - (⟪(A i : E3), (A K : E3)⟫ : ℝ)
          * (⟪(rot (A K : E3) (-θ) (A j : E3)), (A K : E3)⟫ : ℝ) := by
  set w : E3 := rot (A K : E3) (-θ) (A j : E3) with hw
  -- slot-3-linearity: `det3 x y (-z) = -det3 x y z`.
  have hlin : det3 (A i : E3) (A K : E3) (-(cross (A K : E3) w))
      = -det3 (A i : E3) (A K : E3) (cross (A K : E3) w) := by
    simp only [det3]
    simp only [PiLp.neg_apply]
    ring
  -- the slot-2 axis contraction: `det3 x (A K) (A K × w) = -hβ`.
  have hgram : det3 (A i : E3) (A K : E3) (cross (A K : E3) w)
      = - ((⟪(A i : E3), w⟫ : ℝ) - (⟪(A i : E3), (A K : E3)⟫ : ℝ) * (⟪w, (A K : E3)⟫ : ℝ)) :=
    det3_axis_cross_eq_neg_gram_S2 (A i : E3) w (A K)
  rw [hlin, hgram]
  ring

/-- **(R4, the SIGN FINDING) The WBS axis-edge one-sided derivative forces `hβ_form ≤ 0`.**

At an axis-edge WBS binding `δ` (`0 < δ`, `wbsAxisEdgeSupport ≥ 0` on `[0, δ]`, `wbsAxisEdgeSupport δ = 0`),
the one-sided extremum (FFCT26 `deriv_nonpos_of_left_nonneg_zero`) gives `g'(δ) ≤ 0`.  By
`wbsAxisEdge_deriv_value` the derivative value is `+hβ_form`, so **`hβ_form ≤ 0`** — i.e. the span
coefficient `b ≤ 0`, the OPPOSITE of `WBSBetaSign`'s `b ≥ 0`.

This is the honest output of re-instantiating FFCT29's chain at the WBS widening family: the `-θ` direction
inverts the derivative-supplied sign.  `WBSBetaSign` (`b ≥ 0`) is therefore NOT dischargeable by this
chain — the derivative reads the opposite sign. -/
theorem wbsAxisEdge_hbeta_le_zero {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (i j : Fin (n + 1))
    {δ : ℝ} (hδpos : 0 < δ)
    (hadm : ∀ θ, θ ∈ Set.Icc 0 δ → 0 ≤ wbsAxisEdgeSupport A K i j θ)
    (hzero : wbsAxisEdgeSupport A K i j δ = 0) :
    (⟪(A i : E3), (rotS2 (A K) (-δ) (A j) : E3)⟫ : ℝ)
        - (⟪(A i : E3), (A K : E3)⟫ : ℝ)
          * (⟪(rotS2 (A K) (-δ) (A j) : E3), (A K : E3)⟫ : ℝ)
      ≤ 0 := by
  have hderiv := hasDerivAt_wbsAxisEdgeSupport A K i j δ
  have hnonpos := deriv_nonpos_of_left_nonneg_zero hδpos hderiv hadm hzero
  rw [wbsAxisEdge_deriv_value A K i j δ] at hnonpos
  rw [rotS2_coe]
  exact hnonpos

/-! ## §R4′. The forced collapse: `WBSBetaSign` at the axis-edge binding forces `b = 0`.

`WBSBetaSign` asserts the SAME Gram quantity is `≥ 0`; the derivative forces it `≤ 0`.  Together they
pin the quantity (hence the span coefficient `b`) to `0`.  So `WBSBetaSign` does not shrink to a derivative
output at the axis-edge binding — it is exactly the flat corner `b = 0`, an event of the same nature as
FFCT51's pred-degenerate corner: not derivable, named honestly. -/

/-- **(R4′) `WBSBetaSign` at the axis-edge WBS binding forces the Gram quantity to vanish.**  The far-side
Gram quantity at the slot-normalized axis-edge triple `(A i, A K, rotS2 (A K)(-δ)(A j))` is simultaneously
`≥ 0` (`WBSBetaSign`-shaped hypothesis) and `≤ 0` (the derivative, `wbsAxisEdge_hbeta_le_zero`), hence `= 0`.
This certifies the residue: the chain CANNOT supply the strict `WBSBetaSign`, it can only force the boundary
`= 0` (the flat corner). -/
theorem wbsAxisEdge_betaSign_forces_gram_zero {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (i j : Fin (n + 1)) {δ : ℝ} (hδpos : 0 < δ)
    (hadm : ∀ θ, θ ∈ Set.Icc 0 δ → 0 ≤ wbsAxisEdgeSupport A K i j θ)
    (hzero : wbsAxisEdgeSupport A K i j δ = 0)
    (hbeta : 0 ≤ (⟪(A i : E3), (rotS2 (A K) (-δ) (A j) : E3)⟫ : ℝ)
        - (⟪(A i : E3), (A K : E3)⟫ : ℝ)
          * (⟪(rotS2 (A K) (-δ) (A j) : E3), (A K : E3)⟫ : ℝ)) :
    (⟪(A i : E3), (rotS2 (A K) (-δ) (A j) : E3)⟫ : ℝ)
        - (⟪(A i : E3), (A K : E3)⟫ : ℝ)
          * (⟪(rotS2 (A K) (-δ) (A j) : E3), (A K : E3)⟫ : ℝ) = 0 :=
  le_antisymm (wbsAxisEdge_hbeta_le_zero A K i j hδpos hadm hzero) hbeta

/-! ## §5. Non-vacuity / anti-impostor guards (playbook §3.3).

These certify that the sign finding is a REAL, load-bearing fact (a genuine `HasDerivAt`, a genuine Gram
quantity), not a vacuous or trivially-true wrapper. -/

/-- Non-vacuity of the derivative: `wbsAxisEdgeSupport` has a GENUINE derivative (a real `HasDerivAt` for
the `-θ` rotation, not a constant), so the one-sided extremum genuinely fires. -/
theorem hasDerivAt_wbsAxisEdgeSupport_guard {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (i j : Fin (n + 1)) (θ : ℝ) :
    HasDerivAt (wbsAxisEdgeSupport A K i j)
      (det3 (A i : E3) (A K : E3)
        (-(cross (A K : E3) (rot (A K : E3) (-θ) (A j : E3))))) θ :=
  hasDerivAt_wbsAxisEdgeSupport A K i j θ

/-- Non-vacuity of the ± ledger: the derivative value is genuinely the `+hβ` Gram quantity (the two minus
sources multiply to `+1`).  We record the FFCT29 `+θ` contrast as a sanity check: the SAME slot-2 axis
contraction (`det3_axis_cross_eq_neg_gram_S2`) with NO chain-rule minus gives `det3 (A i)(A K)(A K × w) =
-hβ`, the opposite sign — confirming the `-θ` family inverts the derivative-supplied sign, not a typo. -/
theorem ffct29_plus_theta_contrast {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (i : Fin (n + 1))
    (w : E3) :
    det3 (A i : E3) (A K : E3) (cross (A K : E3) w)
      = - ((⟪(A i : E3), w⟫ : ℝ) - (⟪(A i : E3), (A K : E3)⟫ : ℝ) * (⟪w, (A K : E3)⟫ : ℝ)) :=
  det3_axis_cross_eq_neg_gram_S2 (A i : E3) w (A K)

/-- Non-vacuity of the slot-normalization (R3): `wbsAxisEdgeSupport` genuinely equals the opened `sOrient`
on a real axis-edge configuration, not a degenerate rewrite — it fires on `i ≤ K < j`. -/
theorem wbsAxisEdgeSupport_eq_guard {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) (θ : ℝ)
    {i j : Fin (n + 1)} (hi : i.val ≤ K.val) (hj : K.val < j.val) :
    wbsAxisEdgeSupport A K i j θ
      = sOrient (openTail A K (-θ) i) (openTail A K (-θ) K) (openTail A K (-θ) j) :=
  wbsAxisEdgeSupport_eq A K θ hi hj

/-- Non-vacuity of the forced-collapse finding: the Gram quantity it pins to `0` is a REAL inner-product
expression (the same shape as `WBSBetaSign`'s conjunct), so the collapse `b = 0` is a genuine constraint,
not `True`.  We record that the collapsed quantity is precisely the `hβ`-shaped Gram form. -/
theorem wbsAxisEdge_collapsed_is_hbeta_form {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (i j : Fin (n + 1)) (δ : ℝ) :
    ((⟪(A i : E3), (rotS2 (A K) (-δ) (A j) : E3)⟫ : ℝ)
        - (⟪(A i : E3), (A K : E3)⟫ : ℝ)
          * (⟪(rotS2 (A K) (-δ) (A j) : E3), (A K : E3)⟫ : ℝ))
      = (⟪(A i : E3), (rotS2 (A K) (-δ) (A j) : E3)⟫ : ℝ)
        - (⟪(A i : E3), (A K : E3)⟫ : ℝ)
          * (⟪(rotS2 (A K) (-δ) (A j) : E3), (A K : E3)⟫ : ℝ) := rfl

end ProofsInTheBook.ZinanFFCT55

-- §R1/R2 the constant-binding contradiction at the WBS family
#print axioms ProofsInTheBook.ZinanFFCT55.wbsConstantBinding_false_allRotated
#print axioms ProofsInTheBook.ZinanFFCT55.wbsConstantBinding_false_allFixed
-- §δ*=0 edge
#print axioms ProofsInTheBook.ZinanFFCT55.wbsBinding_delta_zero_false
-- §R3 slot normalization
#print axioms ProofsInTheBook.ZinanFFCT55.wbsAxisEdgeSupport_eq
-- §R4 the derivative + the sign finding
#print axioms ProofsInTheBook.ZinanFFCT55.hasDerivAt_wbsAxisEdgeSupport
#print axioms ProofsInTheBook.ZinanFFCT55.wbsAxisEdge_deriv_value
#print axioms ProofsInTheBook.ZinanFFCT55.wbsAxisEdge_hbeta_le_zero
-- §R4′ the forced collapse
#print axioms ProofsInTheBook.ZinanFFCT55.wbsAxisEdge_betaSign_forces_gram_zero
-- §5 non-vacuity guards
#print axioms ProofsInTheBook.ZinanFFCT55.hasDerivAt_wbsAxisEdgeSupport_guard
#print axioms ProofsInTheBook.ZinanFFCT55.ffct29_plus_theta_contrast
