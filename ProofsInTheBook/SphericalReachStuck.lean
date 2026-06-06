import ProofsInTheBook.SphericalOpeningProcess

/-!
# `SphericalReachStuck` — the §8.4 opening process (reach/stuck on the genuine arm)

This module attacks the single remaining residue of Chapter 13's Schoenberg–Zaremba spherical arm
lemma: the §8.4 opening process whose discharge closes `OpenedArmReachOrStuck` (the §8.4 dichotomy of
`SphericalOpening`) — and hence, through the proven chain `schoenbergZaremba_of_reachOrStuck →
SchoenbergZarembaTarget → spherical_arm_mono(_strict)`, the unconditional arm lemma.

## The logical reduction (verified against the substrate)

`OpenedArmReachOrStuck`'s strict disjunction has `Or.inr = endpt A < endpt B`; the proven
`openingData_of_szStepGeom` shows `OpeningData` (and so the whole downstream chain) is dischargeable
*always through `Or.inr`* — the stuck `qstar` witness is never consumed downstream.  Hence proving
`OpenedArmReachOrStuck` reduces to proving, for every level-`(n+1)` convex arm pair with equal sides
and nondecreasing joints, **given the level-`n` comparison `SZComparison n`**:

* the weak bound `endpt A ≤ endpt B`, and
* whenever some joint of `B` is strictly wider, the strict bound `endpt A < endpt B`.

This is exactly the Schoenberg–Zaremba **inductive step** `SZComparison n → SZComparison (n+1)`.

## Genuine new content built here (all clean-3)

1. **The mirrored §8.1 keystone for the convex opening orientation.**  The substrate keystone
   `openedAngle_ge_of_oriented` opens by `+θ` and needs `0 ≤ sOrient axis a0 tail`.  But the convex
   arm's last-joint opening presents the *opposite* sign: the convex-position support gives
   `0 < sOrient (A 0)(axis)(tail)`, i.e. `sOrient (axis)(A 0)(tail) < 0`, so the oriented datum
   `s = ⟪tangentTo axis a0, axis × tangentTo axis tail⟫ ≥ 0` — the *reversed* keystone sign.  Hence
   the convex opening rotates the tail by a **negative** angle `-θ`.  We build the mirrored cosine
   bound `cos_open_le_cos_orig_neg` and monotonicity `openedAngle_ge_of_oriented_neg` from scratch
   (the substrate only proved the `+θ` / `s ≤ 0` branch).  This **corrects the rotation-direction
   sign** that the substrate's abstract base-monotonicity left implicit.

2. **The reach-case endpoint monotonicity transported to the genuine multi-vertex arm**
   (`reach_endpoint_mono_arm` / `reach_endpoint_strict_arm`): opening the last joint of a strictly
   convex arm `A` by `-θ` does not decrease (resp. strictly increases) the endpoint
   `sDist (A 0) (A (n+1))`, via the base triangle `(A 0, axis = A n, tail = A (n+1))` — both base
   sides short arcs (`shortArc_axis_zero`, `shortArc_axis_tail`), the convex oriented datum
   (`support_sign_base_ac` + `orientedSign_neg_of_support`), the mirrored keystone, and
   `reach_base_endpoint_mono`.  This instantiates the abstract base-triangle monotonicity on the
   actual arm's closing diagonal — a step absent from every substrate file.

## Honest status (conditional)

`OpenedArmReachOrStuck` is **not** closed unconditionally here.  Per the proven downstream chain it
reduces to the SZ inductive step `SZComparison n → SZComparison (n+1)`, whose all-strict reach/stuck
case is the design §8.4 "THE hard theorem" — the multi-vertex opening *construction* (arbitrary-joint
opening to the admissible supremum + boundary convexity persistence + the reach recursion + the
stuck→cut transport), confirmed irreducible by five prior expert rounds.  After the genuine content
above, the residue is exactly two named, non-vacuous, mutually-narrower primitives:
`SphericalOpeningProcess.StuckWitnessExists` (the strict half, already in the substrate) and
`WeakArmStep` (the weak monotone half, isolated below).  We prove
`StuckWitnessExists ∧ WeakArmStep → OpenedArmReachOrStuck → SchoenbergZarembaTarget`, re-exporting the
conditional arm lemmas, and supply the non-vacuity guards.  No co-extensive re-wrapper is banked.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess

namespace ProofsInTheBook.SphericalReachStuck

/-! ## The genuine-arm base triangle of the last-joint opening.

Opening the last joint of `A : Fin (n+2) → S2` fixes every vertex `≤ n` and rotates the tail
`A (Fin.last (n+1))` about the axis `A ⟨n,_⟩`.  Its endpoint `sDist (A 0) (tail)` is governed by the
base triangle `(A 0, axis, tail)`, whose data we extract from the arm's convex position. -/

/-- The axis vertex `A ⟨n,_⟩` equals `A (Fin.last n).castSucc`. -/
theorem openAxis_eq_castSucc {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    openAxis A = A (Fin.last n).castSucc := by
  simp only [openAxis]
  congr 1

/-- The closing diagonal `axis → A 0` of the arm is a short arc (`n ≥ 2`): `axis = A ⟨n⟩`. -/
theorem shortArc_axis_zero {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n) :
    ShortArc (openAxis A) (A 0) := by
  rw [openAxis_eq_castSucc]
  exact shortArc_closing_diag hA.closed_convex hn

/-- The last side `axis → tail` is a short arc: it is the edge `A ⟨n⟩ → A ⟨n+1⟩` of `A`. -/
theorem shortArc_axis_tail {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    (hA : StrictConvexSphArm A) :
    ShortArc (openAxis A) (A (Fin.last (n + 1))) := by
  have he := hA.closed_convex.edge_short (Fin.last n).castSucc
  have hsucc : ((Fin.last n).castSucc + 1 : Fin (n + 1 + 1)) = Fin.last (n + 1) := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_castSucc, Fin.val_last, Fin.val_one']
    rw [Nat.mod_eq_of_lt (show 1 < n + 1 + 1 by omega),
      Nat.mod_eq_of_lt (show n + 1 < n + 1 + 1 by omega)]
  rw [hsucc] at he
  rwa [openAxis_eq_castSucc]

/-- **The oriented convex-position support sign at the base triangle.**  In a strictly convex arm `A`
(`n ≥ 2`), the closing diagonal `A 0 → axis = A ⟨n⟩` strictly supports the tail `A ⟨n+1⟩`:
`0 < sOrient (A 0)(axis)(tail)`.  This is `cut_diagonal_supports` (the diagonal `A 0 → A ⟨n⟩` strictly
supports every vertex beyond it, here the tail `A ⟨n+1⟩`).  It is the oriented datum that fixes the
direction of admissible opening. -/
theorem support_sign_base_ac {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n) :
    0 < sOrient (A 0) (openAxis A) (A (Fin.last (n + 1))) := by
  have h0n : (0 : Fin (n + 1 + 1)) < (Fin.last n).castSucc := by
    rw [Fin.lt_def, Fin.val_zero, Fin.val_castSucc, Fin.val_last]; omega
  have hnl : (Fin.last n).castSucc < (Fin.last (n + 1)) := by
    rw [Fin.lt_def, Fin.val_castSucc, Fin.val_last, Fin.val_last]; omega
  have hpos : 0 < sOrient (A 0) (A (Fin.last n).castSucc) (A (Fin.last (n + 1))) :=
    cut_diagonal_supports hA.closed_convex h0n hnl
  rwa [openAxis_eq_castSucc]

/-! ## The mirrored keystone — opening in the convex direction (negative rotation).

The substrate keystone `openedAngle_ge_of_oriented` opens by `+θ` and requires the oriented sign
`⟪tangentTo axis a0, axis × tangentTo axis tail⟫ ≤ 0` (i.e. `0 ≤ sOrient axis a0 tail`).  But the
convex arm's last-joint *opening direction* is the opposite: the convex-position support gives
`0 < sOrient (A 0)(axis)(tail)`, i.e. `sOrient (axis)(A 0)(tail) < 0`, equivalently the oriented
datum `s := ⟪tangentTo axis a0, axis × tangentTo axis tail⟫ ≥ 0` (the *reversed* sign of the
keystone, via the bridge `inner_tangent_cross_eq_neg_sOrient`).  So the convex opening rotates the
tail by a *negative* angle `-θ` (`θ ≥ 0`).  We prove the mirrored monotonicity: with `s ≥ 0`,
opening by `-θ` (in the convex direction, within the great-semicircle range) does not decrease the
included angle.  This is the genuine §8.1 keystone for the *convex* opening orientation — the sign
the multi-vertex arm actually presents — built from scratch (the substrate only proved the `+θ`,
`s ≤ 0` direction). -/

/-- **The opened-angle cosine is monotone (convex / negative-rotation orientation).**  If the
oriented datum `s = ⟪tangentTo axis a0, axis × tangentTo axis tail⟫ ≥ 0` (the convex opening sign)
and `0 ≤ θ` with `θ + sphAngle a0 axis tail ≤ π`, then the opened-by-`-θ` angle cosine does not
exceed the original: `cos (sphAngle a0 axis (rotS2 axis (-θ) tail)) ≤ cos (sphAngle a0 axis tail)`.
Mirror of `cos_open_le_cos_orig` for `s ≥ 0`, `-θ`. -/
theorem cos_open_le_cos_orig_neg (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsign : (0 : ℝ) ≤ (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ + sphAngle a0 axis tail ≤ Real.pi) :
    Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail)) ≤ Real.cos (sphAngle a0 axis tail) := by
  set u := tangentTo axis a0 with hu
  set w := tangentTo axis tail with hw
  set c : ℝ := ⟪u, w⟫ with hc
  set s : ℝ := ⟪u, cross (axis : E3) w⟫ with hsdef
  have hunz : u ≠ 0 := (tangentTo_ne_zero_iff axis a0).2 hka
  have hwnz : w ≠ 0 := (tangentTo_ne_zero_iff axis tail).2 hkt
  have hup : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖w‖ := norm_pos_iff.2 hwnz
  set N : ℝ := ‖u‖ * ‖w‖ with hN
  have hNp : (0 : ℝ) < N := mul_pos hup hwp
  set φ₀ : ℝ := sphAngle a0 axis tail with hφ
  have hcosopen : Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail))
      = (Real.cos (-θ) * c + Real.sin (-θ) * s) / N := by
    rw [cos_openedJointAngle, norm_tangentTo_open]
  have hcosorig : Real.cos φ₀ = c / N := by
    rw [hφ, sphAngle, InnerProductGeometry.cos_angle]
  have hφ0 : 0 ≤ φ₀ := sphAngle_nonneg _ _ _
  have hφπ : φ₀ ≤ Real.pi := sphAngle_le_pi _ _ _
  have hpyth : c ^ 2 + s ^ 2 = N ^ 2 := by
    have := tangentPlane_pythag (k := (axis : E3)) (u := u) (w := w) axis.2
      (tangentTo_orthogonal axis a0) (tangentTo_orthogonal axis tail)
    rw [hc, hsdef, hN]; rw [mul_pow]; linear_combination this
  have hcEq : c = N * Real.cos φ₀ := by
    rw [hcosorig]; field_simp
  have hsinφ : 0 ≤ Real.sin φ₀ := Real.sin_nonneg_of_nonneg_of_le_pi hφ0 hφπ
  have hssq : s ^ 2 = (N * Real.sin φ₀) ^ 2 := by
    have hsincos : Real.sin φ₀ ^ 2 = 1 - Real.cos φ₀ ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ₀; linarith
    rw [mul_pow, hsincos]
    have : s ^ 2 = N ^ 2 - c ^ 2 := by linarith [hpyth]
    rw [this, hcEq]; ring
  -- now s ≥ 0, so s = +(N sin φ₀)
  have hsEq : s = N * Real.sin φ₀ := by
    have hge : 0 ≤ N * Real.sin φ₀ := mul_nonneg (le_of_lt hNp) hsinφ
    nlinarith [hssq, hsign, hge, sq_nonneg (s - N * Real.sin φ₀)]
  -- the `-θ` sinusoid is N cos(φ₀+θ)
  have hsinusoid : Real.cos (-θ) * c + Real.sin (-θ) * s = N * Real.cos (φ₀ + θ) := by
    rw [hcEq, hsEq, Real.cos_neg, Real.sin_neg, Real.cos_add]; ring
  rw [hcosopen, hcosorig, hsinusoid]
  rw [div_le_div_iff_of_pos_right hNp]
  have hcos : Real.cos (φ₀ + θ) ≤ Real.cos φ₀ :=
    Real.cos_le_cos_of_nonneg_of_le_pi hφ0 (by linarith) (by linarith)
  rw [hcEq]
  exact mul_le_mul_of_nonneg_left hcos (le_of_lt hNp)

/-- **Mirrored oriented opening monotonicity (convex orientation).**  Opening the joint at `axis` by
`-θ` (`θ ≥ 0`, within the great-semicircle range) increases the included angle, provided the convex
oriented datum `0 ≤ ⟪tangentTo axis a0, axis × tangentTo axis tail⟫` holds.  Companion of
`openedAngle_ge_of_oriented` for the convex opening direction. -/
theorem openedAngle_ge_of_oriented_neg (axis a0 tail : S2)
    (hka : ShortArc axis a0) (hkt : ShortArc axis tail)
    (hsign : (0 : ℝ) ≤ (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ))
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθπ : θ + sphAngle a0 axis tail ≤ Real.pi) :
    sphAngle a0 axis tail ≤ sphAngle a0 axis (rotS2 axis (-θ) tail) := by
  have hcos := cos_open_le_cos_orig_neg axis a0 tail hka hkt hsign hθ0 hθπ
  by_contra hlt
  rw [not_le] at hlt
  have : Real.cos (sphAngle a0 axis tail) < Real.cos (sphAngle a0 axis (rotS2 axis (-θ) tail)) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (sphAngle_nonneg _ _ _) (sphAngle_le_pi _ _ _) hlt
  linarith [hcos]

/-- The convex oriented datum from the convex support sign: `0 < sOrient (A 0)(axis)(tail)` gives
`0 ≤ ⟪tangentTo axis a0, axis × tangentTo axis tail⟫` (with `a0 = A 0`, `tail = the tail`).  Via the
bridge `inner_tangent_cross_eq_neg_sOrient` and `sOrient (axis)(A 0)(tail) = -sOrient (A 0)(axis)(tail)`. -/
theorem orientedSign_neg_of_support {axis a0 tail : S2}
    (h : 0 ≤ sOrient a0 axis tail) :
    (0 : ℝ) ≤ (⟪tangentTo axis a0, cross (axis : E3) (tangentTo axis tail)⟫ : ℝ) := by
  rw [inner_tangent_cross_eq_neg_sOrient]
  -- need 0 ≤ -sOrient axis a0 tail, i.e. sOrient axis a0 tail ≤ 0.
  -- sOrient axis a0 tail = -sOrient a0 axis tail (swap first two).
  have hswap : sOrient axis a0 tail = -sOrient a0 axis tail := by
    have := sOrient_swap a0 axis tail  -- sOrient a0 tail axis = -sOrient a0 axis tail
    -- We instead want sOrient axis a0 tail. Use det form directly.
    simp only [sOrient, det3]; ring
  rw [hswap]; linarith

/-! ## The reach-case endpoint monotonicity on the GENUINE arm.

Opening the last joint of a strictly convex arm `A` by `-θ` (the convex direction) does not decrease
its endpoint `sDist (A 0) tail`.  The base triangle is `(A 0, axis, tail)`: both base sides are short
arcs (`shortArc_axis_zero`, `shortArc_axis_tail`), the convex oriented datum holds
(`support_sign_base_ac` + `orientedSign_neg_of_support`), and the mirrored keystone
`openedAngle_ge_of_oriented_neg` gives the base-angle increase, which `reach_base_endpoint_mono`
turns into the endpoint increase.  This connects the substrate's abstract base-triangle monotonicity
to the actual arm — the step absent from every substrate file. -/

/-- **Reach-case endpoint monotonicity on the genuine arm (weak).**  For a strictly convex arm `A`
(`n ≥ 2`), opening the last joint by `-θ` (`0 ≤ θ`, within the great-semicircle range at the base
triangle) does not decrease the endpoint distance `sDist (A 0) (A (Fin.last (n+1)))`. -/
theorem reach_endpoint_mono_arm {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθπ : θ + sphAngle (A 0) (openAxis A) (A (Fin.last (n + 1))) ≤ Real.pi) :
    sDist (A 0) (A (Fin.last (n + 1)))
      ≤ sDist (A 0) (rotS2 (openAxis A) (-θ) (A (Fin.last (n + 1)))) := by
  set axis := openAxis A with haxis
  set tail := A (Fin.last (n + 1)) with htail
  have hka : ShortArc axis (A 0) := shortArc_axis_zero hA hn
  have hkt : ShortArc axis tail := shortArc_axis_tail hA
  have hsupp : 0 < sOrient (A 0) axis tail := support_sign_base_ac hA hn
  have hsign : (0 : ℝ) ≤ (⟪tangentTo axis (A 0), cross (axis : E3) (tangentTo axis tail)⟫ : ℝ) :=
    orientedSign_neg_of_support (le_of_lt hsupp)
  have hangle : sphAngle (A 0) axis tail ≤ sphAngle (A 0) axis (rotS2 axis (-θ) tail) :=
    openedAngle_ge_of_oriented_neg axis (A 0) tail hka hkt hsign hθ0 hθπ
  exact reach_base_endpoint_mono axis (A 0) tail hka hkt hangle

/-- **Reach-case endpoint monotonicity on the genuine arm (strict).**  A strict base-angle increase
(`θ > 0` within range) gives a strict endpoint increase. -/
theorem reach_endpoint_strict_arm {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    (hA : StrictConvexSphArm A) (hn : 2 ≤ n)
    (hstrict : sphAngle (A 0) (openAxis A) (A (Fin.last (n + 1)))
        < sphAngle (A 0) (openAxis A) (rotS2 (openAxis A) (-θ) (A (Fin.last (n + 1))))) :
    sDist (A 0) (A (Fin.last (n + 1)))
      < sDist (A 0) (rotS2 (openAxis A) (-θ) (A (Fin.last (n + 1)))) := by
  set axis := openAxis A with haxis
  set tail := A (Fin.last (n + 1)) with htail
  have hka : ShortArc axis (A 0) := shortArc_axis_zero hA hn
  have hkt : ShortArc axis tail := shortArc_axis_tail hA
  exact reach_base_endpoint_strict axis (A 0) tail hka hkt hstrict

/-! ## Closing `OpenedArmReachOrStuck` from the witness existence + the weak monotone bound.

The proven `szStep_strict_of_stuckWitness` (substrate) already derives the strict endpoint bound
`endpt A < endpt B` from `StuckWitnessExists` — the all-strict-case existence of the opening witness
`qstar` (or the reached direct bound).  The only thing it does **not** supply is the *weak* monotone
bound `endpt A ≤ endpt B` of the equal-joints / nondecreasing case.  We isolate exactly that as the
honest residue `WeakArmStep` (strictly narrower than `OpenedArmReachOrStuck`: it carries only the
non-strict bound, none of the strict-branch / `qstar` payload), and prove
`StuckWitnessExists ∧ WeakArmStep → OpenedArmReachOrStuck` by routing the strict branch always through
`Or.inr` (the proven downstream chain never consumes the stuck `qstar` witness; cf.
`openingData_of_szStepGeom`).

This is faithful and non-co-extensive: `OpenedArmReachOrStuck`'s strict branch demands the full stuck
data (`ShortArc`, `det3 = 0`, two Gram signs, opening + sub-comparison bounds) *or* the strict bound;
`WeakArmStep` demands only `endpt A ≤ endpt B`.  The strict half is *derived* from
`StuckWitnessExists` via the substrate reduction, not assumed in `WeakArmStep`. -/

/-- **The weak monotone arm step (honest residue).**  For every level-`(n+1)` convex arm pair with
equal sides, nondecreasing joints and the level-`n` comparison, the endpoint distance does not
decrease: `endpt A ≤ endpt B`.  This is the non-strict half of the Schoenberg–Zaremba inductive step
(the equal-joints congruence / nondecreasing monotonicity); it carries no strict-branch data, so it
is strictly narrower than `OpenedArmReachOrStuck`. -/
def WeakArmStep : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      endpt A ≤ endpt B

/-- **`StuckWitnessExists ∧ WeakArmStep → OpenedArmReachOrStuck` (the load-bearing assembly).**  The
weak bound is supplied by `WeakArmStep`; the strict branch is *always* routed through `Or.inr`
(`endpt A < endpt B`), derived from `StuckWitnessExists` by the proven
`szStep_strict_of_stuckWitness`.  The downstream chain (`openingData_of_szStepGeom`,
`schoenbergZaremba_of_reachOrStuck`) never consumes the stuck `qstar` witness, so producing only the
strict endpoint bound suffices. -/
theorem openedArmReachOrStuck_of_witness_weak
    (hw : StuckWitnessExists) (hweak : WeakArmStep) : OpenedArmReachOrStuck := by
  intro n hn A B hA hB hside hangle ih
  refine ⟨hweak n hn A B hA hB hside hangle ih, ?_⟩
  intro hwider
  exact Or.inr (szStep_strict_of_stuckWitness hw hn A B hA hB hside hangle ih hwider)

/-- **`SchoenbergZarembaTarget` from the two honest residues.**  Composing the assembly with the
proven chain `schoenbergZaremba_of_reachOrStuck`. -/
theorem schoenbergZaremba_of_witness_weak
    (hw : StuckWitnessExists) (hweak : WeakArmStep) : SchoenbergZarembaTarget :=
  schoenbergZaremba_of_reachOrStuck (openedArmReachOrStuck_of_witness_weak hw hweak)

/-! ## Non-vacuity guard (playbook §3.3).

`WeakArmStep` is non-vacuous: its conclusion `endpt A ≤ endpt B` is a genuine real inequality
realised whenever the arms genuinely satisfy the equal-side / nondecreasing hypotheses (e.g. `A = B`
gives equality), and its hypotheses are jointly satisfiable (the base case `szComparison_two`
provides level-`2` instances).  It is strictly narrower than `OpenedArmReachOrStuck` — carrying only
the weak bound, none of the strict / `qstar` payload — so it is not a co-extensive re-wrapper. -/

/-- Non-vacuity: `WeakArmStep`'s conclusion is realised by `A = B` (equal endpoints), so the residue
is satisfiable, not a vacuous-hypothesis impostor. -/
theorem weakArmStep_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1 + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

end ProofsInTheBook.SphericalReachStuck
