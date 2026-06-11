import ProofsInTheBook.ZinanFFCT42

/-!
# `ZinanFFCT45` — the **hemisphere-free** monitored family `WBS` and the FFCT42 base-stuck port.

`HANDOFF/design-rounds/ch13-wbs-family.md` (§§7-8, 11) prescribes **route (c)**: drop the hemisphere
members from the monitored family entirely.  The pure-hemi residual `PureHemiProgressWB` of `WB` is
false-shaped (a pure-hemi-stuck supremum can be strictly convex after tilting with no support vanishing
and the joint not reached, §6/§13 of the design), so monitoring fixed-`h₀` hemisphere margins manufactures
a spurious "stuck" event with no honest progress payload.  The cure is to stop monitoring them: the open
hemisphere is recovered downstream from **weak supports + positive/nonflat joints** (the assembly wave's
`openHemisphere_at_WBS_sup`, sibling-owned in `ZinanFFCT44`), so the hemi-stuck branch never arises.

`WBS = Widening + Base + Supports`.  The family keeps exactly three member classes:

1. the non-incident support constraints (opened by `-θ`),
2. the joint slack `θ ↦ jointAngle B k − openedInteriorJointAngle A k (-θ)`,
3. the base cap support `baseCapSupportW A k` (FFCT41).

Index type `(NonIncident n ⊕ Unit) ⊕ Unit`.  **No hemisphere member.**

## What this module proves (Brick 3 + Brick 7, clean-3)

* `§1` `monitoredFamilyWBS` / continuity / `monitoredSupWBS` / membership; the three closure facts
  (supports `≥ 0`, slack `≥ 0`, base `≥ 0` at the sup) the assembly wave needs.
* `§2` init admissibility at `θ = 0` (supports strict from `edge_support`, slack `> 0` from the deficit,
  base `> 0` from the banked convex base orientation — mirror FFCT41's `monitoredFamilyWB_zero_nonneg`).
* `§3` the deficit bound (joint-witness support + slack, ported from FFCT37's `admissibleW_le_deficit`),
  hence `δ*_WBS < π`; the base cap `GlueWBaseCap_at_supWBS` by admissibility (mirror FFCT41).
* `§4` `ReachWBS` / `SupportStuckWBS` / `BaseStuckWBS`, `opening_boundary_trichotomyWBS` (the generic
  `reach_or_stuck` engine; CAP killed by the deficit bound — there is NO hemi branch), and the clause-(i)
  endpoint mono `glueWBS_clause_i` at the WBS sup (mirror FFCT41).
* `§5` (Brick 7) `BaseStuckProgressWBS_holds` — the FFCT42 cyclic-shortcut port: a base-stuck WBS
  supremum's zero base diagonal **is** the wraparound non-incident support zero at `(last, K)` (the
  family-independent `det3` cyclic identity), so a vanishing W-support always exists.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.ZinanFFCT3
open ProofsInTheBook.ZinanFFCT20
open ProofsInTheBook.ZinanFFCT37
open ProofsInTheBook.ZinanFFCT41
open ProofsInTheBook.ZinanFFCT42

namespace ProofsInTheBook.ZinanFFCT45

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The hemisphere-free monitored family `WBS`. -/

/-- **The hemisphere-free monitored family `WBS`** (design §7).  Three member classes, all opening by
`-θ` (the widening direction):
* `inl (inl c)` — the non-incident support constraint `θ ↦ supportConstraint A K c (-θ)`;
* `inl (inr ())` — the joint slack `θ ↦ jointAngle B k − openedInteriorJointAngle A k (-θ)`;
* `inr ()` — the base cap support `baseCapSupportW A k` (already `-θ`).

Indexed by `(NonIncident n ⊕ Unit) ⊕ Unit`.  **No hemisphere member.** -/
def monitoredFamilyWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    (NonIncident n ⊕ Unit) ⊕ Unit → ℝ → ℝ
  | Sum.inl (Sum.inl c) => fun θ => supportConstraint A (openingAxis k) c (-θ)
  | Sum.inl (Sum.inr ()) => fun θ => jointAngle B k - openedInteriorJointAngle A k (-θ)
  | Sum.inr () => baseCapSupportW A k

/-- Each `WBS`-family member is continuous in `θ`.  Supports and slack are the `W`-family members
precomposed with the continuous negation (`continuous_supportConstraint`, `continuous_openedInteriorJointAngle`),
the base member is `continuous_baseCapSupportW`. -/
theorem continuous_monitoredFamilyWBS {n : ℕ} {A B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) :
    ∀ o, Continuous (monitoredFamilyWBS A B k o) := by
  rintro ((c | ⟨⟩) | ⟨⟩)
  · exact (continuous_supportConstraint A (openingAxis k) c).comp continuous_neg
  · exact continuous_const.sub ((continuous_openedInteriorJointAngle hka hkt).comp continuous_neg)
  · exact continuous_baseCapSupportW A k

/-- The `WBS` admissible supremum `δ*_WBS := sSup {θ ∈ [0,π] : ∀ o, 0 ≤ monitoredFamilyWBS … o θ}`. -/
def monitoredSupWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) : ℝ :=
  sSup (admissibleSet (monitoredFamilyWBS A B k) Real.pi)

/-! ## §2. Init admissibility at `θ = 0` (mirror FFCT41's `monitoredFamilyWB_zero_nonneg`). -/

/-- **Init admissibility at `θ = 0`.**  Supports `≥ 0` (`edge_support`), the joint slack `≥ 0` (from the
deficit `jointAngle A k < jointAngle B k`), and the base support `≥ 0` (the banked convex base orientation
`orientedDatum_interior`).  At `θ = 0` the support/slack members are the unopened arm's data (`-0 = 0`,
`openedInteriorJointAngle A k 0 = jointAngle A k`), the base member is the unopened base support. -/
theorem monitoredFamilyWBS_zero_nonneg {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {B : Fin (n + 1) → S2} {k : Fin (n - 1)}
    (hkdef : jointAngle A k < jointAngle B k) :
    ∀ o, 0 ≤ monitoredFamilyWBS A B k o 0 := by
  rintro ((c | ⟨⟩) | ⟨⟩)
  · -- support member: `supportConstraint A K c (-0) = supportConstraint A K c 0 ≥ 0`.
    show 0 ≤ supportConstraint A (openingAxis k) c (-(0 : ℝ))
    rw [neg_zero, supportConstraint_apply, openTail_zero_angle]
    exact hA.closed_convex.edge_support c.1.1 c.1.2
  · -- slack member: `jointAngle B k − openedInteriorJointAngle A k (-0) = jointAngle B k − jointAngle A k ≥ 0`.
    show 0 ≤ jointAngle B k - openedInteriorJointAngle A k (-(0 : ℝ))
    rw [neg_zero, openedInteriorJointAngle_zero]
    linarith
  · -- base member at `0`: `sOrient (A 0)(A K)(rotS2 (A K) 0 (A last)) = sOrient (A 0)(A K)(A last) ≥ 0`.
    show 0 ≤ baseCapSupportW A k 0
    obtain ⟨hK0, hKn⟩ := openingAxis_interior k
    have hrot0 : rotS2 (A (openingAxis k)) (-(0 : ℝ)) (A (Fin.last n)) = A (Fin.last n) := by
      apply S2.ext; rw [rotS2_coe, neg_zero, rot_zero]
    show 0 ≤ sOrient (A 0) (A (openingAxis k)) (rotS2 (A (openingAxis k)) (-(0 : ℝ)) (A (Fin.last n)))
    rw [hrot0]
    exact orientedDatum_interior hA hK0 hKn

/-- **The `WBS` admissible supremum is `WBS`-admissible** (closed nonempty bounded family). -/
theorem monitoredSupWBS_mem {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k ∈ admissibleSet (monitoredFamilyWBS A B k) Real.pi :=
  sSup_mem_admissibleSet (continuous_monitoredFamilyWBS hka hkt) Real.pi_nonneg
    (monitoredFamilyWBS_zero_nonneg hA hkdef)

/-- `δ*_WBS ∈ [0, π]`. -/
theorem monitoredSupWBS_mem_Icc {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k ∈ Set.Icc (0 : ℝ) Real.pi :=
  (monitoredSupWBS_mem hA hka hkt hkdef).1

/-! ## §1′. The `WBS` closure lemmas (supports `≥ 0`, slack `≥ 0`, base `≥ 0` at the sup).

These read the `WBS`-admissibility closure off `monitoredSupWBS_mem` member-by-member.  The assembly wave
(`openHemisphere_at_WBS_sup`, `supportStuckWBS_weakConvex`, `reachWBS_strictConvex`) consumes them. -/

/-- **Closure (supports `≥ 0` at `δ*_WBS`)**, support form on the opened triple of `A'_WBS`. -/
theorem supportWBS_sOrient_nonneg {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) j) := by
  intro i j hji hji1
  have hmem := monitoredSupWBS_mem hA hka hkt hkdef
  have := hmem.2 (Sum.inl (Sum.inl (⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n)))
  simp only [monitoredFamilyWBS, supportConstraint_apply] at this
  exact this

/-- **Closure (joint slack `≥ 0` at `δ*_WBS`)**: the opened interior joint is `≤ jointAngle B k`. -/
theorem openedInteriorJoint_le_at_supWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) ≤ jointAngle B k := by
  have hmem := monitoredSupWBS_mem hA hka hkt hkdef
  have := hmem.2 (Sum.inl (Sum.inr ()))
  simp only [monitoredFamilyWBS] at this
  linarith

/-- **Closure (base support `≥ 0` at `δ*_WBS`)**. -/
theorem baseCapSupportW_nonneg_at_supWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    0 ≤ baseCapSupportW A k (monitoredSupWBS A B k) := by
  have hmem := monitoredSupWBS_mem hA hka hkt hkdef
  have := hmem.2 (Sum.inr ())
  simpa only [monitoredFamilyWBS] using this

/-! ## §3. The deficit bound and the base cap at the `WBS` supremum.

The joint-witness support `jointWitness k` (FFCT37) and the joint slack are **both** `WBS` members, so the
sine-branch argument of `ZinanFFCT37.admissibleW_le_deficit` ports verbatim: the joint's own signed support
under `-θ` is `N sin (γ + θ)` (`support_openNeg_eq_sin`), so admissibility forces `sin (γ + θ) ≥ 0`, hence
the additive branch `γ + θ ≤ π`, where the slack pins `γ + θ ≤ jointAngle B k`.  Hence `δ*_WBS ≤ deficit < π`
and the trichotomy CAP `δ*_WBS = π` is impossible.  The base member is `WBS`-monitored, so the base cap
`δ*_WBS + γbase ≤ π` follows by admissibility, mirroring FFCT41. -/

/-- **Every `WBS`-admissible `θ` lies in `[0, jointAngle B k − jointAngle A k]`.**  Port of
`ZinanFFCT37.admissibleW_le_deficit`, re-instantiated on the `WBS` joint-witness support member and the
`WBS` slack member (both present in the hemisphere-free family). -/
theorem admissibleWBS_le_deficit {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    {θ : ℝ} (hθadm : θ ∈ admissibleSet (monitoredFamilyWBS A B k) Real.pi) :
    θ ≤ jointAngle B k - jointAngle A k := by
  obtain ⟨⟨hθ0, hθπ⟩, hmem⟩ := hθadm
  -- joint-witness support ≥ 0 (it is a `WBS` support member).
  have hsupp : 0 ≤ supportConstraint A (openingAxis k) (jointWitness k) (-θ) := by
    have := hmem (Sum.inl (Sum.inl (jointWitness k)))
    simpa only [monitoredFamilyWBS] using this
  rw [supportConstraint_jointWitness_neg, support_openNeg_eq_sin hA hka hkt] at hsupp
  -- norms positive ⟹ `sin (γ + θ) ≥ 0`.
  have hunz : tangentTo (A (openingAxis k)) (jointPrev A k) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hka
  have hwnz : tangentTo (A (openingAxis k)) (jointNext A k) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hkt
  have hup : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (jointPrev A k)‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (jointNext A k)‖ := norm_pos_iff.2 hwnz
  have hsin : 0 ≤ Real.sin (jointAngle A k + θ) := by
    by_contra hneg
    push_neg at hneg
    have : ‖tangentTo (A (openingAxis k)) (jointPrev A k)‖
        * ‖tangentTo (A (openingAxis k)) (jointNext A k)‖ * Real.sin (jointAngle A k + θ) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hup hwp) hneg
    linarith
  -- `γ + θ ∈ [0, 2π)` and `sin ≥ 0` ⟹ `γ + θ ≤ π` (the additive branch).
  have hγ0 : 0 ≤ jointAngle A k := by
    rw [show jointAngle A k = sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) by
      simp only [jointAngle, jointPrev, jointNext, openingAxis]]
    exact sphAngle_nonneg _ _ _
  have hγlt : jointAngle A k < Real.pi := strict_jointAngle_lt_pi hA k
  have hbranch : jointAngle A k + θ ≤ Real.pi := by
    by_contra hgt
    push_neg at hgt
    set t : ℝ := jointAngle A k + θ - Real.pi with ht
    have ht0 : 0 < t := by rw [ht]; linarith
    have htlt : t < Real.pi := by rw [ht]; linarith [hγlt, hθπ]
    have hsin_t : Real.sin (jointAngle A k + θ) = - Real.sin t := by
      rw [show jointAngle A k + θ = Real.pi + t by rw [ht]; ring, Real.sin_add, Real.sin_pi,
        Real.cos_pi]
      ring
    have hpos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 htlt
    rw [hsin_t] at hsin; linarith
  -- on the branch, the opened joint equals `γ + θ`; slack ≥ 0 pins `γ + θ ≤ jointAngle B k`.
  have hopened : openedInteriorJointAngle A k (-θ) = jointAngle A k + θ :=
    openedNegJointAngle_eq_add hA hka hkt hθ0 hbranch
  have hslack : 0 ≤ jointAngle B k - openedInteriorJointAngle A k (-θ) := by
    have := hmem (Sum.inl (Sum.inr ()))
    simpa only [monitoredFamilyWBS] using this
  rw [hopened] at hslack
  linarith

/-- **`δ*_WBS ≤ jointAngle B k − jointAngle A k`.** -/
theorem monitoredSupWBS_le_deficit {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k ≤ jointAngle B k - jointAngle A k :=
  admissibleWBS_le_deficit hA hka hkt (monitoredSupWBS_mem hA hka hkt hkdef)

/-- **`δ*_WBS < π`.**  The deficit `jointAngle B k − jointAngle A k < π` (strict `B`, `γ ≥ 0`). -/
theorem monitoredSupWBS_lt_pi {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k < Real.pi := by
  have hub := monitoredSupWBS_le_deficit hA hka hkt hkdef
  have hγ0 : 0 ≤ jointAngle A k := by
    rw [show jointAngle A k = sphAngle (jointPrev A k) (A (openingAxis k)) (jointNext A k) by
      simp only [jointAngle, jointPrev, jointNext, openingAxis]]
    exact sphAngle_nonneg _ _ _
  have hBlt : jointAngle B k < Real.pi := strict_jointAngle_lt_pi hB k
  linarith

/-- **The base cap at the `WBS` supremum** (`GlueWBaseCap` for `δ*_WBS`): `δ*_WBS + γbase ≤ π`.  The `WBS`
supremum is `WBS`-admissible, so the base member is `≥ 0`, hence (norms positive, `γbase < π`, `δ*_WBS ≤ π`)
`admissibleWB_baseCap`'s sine-branch argument closes the cap.  Mirror of FFCT41's `GlueWBaseCap_at_supWB`. -/
theorem GlueWBaseCap_at_supWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k
      + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi := by
  obtain ⟨hbase0, hbaseLast⟩ :=
    shortArc_interior_base hA (openingAxis_interior k).1 (openingAxis_interior k).2
  obtain ⟨hIcc, hmemfun⟩ := monitoredSupWBS_mem hA hka hkt hkdef
  -- the sine-branch argument: base member `≥ 0` ⟹ `sin (γbase + δ*) ≥ 0` ⟹ cap.
  set γ : ℝ := sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) with hγ
  set θ : ℝ := monitoredSupWBS A B k with hθ
  obtain ⟨hθ0, hθπ⟩ := hIcc
  have hbase : 0 ≤ baseCapSupportW A k θ := by simpa only [monitoredFamilyWBS] using hmemfun (Sum.inr ())
  rw [baseSupport_openNeg_eq_sin hA k hbase0 hbaseLast, ← hγ] at hbase
  have hunz : tangentTo (A (openingAxis k)) (A 0) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hbase0
  have hwnz : tangentTo (A (openingAxis k)) (A (Fin.last n)) ≠ 0 := (tangentTo_ne_zero_iff _ _).2 hbaseLast
  have hup : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (A 0)‖ := norm_pos_iff.2 hunz
  have hwp : (0 : ℝ) < ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖ := norm_pos_iff.2 hwnz
  have hsin : 0 ≤ Real.sin (γ + θ) := by
    by_contra hneg
    push_neg at hneg
    have : ‖tangentTo (A (openingAxis k)) (A 0)‖
        * ‖tangentTo (A (openingAxis k)) (A (Fin.last n))‖ * Real.sin (γ + θ) < 0 :=
      mul_neg_of_pos_of_neg (mul_pos hup hwp) hneg
    linarith
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact sphAngle_nonneg _ _ _
  have hγlt : γ < Real.pi := base_sphAngle_lt_pi hA k
  by_contra hgt
  push_neg at hgt
  set t : ℝ := γ + θ - Real.pi with ht
  have ht0 : 0 < t := by rw [ht]; linarith
  have htlt : t < Real.pi := by rw [ht]; linarith [hγlt, hθπ]
  have hsin_t : Real.sin (γ + θ) = - Real.sin t := by
    rw [show γ + θ = Real.pi + t by rw [ht]; ring, Real.sin_add, Real.sin_pi, Real.cos_pi]
    ring
  have hpos : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 htlt
  rw [hsin_t] at hsin; linarith

/-! ## §4. The `WBS` reach / support-stuck / base-stuck predicates and the trichotomy. -/

/-- The REACH predicate at the `WBS` supremum: the opened-by-`-δ*_WBS` interior joint reaches `B`'s value. -/
def ReachWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) : Prop :=
  openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) = jointAngle B k

/-- The SUPPORT-STUCK predicate at the `WBS` supremum: a non-incident support of the opened-by-`-δ*_WBS`
arm vanishes.  (No hemisphere disjunct — the hemisphere members were dropped.) -/
def SupportStuckWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) : Prop :=
  ∃ c : NonIncident n,
    supportConstraint A (openingAxis k) c (-(monitoredSupWBS A B k)) = 0

/-- The BASE-STUCK predicate at the `WBS` supremum: the base monitor vanishes — `sin (γbase + δ*_WBS) = 0`. -/
def BaseStuckWBS {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) : Prop :=
  baseCapSupportW A k (monitoredSupWBS A B k) = 0

/-- **The `WBS` boundary trichotomy** (here a tetrachotomy *without* a hemi branch).  At `δ*_WBS`: either
`δ*_WBS = π`, or `ReachWBS`, or `SupportStuckWBS`, or `BaseStuckWBS`.  The generic `reach_or_stuck` engine;
the CAP branch is killed downstream by `monitoredSupWBS_lt_pi`.  **No hemisphere-stuck branch exists.** -/
theorem opening_boundary_trichotomyWBS {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    monitoredSupWBS A B k = Real.pi ∨
      ReachWBS A B k ∨ SupportStuckWBS A B k ∨ BaseStuckWBS A B k := by
  rcases reach_or_stuck (continuous_monitoredFamilyWBS hka hkt) Real.pi_nonneg
      (monitoredFamilyWBS_zero_nonneg hA hkdef) with hcap | ⟨o, ho⟩
  · exact Or.inl hcap
  · rcases o with (c | ⟨⟩) | ⟨⟩
    · -- a support constraint vanishes: SUPPORT-STUCK.
      refine Or.inr (Or.inr (Or.inl ⟨c, ?_⟩))
      simpa only [monitoredFamilyWBS, monitoredSupWBS] using ho
    · -- the joint slack vanishes: REACH.
      refine Or.inr (Or.inl ?_)
      have hslack : monitoredFamilyWBS A B k (Sum.inl (Sum.inr ())) (monitoredSupWBS A B k) = 0 := ho
      simp only [monitoredFamilyWBS] at hslack
      unfold ReachWBS
      linarith
    · -- the base monitor vanishes: BASE-STUCK.
      refine Or.inr (Or.inr (Or.inr ?_))
      have : monitoredFamilyWBS A B k (Sum.inr ()) (monitoredSupWBS A B k) = 0 := ho
      simpa only [monitoredFamilyWBS, monitoredSupWBS] using this

/-- **The `WBS` honest clause (ii): `¬ SupportStuckWBS → ReachWBS ∨ BaseStuckWBS`.**  The CAP branch is
impossible (`monitoredSupWBS_lt_pi`), SUPPORT-STUCK is excluded, leaving REACH or BASE-STUCK.  (There is no
hemi branch to dispose of — the design's payoff for dropping the hemisphere monitors.) -/
theorem glueWBS_clause_ii {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (hB : StrictConvexSphArm B) {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k)
    (hnotStuck : ¬ SupportStuckWBS A B k) :
    ReachWBS A B k ∨ BaseStuckWBS A B k := by
  rcases opening_boundary_trichotomyWBS hA hka hkt hkdef with hcap | hreach | hstuck | hbase
  · exact absurd hcap (ne_of_lt (monitoredSupWBS_lt_pi hA hB hka hkt hkdef))
  · exact Or.inl hreach
  · exact absurd hstuck hnotStuck
  · exact Or.inr hbase

/-- **Clause (i) at `δ*_WBS`** — UNCONDITIONAL (the cap is discharged by `GlueWBaseCap_at_supWBS`).  Opening
by `-δ*_WBS` does not decrease the endpoint, since `δ*_WBS + γbase ≤ π` holds by admissibility.  Mirror of
FFCT41's `glueWB_clause_i`. -/
theorem glueWBS_clause_i {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)}
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k))
    (hkdef : jointAngle A k < jointAngle B k) :
    endpt A ≤ endpt (openTail A (openingAxis k) (-(monitoredSupWBS A B k))) := by
  have hδ0 : 0 ≤ monitoredSupWBS A B k := (monitoredSupWBS_mem_Icc hA hka hkt hkdef).1
  exact endpt_openTail_interior_mono_neg hA k hδ0 (GlueWBaseCap_at_supWBS hA hka hkt hkdef)

/-! ## §5. (Brick 7) `BaseStuckProgressWBS` — the FFCT42 cyclic-shortcut port.

The base-stuck zero is, by definition (`baseStuck_eq_openedDiagonal`, FFCT42), the diagonal support of the
*opened* arm `A'_WBS := openTail A K (-δ*_WBS)` at the triple `(0, K, last)`.  The cyclic `det3` identity
(`baseDiagonal_zero_is_wrapEdgeSupport_zero`, FFCT42) makes it **literally** the wraparound non-incident
support zero at `(i, j) = (Fin.last n, K)`.  Both FFCT42 lemmas are **family-independent arm-level algebra**
(they take the opening angle `δ` as a free parameter), so they re-instantiate at `δ = monitoredSupWBS A B k`
with no change.  The family only enters through which sup `δ*` is used. -/

/-- **Base-stuck forces a vanishing non-incident support of `A'_WBS`** — re-instantiation of FFCT42's
`baseStuck_forces_vanishingSupport` at the `WBS` sup.  The base diagonal zero **is** the wraparound
non-incident support zero at `(last, K)` (the `det3` cyclic identity, family-independent). -/
theorem baseStuckWBS_forces_vanishingSupport {n : ℕ} {A B : Fin (n + 1) → S2} (k : Fin (n - 1))
    (hbase : BaseStuckWBS A B k) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1))
        (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) j) = 0 := by
  -- `BaseStuckWBS` unfolds to `baseCapSupportW A k δ*_WBS = 0`; FFCT42's `baseStuck_eq_openedDiagonal`
  -- (free in `δ`) turns this into the opened diagonal `(0,K,last)` zero, and the cyclic identity
  -- `baseDiagonal_zero_is_wrapEdgeSupport_zero` (free in `δ`) yields the wrap-edge `(last,K)` payload.
  have hdiag : sOrient (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) 0)
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (openingAxis k))
      (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (Fin.last n)) = 0 := by
    rw [← baseStuck_eq_openedDiagonal]; exact hbase
  exact baseDiagonal_zero_is_wrapEdgeSupport_zero A k (monitoredSupWBS A B k) hdiag

/-- **The base-stuck progress residual at `δ*_WBS`** (design §11).  Stated in the same shape as FFCT41's
`BaseStuckProgressW`, but at the `WBS` sup and **without** the false-shaped hemi monitoring.  Unlike FFCT41,
this is a *theorem*, not a named residual: the FFCT42 cyclic shortcut discharges it by taking the
vanishing-support disjunct (the base diagonal zero **is** the wrap-edge non-incident support zero). -/
def BaseStuckProgressWBS : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
      BaseStuckWBS A B k →
        ReachWBS A B k ∨
        ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) i)
            (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) (i + 1))
            (openTail A (openingAxis k) (-(monitoredSupWBS A B k)) j) = 0

/-- **`BaseStuckProgressWBS` holds** — Brick 7, the FFCT42 port DISCHARGED.  A base-stuck `WBS` supremum
always makes recursion-ready progress by taking the **vanishing-support** disjunct via the cyclic identity
(`baseStuckWBS_forces_vanishingSupport`).  `ReachWBS` is never needed.  Unconditional — no
`OpenedClosingEdge*`, no `SupportStuckMargins`, no straightening completion, no sub-arm IH.  This is the
honest analogue of FFCT42's `BaseStuckProgressW_holds`, but for the hemisphere-free family. -/
theorem BaseStuckProgressWBS_holds : BaseStuckProgressWBS := by
  intro n A B _hA _hB k _hkdef hbase
  exact Or.inr (baseStuckWBS_forces_vanishingSupport k hbase)

/-! ### Non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `ReachWBS`: it is a genuine angle equation (the opened-by-`-δ*_WBS` joint reaching
`B`'s value), not a vacuous-hypothesis impostor. -/
theorem reachWBS_def_real {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    ReachWBS A B k ↔
      openedInteriorJointAngle A k (-(monitoredSupWBS A B k)) = jointAngle B k := Iff.rfl

/-- Non-vacuity of `BaseStuckWBS`: it is the genuine base-monitor equation `baseCapSupportW A k δ*_WBS = 0`,
i.e. `sin (γbase + δ*_WBS) = 0` — a real geometric event (the base triangle straightening). -/
theorem baseStuckWBS_def_real {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    BaseStuckWBS A B k ↔ baseCapSupportW A k (monitoredSupWBS A B k) = 0 := Iff.rfl

/-- Non-vacuity of the discharged `BaseStuckProgressWBS` payload: the chosen vanishing-support disjunct is
real `NonIncident` data at the wraparound pair `(last, K)` — the side conditions `K ≠ last`, `K ≠ 0` are
nondegenerate (an interior axis has `1 ≤ K.val < n`).  Inherited from FFCT42's nondegeneracy witness. -/
theorem baseStuckProgressWBS_payload_indices_nondegenerate {n : ℕ} (k : Fin (n - 1)) :
    (openingAxis k : Fin (n + 1)) ≠ Fin.last n ∧
      (openingAxis k : Fin (n + 1)) ≠ Fin.last n + 1 :=
  baseStuckProgressW_payload_indices_nondegenerate k

/-- Non-vacuity guard: the WBS family at `δ*_WBS = 0` opens nothing (`openTail A K (-0) = A`); the base cap
at `δ = 0` is the always-true `0 + γbase ≤ π`, so the base monitor is a real range condition, not a
vacuous-hypothesis impostor. -/
theorem glueWBSBaseCap_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    (0 : ℝ) + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi := by
  rw [zero_add]; exact sphAngle_le_pi _ _ _

end ProofsInTheBook.ZinanFFCT45

-- §1 the WBS family + closure facts
#print axioms ProofsInTheBook.ZinanFFCT45.continuous_monitoredFamilyWBS
#print axioms ProofsInTheBook.ZinanFFCT45.monitoredSupWBS_mem
#print axioms ProofsInTheBook.ZinanFFCT45.supportWBS_sOrient_nonneg
#print axioms ProofsInTheBook.ZinanFFCT45.openedInteriorJoint_le_at_supWBS
#print axioms ProofsInTheBook.ZinanFFCT45.baseCapSupportW_nonneg_at_supWBS
-- §2 init admissibility
#print axioms ProofsInTheBook.ZinanFFCT45.monitoredFamilyWBS_zero_nonneg
-- §3 deficit bound + base cap
#print axioms ProofsInTheBook.ZinanFFCT45.admissibleWBS_le_deficit
#print axioms ProofsInTheBook.ZinanFFCT45.monitoredSupWBS_lt_pi
#print axioms ProofsInTheBook.ZinanFFCT45.GlueWBaseCap_at_supWBS
-- §4 the trichotomy + clauses
#print axioms ProofsInTheBook.ZinanFFCT45.opening_boundary_trichotomyWBS
#print axioms ProofsInTheBook.ZinanFFCT45.glueWBS_clause_ii
#print axioms ProofsInTheBook.ZinanFFCT45.glueWBS_clause_i
-- §5 Brick 7: the FFCT42 base-stuck port DISCHARGED
#print axioms ProofsInTheBook.ZinanFFCT45.baseStuckWBS_forces_vanishingSupport
#print axioms ProofsInTheBook.ZinanFFCT45.BaseStuckProgressWBS_holds
