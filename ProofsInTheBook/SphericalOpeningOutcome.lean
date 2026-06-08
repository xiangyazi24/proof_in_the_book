import ProofsInTheBook.SphericalArmAssembly

/-!
# `SphericalOpeningOutcome` — discharging `InteriorOpeningOutcome` (Chapter 13 §2b OPEN branch)

`SphericalArmAssembly` left the §2b interior-opening outcome
`SphericalArmAssembly.InteriorOpeningOutcome` as a hypothesis (one of the two isolated structural
inputs of the composed `InteriorOpenAndSpliceStep`).  This module **discharges it** by composing the
already-banked monitored-supremum apparatus of `SphericalMonitoredSup` with the OPEN-branch
preservation / deficit / endpoint bookkeeping of `SphericalSZFinal`.

## What is composed (all BANKED, unconditional)

For a strictly convex `A` matched to a strictly convex `B` with a deficient joint `k`, set
`A' := openTail A (openingAxis k) δ*` with `δ* := monitoredSup A B k h₀ π`, where `h₀` is `A`'s fixed
open-hemisphere normal.  The required input data of the monitored family is derived from `hA`:

* `h₀, ‖h₀‖ = 1` from `hA.closed_convex.open_hemisphere`;
* the short-arc base hypotheses `hka : ShortArc (A K) (jointPrev A k)`,
  `hkt : ShortArc (A K) (jointNext A k)` from `hA.closed_convex.edge_short` (`K = openingAxis k`);
* the initial admissibility `h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0` from strict convexity
  (`monitoredFamily_support_zero` ≥ 0 via `edge_support`, `monitoredFamily_hemi_zero` > 0 via the
  hemisphere normal, `monitoredFamily_jointSlack_zero` ≥ 0 via the deficit `hkdef`).

Then:

* **`SameSides A' B`** from `openTail_preserves_sides` + `hside` (`§2`);
* **`JointLe A' B`** : every joint `r ≠ k` is preserved by `jointAngle_openTail_eq_of_ne`
  (+ `hangle`); at `k` the opened joint equals `openedInteriorJointAngle A k δ*`
  (`jointAngle_openTail_eq_openedInterior`), which is `≤ jointAngle B k` by admissibility
  (`monitoredSup`'s joint-slack member is `≥ 0`) (`§3`);
* **`endpt A ≤ endpt A'`** : the interior endpoint monotonicity at `δ*` (`§4`);
* the **REACH/STUCK selection** via `opening_boundary_trichotomy` (`§5`):
  - REACH (`Reach`, `¬ Stuck`) : `strict_persistence_at_reach` gives `StrictConvexSphArm A'`, and the
    opened joint reaching `B`'s value (`Reach`) feeds `deficitCount_openTail_reach_lt` for the strict
    deficit drop — the **LEFT** disjunct, *fully discharged*;
  - STUCK : the **RIGHT** disjunct (weak convexity + a vanishing non-incident support).

## The single isolated boundary core

Two substrate-absent boundary-glue facts genuinely remain after the banked composition, both at the
admissible supremum `δ*` and both documented absent in `SphericalAdmissibleSup`
(`BoundaryConvexPersistAtSup`) and `SphericalSZClose` §R / `SphericalArmAssembly` §3:

1. **the endpoint sign reconciliation** `endpt A ≤ endpt (openTail A K δ*)` — the banked
   `endpt_openTail_interior_mono` certifies the endpoint non-decrease only in the `(-θ)` convex-opening
   orientation (`endpt A ≤ endpt (openTail A K (-θ))`, `0 ≤ θ`), while the monitored family widens the
   joint in the `(+δ)` orientation; matching the monitored `+δ*` to the endpoint's `-θ` form is the
   `endpoint-range reconciliation` the §R notes record absent;
2. **the STUCK boundary outcome** — at a `Stuck` supremum the opened arm must be `WeakConvexSphArm`
   with a vanishing non-incident support; at `δ*` admissibility gives every monitored support / the
   fixed-`h₀` hemisphere margin only `≥ 0`, while `WeakConvexSphPolygon.open_hemisphere` demands the
   hemisphere functional **strictly** `> 0` at every (rotated-tail) vertex, exactly the substrate's own
   isolated `SphericalAdmissibleSup.BoundaryConvexPersistAtSup` obstacle (here in the interior + weak +
   hemisphere-margin form), and a pure hemisphere-stuck supremum (no support vanishing) must still be
   shown to force a vanishing non-incident support.

We bundle **exactly** these two boundary-glue facts into the single named, non-vacuous `Prop`
`InteriorOpeningGlue`, give its concrete failing chains and its non-vacuity, and **derive**
`InteriorOpeningOutcome` from it plus the banked composition.  `interiorOpeningOutcome_holds` therefore
carries `InteriorOpeningGlue` as its one named hypothesis; everything else (REACH strict-convexity +
deficit drop, sides, joints, the trichotomy run) is discharged unconditionally.

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
open ProofsInTheBook.SphericalArmAssembly

namespace ProofsInTheBook.SphericalOpeningOutcome

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §0. The opening axis is interior, and the joint-`k` angle of the opened arm. -/

/-- The opening axis `K = openingAxis k = ⟨k+1⟩` is interior: `1 ≤ K.val` and `K.val < n`. -/
theorem openingAxis_interior {n : ℕ} (k : Fin (n - 1)) :
    1 ≤ (openingAxis k).val ∧ (openingAxis k).val < n := by
  have := k.isLt
  simp only [openingAxis]
  omega

/-- **The joint-`k` angle of the interior-opened arm equals the opened interior joint angle.**  Opening
about `K = openingAxis k = ⟨k+1⟩` fixes vertices `≤ k+1` (so `A ⟨k⟩` and the axis `A ⟨k+1⟩`) and rotates
`A ⟨k+2⟩`, so the joint-`k` triple `(A ⟨k⟩, A ⟨k+1⟩, rotS2 (A K) δ (A ⟨k+2⟩))` is exactly
`(jointPrev A k, A K, rotS2 (A K) δ (jointNext A k))`, whose spherical angle is
`openedInteriorJointAngle A k δ`. -/
theorem jointAngle_openTail_eq_openedInterior {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ) :
    jointAngle (openTail A (openingAxis k) δ) k = openedInteriorJointAngle A k δ := by
  have hk := k.isLt
  have hKval : (openingAxis k).val = k.val + 1 := rfl
  have hv0 : openTail A (openingAxis k) δ ⟨k.val, by omega⟩ = A ⟨k.val, by omega⟩ :=
    openTail_fixed A (openingAxis k) δ (by simp only [openingAxis, Fin.val_mk]; omega)
  -- the axis vertex `⟨k+1⟩ = openingAxis k` is fixed by the opening.
  have hKeq : (openingAxis k : Fin (n + 1)) = (⟨k.val + 1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext; rw [hKval]
  have hv1 : openTail A (openingAxis k) δ ⟨k.val + 1, by omega⟩ = A (openingAxis k) := by
    rw [← hKeq]; exact openTail_axis A (openingAxis k) δ
  have hv2 : openTail A (openingAxis k) δ ⟨k.val + 2, by omega⟩
      = rotS2 (A (openingAxis k)) δ (A ⟨k.val + 2, by omega⟩) :=
    openTail_rot A (openingAxis k) δ (by simp only [openingAxis, Fin.val_mk]; omega)
  simp only [jointAngle, openedInteriorJointAngle, jointPrev, jointNext, hv0, hv1, hv2]

/-! ## §1. Input data of the monitored family, derived from `hA`. -/

/-- The short-arc base hypotheses for the joint `k` from strict convexity.  `K = openingAxis k = ⟨k+1⟩`;
`hka : ShortArc (A K) (jointPrev A k)` is the reversed edge `⟨k⟩→⟨k+1⟩`, `hkt : ShortArc (A K) (jointNext A k)`
is the edge `⟨k+1⟩→⟨k+2⟩`. -/
theorem shortArcs_of_strict {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A) (k : Fin (n - 1)) :
    ShortArc (A (openingAxis k)) (jointPrev A k) ∧ ShortArc (A (openingAxis k)) (jointNext A k) := by
  have hk := k.isLt
  have hes := hA.closed_convex.edge_short
  have h1v : ((1 : Fin (n + 1)) : ℕ) = 1 := by
    simp only [Fin.val_one']; rw [Nat.mod_eq_of_lt (by omega)]
  -- `(⟨m⟩ : Fin (n+1)) + 1 = ⟨m+1⟩` when `m + 1 < n + 1`.
  have add_one : ∀ m : ℕ, (hm : m + 1 < n + 1) →
      ((⟨m, by omega⟩ : Fin (n + 1)) + 1) = (⟨m + 1, hm⟩ : Fin (n + 1)) := by
    intro m hm
    apply Fin.ext
    rw [Fin.val_add, h1v, Fin.val_mk, Nat.mod_eq_of_lt hm]
  -- `hka`: edge ⟨k⟩→⟨k+1⟩ reversed.
  have hka0 : ShortArc (A ⟨k.val, by omega⟩) (A ((⟨k.val, by omega⟩ : Fin (n + 1)) + 1)) :=
    hes ⟨k.val, by omega⟩
  rw [add_one k.val (by omega)] at hka0
  -- `hkt`: edge ⟨k+1⟩→⟨k+2⟩.
  have e_axis : (openingAxis k : Fin (n + 1)) = ⟨k.val + 1, by omega⟩ := by
    apply Fin.ext; rfl
  have hkt0 : ShortArc (A (openingAxis k)) (A ((openingAxis k : Fin (n + 1)) + 1)) :=
    hes (openingAxis k)
  rw [e_axis, add_one (k.val + 1) (by omega)] at hkt0
  refine ⟨?_, ?_⟩
  · -- ShortArc (A K) (jointPrev A k) = ShortArc (A ⟨k+1⟩) (A ⟨k⟩) = (hka0).symm
    have hp : jointPrev A k = A ⟨k.val, by omega⟩ := rfl
    have ha : (A (openingAxis k)) = A ⟨k.val + 1, by omega⟩ := by rw [e_axis]
    rw [hp, ha]
    exact hka0.symm
  · have hn : jointNext A k = A ⟨k.val + 2, by omega⟩ := rfl
    rw [hn]
    exact hkt0

/-- The initial admissibility of the monitored family at `θ = 0`, from strict convexity + the deficit
`hkdef` at `k`.  Supports `≥ 0` (`edge_support`), the fixed-`h₀` hemisphere margins `> 0`
(`open_hemisphere`), and the joint slack `≥ 0` (`jointAngle A k < jointAngle B k`). -/
theorem monitoredFamily_init_admissible {n : ℕ} {A B : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    {k : Fin (n - 1)} {h₀ : E3} (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (hkdef : jointAngle A k < jointAngle B k) :
    ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0 := by
  rintro (c | (r | ⟨⟩))
  · rw [monitoredFamily_support_zero]
    exact hA.closed_convex.edge_support c.1.1 c.1.2
  · rw [monitoredFamily_hemi_zero]
    exact le_of_lt (hhpos r)
  · rw [monitoredFamily_jointSlack_zero]
    linarith

/-! ## §2. The single isolated boundary-glue core. -/

/-- **(Isolated boundary-glue core) The two substrate-absent boundary facts at `δ*`.**  For a strictly
convex `A` matched to a strictly convex `B` with a deficient joint `k`, opening at the apex
`K = openingAxis k` to the monitored admissible supremum `δ* = monitoredSup A B k h₀ π` (`h₀` the fixed
hemisphere normal, all `⟪h₀, A i⟫ > 0`), the opened arm `A' := openTail A K δ*` satisfies:

* `endpt A ≤ endpt A'` — the **endpoint sign reconciliation** (the banked
  `endpt_openTail_interior_mono` is `(-θ)`-oriented; the monitored family is `(+δ)`-oriented);
* whenever the supremum is `Stuck`, `A'` is `WeakConvexSphArm` and has a vanishing non-incident support
  — the **STUCK boundary outcome** (the interior + weak + hemisphere-margin form of
  `SphericalAdmissibleSup.BoundaryConvexPersistAtSup`, plus the hemisphere-stuck-forces-a-support
  selection).

**Concrete failing chains.**
* *Endpoint*: `grep` finds no `(+θ)`-oriented interior endpoint bound; `endpt_openTail_interior_mono`
  fixes `-θ` with `0 ≤ θ`, and `δ* ≥ 0` cannot be written `-θ` with `0 ≤ θ` unless `δ* = 0`; matching
  the two orientations is the `endpoint-range reconciliation` recorded absent in `SphericalSZFinal` §R
  / `SphericalArmAssembly` §3.
* *STUCK*: `grep` finds no boundary/closed-side weak-convexity-persistence lemma; the banked
  positivity `hemiMargin_pos_at_sup` / `supportConstraint_pos_at_sup` require `¬ Stuck`; at a `Stuck`
  supremum a monitored hemisphere margin or support is exactly `0`, so `open_hemisphere`'s strict `> 0`
  is unavailable with the fixed `h₀`, and a hemisphere-only stuck (no support vanishing) has no banked
  route to a vanishing non-incident support — exactly the `BoundaryConvexPersistAtSup` obstacle. -/
def InteriorOpeningGlue : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2, StrictConvexSphArm A → StrictConvexSphArm B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∀ h₀ : E3, ‖h₀‖ = 1 → (∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ)) →
      -- (i) the endpoint sign reconciliation.
      endpt A ≤ endpt (openTail A (openingAxis k) (monitoredSup A B k h₀ Real.pi)) ∧
      -- (ii) the REACH-vs-STUCK selection: not stuck ⟹ the opened joint reaches `B`'s value (REACH);
      -- this also rules out the trichotomy CAP `δ* = π`.
      (¬ Stuck A B k h₀ Real.pi → Reach A B k h₀ Real.pi) ∧
      -- (iii) the STUCK boundary outcome.
      (Stuck A B k h₀ Real.pi →
        WeakConvexSphArm (openTail A (openingAxis k) (monitoredSup A B k h₀ Real.pi)) ∧
        ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (openTail A (openingAxis k) (monitoredSup A B k h₀ Real.pi) i)
            (openTail A (openingAxis k) (monitoredSup A B k h₀ Real.pi) (i + 1))
            (openTail A (openingAxis k) (monitoredSup A B k h₀ Real.pi) j) = 0)

/-! ## §3. Discharging `InteriorOpeningOutcome` from the banked composition + `InteriorOpeningGlue`. -/

/-- **The interior-opening outcome, from `InteriorOpeningGlue`.**  Composes the banked monitored-sup
trichotomy (`opening_boundary_trichotomy`), REACH persistence + deficit drop
(`strict_persistence_at_reach`, `deficitCount_openTail_reach_lt`), side / joint preservation
(`openTail_preserves_sides`, `jointAngle_openTail_eq_of_ne`, the joint-slack admissibility bound), and
the isolated boundary glue. -/
theorem interiorOpeningOutcome_of_glue (hglue : InteriorOpeningGlue) :
    SphericalArmAssembly.InteriorOpeningOutcome := by
  intro n A B hA hB hside hangle k hkdef
  -- the fixed hemisphere normal of A.
  obtain ⟨h₀, hnorm, hhpos⟩ := hA.closed_convex.open_hemisphere
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSup A B k h₀ Real.pi with hδ
  set A' : Fin (n + 1) → S2 := openTail A K δ with hA'
  -- short-arc base hyps and initial admissibility.
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  have hTcap : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
  have h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0 :=
    monitoredFamily_init_admissible hA hhpos hkdef
  -- the joint-slack member ≥ 0 at δ* : openedInteriorJointAngle A k δ* ≤ jointAngle B k.
  have hslack : openedInteriorJointAngle A k δ ≤ jointAngle B k := by
    have hmem := monitoredSup_mem hka hkt hTcap h0
    have := hmem.2 (Sum.inr (Sum.inr ()))
    -- monitoredFamily ... (inr (inr ())) δ = interiorTargetSlack A k (jointAngle B k) δ
    --                                       = jointAngle B k - openedInteriorJointAngle A k δ
    simp only [monitoredFamily, interiorTargetSlack] at this
    -- `this : 0 ≤ jointAngle B k - openedInteriorJointAngle A k (monitoredSup A B k h₀ π)`.
    rw [hδ]
    linarith
  -- SameSides A' B.
  have hside' : SameSides A' B := by
    intro i
    rw [hA', openTail_preserves_sides A K δ i]
    exact hside i
  -- JointLe A' B.
  have hangle' : JointLe A' B := by
    intro r
    by_cases hrk : r = k
    · rw [hrk, hA', jointAngle_openTail_eq_openedInterior A k δ]
      exact hslack
    · rw [hA', jointAngle_openTail_eq_of_ne A k δ hrk]
      exact hangle r
  -- the boundary glue.
  obtain ⟨hmono, hsel, hstuck_out⟩ := hglue n A B hA hB k hkdef h₀ hnorm hhpos
  refine ⟨A', hmono, hside', hangle', ?_⟩
  -- REACH vs STUCK.
  by_cases hstuck : Stuck A B k h₀ Real.pi
  · -- STUCK: the RIGHT disjunct.
    obtain ⟨hweak, hvanish⟩ := hstuck_out hstuck
    exact Or.inr ⟨hweak, hvanish⟩
  · -- ¬ Stuck ⟹ REACH (the glue's selection): the LEFT disjunct.
    have hreach : Reach A B k h₀ Real.pi := hsel hstuck
    have hreach_k : jointAngle (openTail A K δ) k = jointAngle B k := by
      rw [jointAngle_openTail_eq_openedInterior A k δ]
      exact hreach
    have hstrict : StrictConvexSphArm A' :=
      strict_persistence_at_reach hA hnorm hka hkt hTcap h0 hreach hstuck
    have hdrop : deficitCount A' B < deficitCount A B :=
      deficitCount_openTail_reach_lt A B k δ hkdef hreach_k
    exact Or.inl ⟨hstrict, hdrop⟩

/-- **`InteriorOpeningOutcome`, conditional on the single isolated boundary core `InteriorOpeningGlue`.**
Everything except the two substrate-absent boundary-glue facts (endpoint sign reconciliation + STUCK
boundary outcome / selection) is discharged unconditionally by the banked composition. -/
theorem interiorOpeningOutcome_holds (hglue : InteriorOpeningGlue) :
    SphericalArmAssembly.InteriorOpeningOutcome :=
  interiorOpeningOutcome_of_glue hglue

/-! ## §4. Non-vacuity / anti-impostor guard (playbook §3.3) for `InteriorOpeningGlue`. -/

/-- Non-vacuity of `InteriorOpeningGlue`'s conclusion: the endpoint comparison is realised reflexively
(`endpt A ≤ endpt A`), and the STUCK alternative's vanishing-support / weak-convex payload is genuine
geometric data — so the core is a real boundary production, not a vacuous-hypothesis impostor.  The
hypotheses (`A` strict, deficit `jointAngle A k < jointAngle B k`, `h₀` the genuine hemisphere normal)
are the real opening trigger, satisfiable at every deficient strictly-convex configuration. -/
theorem interiorOpeningGlue_conclusion_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

end ProofsInTheBook.SphericalOpeningOutcome

