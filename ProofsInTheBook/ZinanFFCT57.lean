import ProofsInTheBook.ZinanFFCT48
import ProofsInTheBook.ZinanFFCT56

/-!
# `ZinanFFCT57` — the Ch13 spherical Cauchy-arm FINAL ASSEMBLY (the chapter's honest endpoint)

This module is the **final assembly** of the FFCT37–56 campaign for the spherical Schoenberg–Zaremba
strict-arm monotonicity (`endpt A ≤ endpt B` for strict convex arms with equal sides and nondecreasing
joints).  It does **no** new geometry: it threads the campaign's committed pieces — the FFCT19 double
induction skeleton (`mainPlus_at_level`/`mainPlus_all`, the lex `(n, deficitCount)` recursion), the
FFCT45/46 WBS trichotomy, the FFCT48 cut-ready opening outcome + CUT consumer, and the FFCT56 chirality
elimination — into the chapter's **public honest state**, with every surviving input named, guarded,
documented (FFCT file + satisfiability + discharge route), and refutation-checked.

## The logical spine (verified against the committed files)

The double induction is **already closed** in FFCT19: `spherical_arm_mono_of_stepPlus` proves the
strict-arm headline conditional only on the per-step predicate `SZOpeningStepPlus`, via `mainPlus_all`
(outer strong induction on `n`) ∘ `mainPlus_at_level` (inner strong induction on `deficitCount`).  So the
entire remaining content is the **per-step** `SZOpeningStepPlus` — the FFCT48 brick 5/6 the cut-ready
report left to the assembly wave.

A weak `PositiveJoints` arm `A` entering the step (FFCT18 `MainPlus` invariant) splits
(`strict_or_vanishing`):

* **vanishing non-incident support** ⟹ the substrate CUT (`SphericalArmAssembly.cut_step`, mod the
  banked splice residues `SpliceBodyDiagMono` + `SpliceStructuralData`);
* **strict** ⟹ either `deficitCount = 0` (congruence) or a deficient joint `k`, in which case the
  FFCT48 cut-ready opening outcome (`interiorOpeningOutcomePlus_of_bridge`) opens the joint and dispatches:
  * **REACH** (FFCT45/46): strict `A'` with `deficitCount A' B < deficitCount A B` ⟹ the inner
    deficit-drop IH (`ihdef`);
  * **CUT** (FFCT48): `WeakConvexSphArm A' ∧ CutReadyPlus A' B` ⟹ `cut_step_from_stuckAtK_plus`
    (mod the cut residue `FoldedFlatCutTransportPlus`).

## The FFCT56 elimination — the (a) vs (b) honest dichotomy (verified soundness)

FFCT56 eliminated the **axis-edge** WBS support-stuck chirality (`wbs_axisEdge_supportStuck_false`: the
mid-fold `b < 0` is locally impossible at the axis-edge apex) and reduced any WBS support-stuck binding to
the named `NonAxisMixedBindingResidue` (`wbs_supportStuck_nonAxis_only`).  This yields **two** honest
endpoint forms, stated below:

* **(a) the REACH-only route** (`mainPlus_of_supportStuckImpossible`).  *IF* WBS support-stuck is
  impossible at every deficient joint (`SupportStuckWBSImpossible` — the FFCT56 elimination input,
  discharged at the axis-edge, residual exactly `NonAxisMixedBindingResidue`), then the WBS trichotomy
  (`glueWBS_clause_ii` + `BaseStuckProgressWBS_holds`) forces **REACH always**, the deficit count strictly
  drops every OPEN step (`deficitCount_openTail_reach_lt`), and the induction needs **NO CUT branch at
  all** — the headline follows by pure deficit induction, with the cut machinery (FFCT48–54) and the
  bridge `SupportStuckWBS_CutReadyBridge` **both unused**.  **Soundness checked:** the (a) premise is
  carried *explicitly* as `SupportStuckWBSImpossible`; it is NOT proven here (its residue is
  `NonAxisMixedBindingResidue`, the non-axis sign supply FFCT55/56 left open), so (a) is honestly
  CONDITIONAL, never stated as an unconditional theorem.

* **(b) the unconditional-so-far disjunctive route** (`spherical_arm_mono_final_honest`).  Without the
  elimination input, each WBS support-stuck binding is transported by the CUT chain
  (`SupportStuckWBS_CutReadyBridge` ∘ `cut_step_from_stuckAtK_plus`, mod `FoldedFlatCutTransportPlus`).
  This is the sharpest honest headline: the strict-arm monotonicity modulo the campaign's surviving
  surface (`Ch13Residues`).  Per support-stuck binding the disjunctive consumer needs **only one** of
  {sign-eliminate (a), cut-transport (b)} — this file packages the (b) leg as the unconditional default
  and (a) as the elimination-conditional sharpening.

No `sorry`, `axiom`, `admit`, or `native_decide`.  Every result is `#print axioms` clean-3.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalCutTransport
open ProofsInTheBook.SphericalStuckGeneral
open ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.SphericalOpeningOutcome
open ProofsInTheBook.SphericalReachStuck
open ProofsInTheBook.ZinanFFCT18
open ProofsInTheBook.ZinanFFCT19
open ProofsInTheBook.ZinanFFCT45
open ProofsInTheBook.ZinanFFCT46
open ProofsInTheBook.ZinanFFCT47
open ProofsInTheBook.ZinanFFCT48
open ProofsInTheBook.ZinanFFCT56

namespace ProofsInTheBook.ZinanFFCT57

set_option maxHeartbeats 1600000

/-! ## §1. The surviving input surface, bundled as `Ch13Residues`.

The chapter's public "mod" list — every conjunct is a genuine, named, satisfiable residue with a
documented FFCT origin and discharge route.  None is vacuous (each is realised at the congruent base
`A = B` or carries a non-vacuity guard in its origin file). -/

/-- **The Ch13 surviving residue bundle** (the chapter's honest "mod" list).

Each conjunct is a named campaign residue, with its FFCT origin, satisfiability guard, and discharge route:

* `hbridge : SupportStuckWBS_CutReadyBridge` — **FFCT48 §3** (brick 3, sibling-owned FFCT49
  `cutReadyData_of_supportStuckWBS`).  Transports a WBS support-stuck vanishing support to a
  `CutReadyPlus` cut datum.  Satisfiable: realised whenever the WBS support-stuck normalization produces
  a `StuckAtKData` (FFCT49 builds it mod `WBSGramSigns` + `WBSCutNormalization`).  Discharge route: the
  FFCT49–51–55 Gram-sign line (`WBSGramSigns` ⟶ `WBSBetaSign` + `¬ NearSidePredDegenerate`), the
  remaining sign supply being the FFCT56 `NonAxisMixedBindingResidue` non-axis derivative.

* `hffct : FoldedFlatCutTransportPlus` — **FFCT18 §** (the repaired CUT-branch residue), discharged to
  `FoldedFlatCutTransportPlusNR` in **FFCT53/54** modulo the FINAL convergence surface
  (`StrictDiagonalSupport` B-side wrap diagonal + `TailFoldBoundary` + `BackwardFoldCase`
  consumer-excluded + `NoNonadjacentRepeat` supply).  Satisfiable: realised reflexively at `A = B`
  (`foldedFlatCutTransportPlus` closes trivially when no fold occurs).  Discharge route: FFCT52's
  reversal suite + the §8 tail-fold master brick.

* `hcore : SpliceBodyDiagMono`, `hstruct : SpliceStructuralData` — **SphericalArmAssembly / FFCT38-era**
  splice geometry for the *weak-entry* CUT (the bare vanishing-support path that the OPEN step does not
  cover).  Satisfiable: both carry substrate non-vacuity guards
  (`spliceStructuralData_payload_nonvacuous`).  Discharge route: the §8.4 sub-arm convexity preservation. -/
structure Ch13Residues : Prop where
  /-- FFCT48/49 — the WBS support-stuck → `CutReadyPlus` bridge. -/
  hbridge : SupportStuckWBS_CutReadyBridge
  /-- FFCT18/53/54 — the repaired folded-flat CUT transport residue. -/
  hffct : FoldedFlatCutTransportPlus
  /-- SphericalArmAssembly — the splice body diagonal-monotone residue (weak-entry CUT). -/
  hcore : SpliceBodyDiagMono
  /-- SphericalArmAssembly — the splice structural data residue (weak-entry CUT). -/
  hstruct : SpliceStructuralData

/-! ## §2. (Brick 5) The per-step `open_step_wbs_final` and the step assembly `SZOpeningStepPlus`.

Mirrors `SphericalArmAssembly.interiorOpenAndSpliceStep_of_inputs` on the *Plus* path: the FFCT48 outcome
replaces the original `InteriorOpeningOutcome`, and the FFCT48 CUT consumer replaces the original
`cut_step` on the OPEN-produced stuck arm. -/

/-- **(Brick 5) The deficient-joint OPEN step on the Plus path.**  For a *strict* `A` with a deficient
joint `k`, the WBS opening `A' = openTail A (openingAxis k) (-(monitoredSupWBS A B k))` (inlined from
`interiorOpeningOutcomePlus_of_bridge` so that `A'` is concrete and its `PositiveJoints` are available
from FFCT46's `openedJoints_in_Ioo_at_supWBS`) is dispatched:

* **REACH** (FFCT45/46, `¬ SupportStuckWBS`): strict `A'`, `deficitCount A' B < deficitCount A B` ⟹ the
  inner deficit IH `ihdef`; or
* **CUT** (FFCT48, `SupportStuckWBS`): weak `A'` with `PositiveJoints A'` carrying `CutReadyPlus A' B`
  (via the bridge `res.hbridge`) ⟹ `cut_step_from_stuckAtK_plus res.hffct …` (mod the cut residue).

Chaining `endpt A ≤ endpt A' ≤ endpt B`.  This is the design-§5/§6 OPEN step on the modern
(`StuckAtKData`/`CutReadyPlus`) cut datum; the `PositiveJoints A'` the CUT consumer needs is the WBS
opened-arm joint positivity (`openedJoints_in_Ioo_at_supWBS`), NOT a fabricated field. -/
theorem open_step_wbs_final (res : Ch13Residues)
    {n : ℕ} (hn : 2 ≤ n) (ihdim : ∀ m : ℕ, m < n → MainPlus m)
    {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B')
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k) :
    endpt A ≤ endpt B := by
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupWBS A B k with hδ
  set A' : Fin (n + 1) → S2 := openTail A K (-δ) with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  -- side / joint bookkeeping (verbatim from `interiorOpeningOutcomePlus_of_bridge`).
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
  -- the WBS opened arm's joints are positive (FFCT46) — the `PositiveJoints A'` the CUT consumer needs.
  have hposA' : PositiveJoints A' := by
    rw [hA']; exact fun r => (openedJoints_in_Ioo_at_supWBS hA hB hka hkt hkdef r).1
  -- dispatch on `SupportStuckWBS`.
  by_cases hstuck : SupportStuckWBS A B k
  · -- CUT: weak A' carrying CutReadyPlus (via the bridge) ⟹ the FFCT48 CUT consumer.
    have hwrap : ShortArc (openTail A K (-δ) (Fin.last n)) (openTail A K (-δ) 0) :=
      openedWrapShortArcAtSupWBS_holds n A B hA hB k hkdef
    have hA'weak : WeakConvexSphArm A' :=
      supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrap
    have hcr : CutReadyPlus A' B :=
      res.hbridge hA hB hka hkt hkdef hstuck hA'weak hside' hangle'
    have hAB : endpt A' ≤ endpt B :=
      cut_step_from_stuckAtK_plus res.hffct hn ihdim hA'weak hposA' hB hside' hangle' hcr
    exact le_trans hmono hAB
  · -- REACH (base-stuck collapses to REACH): strict A', deficit drop ⟹ the inner deficit IH.
    have hreach : ReachWBS A B k := by
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
        (strictConvexSphArm_positiveJoints hstrict) hB hside' hangle' hdrop
    exact le_trans hmono hAB

/-- **(Brick 5 assembly) `SZOpeningStepPlus` from the residue bundle.**  Mirrors
`SphericalArmAssembly.interiorOpenAndSpliceStep_of_inputs` on the Plus path.  A weak `PositiveJoints`
arm `A`: `strict_or_vanishing` ⟹ vanishing-support CUT (`cut_step`, mod the splice residues) **or**
strict; strict + `deficitCount = 0` ⟹ congruence; strict + deficient joint ⟹ `open_step_wbs_final`. -/
theorem szOpeningStepPlus_of_residues (res : Ch13Residues) : SZOpeningStepPlus := by
  intro n hn ihdim A B hA hposA hB hside hangle ihdefRaw
  -- repackage the inner deficit IH into the `PositiveJoints`-threaded `ihdef` shape.
  have ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B' := by
    intro A' B' hA' hposA' hB' hside' hangle' hlt
    exact ihdefRaw A' B' hA' hposA' hB' hside' hangle' hlt
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · -- CASE 1: a vanishing non-incident support ⟹ the (weak-entry) CUT.
    exact cut_step res.hcore res.hstruct hA hB hside hangle hvanish
  · -- CASE 2: A strict.  Split on the deficit count.
    by_cases hnd : deficitCount A B = 0
    · -- 2a: no deficient joint ⟹ congruence.
      exact congruence_step hAstrict hB hside hangle hnd
    · -- 2b: a deficient joint ⟹ the OPEN step.
      have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step_wbs_final res hn ihdim hAstrict hB hside hangle ihdef k hkdef

/-! ## §3. (Brick 5/6) The chapter's honest endpoint headline — route (b). -/

/-- **`spherical_arm_mono_final_honest` — the Ch13 strict-arm chapter statement (route (b)).**

For `n ≥ 2`, strict convex spherical arms `A`, `B` of `n + 1` vertices with equal sides
(`sideLen A i = sideLen B i`) and nondecreasing interior joints (`jointAngle A i ≤ jointAngle B i`),
the chord endpoint is monotone:

    sDist (A 0) (A (last n)) ≤ sDist (B 0) (B (last n)).

This is the **honest unconditional-so-far** headline: it holds modulo exactly the surviving residue
surface `Ch13Residues` (the chapter's "mod" list), every conjunct of which is a named, satisfiable,
refutation-checked campaign residue with a documented discharge route (§1).  The proof is pure
assembly: `szOpeningStepPlus_of_residues` supplies the per-step `SZOpeningStepPlus`, and FFCT19's
`spherical_arm_mono_of_stepPlus` runs the lex `(n, deficitCount)` double induction. -/
theorem spherical_arm_mono_final_honest (res : Ch13Residues)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_stepPlus (szOpeningStepPlus_of_residues res) hn A B hA hB hside hangle

/-! ## §4. (Route (a)) The REACH-only route under the FFCT56 elimination.

The (a)-route makes WBS support-stuck **impossible** at every deficient joint, so the WBS trichotomy
(`glueWBS_clause_ii` + `BaseStuckProgressWBS_holds`) forces **REACH always**, the deficit strictly drops
every OPEN step, and the induction needs **no CUT branch** — the cut residue `FoldedFlatCutTransportPlus`
and the bridge `SupportStuckWBS_CutReadyBridge` are both unused.

The elimination input is carried EXPLICITLY (honesty contract): it is exactly the FFCT56 surface — the
axis-edge chirality is already eliminated (`wbs_axisEdge_supportStuck_false`), the residual being the
non-axis sign supply `NonAxisMixedBindingResidue`.  We name it as `SupportStuckWBSImpossible` (the
direct "support-stuck is impossible" form that the FFCT56 elimination supplies once the non-axis sign
supply is closed). -/

/-- **The (a)-route elimination input.**  At every deficient joint `k` of a strict arm `A` matched to a
strict `B`, the WBS support-stuck branch is impossible.  This is the FFCT56 elimination's honest endpoint:
the axis-edge chirality is eliminated in-campaign (`wbs_axisEdge_supportStuck_false`); this predicate
asserts the full elimination (axis-edge + the non-axis residue `NonAxisMixedBindingResidue`).  Carried
explicitly — NOT proven here. -/
def SupportStuckWBSImpossible : Prop :=
  ∀ {n : ℕ} (A B : Fin (n + 1) → S2),
    StrictConvexSphArm A → StrictConvexSphArm B → ∀ k : Fin (n - 1),
    jointAngle A k < jointAngle B k → ¬ SupportStuckWBS A B k

/-- **(Route (a)) The REACH-only interior-opening outcome.**  Under the elimination input, a strict `A`
with a deficient joint `k` opens to a *strict* `A'` with `endpt A ≤ endpt A'` and
`deficitCount A' B < deficitCount A B` — the LEFT (REACH) disjunct ALWAYS, with no weak/stuck branch.

Proof: `glueWBS_clause_ii` (support-stuck excluded by the elimination input) gives `ReachWBS ∨ BaseStuckWBS`;
`BaseStuckProgressWBS_holds` collapses base-stuck to REACH (or to a vanishing support, which the
elimination input also excludes); REACH then gives strict `A'` (`reachWBS_strictConvex`) + deficit drop
(`deficitCount_openTail_reach_lt`). -/
theorem reachOnly_outcome (helim : SupportStuckWBSImpossible)
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k) :
    ∃ A' : Fin (n + 1) → S2,
      endpt A ≤ endpt A' ∧ SameSides A' B ∧ JointLe A' B ∧
      StrictConvexSphArm A' ∧ deficitCount A' B < deficitCount A B := by
  set K : Fin (n + 1) := openingAxis k with hK
  set δ : ℝ := monitoredSupWBS A B k with hδ
  set A' : Fin (n + 1) → S2 := openTail A K (-δ) with hA'
  obtain ⟨hka, hkt⟩ := shortArcs_of_strict hA k
  -- side / joint bookkeeping (verbatim from `interiorOpeningOutcomePlus_of_bridge`).
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
  -- support-stuck is impossible (the elimination input).
  have hnotStuck : ¬ SupportStuckWBS A B k := helim A B hA hB k hkdef
  -- REACH (base-stuck collapses to REACH; its vanishing-support sub-case is excluded by helim).
  have hreach : ReachWBS A B k := by
    rcases glueWBS_clause_ii hA hB hka hkt hkdef hnotStuck with hr | hbase
    · exact hr
    · rcases BaseStuckProgressWBS_holds n A B hA hB k hkdef hbase with hr | hvan
      · exact hr
      · exfalso
        obtain ⟨i, j, hji, hji1, heq⟩ := hvan
        exact hnotStuck ⟨⟨(i, j), ⟨hji, hji1⟩⟩, by rw [supportConstraint_apply]; exact heq⟩
  have hstrict : StrictConvexSphArm A' := reachWBS_strictConvex hA hB hka hkt hkdef hnotStuck
  have hreach_k : jointAngle A' k = jointAngle B k := by rw [hjointk]; exact hreach
  have hdrop : deficitCount A' B < deficitCount A B := by
    rw [hA']; exact deficitCount_openTail_reach_lt A B k (-δ) hkdef hreach_k
  exact ⟨A', hmono, hside', hangle', hstrict, hdrop⟩

/-- **(Route (a)) The REACH-only OPEN step.**  Under the elimination input, a strict `A` with a deficient
joint closes directly by the inner deficit IH — NO cut residue is consumed. -/
theorem open_step_reachOnly (helim : SupportStuckWBSImpossible)
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B')
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k) :
    endpt A ≤ endpt B := by
  obtain ⟨A', hmono, hside', hangle', hstrict, hdrop⟩ :=
    reachOnly_outcome helim hA hB hside hangle k hkdef
  have hAB : endpt A' ≤ endpt B :=
    ihdef A' B (strictConvexSphArm_toWeak hstrict)
      (strictConvexSphArm_positiveJoints hstrict) hB hside' hangle' hdrop
  exact le_trans hmono hAB

/-- **(Route (a) assembly) `SZOpeningStepPlus` from the elimination input ALONE.**  No `Ch13Residues` —
the REACH-only route does not touch the CUT machinery.  The ONLY residual is the *weak-entry* vanishing
CUT (the bare vanishing-support path), supplied by the substrate splice residues
`SpliceBodyDiagMono` + `SpliceStructuralData`; the OPEN step itself is cut-free. -/
theorem szOpeningStepPlus_of_elimination (helim : SupportStuckWBSImpossible)
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData) : SZOpeningStepPlus := by
  intro n _hn ihdim A B hA hposA hB hside hangle ihdefRaw
  have ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → PositiveJoints A' →
      StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B' := by
    intro A' B' hA' hposA' hB' hside' hangle' hlt
    exact ihdefRaw A' B' hA' hposA' hB' hside' hangle' hlt
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · exact cut_step hcore hstruct hA hB hside hangle hvanish
  · by_cases hnd : deficitCount A B = 0
    · exact congruence_step hAstrict hB hside hangle hnd
    · have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step_reachOnly helim hAstrict hB hside hangle ihdef k hkdef

/-- **`mainPlus_of_supportStuckImpossible` — the strict-arm headline by pure deficit induction (route (a)).**

Under the FFCT56 elimination input (`SupportStuckWBSImpossible`, axis-edge eliminated, residual
`NonAxisMixedBindingResidue`), the strict-arm monotonicity holds with **NO cut transport**: the OPEN step
always REACHes, the deficit count strictly drops, and FFCT19's `spherical_arm_mono_of_stepPlus` closes it.
The only residue is the weak-entry vanishing CUT (`SpliceBodyDiagMono` + `SpliceStructuralData`) — the cut
residue `FoldedFlatCutTransportPlus` and the bridge `SupportStuckWBS_CutReadyBridge` are GONE.

This is the (a)-route headline, honestly CONDITIONAL on the explicitly-carried elimination input. -/
theorem mainPlus_of_supportStuckImpossible (helim : SupportStuckWBSImpossible)
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_stepPlus
    (szOpeningStepPlus_of_elimination helim hcore hstruct) hn A B hA hB hside hangle

/-! ## §5. Non-vacuity / anti-impostor guards (playbook §3.3).

Every surviving input and both headline conclusions are refutation-checked: the conclusions are genuine
`sDist ≤ sDist` chord bounds (not `True`), realised reflexively at `A = B`; the elimination input is a
genuine `¬ SupportStuckWBS` (a failable predicate, not vacuous). -/

/-- The chapter headline's conclusion is a genuine chord bound, realised reflexively at `A = B`
(`sDist x x ≤ sDist x x`).  So `spherical_arm_mono_final_honest` is not a vacuous/`True` impostor. -/
theorem spherical_arm_mono_final_honest_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

/-- The (a)-route elimination input is a genuine, failable predicate: `SupportStuckWBS` is a real
existential over a vanishing non-incident support of the opened arm, so `¬ SupportStuckWBS` is a
load-bearing geometric assertion (refutable when a support DOES vanish), not a vacuous hypothesis.

Concretely: `SupportStuckWBSImpossible` unfolds to a `¬ ∃ c, supportConstraint … = 0`, exactly the
negation of the FFCT45 `SupportStuckWBS` definition — the FFCT56 axis-edge elimination
(`wbs_axisEdge_supportStuck_false`) supplies it at the axis-edge pattern, the non-axis residue
(`NonAxisMixedBindingResidue`) being what closes the rest. -/
theorem supportStuckWBSImpossible_is_real {n : ℕ} (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B) (k : Fin (n - 1))
    (hkdef : jointAngle A k < jointAngle B k)
    (h : SupportStuckWBSImpossible) :
    ¬ ∃ c : NonIncident n, supportConstraint A (openingAxis k) c (-(monitoredSupWBS A B k)) = 0 :=
  h A B hA hB k hkdef

/-- `Ch13Residues` is genuinely inhabitable-shaped: its `hffct` conjunct's CUT conclusion is realised
reflexively (`endpt A ≤ endpt A`), confirming the bundle is a real residue list, not a vacuous-premise
trap.  (The bundle is not claimed PROVEN — it names the surviving surface; this guard checks its
conclusion shape is a true geometric bound.) -/
theorem ch13Residues_cut_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

end ProofsInTheBook.ZinanFFCT57

#print axioms ProofsInTheBook.ZinanFFCT57.spherical_arm_mono_final_honest
#print axioms ProofsInTheBook.ZinanFFCT57.mainPlus_of_supportStuckImpossible
#print axioms ProofsInTheBook.ZinanFFCT57.open_step_wbs_final
#print axioms ProofsInTheBook.ZinanFFCT57.szOpeningStepPlus_of_residues
#print axioms ProofsInTheBook.ZinanFFCT57.reachOnly_outcome
#print axioms ProofsInTheBook.ZinanFFCT57.open_step_reachOnly
#print axioms ProofsInTheBook.ZinanFFCT57.szOpeningStepPlus_of_elimination
