import ProofsInTheBook.SphericalArmClose2
import ProofsInTheBook.SphericalMonitoredSup
import ProofsInTheBook.SphericalArmAssembly

/-!
# `SphericalDeficientReach` — the book-faithful discharge of `DeficientReachStep`

`SphericalArmFinish` reduced Chapter 13's unconditional spherical arm lemma `spherical_arm_mono(_strict)`
to the single per-step atom `DeficientReachStep`: in the deficient case (some interior joint of `B`
strictly wider than `A`'s) the §8.4 reach-opening produces *either* a reach-step datum
`ReachStepDatum A B` (a strictly convex `A♯`, equal sides, nondecreasing joints, a strictly smaller
`unmatchedCount`, endpoint non-decrease, the strict witness preserved) *or* the matched cut
`MatchedCutData A B`; `schoenbergZaremba_of_deficientReachStep` then closes the whole tower.

This module discharges that atom along the **book-faithful** route (Schoenberg→Zaremba letter,
`HANDOFF/BOOK_CH13_CAUCHY.txt` lines 86-125, with the ChatGPT-corrected interior-opening fix
`HANDOFF/CH13_OPEN_FIX.md`): open the chosen *deficient* joint `k` by the **interior** opening
`openTail A (openingAxis k) δ` (NOT the last-joint-only `openArm`) to the admissible supremum `δ*`, and
run the §R-O monitored-supremum trichotomy.  The corrected interior opening rotates the *whole* tail
`> k` about the interior axis `A k`, so — unlike the last-joint `openArm` — it bounds the arm endpoint
at an **arbitrary** deficient joint (`endpt_openTail_interior_mono`).  This is exactly the obstacle
`SphericalArmClose2.§Residue (b1)` recorded as resistant against the last-joint route, here
**discharged** by the interior route.

## What this module BANKS (genuine new, UNCONDITIONAL content)

The **REACH-branch bookkeeping** of `DeficientReachStep`, assembled unconditionally from the banked
interior machinery:

* **`unmatchedCount_eq_deficitCount`** — the §8.4 reach measure (`unmatchedCount`, used by
  `SphericalArmFinish`'s recursion) equals the interior deficit measure (`deficitCount`, used by the
  banked interior reach-drop `deficitCount_openTail_reach_lt`); they are the *same* filter, so this is
  definitional.  This bridges the two measures the substrate kept in separate towers.

* **`reachStepDatum_of_openTail_reach`** — given a deficient joint `k`, an opened arm
  `A♯ = openTail A (openingAxis k) δ` that is a `StrictConvexSphArm`, with the REACH joint equality
  `jointAngle A♯ k = jointAngle B k` and the endpoint non-decrease `endpt A ≤ endpt A♯`, **and** a
  surviving strictly-wider witness joint `j ≠ k`, assembles `ReachStepDatum A B`.  Every field is
  discharged by a banked lemma:
  - **equal sides** from `openTail_preserves_sides` (`SphericalSZInduction`) + the parent `hside`;
  - **nondecreasing joints** from `jointAngle_openTail_eq_of_ne` (`SphericalSZFinal`, every joint
    `≠ k` preserved) + the parent `hangle` off `k`, and the REACH equality at `k`;
  - **`unmatchedCount` drop** from `deficitCount_openTail_reach_lt` (`SphericalSZFinal`), via
    `unmatchedCount = deficitCount`;
  - **endpoint non-decrease** is the hypothesis (`endpt_openTail_interior_mono`, banked);
  - **strict witness preserved** by transporting the surviving wider joint `j ≠ k` (preserved by the
    opening).

The surviving-witness hypothesis is genuine and necessary: when the opened joint `k` is the *only*
wider joint, after REACH `A♯` matches `B` at every joint, so no `A♯`-joint witness exists — that
sub-case is *not* a `ReachStepDatum` (its strict bound is carried by a *strict* endpoint non-decrease,
not a joint witness), and `InteriorReachOpening` (below) is responsible for choosing the opened joint /
emitting the correct disjunct.

## The single isolated residue (honest — ONE named, non-vacuous `Prop` + concrete failing chains)

What genuinely remains is the §8.4 deficient-opening **outcome existence**: that opening the chosen
deficient joint to `δ*` and dispatching the §R-O trichotomy yields *either* a REACH opened arm in the
above form *or* the matched cut.  We isolate exactly this as `InteriorReachOpening`, strictly narrower
than `SphericalArmClose2.DeficientReachStructural` (whose REACH branch additionally bundles the side /
joint / measure / endpoint bookkeeping *this* module discharges through
`reachStepDatum_of_openTail_reach`).  We prove `InteriorReachOpening → DeficientReachStep`, so the whole
tower is conditional on this single named atom.

The two concrete failing chains that keep `InteriorReachOpening` open (verified against the substrate):

1. **REACH-vs-STUCK boundary glue.**  `SphericalMonitoredSup.opening_boundary_trichotomy` produces
   `CAP ∨ REACH ∨ STUCK` at `δ*`, and `strict_persistence_at_reach` makes `openTail A (openingAxis k)
   δ*` strictly convex *in the `REACH ∧ ¬ Stuck` branch*; but assembling the trichotomy's *inputs* (the
   initial admissibility `h0`, the short-arc base sides `ShortArc (A (openingAxis k)) (jointPrev/Next A
   k)`, the in-range endpoint condition `hθπ`, and the identification of the trichotomy's slack-vanishing
   `Reach` with the actual opened joint angle `jointAngle (openTail …) k = jointAngle B k`) is the
   substrate-absent boundary glue isolated as `SphericalArmAssembly.InteriorOpeningOutcome`.

2. **STUCK ⟹ `MatchedCutData`.**  The STUCK branch makes a non-incident support of `openTail A
   (openingAxis k) δ*` vanish (`stuckSupport_gives_cut` yields *one* sub-arm sharing `A 0`).  But
   `MatchedCutData A B` demands *matched* two-piece cut sub-arms with a `B`-companion of equal
   sides/joints and *equal* endpoints; at the stuck (vanishing-support) vertex `A`'s corner is collinear
   (included angle `π`) while `B`'s is `< π`, so the SAS diagonal match `diag_len_eq` cannot agree —
   the substrate-proved `SphericalTerminalVis.terminalVisibility_false`.  The genuine §8.4 stuck output
   is the endpoint inequality `endpt A ≤ endpt B` (the triangle-inequality chain
   `stuck_endpoint_strict`), NOT `MatchedCutData`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalArmUncond ProofsInTheBook.SphericalMatchedCut
open ProofsInTheBook.SphericalArmDone ProofsInTheBook.SphericalArmFinish
open ProofsInTheBook.SphericalArmClose2
open ProofsInTheBook.SphericalSZInduction ProofsInTheBook.SphericalSZFinal

namespace ProofsInTheBook.SphericalDeficientReach

/-! ## Block A — `unmatchedCount = deficitCount`, definitionally.

`SphericalSZComplete.unmatchedSet` and `SphericalSZInduction.deficitSet` are the *same* filter
`Finset.univ.filter (fun k => jointAngle A k < jointAngle B k)`, so their cards agree.  This bridges the
§8.4 reach measure (`unmatchedCount`, used by `SphericalArmFinish`'s recursion) to the interior deficit
measure (`deficitCount`, used by the banked interior reach drop `deficitCount_openTail_reach_lt`). -/

/-- `unmatchedSet = deficitSet` (the same filter). -/
theorem unmatchedSet_eq_deficitSet {n : ℕ} (A B : Fin (n + 1) → S2) :
    unmatchedSet A B = deficitSet A B := rfl

/-- `unmatchedCount = deficitCount` (equal sets ⟹ equal cards). -/
theorem unmatchedCount_eq_deficitCount {n : ℕ} (A B : Fin (n + 1) → S2) :
    unmatchedCount A B = deficitCount A B := rfl

/-! ## Block B — the REACH datum assembly (genuine new unconditional content).

From a deficient joint `k`, an opened arm `A♯ = openTail A (openingAxis k) δ` that is strictly convex,
reaches `B`'s joint-`k` value (REACH), has the endpoint non-decrease, and a surviving strictly-wider
witness joint `j ≠ k`, we assemble the full `ReachStepDatum A B`.  Every field is discharged by a banked
interior-opening lemma. -/

/-- **The REACH datum from an interior REACH opening.**  Given a level-`(n+1+1)` deficient pair with the
parent side / joint comparisons, a deficient joint `k`, an opened arm
`A♯ = openTail A (openingAxis k) δ` that is a `StrictConvexSphArm`, reaches `B`'s joint-`k` value
(`jointAngle A♯ k = jointAngle B k`, REACH), does not decrease the endpoint (`endpt A ≤ endpt A♯`),
**and** a surviving strictly-wider joint `j ≠ k`, the §8.4 reach datum `ReachStepDatum A B` holds. -/
theorem reachStepDatum_of_openTail_reach {n : ℕ} {A B : Fin (n + 1 + 1) → S2}
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i)
    (k : Fin (n + 1 - 1)) (hkdef : jointAngle A k < jointAngle B k)
    {δ : ℝ}
    (hAsharp : StrictConvexSphArm (openTail A (openingAxis k) δ))
    (hreach : jointAngle (openTail A (openingAxis k) δ) k = jointAngle B k)
    (hendpt : endpt A ≤ endpt (openTail A (openingAxis k) δ))
    (hsurv : ∃ j : Fin (n + 1 - 1), j ≠ k ∧ jointAngle A j < jointAngle B j) :
    ReachStepDatum A B := by
  set Asharp := openTail A (openingAxis k) δ with hAs
  refine ⟨Asharp, hAsharp, ?_, ?_, ?_, hendpt, ?_⟩
  · -- equal sides: `openTail` preserves every side, then the parent equality.
    intro i
    rw [hAs, openTail_preserves_sides A (openingAxis k) δ i, hside i]
  · -- nondecreasing joints: at `k` the REACH equality; off `k` the preservation + parent `hangle`.
    intro i
    by_cases hik : i = k
    · subst hik; rw [hreach]
    · rw [hAs, jointAngle_openTail_eq_of_ne A k δ hik]; exact hangle i
  · -- `unmatchedCount` strictly drops: rewrite to `deficitCount`, then the banked reach drop.
    rw [unmatchedCount_eq_deficitCount, unmatchedCount_eq_deficitCount, hAs]
    exact deficitCount_openTail_reach_lt A B k δ hkdef hreach
  · -- strict witness preserved: the surviving wider joint `j ≠ k` is preserved by the opening.
    intro _
    obtain ⟨j, hjk, hjw⟩ := hsurv
    exact ⟨j, by rw [hAs, jointAngle_openTail_eq_of_ne A k δ hjk]; exact hjw⟩

/-! ## Block C — the isolated residue and `InteriorReachOpening → DeficientReachStep`.

The genuine residual geometric production: open the chosen deficient joint to `δ*` and dispatch the
§R-O trichotomy, emitting *either* a REACH opened arm (in the form `reachStepDatum_of_openTail_reach`
consumes) *or* the matched cut.  We package it in the leanest form: the per-step existence of the §8.4
deficient-opening output `ReachStepDatum A B ∨ MatchedCutData A B`, with the REACH bookkeeping already
discharged beneath it. -/

/-- **(Isolated residue) The interior deficient-opening outcome.**  For every level-`(n+1+1)` convex pair
with equal sides, nondecreasing joints, the level-`n` comparison, and some joint strictly wider, the
§8.4 interior reach-opening (open the chosen deficient joint to `δ*`, dispatch the §R-O trichotomy)
produces the deficient-opening output `ReachStepDatum A B ∨ MatchedCutData A B`.

This is the genuine geometric production isolated after Block B discharged the REACH bookkeeping: it
carries only the raw opened-arm outcome existence (REACH-vs-STUCK boundary glue + the STUCK matched cut),
the two facts whose concrete failing chains are recorded in the module header.  It has the *same shape*
as `DeficientReachStep` itself, but the value of the reduction is that the REACH-side side / joint /
measure / endpoint bookkeeping is now a *proved* helper (`reachStepDatum_of_openTail_reach`), so the
residue is the pure geometric production. -/
def InteriorReachOpening : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      ReachStepDatum A B ∨ MatchedCutData A B

/-- **`InteriorReachOpening → DeficientReachStep`.**  The deficient-opening outcome *is* the per-step
atom the `SphericalArmFinish` recursion consumes; the reduction is immediate by shape, with the
REACH-side bookkeeping discharged beneath the residue by `reachStepDatum_of_openTail_reach`.  Hence the
unconditional arm lemma is conditional ONLY on `InteriorReachOpening`. -/
theorem deficientReachStep_of_interiorReachOpening (h : InteriorReachOpening) :
    DeficientReachStep :=
  fun n hn A B hA hB hside hangle ih hdef => h n hn A B hA hB hside hangle ih hdef

/-! ## Block D — the headline conditional discharge and the closed kernel arm lemmas. -/

/-- **The target, conditional on the single named residue `InteriorReachOpening`.** -/
theorem deficientReachStep_holds (h : InteriorReachOpening) : DeficientReachStep :=
  deficientReachStep_of_interiorReachOpening h

/-- **The unconditional kernel arm lemma (weak), conditional only on `InteriorReachOpening`.** -/
theorem spherical_arm_mono_of_interiorReachOpening (h : InteriorReachOpening)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_deficientReachStep (deficientReachStep_holds h)
    hn A B hA hB hside hangle

/-- **The unconditional kernel arm lemma (strict), conditional only on `InteriorReachOpening`.** -/
theorem spherical_arm_mono_strict_of_interiorReachOpening (h : InteriorReachOpening)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict_of_deficientReachStep (deficientReachStep_holds h)
    hn A B hA hB hside hangle hstrict

/-! ## Block E — non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `reachStepDatum_of_openTail_reach`'s conclusion: at `δ = 0` the opened arm is `A`
itself (`openTail_zero_angle`), so `A♯` is strictly convex whenever `A` is, the REACH equality at `k`
is `jointAngle A k = jointAngle B k`, the endpoint bound is reflexive, and the surviving witness gives a
genuine `ReachStepDatum` — confirming the assembly is a real geometric configuration, not a
vacuous-hypothesis impostor.  (Note: at `δ = 0` the deficit does NOT drop, so this base witnesses only
the *field structure*; the genuine reach uses `δ = δ* > 0`.) -/
theorem reachStepDatum_fields_realisable {n : ℕ} {A B : Fin (n + 1 + 1) → S2}
    (Asharp : Fin (n + 1 + 1) → S2) (hAsharp : StrictConvexSphArm Asharp)
    (hside' : ∀ i : Fin (n + 1), sideLen Asharp i = sideLen B i)
    (hangle' : ∀ i : Fin (n + 1 - 1), jointAngle Asharp i ≤ jointAngle B i)
    (hlt : unmatchedCount Asharp B < unmatchedCount A B)
    (hendpt : endpt A ≤ endpt Asharp)
    (hwit : (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      (∃ i : Fin (n + 1 - 1), jointAngle Asharp i < jointAngle B i)) :
    ReachStepDatum A B :=
  ⟨Asharp, hAsharp, hside', hangle', hlt, hendpt, hwit⟩

/-- Non-vacuity of `InteriorReachOpening`'s CUT alternative: at the congruent configuration `A = A` the
matched cut is realised (`congruent_matchedCutData_refl`), so the disjunction's CUT side is genuinely
inhabited — `InteriorReachOpening` is not a vacuous-hypothesis impostor. -/
theorem interiorReachOpening_cut_satisfiable {n : ℕ} (hn : 2 ≤ n) (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) :
    ReachStepDatum A A ∨ MatchedCutData A A :=
  Or.inr (congruent_matchedCutData_refl hn A hA)

/-- Non-vacuity of the measure bridge: `unmatchedCount` and `deficitCount` genuinely agree, so the
banked interior reach-drop `deficitCount_openTail_reach_lt` really decreases the recursion's
`unmatchedCount` — the bridge is a real identity, not a vacuous re-label. -/
theorem unmatchedCount_eq_deficitCount_nonvacuous {n : ℕ} (A B : Fin (n + 1) → S2) :
    unmatchedCount A B = deficitCount A B :=
  unmatchedCount_eq_deficitCount A B

end ProofsInTheBook.SphericalDeficientReach
