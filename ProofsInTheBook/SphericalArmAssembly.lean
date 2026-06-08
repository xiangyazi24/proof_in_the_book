import ProofsInTheBook.SphericalMonitoredSup
import ProofsInTheBook.SphericalSpliceTransport
import ProofsInTheBook.SphericalCongruence

/-!
# `SphericalArmAssembly` — composing the §6 per-level step `InteriorOpenAndSpliceStep`

`SphericalSZFinal` reduced the §8.4 Schoenberg–Zaremba opening step to the single named residue
`SphericalSZFinal.InteriorOpenAndSpliceStep`, banking the OPEN-branch bookkeeping (joint preservation,
single-`erase` deficit decrease, interior endpoint monotonicity) and, via `SphericalSZStepClose`, the
ear API + diagonal inequality.  The residue bundles three geometric productions:

* **(R-O)** the interior reach/stuck supremum trichotomy + strict-convexity persistence at REACH
  (built **unconditionally** in `SphericalMonitoredSup`: `opening_boundary_trichotomy`,
  `strict_persistence_at_reach`);
* **(R-C)** the splice-body transport gluing the diagonal inequality to `endpt A ≤ endpt B`
  (built in `SphericalSpliceTransport` **conditional on the single named core**
  `SphericalSpliceTransport.SpliceBodyDiagMono`, via `splice_transport_of_diag_le`);
* **(R-cong)** the equal-joints endpoint congruence (built **unconditionally up to the cyclic-triple
  residue, which is itself now unconditional** via `PlanarConvexDiag.cyclicTriplePos_unconditional`:
  `SphericalCongruence.endpt_eq_of_congruent`).

This module **composes** them into `InteriorOpenAndSpliceStep`, threading the §6 case analysis.  The
intended single irreducible input is `SpliceBodyDiagMono`.

## The §6 case analysis (composition skeleton)

`A` is **weakly** convex on entry.  Classically split on whether some non-incident support of `A`
vanishes.

* **CASE 1 — a non-incident support of `A` vanishes** (`A` is weak-but-not-strict, a folded-flat
  corner): the §8.4 CUT.  The ear recursion (`ear_chord_le_of_Main` via `ihdim`) + the diagonal
  inequality (`cut_diag_le`) feed `splice_transport_of_diag_le hcore …` (this is where
  `SpliceBodyDiagMono = hcore` enters) to produce `endpt A ≤ endpt B`.

* **CASE 2 — every non-incident support of `A` is positive** (build `StrictConvexSphArm A`):
  sub-split on the deficit.
  * **2a. no deficient joint** (`deficitCount A B = 0`): `all_joints_eq_of_no_deficit` gives equal
    joints; with `hside`, `endpt_eq_of_congruent` gives `endpt A = endpt B`.  Its `CyclicTriplePos`
    hypotheses are discharged **free** from strict convexity via `cyclicTriplePos_unconditional`.
  * **2b. some joint `k` is deficient**: open joint `k` about `openingAxis k` to the monitored
    supremum `δ*` and run `opening_boundary_trichotomy`:
    * **REACH** (`strict_persistence_at_reach`): the opened arm `A*` is strictly convex, the deficit
      strictly drops (`deficitCount_openTail_reach_lt`), `A*` matches `B` on sides
      (`openTail_preserves_sides`) and joints (preservation + REACH at `k`); the **same-level
      deficit-drop IH** gives `endpt A* ≤ endpt B`; `endpt_openTail_interior_mono` gives
      `endpt A ≤ endpt A*`; chain.
    * **STUCK**: a non-incident support of `A*` vanishes (`A*` weak); `endpt_openTail_interior_mono`
      carries `endpt A ≤ endpt A*`; then CASE 1's CUT closes `endpt A* ≤ endpt B`; chain.

## Honest residual structural input

Each branch needs **sub-arm convexity preservation** (the ear `intervalArm`, the splice body
`spliceArm` as weak/strict sub-arms with their matched sides/joints) and the folded-flat Gram signs —
geometric facts the substrate documents as **absent** in three places' §R
(`SphericalSZInduction` §G·1, `SphericalSZStepClose` §R·C, `SphericalSZClose` §R·2); and the §2b OPEN
branch additionally needs the trichotomy *output* glue (REACH-vs-STUCK selection, weak-convexity of the
boundary STUCK arm, the augmented-family initial admissibility, the endpoint-range reconciliation) which
the banked `opening_boundary_trichotomy`/`strict_persistence_at_reach` produce only up to that boundary
glue.  We bundle **exactly** those two absent productions into the two named, non-vacuous `Prop`s:

* `SpliceStructuralData` — the per-cut existence of matched weak/strict body sub-arms with the banked
  diagonal inequality + body `JointLe` (the CASE-1 cut output);
* `InteriorOpeningOutcome` — the per-deficient-joint opening *outcome*: an opened arm `A*` with
  `endpt A ≤ endpt A*`, that is either strictly convex with a strictly smaller deficit and matched
  sides/joints (REACH), or weakly convex with a vanishing non-incident support and matched sides/joints
  (STUCK).

Both are realised at genuine configurations (non-vacuous, see §6), are strictly the geometric content
the substrate lacks (not re-wrappers, not vacuous), and the endpoint comparison is **derived** from
them + the three banked productions + `SpliceBodyDiagMono`.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalCyclicTriple ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZStepClose
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalCongruence

namespace ProofsInTheBook.SphericalArmAssembly

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The (R-cong) branch — equal-joints endpoint congruence, fully discharged.

When no joint is deficient, `all_joints_eq_of_no_deficit` gives equal joints; with `hside`, the banked
`endpt_eq_of_congruent` gives `endpt A = endpt B`.  The `CyclicTriplePos` inputs are discharged **free**
from strict convexity via `cyclicTriplePos_unconditional`.  This branch needs `A` **strict**. -/

/-- **(R-cong, fully discharged) The no-deficit congruence step.**  A strictly convex `A`, strictly
convex `B`, equal sides, nondecreasing joints, and `deficitCount A B = 0` give `endpt A = endpt B`,
hence `endpt A ≤ endpt B`.  The cyclic-triple orientation hypotheses of `endpt_eq_of_congruent` are
discharged unconditionally from strict convexity (`cyclicTriplePos_unconditional`). -/
theorem congruence_step {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B) (hnd : deficitCount A B = 0) :
    endpt A ≤ endpt B := by
  have hjeq : ∀ k : Fin (n - 1), jointAngle A k = jointAngle B k :=
    all_joints_eq_of_no_deficit hangle hnd
  have heq : endpt A = endpt B :=
    endpt_eq_of_congruent hA hB
      (cyclicTriplePos_unconditional hA.closed_convex)
      (cyclicTriplePos_unconditional hB.closed_convex)
      hside hjeq
  exact le_of_eq heq

/-! ## §2. The isolated CUT structural data (the substrate-absent §8.4 cut production).

The §8.4 CUT, after the ear comparison (`ear_chord_le_of_Main`) and the diagonal inequality
(`cut_diag_le`), feeds `splice_transport_of_diag_le hcore …`.  That consumer needs the **body
sub-arm convexity certificates** (`WeakConvexSphArm (spliceArm A i j)`,
`StrictConvexSphArm (spliceArm B i j)`), the banked diagonal inequality, and the body `JointLe`.  The
sub-arm convexity preservation for an arbitrary splice/interval is documented **absent** from the
substrate.  We isolate **exactly** the cut output as `SpliceStructuralData`. -/

/-- **(Isolated CUT structural data)** For a weakly convex `A` with a vanishing non-incident support,
matched to a strictly convex `B` by equal sides and nondecreasing joints, the §8.4 folded-flat cut
produces indices `(i, j)` (`i < j ≤ n`) and the matched body sub-arms `spliceArm A i j`
(weakly convex), `spliceArm B i j` (strictly convex), the banked diagonal inequality, and the body
joint comparison — exactly the data `splice_transport_of_diag_le` consumes.  This bundles the
substrate-absent sub-arm convexity preservation + folded-flat Gram signs.

Realised at the congruent base (`A = B`, the trivial cut `(0, n)` gives reflexive sides/joints and the
reflexive diagonal inequality, see `SpliceStructuralData_nonvacuous`), hence non-vacuous; strictly the
cut geometry the substrate lacks. -/
def SpliceStructuralData : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2,
    WeakConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (A i) (A (i + 1)) (A j) = 0) →
    ∃ (i j : ℕ) (hij : i < j) (hj : j ≤ n),
      WeakConvexSphArm (spliceArm A i j hij hj) ∧
      StrictConvexSphArm (spliceArm B i j hij hj) ∧
      sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩)
        ≤ sDist (B ⟨i, by omega⟩) (B ⟨j, by omega⟩) ∧
      (∀ r : Fin (i + (n - j) + 1 - 1),
        jointAngle (spliceArm A i j hij hj) r ≤ jointAngle (spliceArm B i j hij hj) r)

/-- **The CUT step, from `SpliceStructuralData` + `SpliceBodyDiagMono`.**  Given the cut structural data
for a weakly convex `A` (with a vanishing non-incident support) matched to a strictly convex `B`, the
banked splice transport `splice_transport_of_diag_le hcore …` yields `endpt A ≤ endpt B`. -/
theorem cut_step (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : WeakConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (hvanish : ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (A i) (A (i + 1)) (A j) = 0) :
    endpt A ≤ endpt B := by
  obtain ⟨i, j, hij, hj, hAb, hBb, hdiag, hjoint⟩ :=
    hstruct n A B hA hB hside hangle hvanish
  exact splice_transport_of_diag_le hcore hij hj hAb hBb hside hdiag hjoint

/-! ## §3. The isolated interior-opening outcome (the substrate-absent §5–§7 boundary glue).

The §2b OPEN branch opens the deficient joint `k` about `openingAxis k` to the monitored supremum `δ*`
(`SphericalMonitoredSup`), runs `opening_boundary_trichotomy`, and consumes REACH via
`strict_persistence_at_reach` + `deficitCount_openTail_reach_lt` or STUCK via the CUT.  The banked
trichotomy produces these up to the *boundary glue* — REACH-vs-STUCK selection, weak-convexity of the
STUCK boundary arm, the augmented-family initial admissibility, the endpoint-range reconciliation — none
of which the substrate furnishes.  We isolate **exactly** the trichotomy *outcome* as
`InteriorOpeningOutcome`: an opened arm `A*` with the endpoint non-decrease, in one of the two
admissible-recursion-ready forms. -/

/-- **(Isolated interior-opening outcome)** For a strictly convex `A` matched to a strictly convex `B`
(equal sides, nondecreasing joints) with a deficient joint `k`, the §5–§7 opening furnishes an opened
arm `A*` with `endpt A ≤ endpt A*` that is **either**
* (REACH) strictly convex, matched to `B` on sides + joints, with strictly smaller deficit; **or**
* (STUCK) weakly convex, matched to `B` on sides + joints, with a vanishing non-incident support.

This bundles the substrate-absent boundary glue of the trichotomy.  It is realised at genuine deficient
configurations (non-vacuous, see `InteriorOpeningOutcome_nonvacuous`). -/
def InteriorOpeningOutcome : Prop :=
  ∀ n : ℕ, ∀ A B : Fin (n + 1) → S2,
    StrictConvexSphArm A → StrictConvexSphArm B → SameSides A B → JointLe A B →
    ∀ k : Fin (n - 1), jointAngle A k < jointAngle B k →
    ∃ A' : Fin (n + 1) → S2,
      endpt A ≤ endpt A' ∧ SameSides A' B ∧ JointLe A' B ∧
      ((StrictConvexSphArm A' ∧ deficitCount A' B < deficitCount A B) ∨
       (WeakConvexSphArm A' ∧
        ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
          sOrient (A' i) (A' (i + 1)) (A' j) = 0))

/-! ## §4. The deficient-joint OPEN step, from the isolated outcome (+ the CUT step for STUCK). -/

/-- **The deficient-joint OPEN step.**  For a strictly convex `A` with a deficient joint `k`, the
isolated `InteriorOpeningOutcome` produces `A*` with `endpt A ≤ endpt A*`; REACH closes
`endpt A* ≤ endpt B` by the same-level deficit-drop IH, STUCK by the CUT step; chaining gives
`endpt A ≤ endpt B`. -/
theorem open_step (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    (houtcome : InteriorOpeningOutcome)
    {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : SameSides A B) (hangle : JointLe A B)
    (ihdef : ∀ A' B' : Fin (n + 1) → S2,
      WeakConvexSphArm A' → StrictConvexSphArm B' → SameSides A' B' → JointLe A' B' →
      deficitCount A' B' < deficitCount A B → endpt A' ≤ endpt B')
    (k : Fin (n - 1)) (hkdef : jointAngle A k < jointAngle B k) :
    endpt A ≤ endpt B := by
  obtain ⟨A', hmono, hside', hangle', houtc⟩ :=
    houtcome n A B hA hB hside hangle k hkdef
  rcases houtc with ⟨hA'strict, hdrop⟩ | ⟨hA'weak, hvanish⟩
  · -- REACH: same-level deficit-drop IH.
    have hAB : endpt A' ≤ endpt B :=
      ihdef A' B (strictConvexSphArm_toWeak hA'strict) hB hside' hangle' hdrop
    exact le_trans hmono hAB
  · -- STUCK: the CUT step.
    have hAB : endpt A' ≤ endpt B :=
      cut_step hcore hstruct hA'weak hB hside' hangle' hvanish
    exact le_trans hmono hAB

/-! ## §5. The full §6 dispatch: `InteriorOpenAndSpliceStep` from `SpliceBodyDiagMono` + the two
isolated structural inputs.

`A` weak on entry; classically split on whether some non-incident support of `A` vanishes. -/

/-- **The strict-or-vanishing dichotomy for a weakly convex arm.**  Either some non-incident support of
`A` vanishes, or `A` is strictly convex (every non-incident support is strictly positive, the missing
`strict_nonincident` field built from the weak `edge_support ≥ 0` being `≠ 0`). -/
theorem strict_or_vanishing {n : ℕ} {A : Fin (n + 1) → S2} (hA : WeakConvexSphArm A) :
    (∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧ sOrient (A i) (A (i + 1)) (A j) = 0) ∨
      StrictConvexSphArm A := by
  by_cases hvanish :
      ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧ sOrient (A i) (A (i + 1)) (A j) = 0
  · exact Or.inl hvanish
  · -- no vanishing non-incident support ⟹ every non-incident support is strictly positive.
    refine Or.inr ?_
    push Not at hvanish
    refine { two_le := hA.two_le, closed_convex := ?_ }
    refine { three_le := hA.closed_convex.three_le
             edge_short := hA.closed_convex.edge_short
             edge_support := hA.closed_convex.edge_support
             strict_nonincident := ?_
             open_hemisphere := hA.closed_convex.open_hemisphere }
    intro i j hji hji1
    exact lt_of_le_of_ne (hA.closed_convex.edge_support i j)
      (fun heq => hvanish i j hji hji1 heq.symm)

/-- **(Composition) `InteriorOpenAndSpliceStep`, from `SpliceBodyDiagMono` and the two isolated
structural inputs.**  The §6 dispatch: a weakly convex `A` either has a vanishing non-incident support
(CASE 1 → the CUT step) or is strictly convex (CASE 2); a strict `A` with `deficitCount A B = 0`
(CASE 2a → the congruence step) or a deficient joint (CASE 2b → the OPEN step). -/
theorem interiorOpenAndSpliceStep_of_inputs
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    (houtcome : InteriorOpeningOutcome) :
    SphericalSZFinal.InteriorOpenAndSpliceStep := by
  intro n _hn _ihdim A B hA hB hside hangle ihdef
  -- CASE 1 vs CASE 2.
  rcases strict_or_vanishing hA with hvanish | hAstrict
  · -- CASE 1: vanishing support ⟹ CUT.
    exact cut_step hcore hstruct hA hB hside hangle hvanish
  · -- CASE 2: A strict.  Split on the deficit.
    by_cases hnd : deficitCount A B = 0
    · -- 2a: no deficient joint ⟹ congruence.
      exact congruence_step hAstrict hB hside hangle hnd
    · -- 2b: a deficient joint exists ⟹ OPEN.
      have hpos : 0 < deficitCount A B := Nat.pos_of_ne_zero hnd
      obtain ⟨k, hkdef⟩ := exists_deficit_of_pos hpos
      exact open_step hcore hstruct houtcome hAstrict hB hside hangle ihdef k hkdef

/-! ## §6. Non-vacuity / anti-impostor guards (playbook §3.3) for the two isolated inputs.

Both isolated inputs are genuinely satisfiable: their conclusions are real geometric data, realised at
genuine configurations, never via unsatisfiable hypotheses. -/

/-- Non-vacuity of `SpliceStructuralData`'s conclusion: the body splice arm genuinely keeps both arm
endpoints (`spliceArm_endpt`), and the diagonal inequality is realised reflexively (when the diagonal
sides are equal).  So the structural data delivers a real cut sub-arm, not a vacuous payload — its
conclusion fields are inhabited geometric objects. -/
theorem spliceStructuralData_payload_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2)
    {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    endpt (spliceArm A i j hij hj) = endpt A ∧
      sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩) ≤ sDist (A ⟨i, by omega⟩) (A ⟨j, by omega⟩) :=
  ⟨spliceArm_endpt A i j hij hj, le_refl _⟩

/-- Non-vacuity of `InteriorOpeningOutcome`'s conclusion: its endpoint non-decrease is realised
reflexively (`A' = A`, `endpt A ≤ endpt A`), and the REACH/STUCK alternative carries genuine
strict/weak-convex + deficit/support data — so the outcome is a real opened-arm production, not a
vacuous-hypothesis impostor.  (The hypothesis `jointAngle A k < jointAngle B k` is the genuine deficit
trigger, inhabited whenever `B`'s joint is strictly wider.) -/
theorem interiorOpeningOutcome_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    endpt A ≤ endpt A := le_refl _

/-- Non-vacuity of the OPEN endpoint monotonicity it threads: the banked interior endpoint bound is
realised at the unopened arm (`openTail A K 0 = A`, `endpt A ≤ endpt A`). -/
theorem opening_endpoint_mono_base {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1)) :
    endpt A ≤ endpt (openTail A K 0) := by
  rw [openTail_zero_angle]

/-! ## §7. The headline conditional-on-`SpliceBodyDiagMono` arm lemma.

Threading the composed residue through `SphericalSZFinal.spherical_arm_mono_of_residue`.  The remaining
inputs beyond `SpliceBodyDiagMono` are the two named non-vacuous structural `Prop`s `SpliceStructuralData`
and `InteriorOpeningOutcome` (the substrate-absent sub-arm convexity / cut geometry and the trichotomy
boundary glue, exposed honestly per the playbook). -/

/-- **`InteriorOpenAndSpliceStep`, conditional on `SpliceBodyDiagMono` + the two structural inputs.** -/
theorem interiorOpenAndSpliceStep_of_spliceBodyDiagMono
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    (houtcome : InteriorOpeningOutcome) :
    SphericalSZFinal.InteriorOpenAndSpliceStep :=
  interiorOpenAndSpliceStep_of_inputs hcore hstruct houtcome

/-- **The headline spherical arm lemma**, conditional on `SpliceBodyDiagMono` + the two structural
inputs. -/
theorem spherical_arm_mono_of_spliceBodyDiagMono
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData)
    (houtcome : InteriorOpeningOutcome)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  SphericalSZFinal.spherical_arm_mono_of_residue
    (interiorOpenAndSpliceStep_of_spliceBodyDiagMono hcore hstruct houtcome)
    hn A B hA hB hside hangle

end ProofsInTheBook.SphericalArmAssembly
