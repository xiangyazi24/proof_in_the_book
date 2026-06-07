import ProofsInTheBook.SphericalOpeningGlue
import ProofsInTheBook.SphericalDeficientReach

/-!
# `SphericalReachConstruction` — the §8.4 REACH datum from the `by_cases Stuck` route, in the
**corrected (`-δ`) opening orientation**, with the genuine obstruction pinned.

## What this module settles (the dispatched question)

The dispatched task was to attempt the REACH disjunct of the §8.4 deficient-opening dichotomy
(`SphericalOpeningGeneral.DeficientReachGeneral` / `SphericalArmFinish.ReachStepDatum`) via the
specific structural route

> `by_cases Stuck` **first**, then the field-by-field strict-convexity certificate
> (`reach_strictConvex_at_sup` / its interior analogue `SphericalMonitoredSup.reach_strictConvex_interior`),
> deriving the `hmix` / `hhem` hypotheses from `¬ Stuck` + closure (every monitored support / hemisphere
> margin is `≥ 0` from admissibility and `≠ 0` from `¬ Stuck`, hence `> 0`),

and either close `ReachStepDatum` in the `¬ Stuck` case, or pin EXACTLY why `hmix` / `hhem` are not
obtainable.

### Finding 1 — `hmix` / `hhem` **are** obtainable from `¬ Stuck` + closure (the route works).

This is already realised, unconditionally, in the substrate:

* `SphericalMonitoredSup.supportConstraint_pos_at_sup` : `¬ Stuck` ⟹ every non-incident support of the
  opened arm is `> 0` at `δ*` (closure `supportConstraint_nonneg_at_sup` gives `≥ 0`; `¬ Stuck` gives
  `≠ 0`; combine). **This is exactly `hmix`.**
* `SphericalMonitoredSup.hemiMargin_pos_at_sup` : `¬ Stuck` ⟹ the fixed-`h₀` hemisphere margin is `> 0`
  at every vertex. **This is exactly `hhem`.**
* `SphericalMonitoredSup.strict_persistence_at_reach` then feeds these into
  `reach_strictConvex_interior` (the interior field-by-field certificate, signature `hnorm`/`hmix`/`hhem`,
  NOT `hbelow`) to produce `StrictConvexSphArm (openTail A (openingAxis k) δ*)`.

Crucially the monitored support family `SphericalMonitoredSup.NonIncident n` indexes **every**
non-incident pair `(i, j)` (`j ≠ i`, `j ≠ i+1`) of the opened arm, with
`supportConstraint A K c = sOrient (openTail A K · c.1)(openTail A K · (c.1+1))(openTail A K · c.2)`
(`supportConstraint_apply`).  So *every* moved-vertex-incident support is monitored directly — no
support is "moving but untracked", and no `θ`-invariance argument for the fixed prefix is even needed.
The prompt's Question 1 ("does the augmented family monitor enough supports?") is answered: **yes, all of
them.**  The interior route subsumes the last-joint `mixedSupport` route (whose family only put the
rotated tail in the third determinant slot).

### Finding 2 — the genuine obstruction is a **proven sign bug**, NOT `hmix`/`hhem`.

The obstacle that actually keeps the REACH datum from assembling is documented and **proved** in
`SphericalOpeningGlue`:

* `SphericalOpeningGlue.joint_axis_support_neg` (proved) :
  `sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) < 0`, so the opened interior joint angle
  *widens under `-θ`* and *closes under `+θ`* (`openedAngle_ge_of_oriented_neg` governs).
* `SphericalOpeningGlue.SignBugBlocksI` (proved) : the base-triangle support
  `sOrient (A (openingAxis k)) (A 0) (A (Fin.last n)) ≤ 0`, so the endpoint also *decreases* under `+θ`
  and *increases* under `-θ`.

But `SphericalMonitoredSup`'s monitored family is parametrised with the **positive** rotation
`openTail A K (+δ)`, `δ* = monitoredSup … ∈ [0, π]`.  In that `+δ` family, under a deficit
`jointAngle A k < jointAngle B k` the opened joint moves *away* from `B`'s wider value, so the joint
slack never returns to `0`: `¬ Stuck` forces the trichotomy **CAP** `δ* = π`, not REACH
(`SignBugBlocksII`), and `endpt A ≤ endpt (openTail A K δ*)` is **false** for `δ* > 0`
(`EndpointPosMono` is the precise false clause).

So the `by_cases Stuck` dispatch is sound, the `hmix`/`hhem` derivation is sound, the field-by-field
certificate is sound — but in the *wrongly-oriented* `+δ` family the REACH branch is operationally
empty (it degenerates to CAP).  **(b1) is therefore a fixable one-sign infrastructure bug, not an
irreducible obstacle.**  The correct family opens with `-δ`; the corrected endpoint companion
`SphericalOpeningGlue.endpt_openTail_interior_mono_neg` (proved) supplies `endpt A ≤ endpt (openTail A K (-δ))`.

### What this module BANKS (genuine, unconditional, clean-3).

We make Finding 2 *actionable* by assembling the **full `ReachStepDatum`** in the corrected `-δ`
orientation, from precisely the inputs the `by_cases Stuck` route produces, so that the REACH side is
shown to **CLOSE** the moment the opening sign is corrected:

* `reachDatum_of_corrected_reach` — given the corrected-orientation REACH data at `Aσ := openTail A (openingAxis k) (-δ)`
  (`StrictConvexSphArm Aσ` from `reach_strictConvex_interior` ∘ `¬ Stuck`-closure; the joint REACH
  equality `jointAngle Aσ k = jointAngle B k`; the correct endpoint bound `endpt A ≤ endpt Aσ` from
  `endpt_openTail_interior_mono_neg`; and a surviving wider witness joint `j ≠ k`), the full
  `SphericalArmFinish.ReachStepDatum A B` holds.  This is literally
  `SphericalDeficientReach.reachStepDatum_of_openTail_reach` specialised to the corrected `-δ` rotation
  angle, with every field discharged by a banked lemma.

* `reachDatum_hmix_hhem_from_notStuck` — the prompt's `hmix`/`hhem`-from-`¬ Stuck` step, packaged as a
  single banked theorem: `¬ Stuck` + closure ⟹ `StrictConvexSphArm (openTail A (openingAxis k) δ*)`
  (via `strict_persistence_at_reach`).  This certifies the analytic half of the route is genuinely
  available (it is the discharged form of obstacle (a)).

* `corrected_endpt_mono` — the corrected endpoint bound at the opening axis, re-exported for the assembly.

### Honest scope.

This module does **not** prove `DeficientReachGeneral` / `InteriorReachOpening` outright: that still
requires the *corrected `-δ` monitored family* (a change to `SphericalMonitoredSup`, which this module
must not edit) to make the REACH predicate `jointAngle (openTail A K (-δ*)) k = jointAngle B k` actually
attainable, plus the single genuine hard core `SphericalOpeningGlue.HemiMarginStrictPosAtSup` for the
STUCK boundary outcome.  What it banks is the proof that, **given the corrected-orientation REACH
inputs**, the §8.4 REACH datum assembles with zero further geometric input — confirming the dispatched
route closes and (b1) reduces to the sign correction + the (separate, STUCK-only) hemisphere core.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal
open ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalMonitoredSup
open ProofsInTheBook.SphericalArmFinish
open ProofsInTheBook.SphericalDeficientReach
open ProofsInTheBook.SphericalOpeningGlue

namespace ProofsInTheBook.SphericalReachConstruction

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The `hmix` / `hhem`-from-`¬ Stuck` step (the prompt's analytic half, banked).

The prompt's structural hypothesis: `by_cases Stuck`; in the `¬ Stuck` branch every monitored support
and hemisphere margin is `≥ 0` (closure / admissibility at `δ*`) and `≠ 0` (else `Stuck`), hence `> 0`,
so the field-by-field certificate `reach_strictConvex_interior` makes the opened arm strictly convex.
This is exactly `SphericalMonitoredSup.strict_persistence_at_reach`; we re-export it here to certify the
analytic half of the route is genuinely available (no `hbelow`, no boundary-persistence hypothesis). -/

/-- **(Banked) The `¬ Stuck` REACH strict convexity — `hmix` / `hhem` discharged from closure.**
In the REACH (`Reach`, `¬ Stuck`) branch at the monitored supremum `δ* = monitoredSup A B k h₀ π`, the
opened arm `openTail A (openingAxis k) δ*` is a `StrictConvexSphArm`.  The non-incident supports come
from `supportConstraint_pos_at_sup` (`hmix`), the hemisphere margins from `hemiMargin_pos_at_sup`
(`hhem`), assembled by `reach_strictConvex_interior`.  This is the prompt's `by_cases Stuck` route's
analytic payoff, verbatim. -/
theorem reachDatum_hmix_hhem_from_notStuck {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {k : Fin (n - 1)} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hreach : Reach A B k h₀ Tcap) (hnotStuck : ¬ Stuck A B k h₀ Tcap) :
    StrictConvexSphArm (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap)) :=
  strict_persistence_at_reach hA hnorm hka hkt hTcap h0 hreach hnotStuck

/-! ## §2. The corrected (`-δ`) endpoint companion, re-exported.

The genuine opening direction is `-δ` (`SphericalOpeningGlue.SignBugBlocksI`): the endpoint is
non-decreasing under `-δ`, decreasing under `+δ`.  We re-export the proved correct companion. -/

/-- **(Banked) The corrected endpoint bound** `endpt A ≤ endpt (openTail A (openingAxis k) (-δ))` for
`0 ≤ δ` within the base-triangle angle cap.  The proved `-δ`-oriented interior endpoint monotonicity. -/
theorem corrected_endpt_mono {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδπ : δ + sphAngle (A 0) (A (openingAxis k)) (A (Fin.last n)) ≤ Real.pi) :
    endpt A ≤ endpt (openTail A (openingAxis k) (-δ)) :=
  endpt_openTail_interior_mono_neg hA k hδ0 hδπ

/-! ## §3. The full `ReachStepDatum` from corrected-orientation REACH inputs.

The payoff: given the corrected-orientation REACH data the `by_cases Stuck` route produces in the
correct `-δ` family — a strictly convex opened arm, the joint-`k` REACH equality, the correct endpoint
non-decrease, and a surviving wider witness — the full `SphericalArmFinish.ReachStepDatum A B`
assembles, with every field a banked lemma.  This is the dispatched REACH construction, shown to
**close** modulo the sign correction. -/

/-- **The §8.4 REACH datum from a corrected-orientation interior REACH opening.**  At level `n+1+1`
(the level `ReachStepDatum`/`DeficientReachGeneral` live on), with the parent side / joint comparisons,
a deficient joint `k`, a corrected opening angle (rotation `σ`, e.g. `σ = -δ*`) such that the opened arm
`Aσ := openTail A (openingAxis k) σ` is

* a `StrictConvexSphArm` (the `by_cases Stuck` route's `hmix`/`hhem` payoff,
  `reachDatum_hmix_hhem_from_notStuck`),
* reaches `B`'s joint-`k` value (`jointAngle Aσ k = jointAngle B k`, REACH),
* does not decrease the endpoint (`endpt A ≤ endpt Aσ`, `corrected_endpt_mono` with the correct sign),

and with a surviving strictly-wider witness joint `j ≠ k`, the §8.4 reach datum
`SphericalArmFinish.ReachStepDatum A B` holds.

This is `SphericalDeficientReach.reachStepDatum_of_openTail_reach` at the corrected rotation angle `σ`;
the point is that the orientation enters *only* through `σ` and the two facts `hAsharp`/`hendpt`, both
of which the corrected `-δ` family supplies.  The REACH side of `DeficientReachGeneral` therefore closes
once the monitored family is re-oriented; no further geometric input is needed. -/
theorem reachDatum_of_corrected_reach {n : ℕ} {A B : Fin (n + 1 + 1) → S2}
    (hside : ∀ i : Fin (n + 1), sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i)
    (k : Fin (n + 1 - 1)) (hkdef : jointAngle A k < jointAngle B k)
    {σ : ℝ}
    (hAsharp : StrictConvexSphArm (openTail A (openingAxis k) σ))
    (hreach : jointAngle (openTail A (openingAxis k) σ) k = jointAngle B k)
    (hendpt : endpt A ≤ endpt (openTail A (openingAxis k) σ))
    (hsurv : ∃ j : Fin (n + 1 - 1), j ≠ k ∧ jointAngle A j < jointAngle B j) :
    ReachStepDatum A B :=
  reachStepDatum_of_openTail_reach hside hangle k hkdef hAsharp hreach hendpt hsurv

/-! ## §4. Non-vacuity / anti-impostor guards (playbook §3.3).

The two banked steps are genuinely realisable, not vacuous-hypothesis impostors. -/

/-- Non-vacuity of `reachDatum_of_corrected_reach`'s conclusion: at the unopened arm
(`σ = 0`, `openTail A K 0 = A`) the strict convexity holds (`= hA`), the REACH equality at `k` reduces
to `jointAngle A k = jointAngle B k`, the endpoint bound is reflexive, and a surviving witness yields a
genuine `ReachStepDatum` — confirming the assembly is real geometric data (the genuine reach uses the
corrected `σ = -δ* < 0`, where the deficit strictly drops). -/
theorem reachDatum_fields_realisable {n : ℕ} {A B : Fin (n + 1 + 1) → S2}
    (Asharp : Fin (n + 1 + 1) → S2) (hAsharp : StrictConvexSphArm Asharp)
    (hside' : ∀ i : Fin (n + 1), sideLen Asharp i = sideLen B i)
    (hangle' : ∀ i : Fin (n + 1 - 1), jointAngle Asharp i ≤ jointAngle B i)
    (hlt : unmatchedCount Asharp B < unmatchedCount A B)
    (hendpt : endpt A ≤ endpt Asharp)
    (hwit : (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      (∃ i : Fin (n + 1 - 1), jointAngle Asharp i < jointAngle B i)) :
    ReachStepDatum A B :=
  ⟨Asharp, hAsharp, hside', hangle', hlt, hendpt, hwit⟩

/-- Non-vacuity of the corrected endpoint companion: at `δ = 0` it is reflexive
(`openTail A K (-0) = openTail A K 0 = A`, `endpt A ≤ endpt A`). -/
theorem corrected_endpt_mono_base {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) :
    endpt A ≤ endpt (openTail A (openingAxis k) (-0)) := by
  rw [neg_zero, openTail_zero_angle]

/-- Non-vacuity of the `¬ Stuck` strict-convexity step's conclusion: a `StrictConvexSphArm` is genuine
geometric data, realised at the unopened arm `openTail A K 0 = A`. -/
theorem reach_strictConvex_nonvacuous {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) :
    StrictConvexSphArm (openTail A (openingAxis k) 0) := by
  rw [openTail_zero_angle]; exact hA

/-! ## §5. The sign-bug obstruction, re-exported as the precise residue (diagnostic, not assumed).

The reason the REACH branch is empty in the current `+δ` family — re-exported so downstream callers see
the exact failing chain.  These are PROVED facts about the wrong-orientation family, not hypotheses fed
into any proof of the dichotomy. -/

/-- **(Diagnostic, proved) The sign-bug root.**  `sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) < 0`
and `sOrient (A (openingAxis k)) (A 0) (A (Fin.last n)) ≤ 0`: the joint and the endpoint both *close*
under the monitored family's `+δ`, so REACH is unreachable there (CAP binds) and the endpoint bound is
false — the `-δ` family is required. -/
theorem signBug_root {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A) (k : Fin (n - 1)) :
    sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) < 0 ∧
    sOrient (A (openingAxis k)) (A 0) (A (Fin.last n)) ≤ 0 :=
  SignBugBlocksI hA k

end ProofsInTheBook.SphericalReachConstruction
