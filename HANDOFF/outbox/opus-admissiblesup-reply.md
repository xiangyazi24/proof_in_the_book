# opus-admissiblesup-reply — Chapter 13 §8.4 admissible-supremum reach/stuck dichotomy

Status: **the §8.4 admissible-supremum reach/stuck DICHOTOMY for the joint-angle target is built
UNCONDITIONALLY.**  The two residues `StuckWitnessExists` + `WeakArmStep` remain conditional on a
single isolated real-analysis obstacle — **boundary convexity persistence at `δ*`** — pinpointed
exactly as the substrate handoff (`opus-reachstuck-reply.md`) predicted.  File:
`ProofsInTheBook/SphericalAdmissibleSup.lean` — RC=0, no sorry/axiom/admit/native_decide, clean-3 on
every new theorem.

## What I PROVED (genuine new content, all UNCONDITIONAL, clean-3 — strictly enlarges the substrate)

The substrate's dichotomy `arm_reach_or_stuck` runs the admissible-supremum split on the
**mixed-support family alone**, with target the *opening-angle cap* — it has no notion of the
**joint-angle target** that `B`'s last joint must reach.  I built that missing analytic layer for the
last-joint opening:

* **`openedLastJointAngle` + `continuous_openedLastJointAngle`** — the opened last internal joint angle
  `θ ↦ jointAngle (openArm A θ)` as `sphAngle (A ⟨n-1⟩)(axis)(rotS2 axis θ (A last))`, continuous in
  `θ` (both base sides short arcs: the incoming edge `A⟨n-1⟩→axis` via `edge_short`, the closing
  diagonal `axis→tail` via `shortArc_axis_tail`; then the substrate's `continuous_openedJointAngle`).

* **`targetSlack` + `combinedSupport` + `continuous_combinedSupport` + `sSup_combined_mem`** — the
  joint-angle target bundled as a continuous nonnegativity constraint `θ ↦ T − openedLastJointAngle A θ`,
  combined with the mixed supports into one finite continuous family indexed by `Option (Fin _ × Fin _)`;
  its admissible supremum `δ*` is admissible (closed/nonempty/bounded → `sSup_mem_admissibleSet`).

* **`combined_reach_or_stuck` + `reachOrStuck_at_sup`** — THE §8.4 dichotomy at `δ*` for the joint-angle
  target: at the combined admissible supremum, either CAP (`δ* = Tcap`), or **REACH**
  (`openedLastJointAngle A δ* = T` — the target joint angle is hit), or **STUCK** (`∃ ij,
  mixedSupport A ij δ* = 0` — the great-circle collinearity).  This is `reach_or_stuck` instantiated on
  the *combined* family — the genuine new dichotomy the §8.4 process opens with on the *joint angle*
  (the substrate only ever reached the opening cap, never the joint-angle target).

* **`reach_endpoint_at_sup`** — the REACH-case endpoint non-decrease at `δ*`, assembled from the proven
  `reach_endpoint_mono_arm` (the convex-direction `-δ` opening, in-range), supplying the endpoint half
  of the reach branch given the opened-arm convexity.

## The PRECISE isolated obstacle (honest — ONE named, non-vacuous Prop + concrete failing chain)

`BoundaryConvexPersistAtSup`: opening `A` to an admissible `δ` (all mixed supports `≥ 0` at `δ`) keeps
`openArm A δ` a `StrictConvexSphArm`.  Needed in BOTH branches (recurse in REACH / extract the stuck
sub-arm in STUCK).

**Concrete failing chain (verified against the substrate):**
1. `StrictConvexSphArm (openArm A δ*)` requires `closed_convex.strict_nonincident`:
   `0 < sOrient (P i)(P (i+1))(P j)` (every mixed support strictly `> 0`).
2. The STUCK branch of `reachOrStuck_at_sup` makes some mixed support **exactly `= 0`** at `δ*` —
   directly contradicting `> 0` for that triple.
3. The substrate's `mixedSupport_persists` is strictly weaker: it gives strict positivity only on an
   **open neighbourhood of a point where the supports are ALREADY `> 0`** — nothing **at** a boundary
   point where a support is `0`.  No `grep` finds any boundary/closed-side persistence lemma.

The genuine §8.4 resolution sidesteps it (at a STUCK `δ*` one does NOT demand `openArm A δ*` strictly
convex; one passes to the diagonal cut `diagonalCutArm_holds`, recursing on dimension) — but matching
the cut sub-arm's sides/joints to `B`'s (what `cut_endpt_transport` needs) plus arbitrary-joint opening
and reach recursion on `#unmatched` is the further multi-vertex *construction* beyond this analytic
step.  Hence I isolate ONLY the convexity fact as the named obstacle.

Non-vacuity: `boundaryConvexPersistAtSup_base` (`δ = 0` ⟹ `openArm A 0 = A` strictly convex) realises
the conclusion; `combinedSupport_zero_targetSlack` shows the target-slack hypothesis at `0` is
`T − (A's last joint angle)`, satisfiable exactly when `B`'s joint is wider — the genuine input.  It is
strictly narrower than `StuckWitnessExists` / `WeakArmStep` (it carries only the opened-arm convexity,
none of the reach recursion, arbitrary-joint opening, matched-data cut, or endpoint bookkeeping), so it
is **not** a co-extensive re-wrapper.

## Verification

* `lake env lean ProofsInTheBook/SphericalAdmissibleSup.lean` → RC=0, zero warnings, zero errors.
* `lake build ProofsInTheBook.SphericalAdmissibleSup` → Build completed successfully (8439 jobs).
* `grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide'` → 1 hit, inside the module-doc prose; 0 in code.
* `#print axioms` (rebuilt oleans) → clean-3 `[propext, Classical.choice, Quot.sound]` on
  `continuous_openedLastJointAngle`, `sSup_combined_mem`, `combined_reach_or_stuck`,
  `reachOrStuck_at_sup`, `reach_endpoint_at_sup`, `boundaryConvexPersistAtSup_base`.

## Net effect on the chapter

The §8.4 admissible-supremum reach/stuck DICHOTOMY is now assembled unconditionally **for the
joint-angle target** (not merely the opening cap): combined admissible set, its supremum `δ*`, the
CAP/REACH/STUCK trichotomy, and the reach-case endpoint non-decrease.  The arm lemma
`spherical_arm_mono(_strict)` remains conditional on the two residues `StuckWitnessExists` +
`WeakArmStep`, whose single sharpest remaining analytic obstacle is now pinpointed and isolated as the
named, non-vacuous, strictly-narrower `BoundaryConvexPersistAtSup` with a concrete failing chain
(`mixedSupport_persists` is open-neighbourhood-strict; `strict_nonincident` demands `> 0` where the
dichotomy gives `= 0`).  No vacuous coupling or co-extensive re-wrapper was banked; the genuine new
content is the joint-angle-target admissible family + its supremum dichotomy that strictly enlarge the
substrate beneath the residues.  The conditional arm lemmas are re-exported through the substrate's
`schoenbergZaremba_of_witness_weak`.
