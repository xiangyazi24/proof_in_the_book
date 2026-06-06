# opus-armuncond-reply — Chapter 13 spherical arm lemma: assembly + the genuine residue

## Status (honest)

`spherical_arm_mono(_strict)` is **NOT** made fully unconditional this round. The directive's premise
("the math is ALL proved — this is assembly via any-support-cut") does **not** hold on close
inspection of the substrate: the any-support cut `stuckSupport_gives_cut` (PROVED) yields *one
unmatched, endpoint-losing* sub-arm, while the §8.4 endpoint glue (`cut_endpt_transport` /
`bothSided_cut_transport`) consumes *matched two-piece* cut data (companion `B`-side cut, equal sides,
nondecreasing joints, **endpoint preservation**). That matched interior cut / reach-recursion
construction is genuinely **not** in the substrate. I built the maximal genuine assembly around it and
isolated the gap as ONE named non-vacuous `Prop` with a concrete failing chain, per the directive's
contingency clause.

New file: `ProofsInTheBook/SphericalArmUncond.lean` (owned solely by this round). Wired into the lib
root `ProofsInTheBook.lean` (after `SphericalTerminalVis`). No substrate file edited beyond that
one-line import. Branch main, no commits.

## What this round GENUINELY closes (UNCONDITIONAL, clean-3)

The decisive structural insight, now mechanised: **the whole Schoenberg–Zaremba chain bottoms out at a
single endpoint-only per-step pair**, and the `qstar`/closing-betweenness shape is unnecessary.

* **`SZInductiveStep`** := `∀ n ≥ 2, SZComparison n → SZComparison (n+1)` — the endpoint-only step,
  carrying NO `qstar`, NO `span≥0` betweenness, NO Gram signs, NO opening bound.
* **`schoenbergZaremba_of_inductiveStep : SZInductiveStep → SchoenbergZarembaTarget`** and
  **`armUncond_mono/strict_of_inductiveStep`** — a self-contained induction (base `szComparison_two`,
  step from the IH) producing the unconditional kernel arm lemma `spherical_arm_mono`/`_strict` from
  the endpoint-only step alone. This **removes the `SZGeom` / `SZStepGeom` / `StuckWitnessExists` /
  `OpeningStructuralAssembly` / `TerminalVisibility`-shaped hypothesis from the entire chain** — the
  closing-betweenness route (disproved in the terminal-vis round) is fully eliminated.
* **`MatchedCutData A B`** (existence of matched cut sub-arms, endpoint-only) +
  **`step_of_matchedCutData`** (`MatchedCutData → one step`, via the proved `cut_endpt_transport`) +
  **`inductiveStep_of_matchedCutStep`** (`MatchedCutStep → SZInductiveStep`) — the load-bearing
  reduction: the endpoint pair is *derived* from the matched cut through `cut_endpt_transport`, not
  assumed.
* **`anySupport_cutArm`** — re-export of the proved terminal-visibility-free §8.4 Case-2 datum
  (`stuckSupport_gives_cut`): any non-incident vanishing support gives a strictly convex sub-arm
  sharing `A 0`.

## The single remaining residue (named, non-vacuous, concrete failing chain)

**`MatchedCutStep`** : `∀ n ≥ 2, ∀ A B (convex, equal sides, nondecreasing joints), SZComparison n →
MatchedCutData A B` — the per-step *existence* of the matched two-piece diagonal cut (with its `B`-side
companion) / reach recursion. `armUncond_strict_of_matchedCutStep` closes the strict arm lemma from it.

Concrete failing chain (verified against the substrate, file:line):

1. `step_of_matchedCutData` needs `A' B'` with `sideLen A'=sideLen B'`, `jointAngle A'≤jointAngle B'`,
   `endpt A'=endpt A`, `endpt B'=endpt B`, plus the strictness link.
2. `stuckSupport_gives_cut` / `anySupport_cutArm` return ONE `A'` with `A' 0 = A 0` only — no `B'`, no
   side/joint match, and **no endpoint preservation**: `SphericalDiagCut.cutArm` (last-vertex drop) has
   `endpt = sDist (A 0) (A n)`, not `sDist (A 0) (A (last))` (`tailArm` drops the first vertex,
   symmetric loss). There is **no interior-vertex-drop construction anywhere** in the substrate
   (`grep` of `dropVertex/removeNth/succAbove/interior cut` over `Spherical*.lean` → none).
3. `CH13_CAUCHY_FULL_DESIGN.md` §8.4 Case 2 requires the cut to split into **two** matched sub-pieces
   with the `B`-side cut at the *corresponding* diagonal (equal diagonal length by spherical SAS
   `diag_len_eq`); in the *opening* case the cut occurs on the **opened** arm at `δ*`
   (`augmented_reachOrStuck_at_sup`), whose stuck support has no corresponding feature in `B`. Reaching
   the matched configuration needs the reach recursion on `unmatchedCount`
   (`unmatchedCount_lt_of_match`, substrate) to a matched joint, then the *interior* equal-angle cut —
   unrealised by `cutArm`. Even the all-equal/congruent half (`endpt A = endpt B`) needs this: there is
   no `(n+1)`-arm congruence lemma in the substrate (only the `n=2` SAS `diag_len_eq`).

`MatchedCutStep` is strictly narrower than `StuckWitnessExists` / `OpenedArmReachOrStuck` / `SZStepGeom`
(it omits the `qstar`, the `span≥0` betweenness, the two Gram signs, and the opening bound). It is the
genuine geometric output those primitives' construction must furnish, recorded `qstar`-free. No
co-extensive re-wrapper banked; the new content is the harness collapsing the chain onto the single
per-step endpoint pair.

Non-vacuity guards (playbook §3.3): `matchedCutData_satisfiable` (realised by genuine matched data),
`matchedCutData_refl` (congruent base, `A'=B'`), `matchedCutStep_base = szComparison_two`,
`anySupport_cut_payload_nonvacuous`, `inductiveStep_conclusion_satisfiable`.

## Verification

* `rsync` + `ssh uisai1 ... lake env lean ProofsInTheBook/SphericalArmUncond.lean` → **RC=0**.
* `lake build ProofsInTheBook.SphericalArmUncond` → "Build completed successfully (8445 jobs)".
* **FULL `lake build`** (after wiring into lib root) → "Build completed successfully (**8629 jobs**)",
  RC=0, zero errors.
* `#print axioms` (scratch importer, removed after) → **clean-3 `[propext, Classical.choice,
  Quot.sound]`** on: `schoenbergZaremba_of_inductiveStep`, `armUncond_mono_of_inductiveStep`,
  `armUncond_strict_of_inductiveStep`, `step_of_matchedCutData`, `inductiveStep_of_matchedCutStep`,
  `schoenbergZaremba_of_matchedCutStep`, `armUncond_strict_of_matchedCutStep`, `anySupport_cutArm`,
  `szComparison_all_of_step`. No `sorryAx`, no `ofReduceBool`/`native_decide`.
* `grep -nE 'sorry|admit|^axiom|native_decide'` → only the module-doc prose; 0 in code.

## Honest verdict

FAITHFUL PARTIAL. The terminal-visibility round correctly removed a *false sub-obstruction*
(terminal-first identification); this round shows the residue that remains is **architectural-plus-
geometric**: the matched interior-cut / reach-recursion construction (design §8.4 "THE hard theorem"),
which the substrate does not contain. The genuine new content is the **endpoint-only harness** that
collapses the entire conditional chain onto a single, `qstar`-free per-step `Prop` (`MatchedCutStep`)
and re-derives `SchoenbergZarembaTarget` + the unconditional kernel arm lemma from it — eliminating the
disproved closing-betweenness route from the chain. Closing `MatchedCutStep` requires building the
interior-vertex-drop sub-arm (convexity + endpoint preservation + `B`-side matching via `diag_len_eq`)
and the reach recursion on `unmatchedCount` — a real construction, not wiring. That is the precise,
non-vacuous, single-`Prop` frontier for the next round.
