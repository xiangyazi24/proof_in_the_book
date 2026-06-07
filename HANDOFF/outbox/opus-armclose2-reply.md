# opus-armclose2-reply — discharging the two obstacles of `DeficientReachStep`

## Status (honest)

**Obstacle (a)'s analytic core is DISCHARGED as real clean-3 theorems.  Obstacle (b) and the
arbitrary-joint endpoint transport remain the genuine irreducible STRUCTURAL content, now precisely
isolated with concrete file:line failing chains, beneath which (a) no longer sits.  The arm lemma is
NOT made unconditional this round; it stays conditional on the single structural atom
`DeficientReachStructural` (same shape as `DeficientReachStep`).**

The directive's premise — "a prior round confirmed these two inputs are constructive/analytic, not
classical-theorem-hard" — is **half right**: obstacle (a) (the strict-convex persistence up to `δ*`) IS
analytic and is now genuinely closed; obstacle (b) (the `B`-companion matched cut) is **not**
constructive from the listed pieces — it is the substrate's already-recorded terminal-visibility
obstruction, *proved not implied by strict convexity* (`SphericalTerminalVis.terminalVisibility_false`,
clean-3 in the substrate).  Verified against the actual source, not impression.

New file: `ProofsInTheBook/SphericalArmClose2.lean` (owned solely by this round).  One substrate edit:
`ProofsInTheBook.lean` lib root, `import ProofsInTheBook.SphericalArmClose2` after `SphericalArmFinish`.
No edit to `SphericalArmFinish` / `SphericalAdmissibleSup` / `SphericalMatchedCut` was needed — the
discharge of (a) is additive (new file consuming the substrate), so the substrate stays untouched.
Branch main, no commits.

## What this round GENUINELY BANKS (UNCONDITIONAL, clean-3) — obstacle (a)'s analytic core

The binding fact `SphericalAdmissibleSup.reach_strictConvex_at_sup` was *missing* was the persistence of
strict positivity of the monitored supports **up to** `δ*`.  The prior rounds reported "no
strict-up-to-`δ*` persistence lemma exists."  This round supplies exactly it:

* **`pos_at_of_pos_below_of_ne`** — the handoff's verbatim claim, now a theorem: a *continuous*
  `g : ℝ → ℝ` that is `> 0` on `[0, δ)` and `≠ 0` at `δ` (with `0 < δ`) is `> 0` at `δ`.  Proof by the
  intermediate value theorem (`intermediate_value_Icc'` on `[δ/2, δ]`): a function positive
  just-below and nonzero-at the boundary cannot be negative there.  This is the "didn't hit 0 at `δ*`
  ⟹ still `> 0` at `δ*`" disjunct the case-split prior rounds missed.

* **`openArm_support_pos_at_of_below` / `openArm_hemi_pos_at_of_below`** — its specialisations to a
  non-incident opened-arm support and the hemisphere margin (via `continuous_openArm_sOrient` /
  `continuous_openArm_hemisphere`, substrate).

* **`reach_strictConvex_of_below`** — **the discharged form of `reach_strictConvex_at_sup`**: from
  strict convexity on `[0, δ)`, short edges at `δ`, the fixed hemisphere normal positive on `[0, δ)`,
  and **non-vanishing at `δ`** of every support and margin (the REACH disjunct), it derives `hmix` and
  `hhem` and produces `StrictConvexSphArm (openArm A δ)`.  The two free hypotheses of
  `reach_strictConvex_at_sup` are now **derived, not assumed** — exactly the discharge the directive
  asked for in (a).

* **`reachStrictConvex_dichotomy_at`** — **the clean, mutually-exclusive REACH/STUCK dichotomy at `δ`**:
  classically case-split on whether *some* non-incident support of `openArm A δ` vanishes.  No vanish ⟹
  REACH (`reach_strictConvex_of_below`, a genuine `StrictConvexSphArm`); some vanish ⟹ STUCK (a surfaced
  non-incident vanishing triple).  This makes the augmented trichotomy's *non-exclusive* disjuncts (the
  exact gap the prior round flagged: "reach and stuck are not mutually exclusive at the same `δ*`") into
  a usable either/or — the case split is on the supports themselves, not on which constraint the
  supremum binds.

* **`stuck_cut_of_dichotomy`** — the STUCK disjunct feeds `stuckSupport_gives_cut` (substrate) to yield
  a strictly convex cut sub-arm of `openArm A δ` sharing the first endpoint `A 0`.

These are the analytic backbone the substrate lacked.  Obstacle (a) is, in the dischargeable direction,
**closed**: the strictness of the opened supports at `δ*` is no longer a free hypothesis.

## The residue (named, non-vacuous, concrete failing chains) — `DeficientReachStructural`

After (a)'s core, the disjunction `ReachStepDatum A B ∨ MatchedCutData A B` still needs the two
**structural** facts, isolated as the single named `Prop` `DeficientReachStructural` (same shape as
`DeficientReachStep`; `deficientReachStep_of_structural` is an honest same-shaped reduction — NOT
claimed as headline progress, only as the marker that the residue is now the structural atom with (a)
discharged beneath it):

1. **Arbitrary-joint endpoint transport (REACH).**  `SphericalCore.openArm` opens only the *last*
   joint; `SphericalReachStuck.reach_endpoint_mono_arm` proves `endpt A ≤ endpt (opened)` **only** for
   the last-joint base triangle `(A 0, openAxis A = A ⟨n⟩, A (Fin.last (n+1)))`.  The deficient joint
   from `joint_dichotomy` is an arbitrary `i : Fin (n+1-1)`.  The relabel
   `SphericalSZComplete.cyclicShiftPolygon_strictConvex` is a *closed-polygon* symmetry: it preserves
   the convex-polygon fields but does **not** transport the *arm* endpoint pair `(A 0, A last)` (the
   endpoint distance is not cyclically invariant).  So opening an interior deficient joint to `δ*`
   produces a smaller-`unmatchedCount` arm carrying **no** `endpt A ≤ endpt Asharp` bound.  No
   arm-level open-at-`k` endpoint lemma exists (`grep`).

2. **`B`-companion matched corner (STUCK).**  The cut at a stuck vertex of `A` (where a support
   *vanishes*, `SphericalTerminalVis.vanishingSupport_planar_collinear`) has a *collinear / degenerate*
   corner; `B` at the same vertex is non-degenerate.  `MatchedCutData A B` needs the two cut sub-arms
   matched, and the SAS diagonal-length agreement `SphericalSZChain.diag_len_eq` requires the cut-corner
   *included angle to agree* between `A` and `B` — but at the stuck vertex `A`'s angle is `π`
   (collinear) while `B`'s is `< π`.  The two cut diagonals do **not** match.  This is the substrate's
   terminal-visibility obstruction, **proved not implied by strict convexity**
   (`SphericalTerminalVis.terminalVisibility_false`, on the concrete `quadArm` witness).

Both are GENUINE structural content; `DeficientReachStructural` is the residue with obstacle (a)'s
analytic half removed.  `deficientReachStep_of_structural : DeficientReachStructural → DeficientReachStep`,
hence `spherical_arm_mono(_strict)_of_structural` re-export the kernel arm lemmas conditional on it.

## Non-vacuity guards (playbook §3.3)

`pos_at_of_pos_below_of_ne_nonvacuous` (the persistence is a real theorem, witnessed on `g = 1`),
`reachStrictConvex_dichotomy_reach_inhabited` (REACH disjunct inhabited), `stuck_cut_payload_nonvacuous`
(STUCK delivers a real `StrictConvexSphArm`), `deficientReachStructural_cut_satisfiable` (CUT alternative
realised at `A = A` via `congruent_matchedCutData_refl`).  All in-file, clean-3.

## Verification

* `rsync` + `ssh uisai1 ... lake env lean ProofsInTheBook/SphericalArmClose2.lean` → **RC=0**, **0
  errors**, **0 sorry/admit/native_decide** (only a `push_neg` deprecation warning).
* **FULL `lake build`** (lib root wired) → "**Build completed successfully (8643 jobs)**", **0 `error:`**
  in the log.
* `#print axioms` (scratch importer, fresh oleans) → **clean-3 `[propext, Classical.choice, Quot.sound]`**
  on: `pos_at_of_pos_below_of_ne`, `reach_strictConvex_of_below`, `reachStrictConvex_dichotomy_at`,
  `stuck_cut_of_dichotomy`, `deficientReachStep_of_structural`, `spherical_arm_mono_strict_of_structural`.
  No `sorryAx`, no `ofReduceBool`/`native_decide`.
* `grep -nE 'sorry|admit|native_decide|^axiom '` over the new file → **0 in code** (only module-doc prose).

## Honest verdict

Obstacle (a) — the REACH-branch strict-convex persistence up to `δ*` — is **genuinely discharged**: the
missing strict-up-to-boundary persistence (`pos_at_of_pos_below_of_ne`) and the mutually-exclusive
REACH/STUCK dichotomy (`reachStrictConvex_dichotomy_at`) are clean-3 theorems, and
`reach_strictConvex_of_below` *derives* the `hmix`/`hhem` that `reach_strictConvex_at_sup` previously
took as free hypotheses.  Obstacle (b) — the `B`-companion matched cut — does **not** yield to the
relabel+companion plan: the stuck-vertex cut of `A` is collinear-cornered while `B` is not, so
`diag_len_eq` cannot match the diagonals; this is the substrate's terminal-visibility obstruction,
proved false-in-general.  Together with the arbitrary-joint endpoint-transport gap (b1), the residue is
the single structural atom `DeficientReachStructural`, with (a) discharged beneath it.
`spherical_arm_mono(_strict)` therefore remain conditional on `DeficientReachStructural` (≡
`DeficientReachStep`); they are **NOT** unconditional this round.  The chapter's arm lemma is not closed;
its analytic obstacle is closed, and the residue is now purely structural with concrete failing chains.
