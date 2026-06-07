# opus-armfinish-reply — Chapter 13 spherical arm lemma: the terminating well-founded reach recursion

## Status (honest)

**The terminating well-founded recursion is BUILT and fully wired; the arm lemma is now conditional on
ONE strictly-narrower, non-vacuous per-step atom `DeficientReachStep`. It is NOT unconditional — two
genuine mathematical gaps remain (the same two four prior expert rounds + the immediately-prior
`SphericalArmDone` round isolated), now pinned to a single per-step Prop with concrete failing chains.**

The directive's premise — "EVERY piece exists ... this is just the lex-measure recursion assembly" — is,
after exhaustive source verification, **not accurate**. The recursion ASSEMBLY is what was genuinely
missing and is now banked; but two of its required inputs are not proved anywhere in the substrate (they
are *taken as hypotheses* by `reach_strictConvex_at_sup`, or *not produced* by `stuckSupport_gives_cut`).

New file: `ProofsInTheBook/SphericalArmFinish.lean` (owned solely by this round). One substrate edit:
`ProofsInTheBook.lean` lib root, `import ProofsInTheBook.SphericalArmFinish` after `SphericalArmDone`.
Branch main, no commits. No edit to any other substrate file.

## What this round GENUINELY BANKS (UNCONDITIONAL, clean-3) — the recursion the substrate never assembled

The substrate banked every *component* of the §8.4 step (the dichotomy `augmented_reachOrStuck_at_sup`,
the measure `unmatchedCount_lt_of_match`, the reach endpoint bound `reach_endpoint_at_sup`, the matched
cut `frontCut`/`matchedCutData_of_corner`, the cut transport `step_of_matchedCutData`/
`bothSided_cut_transport`, the congruent base `congruent_matchedCutData`) — but **never assembled the
terminating well-founded recursion** that chains them. This round builds exactly that:

* **`defStep_endpt`** — **THE TERMINATING WELL-FOUNDED RECURSION**, by `Nat.strong_induction_on` on the
  measure `unmatchedCount A B` at fixed level `n+1`. Per level the joint dichotomy
  (`SphericalArmDone.joint_dichotomy`) splits: **congruent** (`unmatchedCount = 0` is the base) ⟹
  `congruent_matchedCutData` ⟹ endpoint pair; **deficient** ⟹ the atom gives REACH (recurse at the
  strictly smaller `unmatchedCount Asharp B`, transport across `endpt A ≤ endpt Asharp`) or CUT
  (`MatchedCutData A B` ⟹ endpoint pair). Termination: the measure strictly decreases at fixed `n` in
  REACH; the base `unmatchedCount = 0` is congruent (`congruent_of_unmatchedCount_zero`, proved). This is
  real new content — the lex recursion driver is nowhere in the substrate.

* **`inductiveStep_of_deficientReachStep : DeficientReachStep → SZInductiveStep`** — the recursion
  discharges each inductive step (instantiated at `m = unmatchedCount A B`).

* **`schoenbergZaremba_of_deficientReachStep`, `spherical_arm_mono_of_deficientReachStep`,
  `spherical_arm_mono_strict_of_deficientReachStep`** — the kernel arm lemmas, conditional now ONLY on
  the single per-step atom `DeficientReachStep`. All **clean-3 axioms**.

* **A genuine finding (`Block E`):** `DeficientReachStep` does **NOT** discharge `DeficientReachOpen`
  (the immediately-prior round's residue). The reach branch produces only an endpoint **inequality**
  `endpt A ≤ endpt Asharp`, never the endpoint **equality** that `MatchedCutData A B` demands (the matched
  joint is not yet achieved in the reach branch). So the recursion CANNOT factor through
  `MatchedCutData A B` in the reach branch — it must target the endpoint *pair* directly. This corrects
  the recursion target and makes `DeficientReachStep` strictly weaker than `DeficientReachOpen`.

## The single remaining residue (named, non-vacuous, concrete failing chains)

**`DeficientReachStep`**: for every level-`(n+1)` convex pair with equal sides, nondecreasing joints,
`SZComparison n`, *and some joint strictly wider*, the §8.4 reach-opening produces *either* a reach-step
datum `ReachStepDatum A B` (a strictly convex `Asharp` matched against `B`, with
`unmatchedCount Asharp B < unmatchedCount A B`, `endpt A ≤ endpt Asharp`, the wider-joint witness
preserved) *or* the matched cut `MatchedCutData A B`. It carries none of the `qstar` / `span≥0`
betweenness / Gram-sign payload of `StuckWitnessExists`; it is the leanest endpoint-only form of the
opening output.

Its two branches are exactly the two facts that genuinely resist (verified by `grep` against the entire
substrate, file:line):

1. **REACH branch — strict positivity of the opened supports at `δ*` is unavailable.**
   `SphericalAdmissibleSup.reach_strictConvex_at_sup` (`:346`) *takes* `hmix` (every opened mixed support
   `> 0`) and `hhem` (hemisphere margin `> 0` at every opened vertex) as **hypotheses**. The augmented
   dichotomy `augmented_reachOrStuck_at_sup` (`:303`) delivers only a *disjunction*; by the definition of
   the admissible supremum (`SphericalRotation.reach_or_stuck`, `:384`) *some* constraint is tight at
   `δ*`, and the REACH disjunct (target slack tight, `δ* < Tcap`) does **not** exclude a mixed support /
   hemisphere margin being tight at the *same* `δ*` (reach and stuck are not mutually exclusive there).
   No "strict-up-to-`δ*`" persistence exists: `mixedSupport_persists` (`SphericalHingeCut.lean:213`) and
   `openArm_strictConvex_nhds` (`SphericalArmClose.lean:246`) propagate strictness only *from* an
   already-strict point *to* a neighbourhood, never *to* the boundary supremum. So the reach-step arm
   `Asharp : StrictConvexSphArm` cannot be produced. (This is the unmonitored-hemisphere /
   boundary-persistence-at-`δ*` analytic obstacle; `SphericalArmClose.boundaryConvexPersist` is true only
   in *interval* form — it assumes strictness on all of `[0, δ]`.)

2. **STUCK branch — the matched `B`-companion two-piece cut is unavailable.**
   `SphericalTerminalVis.stuckSupport_gives_cut` (`:286`) yields *one* sub-arm sharing `A 0`, with **no**
   `B`-companion, **no** side/joint match to `B`, and **no** endpoint preservation (the vanishing support
   sits at an arbitrary non-incident pair, not aligned with `frontCut`'s vertex-`1` drop; the last-vertex
   `cutArm` has `endpt = sDist (A 0)(A n)`, not `sDist (A 0)(A last)`). The matched `frontCut` cut
   requires the **first joint matched** (`frontCut_matched_sides`, `cornerAngle_le_of_cone`) — exactly the
   wider joint in the deficient case, unavailable until a matched joint is *achieved*. Arm-level `openArm`
   opens only the *last* joint; the closed-polygon relabel `cyclicShiftPolygon_strictConvex` does not
   transport the *arm* endpoint/side/joint indexing.

Both branches are genuine mathematical content, not wiring. `DeficientReachStep` is strictly narrower than
`DeficientReachOpen` / `OpeningStructuralAssembly` / `StuckWitnessExists`.

## Non-vacuity guards (playbook §3.3)

`reachStepDatum_satisfiable` (the reach datum realised from genuine data), `deficientReachStep_cut_satisfiable`
(the CUT alternative realised at `A = A` via `congruent_matchedCutData_refl`), `defStep_base_congruent`
(`unmatchedCount = 0` ⟹ congruent), `defStep_endpt_conclusion_satisfiable` (the endpoint pair realised
reflexively). All in-file, clean-3.

## Verification

* `rsync` + `ssh uisai1 ... lake env lean ProofsInTheBook/SphericalArmFinish.lean` → **RC=0**, zero errors,
  zero warnings.
* **FULL `lake build`** (lib root wired) → "**Build completed successfully (8641 jobs)**", **0 `error:`**
  in the log.
* `#print axioms` (scratch importer) → **clean-3 `[propext, Classical.choice, Quot.sound]`** on:
  `spherical_arm_mono_strict_of_deficientReachStep`, `spherical_arm_mono_of_deficientReachStep`,
  `schoenbergZaremba_of_deficientReachStep`, `inductiveStep_of_deficientReachStep`, `defStep_endpt`.
  No `sorryAx`, no `ofReduceBool`/`native_decide`.
* `grep -nE 'sorry|admit|native_decide'` / `^axiom ` over the new file → **0 in code** (only module-doc prose).

## Honest verdict

The terminating well-founded recursion — the one genuinely missing assembly the whole tower was reduced
to — is **built, axiom-clean, full-build-clean**, and the chapter's arm-lemma residue is collapsed onto a
**single, strictly-narrower, non-vacuous per-step atom `DeficientReachStep`** (reach-step-or-cut in the
deficient case), with the corrected endpoint-pair recursion target (a finding: the reach branch yields an
endpoint *inequality*, so the recursion cannot factor through `MatchedCutData A B` / `DeficientReachOpen`).
`spherical_arm_mono/_strict` therefore remains conditional on `DeficientReachStep`; it is **NOT**
unconditional. The two irreducible inputs — (1) REACH-branch strict positivity at `δ*` (unmonitored-
hemisphere boundary persistence) and (2) the STUCK-branch matched `B`-companion cut + arbitrary-interior-
joint arm opening — are genuine mathematics, neither dischargeable from the listed pieces. The directive's
claim that both `reach_strictConvex_at_sup` supplies its own strictness and that `frontCut` gives a matched
cut on ANY arm is inaccurate: `reach_strictConvex_at_sup` *takes* strictness as a hypothesis the dichotomy
does not deliver, and `frontCut`'s matched-sides require the first joint matched, which the deficient case
lacks until the reach branch achieves it. The chapter's arm lemma is NOT closed this round; the residue is
the leanest it has ever been.
