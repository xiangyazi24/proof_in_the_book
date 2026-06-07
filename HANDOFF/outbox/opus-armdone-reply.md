# opus-armdone-reply — Chapter 13 spherical arm lemma: the reach/stuck dichotomy assembly

## Status (honest)

**The dichotomy is wired; the congruent branch is fully UNCONDITIONAL; the residue is collapsed to ONE
named, non-vacuous `Prop` — but `spherical_arm_mono/_strict` is NOT yet unconditional.**

The directive's literal target — discharge `MatchedFirstJointStep` to get the unconditional arm lemma —
is **not achievable as stated**, and the substrate's own prior round already flagged why
(`opus-conemembership-reply.md` §"matched joint can only be carried, never derived"):
`MatchedFirstJointStep` quantifies over *every* convex pair `A, B` with `≤`-nondecreasing joints and
asserts `jointAngle A 0 = jointAngle B 0`. That equality is **false for a generic pair** (the strict
case is exactly when some joint is wider). The matched joint is not a property of the *given* `A, B`; it
is *achieved* by the §8.4 reach-opening, which transforms `A` into a new arm with one more matched joint.
So the genuine target is the dichotomy at the level where it is sound (`SZInductiveStep` /
`MatchedCutStep`), which is what this round builds.

New file: `ProofsInTheBook/SphericalArmDone.lean` (owned solely by this round). One substrate edit:
`ProofsInTheBook.lean` lib root, `import ProofsInTheBook.SphericalArmDone` after
`SphericalConeMembership`. Branch main, no commits. No edit to any other substrate file (the
`SphericalArmUncond/MatchedCut/CornerStep/ConeMembership` chain is consumed cleanly, not modified).

## What this round GENUINELY closes (UNCONDITIONAL, clean-3) — the congruent branch + the dichotomy

* **`congruent_matchedFirstJointFacts`** — *the matched joint, ACHIEVED in the congruent case*. When `A`
  and `B` agree on *all* joints (and sides), `MatchedFirstJointFacts n A B` holds **unconditionally**:
  joint 0 is matched (a special case of all-matched), the corner short-arcs come from convex position
  (`corner_shortArcs`, via `frontCut`'s edge 0), the corner-triangle sides match — including the diagonal
  `A2A0 = B2B0` by spherical SAS (`diag_len_eq` on the corner triangle `(A0,A1,A2)`) — and the strictness
  link is vacuous. This is exactly the configuration `MatchedFirstJointStep` asks for, *present*, not
  assumed. **Clean-3 axioms.**

* **`congruent_matchedCutData`** — the congruent `MatchedFirstJointFacts` upgrade, through the proved
  cone membership (`cornerConeFacts_of_matchedFirstJoint`), the corner-angle discharge
  (`cornerFacts_of_cone`), and the `frontCut` assembly (`matchedCutData_of_corner`), to a full
  `MatchedCutData A B` — **no residue consumed**. The cut closes the step through the proved
  `step_of_matchedCutData` + `cut_endpt_transport`. **Clean-3 axioms.**

* **`joint_dichotomy`** — the per-step split: nondecreasing joints are either all equal (congruent) or
  some joint is strictly wider (deficient). Total (`joint_dichotomy_total`).

* **`matchedCutStep_of_deficientReachOpen : DeficientReachOpen → MatchedCutStep`** — the FINAL WIRING:
  each level's matched-cut data is produced by the dichotomy — congruent ⟹ `congruent_matchedCutData`
  (unconditional), deficient ⟹ the residue. The matched joint is ACHIEVED (congruent base / deficient
  reach-opening), never carried as a false equality.

* **`inductiveStep_of_deficientReachOpen`**, **`schoenbergZaremba_of_deficientReachOpen`**,
  **`spherical_arm_mono_of_deficientReachOpen`**, **`spherical_arm_mono_strict_of_deficientReachOpen`** —
  the unconditional kernel arm lemmas, conditional now ONLY on the single residue `DeficientReachOpen`.
  All **clean-3 axioms**.

## The single remaining residue (named, non-vacuous, concrete failing chain)

**`DeficientReachOpen`**: for every level-`(n+1)` convex pair with equal sides, nondecreasing joints,
`SZComparison n`, *and some joint strictly wider*, the §8.4 reach-opening produces `MatchedCutData A B`.

It is strictly narrower than the prior tower's residues: it is restricted to the **deficient case**
(the congruent case is now discharged unconditionally by Block A — genuine new content), and carries
none of the `qstar` / `span≥0` betweenness / Gram-sign payload of `StuckWitnessExists` /
`OpenedArmReachOrStuck`.

**Concrete failing chain (verified against the substrate, file:line):**

1. To produce `MatchedCutData A B` in the deficient case one must *achieve* a matched joint by opening
   `A`'s first deficient joint to the admissible supremum `δ*` (`augmented_reachOrStuck_at_sup`,
   `SphericalAdmissibleSup.lean:303`, PROVED), then take the interior cut at the matched joint.

2. The REACH branch needs the opened arm `openArm A δ*` to be a `StrictConvexSphArm`
   (`reach_strictConvex_at_sup`, `SphericalAdmissibleSup.lean:346`). That lemma's hypotheses `hmix`/`hhem`
   demand **strict** positivity of every mixed support *and* the hemisphere functional **at `δ*`** — but
   the admissible-supremum dichotomy only guarantees **nonnegativity** there, and the
   `open_hemisphere` functional at the rotated tail is **not monitored** by the admissible set, so it can
   degenerate strictly at `δ*` (`SphericalArmClose.lean:316-324`: "No persistence lemma exists";
   `SphericalSZStep.lean:68`). This is the irreducible boundary-persistence-at-`δ*` analytic obstacle the
   substrate named `BoundaryConvexPersist` — true only as an interval hypothesis on all of `[0,δ*]`, not
   derivable at the boundary.

3. The STUCK branch (`stuckSupport_gives_cut`, PROVED) yields *one* sub-arm sharing `A 0` but **no
   `B`-side companion**, no side/joint match to `B`, and no endpoint preservation (the last-vertex-drop
   `cutArm` has `endpt = sDist (A 0)(A n)`, not `sDist (A 0)(A last)`;
   `SphericalArmUncond.lean:342-352`). Building the matched two-piece cut with the `B`-companion at the
   corresponding diagonal (SAS-matched length) plus the reach recursion on `unmatchedCount`
   (`unmatchedCount_lt_of_match`, PROVED) is the multi-vertex §8.4 construction.

This is the same irreducible §8.4 opening-witness construction four prior expert rounds isolated as
`StuckWitnessExists` ≡ `OpenedArmReachOrStuck` ≡ `MatchedCutStep` ≡ `OpeningStructuralAssembly`
(`SphericalOpeningProcess.lean:437-443`). The directive's premise that "every analytic/geometric piece
is proved, this is just the final wiring" is accurate for the *lemmas* (cone membership, SSS, the
dichotomy *existence*, the reach endpoint bound, the cut), and the wiring (`inductiveStep_of_*`,
`matchedCutData_of_corner`, `cornerConeFacts_of_matchedFirstJoint`) was indeed already in the substrate;
what remains is the **combinatorial assembly into a terminating recursion that produces the matched
`B`-companion cut**, on top of the unmonitored-hemisphere boundary obstacle in the REACH branch — both
genuine, neither dischargeable from the listed pieces.

The genuine *new* unconditional content this round banks is the **congruent branch** of the dichotomy
(`congruent_matchedCutData`, fully axiom-clean) and the **dichotomy collapse** of the residue from the
whole tower onto the single deficient-case `DeficientReachOpen`.

## Non-vacuity guards (playbook §3.3)

`congruent_matchedFirstJointFacts_refl` (realised at `A = B`), `congruent_matchedCutData_refl`
(`MatchedCutData A A` realised), `deficientReachOpen_conclusion_satisfiable` (the residue's conclusion is
realised by genuine endpoint-preserving matched cut sub-arms via `matchedCutData_satisfiable`),
`joint_dichotomy_total` (the split is exhaustive).

## Verification

* `rsync` + `ssh uisai1 ... lake env lean ProofsInTheBook/SphericalArmDone.lean` → **RC=0**, zero errors
  (only deprecation/linter warnings on `Fin.coe_*`).
* **FULL `lake build`** (lib root wired) → "**Build completed successfully (8639 jobs)**", RC=0,
  **0 `error:`** in the log.
* `#print axioms` (scratch importer) → **clean-3 `[propext, Classical.choice, Quot.sound]`** on:
  `congruent_matchedFirstJointFacts`, `congruent_matchedCutData`, `matchedCutStep_of_deficientReachOpen`,
  `schoenbergZaremba_of_deficientReachOpen`, `spherical_arm_mono_of_deficientReachOpen`,
  `spherical_arm_mono_strict_of_deficientReachOpen`. No `sorryAx`, no `ofReduceBool`/`native_decide`.
* `grep -nE 'sorry|admit|axiom|native_decide'` over the new file → **0 in code** (only module-doc prose).

## Honest verdict

The reach/stuck dichotomy is assembled onto `SZInductiveStep`/`MatchedCutStep`, the **congruent base is
discharged unconditionally** (the matched joint genuinely ACHIEVED, axiom-clean — real new substrate),
and the chapter's arm-lemma residue is collapsed from the five-layer conditional tower onto the **single,
strictly-narrower, non-vacuous `DeficientReachOpen`**: the deficient-case production of the matched cut.
Its irreducible content is (a) the unmonitored-hemisphere boundary persistence at `δ*` in the REACH
branch and (b) the matched `B`-companion two-piece cut + reach recursion — the same §8.4 opening-witness
construction prior rounds isolated. `spherical_arm_mono/_strict` therefore remains conditional on
`DeficientReachOpen` (equivalently `OpeningStructuralAssembly`); it is **not** unconditional this round.
