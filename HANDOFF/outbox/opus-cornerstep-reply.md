# opus-cornerstep-reply — Chapter 13 spherical arm lemma: discharging the cut-corner residue

## Status (honest)

FAITHFUL PARTIAL — substantial. `MatchedCutCornerStep` is **not** made fully unconditional, but the
**cut-corner angle inequality (Fact 1)** — the first of the two scalar facts and the one the directive
specified as derivable via spherical cosine rule + tangent-angle additivity — is now **genuinely built
end-to-end** as real new substrate, and `MatchedCutCornerStep` is reduced to a single, strictly narrower,
named non-vacuous `Prop` whose residual payload is the one irreducible analytic primitive (tangent-cone
membership) plus the already-known §8.4 matched-joint existence.

On close inspection, `MatchedCutCornerStep` is **not unconditionally true as stated**: its first
conjunct demands `jointAngle A 0 = jointAngle B 0` for *every* convex pair with only `hangle : ≤`, but
joint 0 can be strictly narrower in `A` — this is exactly the irreducible §8.4 opening / matched-joint
residue (`SZStepGeom` ≡ `StuckWitnessExists`), which the substrate has repeatedly and correctly isolated
as "THE hard theorem". So Fact 2 cannot be discharged unconditionally; it can only be carried as a
hypothesis. What this round genuinely closes is the **angle-arithmetic** that converts
`cutCorner_tangent_decomp`'s determinant-sign data into the corner *angle inequality* — the piece the
prior round (`opus-matchedcut-reply.md`) flagged as "genuine spherical geometry the substrate does not
contain".

New file: `ProofsInTheBook/SphericalCornerStep.lean` (owned solely by this round). One substrate edit:
`ProofsInTheBook.lean` lib root, adding `import ProofsInTheBook.SphericalCornerStep` after
`SphericalMatchedCut`. Branch main, no commits.

## What this round GENUINELY closes (UNCONDITIONAL, clean-3) — the corner angle arithmetic

Real new substrate, none of which existed before (the prior round had only the determinant SIGN
pattern `cutCorner_tangent_decomp`, explicitly NOT the angle inequality):

* **`cos_sphAngle`** — the explicit cosine of the spherical angle,
  `cos (sphAngle u v w) = ⟪tangentTo v u, tangentTo v w⟫ / (sin(uv)·sin(vw))` at a short-arc vertex
  (the inversion of `inner_tangent_tangent`).
* **`sphAngle_eq_of_sides`** — **spherical SSS congruence**: two spherical triangles with all three
  sides equal have equal angle at the middle vertex. Proved by solving the cosine rule for `cos γ` and
  applying `arccos` (both angles in `[0,π]`). This is `diag_len_eq` (SAS) read backwards.
* **`sphAngle_additive_of_tangent_between`** — **unoriented tangent-angle additivity (HINGE Lemma 11.3,
  the additive identity)**: if the diagonal tangent ray `tangentTo v b ∈ span ℝ≥0 {tangentTo v a,
  tangentTo v c}`, then `sphAngle a v c = sphAngle a v b + sphAngle b v c`. Derived from Mathlib's
  `InnerProductGeometry.angle_eq_angle_add_angle_iff` (the nonnegative-cone-membership direction). This
  is the genuine additive identity behind the determinant sign pattern — the thing `grep` found
  *absent* from the substrate in the prior round.
* **`cornerTriangle_eq`** — the corner-triangle angle at `A 2` agrees between `A` and `B` (SSS, via the
  two matched parent sides + the matched diagonal `A0A2 = B0B2` from `diag_len_eq`).
* **`cornerAngle_le_of_cone`** — **the cut-corner angle inequality (Fact 1)**:
  `sphAngle (A0)(A2)(A3) ≤ sphAngle (B0)(B2)(B3)`, proved from the additive identity (corner angle =
  parent joint ⟨1⟩ MINUS the congruent corner-triangle angle) + SSS congruence + the parent joint
  inequality `jointAngle A ⟨1⟩ ≤ jointAngle B ⟨1⟩`. This is the directive's primary Fact 1, fully
  derived — given the two HINGE 11.3 tangent-cone memberships as hypotheses.

These assemble into the conditional discharge:

* **`cornerFacts_of_cone`** — `CornerConeFacts → CornerFacts` (the corner inequality via
  `cornerAngle_le_of_cone`, the matched first joint + strictness link carried through).
* **`matchedCutCornerStep_of_cone : MatchedCutCornerConeStep → MatchedCutCornerStep`**, and through the
  proved `SphericalMatchedCut` assembly: **`schoenbergZaremba_of_cone`**, **`armUncond_mono_of_cone`**,
  **`armUncond_strict_of_cone`** — the unconditional kernel arm lemma, conditional now only on the
  single isolated `MatchedCutCornerConeStep`.

## The single remaining residue (named, non-vacuous, concrete failing chain)

**`MatchedCutCornerConeStep`** (def via `CornerConeFacts n hn A B`): for every level-`(n+1)` convex
pair with equal sides, nondecreasing joints, and `SZComparison n`, the `CornerConeFacts` hold — its
payload is strictly:

1. **matched first joint** `jointAngle A 0 = jointAngle B 0` (the §8.4 matched-joint existence —
   produced in general by the reach recursion `unmatchedCount`; in the all-strict opening case no
   equal-angle cut exists, the irreducible §8.4 opening residue);
2. **the two HINGE 11.3 tangent-cone memberships** `tangentTo (A 2)(A 0) ∈ span ℝ≥0 {tangentTo (A 2)
   (A 1), tangentTo (A 2)(A 3)}` (and the `B`-side) — the genuine analytic fact converting
   `cutCorner_tangent_decomp`'s determinant signs to the nonnegative-cone membership;
   plus the corner-triangle short-arc nondegeneracy + matched sides + the strictness link.

Concrete failing chain (verified against the substrate, file:line):

1. `cornerFacts_of_cone` discharges the corner angle inequality from item (2) via
   `cornerAngle_le_of_cone` + the additivity + SSS built here. The first joint (item 1) and the
   strictness link are carried, NOT derived.
2. **Item 2 (tangent-cone membership)** is the bridge "determinant sign ⟹ `span ℝ≥0` membership in the
   2D tangent plane". The substrate has `cutCorner_tangent_decomp` (`SphericalCyclicTriple.lean:170`,
   the three strict cyclic `sOrient > 0` signs) but no lemma turning those signs into a nonnegative
   tangent-plane combination. That bridge is the gnomonic / oriented-angle development (a 2D
   `Orientation`-based "ray-between-iff-consistent-signs" cone lemma + the `det3 v · ·` ⟷
   tangent-plane `det` transfer): `grep` for any `det → span ℝ≥0` / `sameRay` / cone lemma over the
   spherical files and the project Mathlib (`Angle/Unoriented/Basic.lean`) → none of the needed shape.
   This is the same multi-hundred-line analytic core the prior rounds isolated (sibling of
   `oriented_ray_between` but for projected tangent directions rather than sphere points).
3. **Item 1 (matched first joint)** is the §8.4 reach recursion / all-strict opening residue:
   `MatchedCutCornerStep`'s first conjunct is *false* as an unconditional statement (joint 0 need not
   be matched under `hangle : ≤`), so it can only be carried as a hypothesis. This is the substrate's
   already-named irreducible `SZStepGeom` ≡ `StuckWitnessExists` ≡ `OpeningData`.

`MatchedCutCornerConeStep` is strictly narrower than `MatchedCutCornerStep`: it replaces the opaque
corner *angle inequality* (and the SAS-diagonal apparatus) with the explicit *cone membership* — the
angle arithmetic (additivity + SSS) that converts cone membership to the angle inequality is now
discharged in this module. It is not a co-extensive re-wrapper: the new content is the entire
spherical-angle arithmetic layer (`cos_sphAngle`, `sphAngle_eq_of_sides`,
`sphAngle_additive_of_tangent_between`, `cornerTriangle_eq`, `cornerAngle_le_of_cone`), reducing the
corner residue from "the corner angle inequality (HINGE 11.3, no infrastructure)" to "the tangent-cone
membership (HINGE 11.3 cone form) + matched-joint existence".

Non-vacuity guards (playbook §3.3): `cornerConeFacts_refl` (congruent base `A = B`, with the cone
membership a genuine hypothesis), `tangentCone_self_mem` (the cone membership is inhabited),
`sphAngle_eq_of_sides_refl`, `cornerAngle_le_refl`.

## Verification

* `rsync` + `ssh uisai1 ... lake env lean ProofsInTheBook/SphericalCornerStep.lean` → **RC=0**, zero
  warnings, zero errors.
* `lake build ProofsInTheBook.SphericalCornerStep` → "Build completed successfully (8447 jobs)".
* **FULL `lake build`** (after wiring into lib root) → "Build completed successfully (**8633 jobs**)",
  RC=0, **0 `error:`** in the log.
* `#print axioms` (scratch importer, removed after) → **clean-3 `[propext, Classical.choice,
  Quot.sound]`** on: `armUncond_strict_of_cone`, `armUncond_mono_of_cone`, `schoenbergZaremba_of_cone`,
  `matchedCutCornerStep_of_cone`, `cornerFacts_of_cone`, `cornerAngle_le_of_cone`,
  `sphAngle_additive_of_tangent_between`, `sphAngle_eq_of_sides`, `cos_sphAngle`, `cornerConeFacts_refl`.
  No `sorryAx`, no `ofReduceBool`/`native_decide`.
* `grep -nE 'sorry|admit|^axiom|native_decide'` over the new file → only module-doc prose; **0 in code**.

## Honest verdict

The directive framed the residue as "TWO concrete scalar facts". On grinding them out, only **Fact 1
(the cut-corner angle inequality)** is genuine, self-contained spherical geometry — and it is now fully
built: the unoriented tangent-angle additivity (HINGE 11.3 additive identity), the spherical SSS
congruence, and the corner-angle inequality are real, axiom-clean substrate. **Fact 2 (the matched
first joint)** is not a separable scalar fact but the irreducible §8.4 matched-joint / all-strict
opening residue (`MatchedCutCornerStep`'s first conjunct is unconditionally false), and the angle
inequality itself rests on the **tangent-cone membership** — the determinant-sign ⟹ nonnegative-cone
bridge (gnomonic / oriented-angle, HINGE 11.3 cone form) that no substrate lemma supplies. Both are
isolated, endpoint-only, as the single named non-vacuous `MatchedCutCornerConeStep`, strictly narrower
than the prior `MatchedCutCornerStep`, with the corner angle-arithmetic now real substrate beneath it.
That is the precise frontier for the next round: the tangent-cone membership (HINGE 11.3 cone form) +
the §8.4 matched-joint existence.
