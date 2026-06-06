# opus-conemembership-reply — Chapter 13 spherical arm lemma: discharging the tangent-cone membership

## Status (honest)

**THE TARGET IS DISCHARGED.** The HINGE 11.3 **tangent-cone membership** — the directive's specified
"FINAL residue", the conversion of `cutCorner_tangent_decomp`'s determinant signs into genuine
`span ℝ≥0` membership — is now **fully built and UNCONDITIONAL** (clean-3 axioms). The cut diagonal's
tangent ray provably lies in the nonnegative cone of the two adjacent edge tangent rays at the cut apex
`A 2`.

This removes the cone membership from the residue entirely. The remaining residue after this round is
**strictly the §8.4 matched-first-joint** (`jointAngle A 0 = jointAngle B 0` + matched corner-triangle
sides), which the prior round (`opus-cornerstep-reply.md`) and the substrate correctly and repeatedly
isolated as the irreducible §8.4 opening / all-strict residue — and which `MatchedCutCornerStep`'s first
conjunct shows is **unconditionally false** under `hangle : ≤` alone, so it can only be carried, never
derived, here. I isolate it as the new strictly-narrower `Prop` `MatchedFirstJointStep`.

New file: `ProofsInTheBook/SphericalConeMembership.lean` (473 lines, owned solely by this round). One
substrate edit: `ProofsInTheBook.lean` lib root, `import ProofsInTheBook.SphericalConeMembership` after
`SphericalCornerStep`. Branch main, no commits. `SphericalCornerStep.lean` / `SphericalMatchedCut.lean`
were **not** modified — the new file consumes their exported `MatchedCutCornerConeStep` /
`CornerConeFacts` / `frontCut` cleanly.

## What this round GENUINELY closes (UNCONDITIONAL, clean-3) — the tangent-cone membership

Real new substrate, the gnomonic/planar-cone bridge the prior round flagged as entirely absent:

* **`mem_span_nnreal_of_planar_signs`** — *the planar nonneg-cone-from-signs lemma* (directive deliverable
  (1)). For `u, v, w` all orthogonal to a common `m ≠ 0` (coplanar in the 2-plane `m^⊥`) with `v,w`
  independent (`det3 m v w ≠ 0`), if `0 ≤ det3 m u w · det3 m v w` and `0 ≤ det3 m v u · det3 m v w`,
  then `u ∈ span ℝ≥0 {v, w}`. This is `betweenness_span_nnreal`'s convex-position algebra
  (`normsq_smul_b` + the Gram-coordinate sign extraction) transported from the sphere to the tangent
  plane: a ray whose planar orientation against both bounding edges is sign-consistent is a nonnegative
  combination. Supporting: `cross_parallel_of_perp` (`v×w = (det3 m v w / ‖m‖²)•m` for `v,w ⟂ m`),
  `inner_cross_perp` (the `⟪v×w, u⟫ = 0` coplanarity input).

* **`det3_tangentTo_eq`** — *the gnomonic transport tangent ↔ planar orientation* (directive deliverable
  (2)). `det3 m (p) (q) = det3 m (tangentTo m p) (tangentTo m q)`: each neighbour's component along the
  apex `m` is a repeated first column, so the spherical orientation `sOrient m (A i)(A j)` is exactly the
  planar orientation of the two tangent directions in `m^⊥`. Proved from `decompose_unit_along_tangent`
  + `det3` multilinearity (`det3_add_mid/_right`, `det3_smul_mid/_right`) and the three vanishing
  repeated-`m`-column determinants.

* **`cutCorner_cone_membership`** — *the residue, discharged* (directive deliverable (3)). For a strictly
  convex spherical polygon `P : Fin N → S2` with the apex window `0<1<2<3`, the diagonal tangent ray
  `tangentTo (P 2)(P 0) ∈ span ℝ≥0 {tangentTo (P 2)(P 1), tangentTo (P 2)(P 3)}`. The proof: the three
  increasing-order triples `det3(P0)(P1)(P2)`, `det3(P0)(P2)(P3)`, `det3(P1)(P2)(P3)` are positive by
  `cyclicTriplePos_unconditional` (the now-unconditional HINGE 2.3); transporting the three apex-`2`
  orientations to the tangent plane (`det3_tangentTo_eq`) and reordering by `det3` antisymmetry, all
  three apex-`2` orientations `det3(P2)(P0)(P3)`, `det3(P2)(P1)(P3)`, `det3(P2)(P1)(P0)` are **negative**
  (each is an odd permutation of a positive increasing triple), so the two required sign **products are
  positive** — feeding `mem_span_nnreal_of_planar_signs`.

* **`armCutCorner_cone_membership`** — the same in the level-`(n+1)` arm indexing (`A : Fin (n+1+1) → S2`,
  `n ≥ 2`, closure `hA.closed_convex`, apex `A ⟨2⟩`), matching the `(⟨2,_⟩, ⟨3,_⟩)` shape `CornerConeFacts`
  consumes. Supporting Fin arithmetic: `two_val`, `three_val`, `cut_indices_lt`, `fin_two_eq`,
  `fin_three_eq`.

## The reduction to the strictly-narrower residue

With the cone membership now PROVED substrate, `CornerConeFacts`' two cone-membership conjuncts are
supplied unconditionally, leaving only the §8.4 matched-joint data:

* **`MatchedFirstJointFacts` / `MatchedFirstJointStep`** — `CornerConeFacts` / `MatchedCutCornerConeStep`
  with the two cone memberships **removed** (now discharged). Payload: the matched first joint, the
  matched corner-triangle sides, the short-arc nondegeneracy, and the strictness link.
* **`cornerConeFacts_of_matchedFirstJoint`** — supplies the two cone memberships via
  `armCutCorner_cone_membership` for `A` and `B`, upgrading `MatchedFirstJointFacts → CornerConeFacts`.
* **`matchedCutCornerConeStep_of_matchedFirstJoint : MatchedFirstJointStep → MatchedCutCornerConeStep`**,
  and through the proved `SphericalCornerStep` assembly: **`schoenbergZaremba_of_matchedFirstJoint`**,
  **`armUncond_mono_of_matchedFirstJoint`**, **`armUncond_strict_of_matchedFirstJoint`** — the
  unconditional kernel arm lemma, conditional now ONLY on `MatchedFirstJointStep` (the §8.4 matched-joint
  existence), with the entire tangent-cone analytic core discharged beneath.

## The single remaining residue (named, non-vacuous, concrete failing chain)

**`MatchedFirstJointStep`** (via `MatchedFirstJointFacts`): for every level-`(n+1)` convex pair with equal
sides, nondecreasing joints, and `SZComparison n`, the matched first joint
`jointAngle A 0 = jointAngle B 0` holds (plus the matched corner-triangle sides, short-arc
nondegeneracy, strictness link — all carried).

Concrete failing chain (verified against the substrate, file:line):

1. The **cone membership** (prior frontier item 2) is now `armCutCorner_cone_membership`
   (`SphericalConeMembership.lean`), proved unconditionally from `cyclicTriplePos_unconditional`
   (`PlanarConvexDiag.lean:195`) + the planar cone lemma. **No longer a residue.**
2. The **matched first joint** (prior frontier item 1) is the §8.4 reach recursion / all-strict opening
   residue. `MatchedCutCornerStep`'s first conjunct (`SphericalMatchedCut.lean:638`) is *false* as an
   unconditional statement (joint 0 need not be matched under `hangle : ≤`), so it can only be carried as
   a hypothesis — exactly the substrate's already-named irreducible `SZStepGeom` ≡ `StuckWitnessExists`
   ≡ `OpeningData` ≡ `MatchedCutStep` (the §8.4 matched-cut existence). The matched corner-triangle
   sides ride along with it (the diagonal `A1A0 = B1B0` is the SAS companion of the matched joint).

`MatchedFirstJointStep` is strictly narrower than the prior `MatchedCutCornerConeStep`: it drops the two
tangent-cone memberships entirely (discharged here). The angle arithmetic (additivity + SSS, prior round)
and now the tangent-cone membership (this round) are both real substrate beneath it; the residue is the
pure §8.4 matched-joint existence with no analytic-geometry payload.

Non-vacuity guards (playbook §3.3): `planar_cone_self_mem` (the cone contains its generators),
`det3_tangentTo_self` (the gnomonic transport carries content), `cutCorner_cone_membership_nonvacuous`
(the discharged membership is realised on every convex arm with a degree-`≥4` apex window),
`matchedFirstJointFacts_refl` (the residue is realised at the congruent `A = B`).

## Verification

* `rsync` + `ssh uisai1 ... lake env lean ProofsInTheBook/SphericalConeMembership.lean` → **RC=0**, zero
  warnings, zero errors.
* **FULL `lake build`** (after wiring into lib root) → "**Build completed successfully (8636 jobs)**",
  RC=0, **0 `error:`** in the log.
* `#print axioms` (scratch importer) → **clean-3 `[propext, Classical.choice, Quot.sound]`** on all of:
  `cutCorner_cone_membership`, `armCutCorner_cone_membership`, `mem_span_nnreal_of_planar_signs`,
  `det3_tangentTo_eq`, `matchedCutCornerConeStep_of_matchedFirstJoint`,
  `schoenbergZaremba_of_matchedFirstJoint`, `armUncond_mono_of_matchedFirstJoint`,
  `armUncond_strict_of_matchedFirstJoint`. No `sorryAx`, no `ofReduceBool`/`native_decide`.
* `grep -nE 'sorry|admit|axiom|native_decide'` over the new file → **0 in code** (only module-doc prose).

## Honest verdict

The directive's target — "discharge `MatchedCutCornerConeStep` = the tangent-cone membership ... convert
`cutCorner_tangent_decomp`'s DETERMINANT SIGNS into span ℝ≥0 membership (HINGE 11.3 cone form)" — is
**fully achieved, unconditionally and axiom-clean**. All three specified deliverables are built: (1) the
planar nonneg-cone-from-signs lemma, (2) the gnomonic transport tangent↔planar, (3) the cone membership
for the cut corner. The route was exactly the directive's: the apex tangents are coplanar in `m^⊥`
(`m = A 2`), so `det3` of any three vanishes for free and `normsq_smul_b` gives the explicit coplanar
decomposition; the Gram-coordinate signs are the planar det2 signs, which `det3_tangentTo_eq` identifies
with the `sOrient` data of `cutCorner_tangent_decomp` — and those, via `cyclicTriplePos_unconditional` +
`det3` antisymmetry, make both sign products positive.

What this does **not** make unconditional is `MatchedCutCornerConeStep` *as originally stated*, because it
bundled the cone membership with the matched-first-joint, and the latter is the genuine §8.4 opening
residue (unconditionally false under `hangle : ≤`). The honest outcome is therefore: the cone membership
is removed from the residue (no longer a hypothesis anywhere), and the frontier is now the single,
strictly-narrower, non-vacuous `MatchedFirstJointStep` — the §8.4 matched-joint existence, the same
irreducible opening primitive the substrate has consistently named. That is the precise frontier for the
next round, with no remaining analytic-geometry content beneath it.
