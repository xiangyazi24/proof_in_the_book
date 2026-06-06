# opus-matchedcut-reply — Chapter 13 spherical arm lemma: the interior-vertex matched cut

## Status (honest)

FAITHFUL PARTIAL. `spherical_arm_mono(_strict)` is **NOT** made fully unconditional this round, but the
load-bearing **interior-vertex matched-cut CONSTRUCTION** the directive asked for is genuinely built and
verified, and the residue is driven down from "matched two-piece cut existence (no construction at all)"
to **two precise residual geometric facts** isolated as ONE named, non-vacuous `Prop`.

The directive's premise ("the math is ALL proved — this is the interior-cut Fin-reindexing CONSTRUCTION
+ endpoint matching") holds for the *construction* part (now done) but NOT for the closing inequality:
on close inspection the cut's **corner joint-angle inequality** (HINGE Lemma 11.3, the cut-corner
tangent-angle additivity) is genuine spherical geometry the substrate does not contain — it proves only
the determinant SIGN pattern `cutCorner_tangent_decomp` (diagonal ray inside the tangent cone), not the
resulting angle inequality. Plus the matched-joint existence in the all-strict opening case. Those two
are isolated, per the directive's contingency clause.

New file: `ProofsInTheBook/SphericalMatchedCut.lean` (751 lines, owned solely by this round). Wired into
the lib root after `SphericalArmUncond`. No other substrate file edited. Branch main, no commits.

## What this round GENUINELY closes (UNCONDITIONAL, clean-3) — the interior cut

The any-support cut (`SphericalDiagCut.cutArm`, last-vertex drop) and its `B`-companion
(`SphericalSZComplete.cutArmB`) BOTH lose the parent endpoint (`endpt = sDist (A 0)(A n)`, not
`sDist (A 0)(A last)`). The prior round flagged "**no interior-vertex-drop construction anywhere** in the
substrate". This round builds it, fully:

* **`frontCut A`** — the first-interior-vertex drop (`A 0, A 2, A 3, …, A (n+1)`), the endpoint-
  preserving interior cut replacing edges `A0→A1→A2` by the diagonal chord `A0→A2`. (`Fin (n+1)`
  reindexing skipping vertex `1`; `gidx` skips parent-index `1`, which is exactly what makes the
  diagonal endpoints `A0,A2` with no retained vertex between them.)
* **`frontCut_strictConvexArm`** — the FOUR `StrictConvexSphPolygon` fields of the cut arm, transported
  across the reindexing. The single new diagonal edge `A0→A2` supports every retained vertex via the
  PROVED cyclic-triple positivity (`cyclicTriple_pos_of_diag_holds` / `subseqDiag_support_holds`, both
  unconditional via `planarConvexDiagPos_holds`); the closing edge is `A`'s own closing edge; the
  interior edges inherit from `A`. (Edge_short, edge_support, strict_nonincident, open_hemisphere — all
  four, no `sorry`.)
* **`frontCut_endpoint`** — endpoint preservation `endpt (frontCut A) = endpt A` (both `A 0` and
  `A (last)` survive the skip). This is exactly the property `cutArm` lacks.
* **`frontCut_matched_sides`** — the matched cut sides: side `0` is the diagonal, equal between `A`/`B`
  by the spherical SAS `diag_len_eq` (`frontCut_diag_side_eq`) GIVEN the first joint matched; sides
  `i ≥ 1` are inherited parent sides, equal by `hside`.
* **`frontCut_jointAngle_zero` / `_succ` / `_succ_le`** — the cut-arm joint angles: joint `0` is the new
  corner angle `sphAngle (A0)(A2)(A3)` at the diagonal endpoint (NOT a parent joint); joints `i ≥ 1` are
  the inherited parent joints `jointAngle A ⟨i+1⟩` (so their inequality follows from `hangle`). This
  pins down the corner as the *only* non-inherited joint.

These assemble into:

* **`matchedCutData_of_corner`** — from the two corner facts + the parent hypotheses, the `frontCut`
  sub-arms realise `MatchedCutData A B` (strict convexity + matched sides + nondecreasing joints +
  endpoint preservation + strictness link). The genuinely load-bearing assembly.
* **`matchedCutStep_of_corner : MatchedCutCornerStep → MatchedCutStep`**, and through the proved
  `SphericalArmUncond` collapse: **`schoenbergZaremba_of_corner`**, **`armUncond_mono_of_corner`**,
  **`armUncond_strict_of_corner`** — the unconditional kernel arm lemma, conditional now only on the
  single isolated `MatchedCutCornerStep`.

## The single remaining residue (named, non-vacuous, concrete failing chain)

**`MatchedCutCornerStep`** (def via `CornerFacts n hn A B`): for every level-`(n+1)` convex pair with
equal sides, nondecreasing joints, and `SZComparison n`, the `CornerFacts` hold — namely

1. **first joint matched**: `jointAngle A 0 = jointAngle B 0` — needed for the diagonal cut side to
   agree between `A` and `B` by spherical SAS (`frontCut_diag_side_eq`); and
2. **corner angle inequality**: `sphAngle (A0)(A2)(A3) ≤ sphAngle (B0)(B2)(B3)` — the cut-arm joint `0`
   is this NEW corner angle (`frontCut_jointAngle_zero`);

plus the strictness link.

Concrete failing chain (verified against the substrate, file:line):

1. `matchedCutData_of_corner` needs the cut arms' joint inequality `jointAngle (frontCut A) i ≤
   jointAngle (frontCut B) i` for ALL `i`. For `i ≥ 1` this is inherited from `hangle`
   (`frontCut_jointAngle_succ_le`, PROVED). For `i = 0` it is the corner angle comparison
   `sphAngle (A0)(A2)(A3) ≤ sphAngle (B0)(B2)(B3)`, which is **not** a parent joint and is **not**
   implied by `hangle`/`hside`: it depends on the diagonal direction.
2. The substrate has the corner determinant SIGN pattern `cutCorner_tangent_decomp`
   (`SphericalCyclicTriple.lean:170`, the diagonal ray strictly inside the tangent cone) but NOT the
   tangent-angle additivity `∠(q₋,q,q₊_old) = ∠(q₋,q,diag) + ∠(diag,q,q₊_old)` (HINGE Lemma 11.3) that
   converts the sign pattern into the angle inequality. `grep` for `sphAngle_add` / angle additivity at a
   vertex over `Spherical*.lean` → none. (The substrate's only angle-additivity is Mathlib's
   `angle_le_angle_add_angle` for the spherical *triangle inequality of distances*, `SphericalArm.lean:92`,
   which is sub-additive and the wrong direction for a clean corner `≤`.)
3. The first-joint-matched requirement is the **matched-joint existence**: cutting at vertex `1` needs
   joint `0` matched; in general the §8.4 reach recursion (`unmatchedCount`, `unmatchedCount_lt_of_match`,
   substrate) is what produces a matched interior joint to cut at, and in the all-strict opening case (no
   interior matched joint) there is no equal-angle cut at all — the irreducible §8.4 opening residue
   (`StuckWitnessExists` ≡ `OpeningData` ≡ `SZStepGeom`).

`MatchedCutCornerStep` is strictly narrower than `MatchedCutStep` (it carries only the two scalar facts
above + the strictness link, NOT the full matched-cut data, which is now CONSTRUCTED from it via the
interior cut). It is not a co-extensive re-wrapper: the genuine new content of this module is the entire
interior-cut machinery (reindexing + 4-field convexity + endpoint preservation + SAS side matching +
joint-angle reduction), reducing the cut residue from "the whole matched two-piece cut" to "the corner
angle comparison + matched-joint existence".

Non-vacuity guards (playbook §3.3): `cornerFacts_refl` (congruent base `A = B`),
`cornerFacts_angle_satisfiable`, `frontCut_endpoint_nonvacuous` (the interior cut genuinely preserves
the endpoint — the property `cutArm` lacks), `frontCut_strictConvex_nonvacuous`.

## Verification

* `rsync` + `ssh uisai1 ... lake env lean ProofsInTheBook/SphericalMatchedCut.lean` → **RC=0**.
* `lake build ProofsInTheBook.SphericalMatchedCut` → "Build completed successfully (8446 jobs)".
* **FULL `lake build`** (after wiring into lib root) → "Build completed successfully (**8632 jobs**)",
  RC=0, zero errors.
* `#print axioms` (scratch importer, removed after) → **clean-3 `[propext, Classical.choice,
  Quot.sound]`** on: `armUncond_strict_of_corner`, `armUncond_mono_of_corner`,
  `schoenbergZaremba_of_corner`, `matchedCutStep_of_corner`, `matchedCutData_of_corner`,
  `frontCut_strictConvexArm`, `frontCut_endpoint`, `frontCut_matched_sides`, `frontCut_jointAngle_zero`,
  `cornerFacts_refl`. No `sorryAx`, no `ofReduceBool`/`native_decide`.
* `grep -nE 'sorry|admit|^axiom|native_decide'` over the new file → only the module-doc prose; **0 in
  code**.

## Honest verdict

The prior round (`opus-armuncond-reply.md`) collapsed the whole SZ chain onto the single per-step
endpoint pair and named `MatchedCutStep` but built **no** matched cut. This round builds the genuine
endpoint-preserving **interior-vertex matched cut** end-to-end (the construction the directive specified
as "THE MISSING CONSTRUCTION"): the `Fin`-reindexing, the four convexity fields via the proved cyclic-
triple diagonal positivity, endpoint preservation, the SAS-matched cut side, and the joint-angle
reduction. With the cut fully constructed, `MatchedCutStep` is closed FROM the single isolated
`MatchedCutCornerStep`, whose payload is exactly the two scalar facts the interior cut cannot furnish
from convex position: the **cut-corner angle inequality** (HINGE Lemma 11.3 tangent-angle additivity)
and the **matched-joint existence** (§8.4 reach recursion / all-strict opening). That is the precise,
non-vacuous, single-`Prop` frontier for the next round — strictly narrower than the prior `MatchedCutStep`
residue, and the construction beneath it is now real substrate rather than a wiring stub.
