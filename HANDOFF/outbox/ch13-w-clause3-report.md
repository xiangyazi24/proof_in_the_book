# Ch13 — `-δ` widening glue: clause (iii) + outcome + headline swap (completes the sign-bug fix)

**File:** `ProofsInTheBook/ZinanFFCT38.lean` (507 lines, NEW, single writer)
**Status:** Compiles 0 errors, clean-3 (`[propext, Classical.choice, Quot.sound]` — NO `sorryAx`,
no `ofReduceBool`/`native_decide`), no `sorry`/`axiom`/`admit`. Verified on uisai2 via
`lake env lean ProofsInTheBook/ZinanFFCT38.lean` against the committed FFCT37/FFCT36 oleans.
**Not committed** (per instructions).

## What this delivers (clean-3)

- **`glueWClauseIII_of_residues`** — discharges FFCT37's `GlueWClauseIII` (exact shape) modulo the two
  named W-residuals.
- **`interiorOpeningGlueW_full : GlueWBaseCap → HemiMarginStrictPosAtSupW → OpenedEdgesDistinctW →
  InteriorOpeningGlueW`** — clauses (i)/(ii) from FFCT37 (i mod base cap, ii unconditional), (iii) here.
- **`interiorOpeningOutcomeW_of_glue` / `interiorOpeningOutcomeW_of_residues`** — produces the
  family-agnostic `SphericalArmAssembly.InteriorOpeningOutcome` from the W glue.
- **`mainPlus_headline_final`** — the chapter-13 spherical arm lemma
  `sDist (A 0)(A last) ≤ sDist (B 0)(B last)`, with `InteriorOpeningGlue` REPLACED by the `-δ` residual
  surface. **The new honest endpoint of Chapter 13.**

## The final Ch13 residue surface (the truth)

`mainPlus_headline_final` carries exactly FIVE named, satisfiable, non-vacuous hypotheses:

| Residue | Source | Status |
|---------|--------|--------|
| `SpliceBodyDiagMono` | `SphericalSpliceTransport` | named (pre-B1 splice geometry) |
| `SpliceStructuralData` | `SphericalArmAssembly` | named (pre-B1 cut sub-arm geometry) |
| `GlueWBaseCap` | `ZinanFFCT37` | named (endpoint base-angle cap, clause (i)) |
| `HemiMarginStrictPosAtSupW` | `ZinanFFCT38` | named (strict hemi margins at a `StuckW` sup, clause (iii)) |
| `OpenedEdgesDistinctW` | `ZinanFFCT38` | named (consecutive opened vertices distinct, clause (iii)) |

**GONE from the old (FFCT35) surface:**
- `InteriorOpeningGlue` (its clauses (i)/(ii) were sign-bug-FALSE for the `+δ` family) — now clauses
  (i)/(ii) are UNCONDITIONAL via the corrected `-δ` family (FFCT37 `glueW_clause_i` mod base cap,
  `glueW_clause_ii` outright). The `+δ` sign bug is FIXED.
- `EquatorSpreadExcluded` — DEAD (FFCT36's Hahn–Banach/Riesz separation discharged the equator residual
  outright; the W clause-(iii) hemi branch uses the equator-free `hemiStuck_dichotomy_tangentFree`).
- `GramSignsAtInteriorBinding` / `NearSideCoeffNonneg` / `HemiStuckVanishingSupport` — NOT consumed. The
  headline route uses clause (iii)'s `WeakConvexSphArm + ∃ vanishing support` form feeding the CUT step,
  NOT the betweenness dispatch (which is what consumed the Gram/NearSide signs in FFCT35). The hemi-stuck
  vanishing-support remnant is eliminated by the contradiction argument below.

## What mirrored cleanly (and how)

The `+`-family clause-(iii) machinery is almost entirely **arm-level** (statements about a generic
`openTail A K δ` at free `δ`, `K`), so it instantiated verbatim at the opening angle `-δ*_W`
(recall `openTailW A K δ*_W = openTail A K (-δ*_W)` is `rfl`):

- `weakConvex_of_supportStuck_of_hemiPos` (SphericalOpeningGlue) — support-stuck weak-convex payload.
- `vanishing_support_of_supportStuck` (SphericalOpeningGlue) — vanishing-support payload.
- `hemiStuck_dichotomy_tangentFree` (FFCT36) — the hemi branch; EQUATOR-FREE, so no equator residual.
- `reach_strictConvex_interior` (SphericalMonitoredSup) — REACH strict convexity.
- `deficitCount_openTail_reach_lt`, `jointAngle_openTail_eq_of_ne`, `openTail_preserves_sides`,
  `jointAngle_openTail_eq_openedInterior` — REACH-side bookkeeping; all δ-free.

The only `monitoredSup`-pinned ingredients (the closure `≥ 0` supports/margins) were re-derived for the
widening family in §1 (`supportConstraintW_nonneg_at_sup`, `hemiMarginW_nonneg_at_sup`, and their
`sOrient`/inner-product forms) directly from `monitoredSupW_mem` — since
`monitoredFamilyW o θ = monitoredFamily o (-θ)`, admissibility of `δ*_W` is exactly support/hemi `≥ 0`
at `-δ*_W`. No `+δ`-pinned closure lemma was reused (they would give the wrong angle).

**REACH equation direction (the prompt's flagged subtlety):** `ReachW` is
`openedInteriorJointAngle A k (-δ*_W) = jointAngle B k`, and
`jointAngle_openTail_eq_openedInterior A k (-δ*_W)` bridges it to
`jointAngle (openTail A K (-δ*_W)) k = jointAngle B k`, which `deficitCount_openTail_reach_lt` consumes
at `δ = -δ*_W`. No sign mismatch.

## No `+δ`-pinned blockers

`InteriorOpeningOutcome` is **family-agnostic** (it asks for an `∃ A'` with endpoint-mono + sides +
joints + (REACH ∨ STUCK)), so the W glue discharges it directly — no downstream consumer rewiring was
needed; `mainPlus_headline_final` plugs straight into the banked
`spherical_arm_mono_of_spliceBodyDiagMono`.

## Honesty note on the hemi-stuck weak-convex sub-case (faithful, not vacuous)

In `stuckOutcomeW_weakConvex_of_residues`, the hemi-stuck branch runs the equator-free dichotomy. Its
left disjunct (a vanishing support) routes to the support sub-branch. Its right disjunct
(`WeakConvexSphArm`) is reached only when ALL supports are strictly positive; but a hemi-stuck supremum
has a *vanishing* hemiMargin, which directly contradicts the named `HemiMarginStrictPosAtSupW` (strict
`> 0` at every vertex). So that sub-case is genuinely impossible (`exfalso` + `linarith`), NOT a vacuous
hypothesis — the named residual is used to refute it, faithfully.

## Non-vacuity guards (playbook §3.3)

`hemiMarginStrictPosAtSupW_conclusion_nonvacuous`, `openedEdgesDistinctW_nonvacuous`,
`mainPlus_headline_final_conclusion_satisfiable`, `stuckOutcomeW_conclusion_nonvacuous` — each confirms
the residual conclusion is real geometric content (realised at `δ*_W = 0` / reflexively at `A = B`),
not `True`.

## Wiring note for the integrator

To surface in the audit: add `import ProofsInTheBook.ZinanFFCT38` to `Audit.lean` and a
`#print axioms ProofsInTheBook.ZinanFFCT38.mainPlus_headline_final`. The four headline-chain theorems
already self-report clean-3 via the in-file `#print axioms`.
