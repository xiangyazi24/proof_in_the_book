# Ch13 — Corrected `-δ` (widening) monitored family: glue clauses (i)/(ii)

**File:** `ProofsInTheBook/ZinanFFCT37.lean` (594 lines, NEW, single writer)
**Status:** Compiles 0 errors, clean-3 (`[propext, Classical.choice, Quot.sound]`), no
`sorry`/`axiom`/`admit`/`native_decide`. Verified on uisai2 against the full-build oleans.
**Olean built:** `.lake/build/lib/lean/ProofsInTheBook/ZinanFFCT37.olean`.

## What closed (clauses (i) AND (ii) UNCONDITIONAL)

The documented substrate sign bug (`SphericalOpeningGlue`: the `+δ` family opens in the *closing*
direction) is fixed by the widening family `monitoredFamilyW := fun o θ => monitoredFamily … (-θ)`.

- **§1 widening family** — `openTailW`, `monitoredFamilyW`, `monitoredSupW`, `ReachW`, `StuckW`;
  `continuous_monitoredFamilyW` (`(continuous_monitoredFamily …).comp continuous_neg`),
  `monitoredFamilyW_zero` (`-0 = 0`, reuses the original init-admissibility verbatim),
  `monitoredSupW_mem` / `_mem_Icc`.
- **§2 trichotomyW** — `opening_boundary_trichotomyW`: `monitoredSupW = Tcap ∨ ReachW ∨ StuckW`.
  Pure transliteration of the banked proof on the family-generic `reach_or_stuck`.
- **§5 clause (i)** — `glueW_clause_i`: `endpt A ≤ endpt (openTailW A (openingAxis k) δ*)`.
  `openTailW K δ* = openTail K (-δ*)`, `δ* ≥ 0` (sup of a set containing 0), discharged by the banked
  `endpt_openTail_interior_mono_neg`. **Requires the base-angle cap** `δ* + sphAngle (A0)(AK)(A_last) ≤ π`
  — see residual below. **Clause (ii)** is fully unconditional.
- **§4 clause (ii)** — `glueW_clause_ii`: `¬ StuckW → ReachW`, UNCONDITIONAL. The genuine work.

## The §4 identity used (the crux, NO residual)

Two new exact identities, both proved from `joint_axis_support_neg` (banked) + Pythagoras:

1. **Exact oriented datum** `joint_orientedDatum_eq`:
   `⟪u, a × w⟫ = +‖u‖‖w‖ · sin γ` (the `+` orientation — *opposite* to FFCT20's
   `OpeningDirectionPositive`). From `joint_axis_support_neg` (`s > 0`) + `c²+s²=N²`, `c = N cos γ`.

2. **Mirrored angle addition** `openedNegJointAngle_eq_add` (via
   `sphAngle_axis_rotS2_neg_eq_add_of_oriented`, the `-θ` mirror of FFCT20 Brick 2):
   `openedInteriorJointAngle A k (-θ) = jointAngle A k + θ` on the branch `γ + θ ≤ π`.

3. **Branch-free support sinusoid** `support_openNeg_eq_sin` — the load-bearing fact:
   `sOrient (jointPrev)(A K)(rotS2 (A K)(-θ)(jointNext)) = ‖u‖‖w‖ · sin (γ + θ)`,
   for **every** `θ` (computed via `rot_cross` + `inner_rot_tangent` + `cross_cross`).

**Closing the CAP branch (the subtlety):** the joint's own signed support is monitored by the
non-incident pair `jointWitness k = ((k, k+2))` (`supportConstraint_jointWitness_neg`). Admissibility
forces this support `≥ 0`, hence by (3) `sin (γ+θ) ≥ 0`; with `θ∈[0,π]`, `γ<π` (`strict_jointAngle_lt_pi`)
this gives `γ+θ ≤ π` (the additive branch — the rotation cannot pass the antipodal peak while the
support stays `≥ 0`). On the branch (2) makes `opened = γ+θ`, and slack `≥ 0` pins `γ+θ ≤ jointAngle B k`,
so `θ ≤ jointAngle B k − γ` (`admissibleW_le_deficit`). Therefore
`monitoredSupW ≤ jointAngle B k − jointAngle A k < π` (`monitoredSupW_lt_pi`) — **the CAP `δ*=π` is
impossible**, so `¬StuckW ⟹ ReachW`. This needed NO hemisphere residual: the joint support alone
keeps `δ*` in-branch.

## Residual (ONE, named, satisfiable — clause (i)'s cap only)

- **`GlueWBaseCap`** : `monitoredSupW A B k h₀ π + sphAngle (A0)(A(openingAxis k))(A_last) ≤ π`.
  The endpoint-*base*-triangle great-semicircle cap that `endpt_openTail_interior_mono_neg` consumes.
  The joint support bounds `δ* ≤ π − jointAngle A k`, but the endpoint base angle `sphAngle (A0)(AK)(A_last)`
  is a *different* triple (NOT a monitored `supportConstraint` — its middle vertex would need an edge
  endpoint), so the base cap is not pinned by the present family. Geometrically true (the opened base
  support stays `≥ 0` at the admissible sup); exposed as the substrate's recorded
  *endpoint-range reconciliation*. Non-vacuous (`glueWBaseCap_nonvacuous`: at `δ*=0` it is `sphAngle ≤ π`).
  Clause (ii) does NOT depend on it.

## Bundle + next worker

- **`GlueWClauseIII`** : the `-δ*` STUCK boundary outcome (weak-convex + vanishing non-incident
  support) — the next worker's job, defined separately.
- **`InteriorOpeningGlueW`** : the 3-clause `-δ` mirror of `InteriorOpeningGlue`.
- **`interiorOpeningGlueW_of_clauseIII (hcap : GlueWBaseCap) (hIII : GlueWClauseIII) : InteriorOpeningGlueW`**
  — clauses (i),(ii) discharged; (i) modulo the named base cap, (ii) unconditionally; (iii) supplied.

Non-vacuity guards: `reachW_def_nonvacuous`, `support_openNeg_eq_sin_zero`, `glueWBaseCap_nonvacuous`,
`openTailW_zero`.

Not committed (per instructions).
