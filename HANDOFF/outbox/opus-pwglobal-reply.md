# opus-pwglobal — Chapter 36 GLOBAL ray-independence assembly

**Status: DONE.** New file `ProofsInTheBook/PolygonWallGlobal.lean` (582 lines, 0
sorry / 0 axiom / 0 admit / 0 native_decide). Verifies clean on uisai1.
`PolygonWall.lean` untouched. Branch `main`, no commits.

## What was built

Assembled the per-wall local-zero layer of `PolygonWall.lean`
(`rfcount_eventually_zero_of_wall`, `rpair_count_eventually_const_noWall`,
`rfcount_eventually_eq_of_noWall_noEvent`) into a **global** ray-independence
theorem, internalising the edge-parallel-wall obstruction the chapter flagged as the
Jordan analytic core. Walls are now **crossed**, not avoided — the previous
`ValidDirPathSeg` / `DirComparableSeg` (no-wall) hypothesis is gone.

Decomposition (each part verified incrementally):

1. **Raw count** `rcrossSum P r₁ r₂ x t = ∑ i, rfcount … i t` + congruence bridge
   `crossingNumber'_eq_rcrossSum` (= `CrossingNumber' P ρ x` whenever `ρ.r = dirAt r₁ r₂ t`).
2. **Per-parameter eventual parity constancy** `rcrossSum_parity_eventually_const`:
   at `t₀` with `dirAt t₀ ≠ 0`, off-boundary, under the generic-wall residual, the
   `Fin n` edges partition into walls `W` (each `rfcount ≡ 0` near `t₀`), non-wall
   `R`-events paired with their `cyclicNext` (parity-const), and non-wall `Rest`
   (count-const). `N = R.image cyclicNext`; the residual forces every event-edge's
   successor non-wall, closing the pairing.
3. **Global glue** over the preconnected `Icc 0 1` subtype (`IsLocallyConstant` +
   `apply_eq_of_preconnectedSpace`) ⟹ `rcrossSum_parity_endpoints`: parity at
   `dirAt 0 = r₁` equals parity at `dirAt 1 = r₂`.
4. **Endpoint bridge** ⟹ `crossingNumber'_wallGlobal` / `closedRegion'_wallGlobal`:
   ray-independence for any two `RayDirection`s whose connecting segment avoids the
   zero direction and meets only generic walls — **no no-wall hypothesis**.
5. **Discharge** `unconditionalRayIndepInput_of_genericChain : GenericChainInput P →
   UnconditionalRayIndepInput P` (the kept ray-choice oracle of `PolygonFinish`).
6. **Downstream wiring**: `triangleExteriorEven_of_genericChain` and
   `artGallery_strict_genericChain` — `PolygonSeparation.chapter36_headline_separation`'s
   ray-choice input `∀ Q:3-gon, UnconditionalRayIndepInput Q` is now *produced* from
   the generic-chain residual. The `⌊n/3⌋` art-gallery bound is unconditional in the
   ray-choice modulo only the isolated residual + the development's already-named
   planar inputs (`ResidualGeometryData`, `TriangleConvexLeaf`, `DiagonalAttachInput`).

## The single isolated residual (honest, non-vacuous)

After genuine exhaustion, one joint resists: the **event-at-wall coincidence** — a
non-wall vertex event (`ds1Of i t₀ = 0`) whose `cyclicNext` edge is itself a wall
(`dirDen (next i) t₀ = 0`), a measure-zero simultaneity of a vertex crossing and an
edge-parallel direction that `PolygonWall` does not pair. Isolated as ONE named Prop:

```
GenericWallSeg P r₁ r₂ x :=
  ∀ t₀ ∈ Icc 0 1, ∀ i, dirDen P r₁ r₂ i t₀ = 0 →
    ds0Of P r₁ r₂ x i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x i t₀ ≠ 0
```
("on `[0,1]`, no edge-parallel wall has a vertex on the ray line" — equivalently `x`
is never on the line of an edge whose direction is being swept parallel). It is
strictly **weaker/cleaner** than the prior no-wall residual: walls are permitted, only
required generic. The antipodal/zero-direction case is the second, separately named
`SegAvoidsZero`; both are bundled into `GenericChainInput` for the two-segment chain.

**Non-vacuity proven (not unsatisfiable, not trivially-true):**
- `genericWallSeg_of_validDirPathSeg` — a no-wall segment satisfies it vacuously;
- `genericChainAt_refl` — reflexive pair `(ρ,ρ)` via the constant intermediate;
- `genericChainAt_of_sameSide` — two *genuinely distinct* same-side directions admit
  the direct chain (inhabits the residual off the diagonal).
Crucially `GenericWallSeg` *permits* real walls (`dirDen i t₀ = 0` allowed when `x`
off that edge's line), so `closedRegion'_wallGlobal` genuinely transports across walls
— the wall-crossing content is not vacuous.

## Verification (uisai1, `lake env lean`, RC=0)

`#print axioms` — all **clean-3** `[propext, Classical.choice, Quot.sound]` (no
`sorryAx`, no `ofReduceBool`/`native_decide`):

- `rcrossSum_parity_eventually_const`  (the core assembly)
- `closedRegion'_wallGlobal`, `crossingNumber'_wallGlobal`  (wall-crossing ray-indep)
- `unconditionalRayIndepInput_of_genericChain`  (discharges the kept oracle)
- `closedRegion'_ray_indep_unconditional`
- `triangleExteriorEven_of_genericChain`  (the discharged PolygonSeparation hook)
- `artGallery_strict_genericChain`  (the discharged downstream artGallery_strict hook)
- `genericChainAt_refl`, `genericChainAt_of_sameSide`  (non-vacuity witnesses)

Dependency oleans (`lake build ProofsInTheBook.PolygonWall ProofsInTheBook.PolygonIccEngine`)
and the new module's olean (`lake build ProofsInTheBook.PolygonWallGlobal`) both
"Build completed successfully". Temp audit file removed. Never ran `lake build`/
`lake env lean` locally on the Mac.

## Faithfulness verdict (playbook Group C)

**FAITHFUL** wall-crossing core (`closedRegion'_wallGlobal`): the assembly is the
genuine local-constancy + no-jump-at-isolated-walls over compact `[0,1]` ⟹ global
constancy argument; hypotheses permit walls.
**CONDITIONAL-honest** end-to-end (`artGallery_strict_genericChain`): conditional on
the single, weaker, non-vacuous `GenericChainInput` residual (antipodal + event-at-wall
finite avoidance on the direction circle) plus the development's pre-existing planar
inputs. The wall obstruction itself — the chapter's flagged analytic core — is now
fully proved (no longer an input).
