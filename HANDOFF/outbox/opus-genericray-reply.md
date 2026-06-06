# opus-genericray — Chapter 36 generic-position existence for wall-global ray independence

**Status: PARTIAL (unconditional on the generic stratum) + a rigorous correction of
the residual's nature.** New file `ProofsInTheBook/PolygonGenericRay.lean` (372 lines,
0 sorry / 0 axiom / 0 admit / 0 native_decide). Verifies clean on uisai1 (RC=0, olean
"Build completed successfully", `#print axioms` clean-3 on every result). Branch
`main`, no commits, no other file touched.

## Headline finding (corrects the task premise)

The residual `GenericChainInput P` of `PolygonWallGlobal` is **NOT a finite-avoidance
lemma** — it is **provably FALSE in general**, hence *not* dischargeable, and the
unconditional `artGallery_strict` **cannot** factor through it. The true remaining gap
is a genuine analytic one (degenerate-wall parity transport), not generic position.

What IS pure finite avoidance — and is now discharged unconditionally — is the
**generic stratum**: every off-boundary `x` lying off all edge lines.

## What was proved (all unconditional, clean-3)

### The reduction (genuine new math)
`genericWallSeg_of_offAllEdgeLines` : `GenericWallSeg P r₁ r₂ x` depends on the
directions only through `SegAvoidsZero`. Precisely, at a *wall* `t₀`
(`dirDen i t₀ = 0`) with `dirAt … t₀ ≠ 0`, both endpoint side values are nonzero iff
`x` is **off the line of edge `i`** (`det2 (edgeVec i) (P.q i − x) ≠ 0`). Proof: if
`ds0Of i t₀ = 0` too, the nonzero direction is `det2`-orthogonal to both `edgeVec i`
and `P.q i − x`, forcing them parallel (`eq_zero_of_det2_eq_zero`), i.e. `x` on the
line. So **whenever `x` is off every edge line, every wall is generic, for every
segment** — no genericity in the *direction* is needed.

### The unconditional discharge on the generic stratum (finite avoidance)
`genericChainAt_of_offAllEdgeLines` : for `x` off **all** edge lines, **any** pair
`ρ, σ` admits a generic connecting intermediate `μ = mkPt 1 s`, hence
`GenericChainAt P ρ σ x`. The intermediate is built by avoiding the finite bad slope
set (edge slopes ∪ the ≤ 2 antiparallel slopes of `ρ.r, σ.r`):
- avoiding edge slopes ⟹ `μ` is a genuine `RayDirection` (reuses
  `slope_eq_badSlope_of_det2_mkPt_one_eq_zero`);
- avoiding the antiparallel slopes ⟹ both segments `SegAvoidsZero`
  (`segAvoidsZero_to_mkPt`: the segment `dirAt a (mkPt 1 s)` hits `0` only if
  `a 0 < 0` and `s = a 1 / a 0`);
- `GenericWallSeg` is then automatic on both segments by the reduction.

This is exactly the finite bad-direction avoidance the task asked for; it succeeds
**without any residual** on the generic stratum.

### The obstruction on the on-edge-line stratum (why GenericChainInput is false)
- `genericWallSeg_fails_on_edge_line` : at a wall of edge `i` with `x` *on* edge `i`'s
  line, `ds0Of i t₀ = 0` — the wall is **degenerate**, so `GenericWallSeg` (which
  demands side values nonzero at every wall) is violated. (Holds with no nonzero-dir
  hypothesis — the degeneracy is purely the collinearity.)
- `segment_has_wall_of_straddle` : if `ρ.r, σ.r` lie on strictly opposite `det2`-sides
  of `edgeVec i`, the affine `dirDen i` changes sign on `[0,1]` (IVT,
  `intermediate_value_Icc`), so the connecting straight segment **has a wall** for
  edge `i`.
- `genericChainAt_false_of_straddle_on_line` : therefore, for `x` on edge `i`'s line
  with `ρ, σ` straddling it, **`¬ GenericChainAt P ρ σ x`** — whichever side the single
  intermediate `μ` falls (`det2 μ.r e_i ≠ 0`), one sub-segment straddles edge `i`,
  hits its wall, and that wall is degenerate (x on line), contradicting that segment's
  `GenericWallSeg`.

Consequently `GenericChainInput P` (∀ pair, ∀ off-boundary `x`) is **unsatisfiable**
for any polygon admitting an off-boundary `x` on an edge line plus a straddling pair —
which is generic (constructible already for a triangle). So
`PolygonWallGlobal.unconditionalRayIndepInput_of_genericChain` is a *vacuously safe but
unusable* implication, and I deliberately did **not** ship a co-extensive re-wrapper
conditional on the on-edge-line stratum (it would be conditional on a false
hypothesis — the playbook's VACUOUS-conditional anti-pattern).

## The true residue (numerically confirmed TRUE, analytically deep)

`UnconditionalRayIndepInput P` is itself a **true** theorem even for on-edge-line `x`
(verified: dense direction scans give a single region parity for several on-edge-line
off-boundary `x` on a concrete triangle). The reason `GenericChainInput` misses it:
the *degenerate wall* is fine (the wall edge contributes 0,
`PolygonWall.rfcount_eventually_zero_of_degenerateWall`), and at the **event-at-wall
coincidence** (ray ∥ an edge AND through a vertex) the crossing parity is preserved —
but by a **double-event pairing of two *other* edges**, not the generic
`(i, cyclicNext i)` pairing that `PolygonWallGlobal.rcrossSum_parity_eventually_const`
uses. Concrete trace (triangle `A=(0,0),B=(4,0),C=(1,3)`, `x=(2,6)` on line `CA`, dir
sweeping through `‖CA`): per-edge counts flip `[0,0,0] → [1,1,0]` across the wall —
edges `e0,e1` flip *together* (parity stays even), the wall edge `e2` stays 0.

So the genuine remaining work for the fully unconditional headline is a **new global
parity-constancy assembly that handles the degenerate wall directly** (the
double-event pairing at a degenerate wall), replacing `PolygonWallGlobal`'s
`GenericWallSeg`-gated `rcrossSum_parity_eventually_const`. That is a substantial,
delicate re-derivation (the pairing partners differ from the generic case), not
finite avoidance — and writing it requires the per-degenerate-wall pairing combinatorics,
which I did not attempt to fake (a wrong pairing would yield a false theorem).

## Named residue (honest, single, NOT a re-wrapper)

`OffAllEdgeLines P x` (def) — the generic stratum, fully discharged. Its complement
(`x` on some edge line) is where the degenerate-wall transport is needed. There is no
co-extensive Prop banked: the obstruction theorems make the residue's nature explicit
rather than re-wrapping it.

## Verification (uisai1)

- `lake env lean ProofsInTheBook/PolygonGenericRay.lean` → RC=0, no errors/warnings.
- `lake build ProofsInTheBook.PolygonGenericRay` → "Build completed successfully (8440 jobs)".
- `#print axioms` clean-3 `[propext, Classical.choice, Quot.sound]` on:
  `genericWallSeg_of_offAllEdgeLines`, `genericChainAt_of_offAllEdgeLines`,
  `segAvoidsZero_to_mkPt`, `genericWallSeg_fails_on_edge_line`,
  `segment_has_wall_of_straddle`, `genericChainAt_false_of_straddle_on_line`.
- Never ran `lake build` / `lake env lean` on the local Mac.

## Faithfulness verdict (playbook Group C)

- `genericChainAt_of_offAllEdgeLines` : **FAITHFUL**, unconditional, non-vacuous
  (`OffAllEdgeLines` satisfiable; the construction produces real chains for arbitrary
  pairs). Genuine finite-avoidance existence on the generic stratum.
- `genericChainAt_false_of_straddle_on_line` : **FAITHFUL** disproof — establishes
  `GenericChainInput` is not a dischargeable target.
- No conditional-on-the-residue headline was shipped, by design, because the only
  available interface (`GenericChainInput`) is false on the residue stratum — shipping
  it would be a vacuous conditional. The fully unconditional `artGallery_strict`
  remains open on the **degenerate-wall parity-transport** residue (true theorem, deep
  assembly), which is now precisely characterized.
