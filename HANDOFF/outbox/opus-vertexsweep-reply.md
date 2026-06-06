# Ch36 — Vertex-sweep parity bookkeeping (`VertexSweepNeutral`) — Reply (opus-vertexsweep)

**Status: DELIVERED + VERIFIED, with a load-bearing FINDING — the unrestricted
`VertexSweepNeutral` is FALSE.**  The genuine vertex-sweep parity mathematics is
proved unconditionally; the predicate is then closed in its maximal *provable*
form under a single corrected hypothesis (`NoTangentialVertexSweep`) that
excludes exactly the one case that is not merely resistant but outright false.

New file `ProofsInTheBook/PolygonVertexSweep.lean` (imports
`ProofsInTheBook.PolygonLocalConstancy`) compiles clean on **uisai2** (uisai1
down). 862 lines, 0 sorry / 0 axiom / 0 admit / 0 native_decide / 0 warnings.
Branch `main`, no commits, no codex/OpenAI tooling, never ran lake locally. Own
only the new file.

## Verification

```
rsync -az ProofsInTheBook/PolygonVertexSweep.lean uisai2:.../ProofsInTheBook/
ssh uisai2 'lake env lean ProofsInTheBook/PolygonVertexSweep.lean'   # EXIT 0, no warnings
ssh uisai2 'lake build ProofsInTheBook.PolygonVertexSweep'           # Build completed
```
Dep oleans built first: `lake build ProofsInTheBook.PolygonLocalConstancy` → 8424/8424 ✔.

`#print axioms` on every headline → `[propext, Classical.choice, Quot.sound]`
ONLY (no `sorryAx`, no custom axiom, no `ofReduceBool`/`trustCompiler`):
`vertexSweepNeutral_of_noTangential`,
`openSegmentRegionLocallyConstant_of_noTangential`,
`exists_diagonal_noTangential`, `exists_convex_vertex_noTangential`,
`crossingNumber_eventually_const`, `pair_eventually_toggle_of_sameSide`,
`pair_eventually_false_of_backward`, `pair_bands_move_together_of_oppSide`,
`u_eq_zero_of_u_eq_one_next`, `cyclicNext_cyclicPrev`.

**Faithfulness (type-checked against the IMPORTED predicates, not redefined
impostors):** `vertexSweepNeutral_of_noTangential` produces the exact
`PolygonLocalConstancy.VertexSweepNeutral P ρ x y`, and
`openSegmentRegionLocallyConstant_of_noTangential` the exact
`PolygonParity.OpenSegmentRegionLocallyConstant P ρ x y`.  So the existing
assemblers (`earTransversality_of`, `slideTransversality_of`,
`exists_diagonal_slim`) genuinely consume the output.

## The decisive finding: `VertexSweepNeutral` (unrestricted) is FALSE

The task framed the opposite-side forward sweep as "one truly resistant toggle
case."  Working it out exactly (Cramer slopes `αᵢ = det2 ρ.r d / D_i`,
`αₖ = det2 ρ.r d / D_k`, with `uOf i t₀ = 1`, `uOf k t₀ = 0`, shared `τ_v`),
that case does not merely resist — it makes the predicate **false**.

**Exact counterexample (rational arithmetic, fully reproducible):** square
`{(0,0),(4,0),(4,4),(0,4)}`, ray `ρ.r = (1, 3/10)`, boundary-free vertical
segment `x = (-1,-1/2) → y = (-1,9/2)` (segment has `X=-1`, the square has
`X∈[0,4]`, so it never meets the boundary).  At `t₀ = 21/25` the ray through
`z(t₀) = (-1, 37/10)` passes exactly through vertex `(0,4)` (an opposite-side
forward sweep).  Half-open crossing count just-before / at / just-after `t₀`:
`2 / 1 / 0` — region parity `0 / 1 / 0`, **not** locally constant.  Every
hypothesis of `VertexSweepNeutral` (boundary-free open segment, interior `t₀`,
vertex event) holds, the conclusion fails.

I did **not** fake a proof of the false statement.  Instead I isolated the cause
to a single named, satisfiable, *strictly-needed* hypothesis and proved the
predicate under it.

## What is proven UNCONDITIONALLY (the genuine new content)

1. **Event pairing** (`reconstruct_u_eq_one/zero`, `u_eq_zero_of_u_eq_one_next`,
   `u_eq_one_of_u_eq_zero_prev`, `cyclicNext_cyclicPrev`, `cyclicNext_injective`):
   a `u=1` event on edge `i` forces a `u=0` event on `cyclicNext i` at the same
   base point with matching ray parameter `τ_v`, and conversely.  The half-open
   `[0,1)` vertex pairing is a bijection via `cyclicNext`.

2. **Exact slope formula** (`uOf_slope`, `uOf_affine_about`): the edge parameter
   is affine in `t` with slope `det2 ρ.r (y-x) / crossDen`.

3. **Backward neutrality** (`pair_eventually_false_of_backward`): `τ_v < 0` ⟹
   near `t₀` neither incident edge crosses; pair contributes the constant `0`.

4. **Same-side forward neutrality** (`pair_eventually_toggle_of_sameSide`): the
   crux.  `τ_v > 0` and same-sign denominators (`0 < crossDen i · crossDen k`,
   `det2 ρ.r (y-x) ≠ 0`) ⟹ near `t₀` exactly one of `{i,k}` crosses (they
   toggle: `i` leaves at `u<1` exactly as `k` enters at `u≥0`); pair contributes
   the constant `1`.  Real proof via the `sᵢ·sₖ > 0` sign equivalence.

5. **Crossing-number constancy assembly** (`crossingNumber_eq_sum`,
   `pair_count_eventually_const`, `fcount_eventually_const_of_noEvent`,
   `crossingNumber_eventually_const`): `CrossingNumber` is the `univ`-sum of
   status indicators; partitioning `univ` into the `u=1` representatives `R`,
   their `cyclicNext`-images `N` (= the `u=0` set), and the non-event rest, and
   reindexing `∑_N = ∑_{i∈R} fcount (cyclicNext i)` via injectivity, the sum is
   eventually constant.  Hence (off boundary) the region indicator is constant.

6. **The obstruction, recorded rigorously** (`pair_bands_move_together_of_oppSide`):
   in the opposite-side forward case the two edge-bands are *equivalent* on a
   punctured neighbourhood of `t₀` — they move together, giving the `2/1/0`
   break.  This is a proved Lean lemma demonstrating the same-side hypothesis in
   item 4 is necessary, not an assumption.

## The corrected, provable residue

`NoTangentialVertexSweep P ρ x y` (def): along the boundary-free open segment, at
every interior event parameter the ray is non-parallel to the segment and every
`u=1` event edge is `EdgeNeutralAt` (backward or same-side forward).  This
excludes exactly the opposite-side forward sweep.

* `vertexSweepNeutral_of_noTangential` : `NoTangentialVertexSweep → VertexSweepNeutral`.
* `openSegmentRegionLocallyConstant_of_noTangential` : the `loc` residue, via the
  imported `openSegmentRegionLocallyConstant_of_sweepNeutral`.
* `A3ResiduesNoTangential` + `a3ResiduesSlim_of_noTangential` +
  `exists_convex_vertex_noTangential` + `exists_diagonal_noTangential` (`4 ≤ n`):
  the A3 headlines through the corrected residue surface.

`NoTangentialVertexSweep` is satisfiable and faithful: it holds automatically for
the **interior diagonal segments** consumed downstream (ear/slide bases with
vertex endpoints) — an interior point's ray has odd total crossing parity, so no
opposite-side forward vertex sweep occurs along it (verified by rational
arithmetic for every convex diagonal tested: 0 breaks).  It is strictly weaker
than the `loc` predicate and is *not* the conclusion in disguise (when no event
occurs it is vacuously discharged and `loc` is fully unconditional for that
segment).

## Audit verdicts (playbook Group C)

- Items 1–6 (pairing, slopes, backward + same-side neutrality, the assembly, the
  obstruction): **FAITHFUL** (unconditional, non-vacuous).
- `vertexSweepNeutral_of_noTangential`,
  `openSegmentRegionLocallyConstant_of_noTangential`,
  `exists_diagonal_noTangential`: **CONDITIONAL-honest** on
  `NoTangentialVertexSweep` (+ pre-existing `free`, `extreme`).
- The prior handoff's bare `VertexSweepNeutral` clause in `A3ResiduesSweep`
  (`PolygonLocalConstancy`): now shown **IMPOSTOR-risk / FALSE-in-general** — it
  is a false predicate for arbitrary boundary-free segments.  Downstream code
  should route through `A3ResiduesNoTangential` (this file), whose vertex-sweep
  clause is the provable one.

## Chapter 36's sharpest current frontier

`exists_diagonal` (`4 ≤ n`) now holds with the `loc` clause discharged down to
its irreducible kernel: the Cramer/affine analysis, the `τ=0` boundary
exclusion, per-edge no-event constancy, **and now the full vertex-sweep parity
bookkeeping (event pairing + backward + same-side forward, with the
crossing-number assembly)** are all unconditional.  The *sole* remaining
geometric hypothesis is `NoTangentialVertexSweep` — the exclusion of
opposite-side forward vertex sweeps — which is no longer a black box but a
precisely characterized, satisfiable condition with a proved obstruction lemma
and a known discharge route (interior diagonal segments).  The frontier is thus:
prove `NoTangentialVertexSweep` holds for the specific ear/slide diagonal
segments from the parity-of-interior-points argument (the only ingredient still
exposed as a hypothesis), which would make `exists_diagonal` fully
unconditional.
