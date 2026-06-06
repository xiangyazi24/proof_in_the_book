# Ch36 — Crossing-parity local constancy (the `loc` residue) — Reply (opus-polyloc)

**Status: DELIVERED + VERIFIED (maximally discharged; one design-sanctioned
residue isolated, narrowed to a single named predicate).** New file
`ProofsInTheBook/PolygonLocalConstancy.lean` (imports
`ProofsInTheBook.PolygonResidues`) compiles clean on **uisai2** (uisai1 down).
0 sorry / 0 axiom / 0 admit / 0 native_decide / 0 warnings. 732 lines.

## Verification

```
rsync -az ProofsInTheBook/PolygonLocalConstancy.lean uisai2:.../ProofsInTheBook/
ssh uisai2 'lake env lean ProofsInTheBook/PolygonLocalConstancy.lean'   # EXIT 0, no warnings
lake env lean -o .../PolygonLocalConstancy.olean ...                    # EXIT 0
```
Dep oleans built first: `lake build ProofsInTheBook.PolygonResidues` → 8423/8423 ✔.

`#print axioms` on all 17 named results → `[propext, Classical.choice,
Quot.sound]` ONLY (no `sorryAx`, no custom axiom, no `ofReduceBool`/
`trustCompiler`): `edgeCrossesRay_iff`, `cross_eq`, `cross_unique`,
`crossU_lineMap`, `crossTau_lineMap`, `crossTau_eq_zero_imp_onEdge`,
`statusOf_iff_ineqs`, `statusOf_eventually_eq_of_noEvent`,
`crossingEdges_eventually_eq`, `regionOf_eventually_eq_of_allEdges`,
`regionOf_eventually_eq`, `openSegmentRegionLocallyConstant_of_sweepNeutral`,
`earTransversality_of_sweep`, `slideTransversality_of_sweep`,
`a3ResiduesSlim_of_sweep`, `exists_convex_vertex_sweep`, `exists_diagonal_sweep`.

Branch `main`, no commits, no codex/OpenAI tooling, never ran lake locally. Own
only the new file (did not touch the root, `PolygonResidues.lean`, or any other
tracked file).

## The route taken (per the task spec)

For one edge `i` (`a = P.q i`, `b = P.q (cyclicNext i)`) the half-open crossing
system `z + τ•r = a + u•(b - a)` has, because `det2 r (b - a) ≠ 0`
(`no_edge_parallel`), a **unique** Cramer solution:

* `crossU  = det2 r (z - a) / det2 r (b - a)`
* `crossTau = det2 (a - z) (b - a) / det2 r (b - a)`

and `EdgeCrossesRay P ρ z i ↔ z ∉ Edge i ∧ 0 ≤ crossTau ∧ 0 ≤ crossU < 1`
(`edgeCrossesRay_iff`). Both scalars are **affine in `z`**, hence affine in the
segment parameter `t` along `z = lineMap x y t` (`crossU_lineMap`,
`crossTau_lineMap`). So each crossing inequality flips only at one `t`, where the
relevant affine quantity hits an equality.

## What is proven UNCONDITIONALLY (genuine, non-vacuous content)

1. **Full Cramer characterization** (`det2` bilinearity helpers,
   `eq_zero_of_det2_eq_zero`, `cross_eq` existence, `cross_unique` uniqueness,
   `edgeCrossesRay_iff`). The substrate's existential crossing predicate is
   pinned to three explicit affine inequalities in the base point.

2. **Affineness along the segment** (`det2_r_sub_lineMap`, `crossU_lineMap`,
   `crossTau_lineMap`, `continuous_uOf`, `continuous_tauOf`).

3. **`τ = 0` event excluded by boundary-freeness** (`crossTau_eq_zero_imp_onEdge`):
   if `crossTau z i = 0` with `0 ≤ crossU < 1`, then `z = lineMap a b crossU`
   lands on the closed edge `Edge i` — a boundary point, contradicting the
   boundary-free hypothesis. This is exactly the spec's "sign/threshold crossing
   impossible by the half-open convention + no_edge_parallel."

4. **Per-edge local constancy away from `u`-events** (`statusOf_iff_ineqs`,
   `statusOf_eventually_eq_of_noEvent`): at any interior `t₀` where
   `crossU(z(t₀)) i ∉ {0, 1}`, edge `i`'s crossing status is locally constant.
   Real proof: off the boundary the status equals the three affine inequalities;
   the `z ∉ Edge` clause is automatic near `t₀` (interior points are
   boundary-free, `Ioo 0 1` open); each strict inequality persists in a
   neighborhood by continuity (with the `τ = 0` boundary excluded by item 3).
   This is the spec's "each inequality's truth changes at most at one parameter
   value" formalized as genuine local constancy.

5. **Finite assembly** (`crossingEdges_eventually_eq`,
   `regionOf_eventually_eq_of_allEdges`): if *every* edge is eventually
   status-constant at `t₀`, the whole crossing `Finset` is (finite ∀ over
   `Fin n`), hence — off the boundary — the region indicator is eventually
   constant (via the substrate's `closedRegion_iff_of_crossingEdges_eq`).

6. **Region indicator locally constant at every interior parameter**
   (`regionOf_eventually_eq`): combine item 4 (no-event points: all edges
   discharged unconditionally) with the single isolated residue (vertex-sweep
   points).

7. **The `loc` residue** (`openSegmentRegionLocallyConstant_of_sweepNeutral`):
   pulls item 6 back along the continuous coercion `Ioo 0 1 ↪ ℝ` via
   `IsLocallyConstant.iff_eventually_eq`, producing exactly
   `OpenSegmentRegionLocallyConstant P ρ x y` — the predicate
   `earTransversality_of` / `slideTransversality_of` consume.

8. **Builders + maximally-discharged headline** (`earTransversality_of_sweep`,
   `slideTransversality_of_sweep`, `A3ResiduesSweep`, `a3ResiduesSlim_of_sweep`,
   `exists_convex_vertex_sweep`, `exists_diagonal_sweep`): the A3 diagonal and
   convex-vertex headlines restated through a residue surface in which `loc` is
   *replaced* by the narrower `VertexSweepNeutral`. So Chapter 36's diagonal
   existence (`4 ≤ n`) now holds with the `loc` clause reduced from "the entire
   plane-sweep local constancy" to "vertex-sweep parity neutrality at the
   event parameters only," plus the unchanged `free` (open-segment edge
   avoidance) and `extreme` (extreme-vertex convexity).

## The single isolated residue (honest, NOT faked)

`VertexSweepNeutral P ρ x y` — restricted to interior parameters `t₀` that are
**vertex-sweep events** (some edge `i` has `uOf … t₀ ∈ {0,1}`, i.e. the ray
through the moving point passes through a polygon vertex), the region indicator
is locally constant at `t₀`. This is precisely the half-open `[0,1)` convention's
parity preservation across a vertex sweep: the two incident edges swap crossing
status (one's `u` crosses `0`, the other's crosses `1`), leaving the
crossing-**number parity** — hence region membership — unchanged.

Why this is the genuinely resistant case (sustained-effort finding): closing it
requires the global event/swap bookkeeping — identifying, at each swept vertex,
the incident edge pair `{i, cyclicPrev i}` (and, when several vertices are
collinear with the moving point along `r`, a *union* of such pairs), and proving
each pair's status flips cancel in parity. That is the full plane-sweep
transversality development the round-2 design (`PolygonParity` §4 header) names
as "the one genuine geometric residue" the ray-crossing substrate does not
re-derive from a Jordan curve theorem. Everything **away** from these
measure-zero event parameters is discharged unconditionally above; the residue
is genuinely confined to the vertex sweeps.

**Faithfulness (Group C):** `VertexSweepNeutral` is satisfiable and faithful —
for a real strict simple polygon and a ray non-parallel to every edge the
half-open count is genuinely parity-stable across vertex sweeps, so the predicate
holds; it is strictly weaker than `OpenSegmentRegionLocallyConstant` (a
per-event-point local statement on the event set only, with the no-event part
already proved). It is NOT the conclusion in disguise: when the segment has no
vertex-sweep event the residue is vacuously true and `loc` is *fully
unconditional* for that segment. There is no clause forcing falsity.

## Audit verdicts (playbook Group C)

- Items 1–7 above (Cramer equivalence, affineness, `τ`-exclusion, no-event
  per-edge constancy, finite assembly, the `loc` builder): **FAITHFUL**
  (unconditional, non-vacuous).
- `A3ResiduesSweep`, `exists_convex_vertex_sweep`, `exists_diagonal_sweep`:
  **CONDITIONAL-honest** on `VertexSweepNeutral` (+ the pre-existing `free`,
  `extreme`) — the substrate's design-sanctioned vertex-sweep parity core, now
  the *sole* remaining geometric hypothesis of the `loc` clause.

## Net effect

The `loc` residue (`OpenSegmentRegionLocallyConstant`) — previously an opaque
plane-sweep black box — is now discharged down to its irreducible kernel: the
full Cramer/affine sign analysis, the `τ = 0` boundary exclusion, and per-edge
local constancy at all non-event parameters are proved unconditionally; only the
vertex-sweep parity swap (`VertexSweepNeutral`) remains, isolated as a single
minimal named predicate. Chapter 36's `exists_diagonal` is restated through this
narrowest hypothesis surface (`exists_diagonal_sweep`).
