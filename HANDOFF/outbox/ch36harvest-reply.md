# Ch36 harvest reply (Opus worker, 2026-06-10)

**File:** `ProofsInTheBook/ZinanCh36Harvest.lean` (created; no other edits). Type-checks clean on
uisai2 (`lake env lean`), 8 theorems all clean-3 {propext, Classical.choice, Quot.sound}, zero
sorry/axiom/admit/native_decide, zero errors/warnings. Deps `ZinanCh36Interval` +
`PolygonGeometryDischarge` + `PolygonWindingPath` + `PolygonLocalJump` + `PolygonEarDelete` built
clean (8523 jobs).

## Where the chain reaches (delivered, UNCONDITIONAL)

Stage 1 — kernel consumers. `rayCrossingAlternation_final` (now unconditional, general n, modulo the
two genericity guards `hoff`+`hvert`, the latter genuinely necessary) feeds
`windCross_mem_of_alternation`:
- `windCross_mem_kernel`, `oWind_mem_kernel` — the winding BOUND `windCross ∈ {0,1,-1}` at every
  generic off-boundary point, general n, with NO external residue.

Stage 2 — the bound discharges the integer split-determination consumers' `hLb`/`hRb` premises:
- `sub_regions_not_both_inside_kernel` — disjointness of the two ear sub-regions, with the bound
  premises internalised (only the parent value `windCross_P = 1` left as input).
- `earDeletedExterior_winding_route` — the winding route to `earDeletedExterior`: derives
  `windCross_R = 0` ALGEBRAICALLY from the diagonal split (NOT the refuted half-plane), from the
  two interior facts `windCross_L = 1`, `windCross_P = 1`.

## Where the chain STOPS (precise residue)

The alternation kernel pins winding MEMBERSHIP in {0,1,-1}, not the interior VALUE. Every consumer
below the bound needs a specific interior value:
- `earDeleted_exterior_of_bound` needs `windCross_P = 1` (interior of parent) AND `windCross_L = 1`
  (sign, not just ≠ 0).
- `EarCutData.earDeletedExterior` ≡ `EarDeletedWindingZero` ≡ `windCross_R = 0`.
- `InteriorOddSeed` ≡ `windCross_P ≠ 0` at the interior ear point.

These are the interior-vs-exterior face of the Jordan curve theorem — exactly the residue the four
equivalent kernel faces REDUCE TO. The alternation kernel is the WEAKEST of the four (yields the
bound only) and supplies none of them. The value-producing substrate route
(`ExteriorWindingZero_halfplane` → `EarHalfPlaneContainment`) is MACHINE-REFUTED
(`stop_route_refuted`, re-exported); the recommended position-vector `thetaPos` route (residue map
item 6) is not built. Documented in `stop_residue_is_interior_value`, `stop_route_refuted`.

## Stages 3–4 (conditional surface, named not closed)

- `isConvexVertex'_of_stop_residue` — `InteriorOddSeed` closes the convex-vertex field of the
  bundle (re-export). This is the single field `PolygonGeomResidue` still needs; the other halves
  (OffDiagDisjoint via segment identity, ray-independence/RegionSplitGenericity, parity) are
  already discharged in `PolygonGeometryDischarge`.
- `artGallery_strict_over_residue` — the ⌊n/3⌋ headline, conditional on exactly
  `PolygonGeomResidue` (irreducible kernel `InteriorOddSeed`) + `M` (re-export). NOT closed by this
  harvest: the convex-vertex residue is `InteriorOddSeed`, the interior value the alternation
  kernel does not supply.

**Net:** the kernel closes the BOUND-level consumers unconditionally; the chain stops at the
interior-value Jordan keystone (`InteriorOddSeed`). `earDeletedExterior` / `PolygonGeomResidue` /
the ⌊n/3⌋ headline remain honestly conditional on `InteriorOddSeed`. M not attempted (chain stops
upstream of it at the residue).
