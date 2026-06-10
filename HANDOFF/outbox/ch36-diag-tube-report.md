# Ch36 Diagonal-Tube Synchronization — bricks 4, 5, 7 (report)

**File:** `ProofsInTheBook/ZinanCh36DiagTube.lean` (297 lines, 0 errors, clean-3).
**Status:** Brick 4 UNCONDITIONAL. Bricks 5+7 LANDED conditional on ONE named, satisfiable
geometric primitive (`DiagTubeStraddle`), with everything else proved unconditionally around it.
No `sorry` / `admit` / `axiom` / `native_decide`.

`#print axioms` for all five public results = `[propext, Classical.choice, Quot.sound]` (clean-3,
no `sorryAx`).

## Brick 4 — the diagonal midpoint facts (UNCONDITIONAL, commit-grade)

* `diagMid P i j := AffineMap.lineMap (P.q i) (P.q j) (1/2)` — chosen as the `1/2` line-map point
  (not `midpoint`) so open-segment membership is a one-line `Ioo` fact.
* `diagMid_mem_openSegment`, `diagMid_mem_segment` — membership in the (open/closed) diagonal segment.
* `diagMid_off_parent_boundary` — from `IsDiagonal'`'s boundary clause
  `seg ∩ {OnBoundary} = {P.q i, P.q j}`: the midpoint is in the segment, so if on the boundary it
  equals an endpoint, but an endpoint in its own open segment forces `P.q i = P.q j` (refuted via
  `left/right_mem_openSegment_iff` + `i ≠ j` + vertex injectivity).
* `diagMid_mem_closedRegion`, `diagMid_odd_crossing` — `IsDiagonal'` puts the segment in
  `ClosedRegion'`; off the boundary, `ClosedRegion' = OnBoundary ∨ Odd CrossingNumber'` gives ODD.
* `diagMid_parent_wind_ne_zero` — odd crossing ⟹ `windCross ≠ 0` via
  `windCross_ne_zero_of_odd_crossing`.

These route exactly as the design's brick-4 sketch (segment-in-region + odd-crossing bridge).

## Brick 5 — two-sided tube points (parent equality + child jumps LANDED; straddle named)

* `DiagTubeStraddle h lax rax σL σR` — the named primitive: for any nhds `U` of `diagMid`, two
  points `zp, zm ∈ U` off all three boundaries (P, L, R), with the child crossing sets at `zp`/`zm`
  differing by EXACTLY one edge on each child (singleton symmetric difference = `{eL}` / `{eR}`).
* `exists_two_sided_diag_points` — consumes `DiagTubeStraddle` and LANDS the full brick-5 output:
  - **parent-winding equalities** `windCross P ρ zp = windCross P ρ (diagMid)` (and `zm`) —
    UNCONDITIONAL, via `windCross_locally_constant_off_boundary` (instantiate `U` = the
    constancy neighborhood `{y | windCross P ρ y = windCross P ρ (diagMid)}`, which is a nhds since
    `diagMid` is off the parent boundary);
  - **child jumps** `windCross L σL zp ≠ windCross L σL zm` and the R mirror — UNCONDITIONAL given
    the straddle's singleton symmDiffs, via brick 3 `windCross_ne_of_symmDiff_singleton`.

## Brick 7 — synchronization master (LANDED conditional on `DiagTubeStraddle`)

* `split_child_signs_eq` — exactly the requested signature (`hLr : σL.r = ρ.r`, `hRr`, the two
  `RayWindValuesWithSign` packages, plus `DiagTubeStraddle`). Assembly: tube points (brick 5) →
  child value dichotomies (`RayWindValuesWithSign.values`, guard-free) → split identities
  `L+R=P` at each point (`windCross_split_common`) → parent equal+nonzero (= value at `diagMid`,
  brick 4) → `signs_eq_from_split_local` (brick 6). **Note confirmed:** brick 6 needs BOTH child
  jumps (`hLjump` AND `hRjump`), so both child symmDiffs are required — the straddle supplies both.

## THE ONE MISSING PRIMITIVE (honesty contract)

`DiagTubeStraddle` packages exactly one geometric fact that is NOT in the substrate: the
**transversal single-edge flip** of the shared diagonal — that `zp, zm` straddling the diagonal
LINE at ε distance have child crossing sets differing by *exactly* the diagonal edge.

This is precisely the **singleton-symmetric-difference** primitive that `PolygonLocalJump`
(file header §1, committed) explicitly isolates as the chapter's one missing planar-Jordan keystone:

> "To prove the symmetric difference is a singleton one must show that every other edge keeps its
> crossing status ... the genuine Jordan content (which edges change across the sweep) remains the
> one missing primitive."

The substrate provides the OPPOSITE polarity for free: `windCross_locally_constant_off_boundary`
gives that ALL edges keep their status between two nearby SAME-side points (symmDiff = ∅). The
OPPOSITE-side flip of one designated edge (symmDiff = singleton) is the transversal content and is
not landed. Constructing it = re-deriving the design's unlanded brick 10
(`exists_near_diag_point_off_all`: punctured-normal escape + finite-segment separation), which is
out of scope for this worker and is the named Jordan residue, not wiring.

### Why I did not fold the off-boundary/nhds construction into a thinner residue

I considered reducing the residue to ONLY the symmDiff by constructing `zp/zm = diagMid ± ε·perpVec`
concretely and proving the off-all-boundary + nhds parts. That requires (a) `IsClosed (OnBoundary)`
for polygons (NOT landed) and (b) finite-segment separation of `diagMid` from all OTHER child/parent
edges with a transversal escape off the diagonal segment — which IS the design's brick 10. Both are
the same missing planar geometry. So the honest packaging keeps the off-boundary facts inside
`DiagTubeStraddle` (they come with the real straddle construction) rather than fabricating them.

### Non-vacuity certificate (§3.3)

`diagTubeStraddle_forces_child_jumps` certifies `DiagTubeStraddle` is not a disguised `False`
(which `#print axioms` cannot detect): under it, two points genuinely arise with DISTINCT left and
right child windings and a constant nonzero parent winding — a non-degenerate winding configuration
that a `False`-equivalent premise could not single out. This mirrors the accepted precedent
`PolygonLocalJump.localJumpSeed_forces_odd`. The hypothesis is satisfiable exactly when the diagonal
straddle is, i.e. for the real geometry.

## Best attack sketch for closing `DiagTubeStraddle` (next wave)

Goal (per child, say L with diagonal edge `eL`):
`symmDiff (CrossingEdges' L σL zp) (CrossingEdges' L σL zm) = {eL}` with `zp,zm = diagMid ± ε·perpVec(ρ.r)` for small ε.

1. **Other edges stable (symmDiff ⊆ {eL}):** every child edge `k ≠ eL` is a closed segment not
   containing `diagMid` (diagMid is interior to the diagonal `eL`, at positive distance from the
   finitely many other edges). For ε below the min of those distances, `zp` and `zm` lie in a common
   ball avoiding edge `k`'s crossing-discontinuity locus; mirror the per-edge eventual constancy of
   `sEdge_eventually_eq_rest` / `signedPair_eventually_eq` (`PolygonWindingExterior`) — those prove
   each edge's crossing status is eventually constant at an off-edge base point.
2. **Diagonal edge flips (`eL ∈ symmDiff`):** `EdgeCrossesRay' = SpanCrossesSide ∧ 0 ≤ crossTau`.
   For edge `eL` = diagonal `(P.q i, P.q j)`, `side ρ.r z (P.q i)` and `side ρ.r z (P.q j)` are
   affine in `z` (`side_lineMap`); as `z` crosses the diagonal LINE (the `zp→zm` segment crosses it
   at `diagMid`), the `Span`/`crossTau`-sign of edge `eL` flips exactly once. The `det2`-affineness
   machinery in `ZinanCh36NonInterleave` (`sweepDir = perpVec r + λ•r`, `det2_sweepDir_left` affine
   in λ) is the right substrate to drive the single sign change.
3. **Assemble** via `Finset.ext`: membership in exactly one of the two crossing sets ⟺ `k = eL`.

Step 2 is the genuine Jordan transversality; step 1 is the finite-separation bookkeeping (design's
brick 10). Both are real geometry, not wiring, hence correctly left as the named residue here.

## Build / verify

```
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake build ProofsInTheBook.ZinanCh36SignSync'   # oleans
scp ProofsInTheBook/ZinanCh36DiagTube.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean ProofsInTheBook/ZinanCh36DiagTube.lean'
```
→ 0 errors; all five `#print axioms` = clean-3.
