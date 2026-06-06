# opus-sidecross — Side-coordinate crossing convention (Ch36 tangent repair)

**STATUS: COMPLETE.** New file `ProofsInTheBook/PolygonSideCrossing.lean`
(1308 lines) compiles clean on uisai1, **0 sorry / 0 axiom / 0 admit /
0 native_decide**, all headline theorems **clean-3**
(`{propext, Classical.choice, Quot.sound}`).

Branch: `main` (no switches). No commits made. Only the one NEW file touched;
not imported anywhere, so no other build is disturbed.

NOTE on server: the repo lives on **uisai1**, not uisai2 (uisai2 has no
`~/repos/proof_in_the_book`). Verified exclusively via rsync→uisai1
`lake env lean` per the kernel-panic rule; never ran lake locally.

## What was built (the ruling, implemented)

### 1. New predicate (side-coordinate half-open + forward)
- `side r x v := det2 r (v - x)` (bare ray vector; `side ρ.r x v` is the tied form).
- `Span a b := (a ≤ 0 ∧ 0 < b) ∨ (b ≤ 0 ∧ 0 < a)` (nonpositive included,
  positive excluded — the classical scanline rule).
- `SpanCrossesSide P ρ x i := Span (side ρ.r x (q i)) (side ρ.r x (q (next i)))`.
- `EdgeCrossesRay' := SpanCrossesSide ∧ 0 ≤ crossTau` (forward guard reuses the
  EXISTING Cramer ray parameter `crossTau` from `PolygonLocalConstancy` verbatim).
- `CrossingNumber'`, `ClosedRegion' := OnBoundary ∨ Odd (CrossingNumber')`.

### 2. Kernel sanity — square counterexample FIXED (machine-checked)
Square `{(0,0),(4,0),(4,4),(0,4)}`, ray `(1,3/10)`, outside segment `X=-1`,
event at the vertex `(0,4)`. Two independent checks in-file:
- `#eval` of a ℚ evaluator: raw counts **2 / 0 / 0** across just-before / at /
  just-after the event; parities **0 / 0 / 0** (CONSTANT even). Old convention
  gave `2 / 1 / 0` → parity `0 / 1 / 0` (the break). The vertex hit now
  contributes 0, not 1.
- A `decide`-proven `example` (integer mirror, denominator cleared) certifying
  the three parities are all `0`. No `native_decide`.

### 3. Vertex events neutral BY CONSTRUCTION → UNCONDITIONAL local constancy
- `span_mod_two_through_vertex (ha : a≠0) (hb : b≠0) :`
  `([Span a s] + [Span s b]) % 2 = [Span a b]` — the whole vertex repair: the
  combined span contribution of the two incident edges is independent of the
  swept-vertex side `s`. `a,b ≠ 0` is FREE at any single event
  (`no_adjacent_vertices_both_on_rayLine` + `event_far_endpoints_ne`).
- `pair_count_eventually_const'` — the incident pair `(i, cyclicNext i)` has
  eventually-constant parity at a side-zero event, in BOTH regimes (backward:
  both uncounted; forward: count = span, parity `= [Span a b]`, locally constant).
  **No same-side/opposite-side split, no `NoTangentialVertexSweep`.** The
  side-zero ↔ `crossU=1`/`crossU=0` bridge (`side_next/start_zero_iff_crossU_*`)
  lets it reuse `PolygonVertexSweep`'s Cramer pairing
  (`u_eq_zero_of_u_eq_one_next`, `crossTau_event_eq`).
- `statusOf'_eventually_eq_of_noEvent` — non-event per-edge constancy (a
  `crossTau=0` span crossing is a boundary point, excluded:
  `crossTau_eq_zero_span_imp_onEdge`).
- `crossingNumber'_parity_eventually_const` — **UNCONDITIONAL** assembly: R (u=1)
  / N (u=0, = cyclicNext''R) / Rest partition, pair lemma on R, no-event on Rest,
  summed mod 2. This is the headline: parity locally constant at EVERY interior
  parameter, vertex sweeps included, with no extra hypothesis.
- `openSegmentRegionLocallyConstant'_unconditional` — the corrected `loc`
  residue, **discharged with no hypothesis** (vs. the old one which needs
  `VertexSweepNeutral`/`NoTangentialVertexSweep`, false in general).

### 4. Interface re-derivation for the A3 chain (cheaper route taken)
Took the ruling's **unconditional `exists_diagonal'` chain** (not the
generic-agreement bridge — that would need proving old≡new parity, a generic-ray
argument the ruling flags as more expensive). Around `ClosedRegion'`:
- `openSegment_region'_const_of_boundary_free` (connectedness of (0,1)).
- `IsDiagonal'`, `isDiagonal'_of_certificate` (the `loc` clause now free).
- `IsConvexVertex'`, ear/slide certificates
  (`convex_vertex_empty_triangle_gives_ear'`, `slide_last_vertex_gives_diagonal'`),
  reusing ALL region-agnostic combinatorics/triangle-containment from
  `PolygonConvexVertex` verbatim.
- **`exists_diagonal'`** (4 ≤ n): every strict simple polygon has a corrected
  diagonal, given a primed-convex vertex + branch-aware *free-segment* dispatcher
  `DiagonalTransversality'` (carries only `free`; `loc`/sweep eliminated).

## Migration-plan reuse (survived verbatim)
`StrictSimplePolygon`, `RayDirection`, `det2`/Cramer (`crossTau`, `crossDen`,
`cross_eq`, `cross_unique`), affine sweep (`crossTau_lineMap`, continuity),
boundary predicate, `bdry_of_free`, the cyclic pairing of `PolygonVertexSweep`,
and the whole combinatorial A3 layer. Only the crossing *predicate* and the
vertex-event lemmas changed, exactly as §11 prescribed.

## Honest scoping
- The **one** place that could be called a joint: the downstream consumers
  (`PolygonResidues`/`PolygonConvexVertex`/region-cut layer) are still hardwired
  to the OLD `ClosedRegion`. Per the ruling, the faithful repair requires those
  to migrate to `ClosedRegion'`. I provide the full corrected interface
  (`IsDiagonal'`, `exists_diagonal'`, `IsConvexVertex'`, `loc'`) self-contained
  in this file; wiring it INTO the consumers requires editing files I do not own.
  This is a clean, named hand-off boundary, not a gap in the math: the corrected
  side does the diagonal existence end-to-end unconditionally. No truly resistant
  *proof* joint remained — nothing was isolated/assumed.
- `IsConvexVertex'` (adjacentTriangle ⊆ ClosedRegion') and the `free` residues
  are the genuine, non-vacuous geometric inputs — identical in kind to the old
  chain's, minus the now-proven `loc`.

## Verification
```
rsync -az .../PolygonSideCrossing.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
  && lake env lean ProofsInTheBook/PolygonSideCrossing.lean'   # exit 0
```
`#print axioms` on `crossingNumber'_parity_eventually_const`,
`openSegmentRegionLocallyConstant'_unconditional`, `exists_diagonal'`,
`isDiagonal'_of_certificate`, `span_mod_two_through_vertex` → all
`[propext, Classical.choice, Quot.sound]`. Kernel `#eval` prints `2 0 0 0 0 0`.
