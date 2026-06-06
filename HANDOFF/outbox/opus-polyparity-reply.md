# Ch36 Round-2 Parity Machinery — Reply (opus-polyparity)

**Status: DELIVERED + VERIFIED.** `ProofsInTheBook/PolygonParity.lean` compiles clean
on uisai2 (Lean v4.30.0-rc2, Mathlib). 0 sorry / 0 axiom / 0 admit / 0 native_decide.
All headline theorems `#print axioms` → `{propext, Classical.choice, Quot.sound}` only.

## Routing note (read this)
The task pointed me at `HANDOFF/CH36_PARITY_ROUND2.md`, but that file's *content* is the
**combinatorial-map / hypermap** Jordan route (darts, σ/α, cut-and-cap, χ≤2) — a different
substrate (the Ch35 genus-free chain). The file I *own* (`PolygonParity.lean`) and its base
API (`PolygonSubstrate`/`PolygonDiagonal`) are the **ray-crossing polygon substrate**
(`CrossingNumber`, `RayDirection`, half-open crossing, `ClosedRegion`, `IsDiagonal`). The
task's own vocabulary — local constancy of `CrossingNumber`, single-edge jump, half-open
vertex convention, interior→exterior boundary crossing, convex-vertex/slide — matches the
polygon substrate exactly (and the existing file header). I followed the **polygon** round-2
design as embodied in the file header + `CH36_13_POLYGON_DESIGN.md`, which is the consistent,
verifiable path. If the intent was actually the hypermap route, that is a *separate* file and
substrate (the `opus-cutcap*`/`opus-cc*`/`jordan_simple_cycle_of_chi_two` line) — flag me.

## Baseline fix (the file did not compile as inherited)
The pre-existing `PolygonParity.lean` was broken on the current toolchain:
- `Finset.card_insert_of_not_mem` → renamed `Finset.card_insert_of_notMem` (2 sites).
- The parity-flip `omega` proofs were unsound on the new `Odd`/`Nat` API; rewrote
  `odd_crossingNumber_iff_not_odd_of_symmDiff_singleton` via `Nat.odd_add_one`.
Now green. The two inherited core lemmas (`card_eq_succ_or_succ_of_symmDiff_singleton`,
the parity flip) are the verified heart of item (b) and are retained.

## New content delivered (all verified, in dependency order)

**§3 Item (a), bookkeeping core (unconditional)**
- `crossingNumber_eq_of_crossingEdges_eq` — equal crossing sets ⇒ equal crossing number.
- `closedRegion_iff_of_crossingEdges_eq` — off the boundary, equal crossing sets ⇒ equal
  region membership. (Membership form consumed by the Jordan substitute.)

**§4 Interior→exterior boundary-crossing theorem (the finite Jordan substitute)**
- `SegmentRegionLocallyConstant` — **named residue (a), topological form**: off the boundary,
  region-membership along the segment is locally constant in `t∈[0,1]`. Non-vacuous, documented.
- `interior_to_exterior_meets_boundary` — **MAIN: the Jordan substitute.** A segment from a
  region point to a non-region point meets the boundary. Real proof: `by_contra` ⇒ segment
  boundary-free ⇒ residue gives `IsLocallyConstant` ⇒ `isClopen_fiber` ⇒ `[0,1]` preconnected
  (`PreconnectedSpace (Icc 0 1)`) ⇒ fiber is all-or-nothing ⇒ endpoints `t=0`(x, in) /
  `t=1`(y, out) contradict. No JCT.
- `seg_subset_region_of_boundary_free` — contrapositive workhorse for **interior-to-interior**
  segments (both endpoints boundary-free).

**§5 Item (c), half-open vertex convention (unconditional)**
- `halfOpen_crossing_point_ne_terminal` — the half-open `[0,1)` crossing point is never the
  edge's *terminal* vertex `b` (when `a≠b`). Algebraic core via `lineMap` injectivity.
- `edge_terminal_vertex_not_halfOpen_crossing` — instantiated to polygon edges: a ray hitting
  `q(next i)` is *not* counted on edge `i`, forcing the count onto the single other incident
  edge. This is the single-vertex-counting guarantee of (c).

**§6 Open-segment constancy + diagonal certification (push beyond)**
- `OpenSegmentRegionLocallyConstant` — open-segment form of residue (a) (excludes the vertex
  endpoints, which are on the boundary). Non-vacuous.
- `openSegment_region_const_of_boundary_free` — region membership constant across the
  boundary-free *open* segment, seeded by one interior region point. Connectedness via
  `PreconnectedSpace (Ioo 0 1)` (derived from `isPreconnected_Ioo`).
- `isDiagonal_of_certificate` — **feeds the convex-vertex / slide layer.** Produces the full
  `IsDiagonal P ρ i j` from: combinatorial data (`i≠j`, non-adjacent), open-segment local
  constancy, the open-segment boundary certificate, ONE interior region witness, and the
  endpoint-only boundary-intersection clause. The `seg ⊆ region` conjunct (the hard clause)
  is genuinely *derived* here (endpoints in region as boundary points via `Or.inl`; interior
  by constancy), not assumed. This is precisely the residue-discharge the
  `slide_last_vertex_gives_diagonal` / `convex_vertex_empty_triangle_gives_ear` targets need.

## Design-sanctioned residues isolated (named Props, non-vacuous, documented)
- `SegmentRegionLocallyConstant`, `OpenSegmentRegionLocallyConstant` — the item-(a)
  transversality input (region-membership locally constant off the boundary). Genuinely
  geometric, strictly weaker than and distinct from the conclusions; for a real polygon + a
  ray non-parallel to every edge each edge's half-open crossing status is a transversal
  open/closed condition, so they hold. They are NOT the conclusion in disguise.

## Faithfulness audit (self, adversarial)
- Vacuity check on `isDiagonal_of_certificate`: hypotheses are jointly satisfiable (real
  diagonal: open segment strictly interior ⇒ boundary-free, interior points odd-crossing ⇒
  in region, boundary meets only endpoints). The `seg⊆region` clause is derived. FAITHFUL.
- No `def : Prop` used to dodge a `theorem`; the two residue `def`s are *hypothesis*
  predicates (appear only as premises), never as a standalone "result".
- `crossingNumber_eq_card := rfl` is a legitimate definitional-unfold lemma, not an impostor.

## Verification
```
rsync -az .../ProofsInTheBook/PolygonParity.lean uisai2:.../ProofsInTheBook/
ssh uisai2 'cd ~/repos/proof_in_the_book && lake env lean ProofsInTheBook/PolygonParity.lean'  # EXIT 0
ssh uisai2 'cd ~/repos/proof_in_the_book && lake build ProofsInTheBook.PolygonParity'          # ✔ 8421 jobs
# #print axioms on all 6 headline decls → {propext, Classical.choice, Quot.sound}
```
447 lines, 14 declarations (3 inherited+fixed, 11 new). uisai1 was down; all work on uisai2.

## What remains (not in this layer's scope; needs genuine convex geometry)
`exists_convex_vertex`, the full ear lemma, and the A4 region-split equalities are NOT here:
they require the extreme-point / slide geometry that lives above the parity substrate. This
file delivers the parity foundation (a),(b),(c) + the Jordan substitute + the diagonal
certificate that those arguments will call to discharge their `seg⊆region` obligation.
