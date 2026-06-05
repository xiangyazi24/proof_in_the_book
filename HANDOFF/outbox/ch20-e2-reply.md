# Ch20 E2 reply

## Progress

- `ProofsInTheBook/Chapter20DissectionEngine.lean`
  - Changed import from `Chapter20Dissection` to `Chapter20`; the former `.olean`
    was absent and the engine only needs symbols already exported by `Chapter20`.
  - Fixed `sideInteriorChain`: `Finset.sort` failed because
    `fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂` has no
    `Std.Antisymm` instance on vertices.  Replaced it with
    `Finset.toList.insertionSort`, preserving side-parameter ordering without
    requiring antisymmetry.
  - Rewrote `OnSquareBoundary` using `Sym2.fromRel`; this avoids the fragile
    Prop-valued `Sym2.lift` equality obligation while keeping the same meaning.

- `ProofsInTheBook/Chapter20E2Diagonal.lean`
  - Added the diagonal split sanity witness:
    `Chapter20E2Diagonal.diagonalSquareDissection : SquareDissection`.
  - Proved `coord_inj`, `nondeg`, `equalArea`.
  - Proved `cover` by explicit descriptions of the two convex hulls:
    lower triangle `{p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1}` and upper triangle
    `{p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}`.
  - Proved `disjoint_int` using metric-interior arguments across the diagonal.

## Verification

- `PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter20DissectionEngine.lean`
  passes, with exactly the two pre-existing E2 `sorry` warnings.
- To check the helper import without `lake build`, I generated only the owned
  engine olean:
  `PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean -o .lake/build/lib/lean/ProofsInTheBook/Chapter20DissectionEngine.olean ProofsInTheBook/Chapter20DissectionEngine.lean`
- `PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter20E2Diagonal.lean`
  passes.
- I did not run `lake build`.

## Blocker for E2

The two E2 theorem bodies are still blocked.  The first missing Mathlib-level
geometry lemma is the nondegenerate triangle frontier classification:

```lean
theorem frontier_convexHull_triangle_of_doubleArea_ne_zero
    (a b c : ℝ × ℝ) (hnd : doubleArea a b c ≠ 0) :
    frontier (convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))) =
      segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a
```

The immediate blocked subgoal in the E2 route is:

```lean
a b c x : ℝ × ℝ
hnd : doubleArea a b c ≠ 0
hx : x ∈ frontier (convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)))
⊢ x ∈ segment ℝ a b ∨ x ∈ segment ℝ b c ∨ x ∈ segment ℝ c a
```

I searched Mathlib for:

- `frontier.*convexHull`, `convexHull.*frontier`
- `frontier.*closedInterior`, `closedInterior.*frontier`
- `Simplex.*frontier`, `frontier.*Simplex`
- `mem_frontier.*convexHull`, `face.*frontier`

No usable theorem exists.  Mathlib has `Affine.Simplex.closedInterior`,
`Affine.Simplex.mem_closedInterior_face_iff_wbtw`, and barycentric-coordinate
interior facts, but not the ambient topological frontier of a 2-simplex as the
union of its three 1-faces.  E2 also needs a local line-separation/half-disk
connectedness package; searches for `half.*disk`, `half.*ball`,
`connected.*half`, and line-separation lemmas did not find such an API.

So the precise next brick is to prove the triangle frontier classification
locally, then use it to show that any atomic segment contained in a triangle
frontier is contained in one of that triangle's three sides.

## Round 2 update

- Added `ProofsInTheBook/Chapter20E2Frontier.lean`.
- Proved the requested frontier classification, with no `sorry`/`axiom`:

```lean
theorem frontier_convexHull_triangle_of_doubleArea_ne_zero (a b c : ℝ × ℝ)
    (hnd : doubleArea a b c ≠ 0) :
    frontier (convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))) =
      segment ℝ a b ∪ segment ℝ b c ∪ segment ℝ c a
```

Implementation route:

- Proved `frontier_filled2Simplex` directly from
  `interior_filled2Simplex_eq`.
- Packaged `triangleAffine` as an affine map and a homeomorphism when
  `doubleArea a b c ≠ 0`, using `det_triangleEdgeMap` and
  `LinearMap.equivOfDetNeZero`.
- Transported `frontier_filled2Simplex` through `Homeomorph.image_frontier`.

Verification run:

```bash
PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter20E2Frontier.lean
PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean -o .lake/build/lib/lean/ProofsInTheBook/Chapter20E2Frontier.olean ProofsInTheBook/Chapter20E2Frontier.lean
PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter20DissectionEngine.lean
```

The helper verifies cleanly.  The engine verifies after generating the helper
olean, with exactly the two original E2 `sorry` warnings.

Additional Round 2 support lemmas now proved in the same helper:

```lean
theorem interior_convexHull_triangle_of_doubleArea_ne_zero
lemma doubleArea_edge_triangleAffine
lemma doubleArea_edge_mul_nonneg_of_mem_convexHull
lemma doubleArea_edge_mul_pos_of_mem_interior_convexHull
theorem frontier_unitSquare
```

These give the signed half-plane side of the next step: relative to an oriented
edge `a b`, the closed triangle lies in the closed signed half-plane and its
interior lies in the corresponding open signed half-plane (expressed as the
sign of `doubleArea a b x * doubleArea a b c`).
`frontier_unitSquare` gives the coordinate classification of the square
frontier needed for the boundary-side case.

Current remaining blocker for closing E2:

```lean
-- Needed local planar-incidence lemma.
-- For an atomic edge e = s(p,q), let I(e) be the triangles whose subdivided
-- boundary lists contain e.  Using the midpoint/relative-interior point m of
-- segment (coord p) (coord q), prove:
--   * if segment (coord p) (coord q) ⊆ frontier square, then #I(e) = 1;
--   * otherwise #I(e) = 2.
--
-- The proof must combine:
--   1. frontier_convexHull_triangle_of_doubleArea_ne_zero, to classify every
--      incident triangle side as one of its three closed edges;
--   2. a signed-half-plane lemma for a nondegenerate triangle along a chosen
--      edge: its interior near a relative-interior point of the edge occupies
--      exactly the open half-plane determined by the opposite vertex;
--   3. disjoint_int, to rule out two incident triangles on the same side;
--   4. cover, to force the missing opposite-side triangle for non-boundary
--      atomic edges, and to force absence of the outside-side triangle for
--      square-boundary atomic edges.
```

I did not find an existing Mathlib lemma packaging this local half-plane /
finite-cover argument.  The new frontier lemma removes the previous
`convexHull` frontier blocker, but the two E2 statements in
`Chapter20DissectionEngine.lean` are still open.

## Round 3 partial update

I did not close the two E2 theorem bodies.  I added and verified several
needed bricks, but the final finite-cover local-incidence argument is still not
formalized.

New proved helpers in `ProofsInTheBook/Chapter20DissectionEngine.lean`:

```lean
mem_sideInteriorChain_iff
sideInteriorChain_nodup
sideChain_nodup
endpoints_mem_of_mem_consecutiveEdges
consecutiveEdges_nodup_of_nodup
not_diag_mem_consecutiveEdges_of_nodup
endpoints_onSide_of_mem_sideAtomicEdges
sideAtomicEdges_nodup
tri_v₁_ne_v₂
tri_v₂_ne_v₃
tri_v₃_ne_v₁
linearIndependent_pair_of_doubleArea_ne_zero
adjacent_sideAtomicEdges_disjoint
triAtomicEdges_nodup
incidentTris
atomicMult_eq_incidentTris_card
midpoint_mem_openSegment_of_wbtw_of_ne
```

These prove the requested mechanical count bridge:

```lean
atomicMult D e = (incidentTris D e).card
```

New proved helpers in `ProofsInTheBook/Chapter20E2Frontier.lean`:

```lean
openSegment_edge_to_opposite_subset_interior_convexHull
exists_openSegment_to_sameSide_mem_interior_convexHull
```

The second helper is the local half-plane direction needed for the
`disjoint_int` step: if `m` is in the open side `ab` and `d` is on the same
strict signed side of `ab` as the opposite vertex `c`, then the ray from `m`
toward `d` contains a point in the interior of triangle `abc`.

Verification run:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter20E2Frontier.lean
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter20DissectionEngine.lean
```

Both commands pass.  The engine still reports exactly the two E2 `sorry`
warnings.  I did not run `lake build`.

Precise remaining blocker:

```lean
-- Formalize the finite-cover local incidence step.
-- For e = s(a,b), m = midpoint (coord a) (coord b):
-- 1. from h : e ∈ triAtomicEdges i, package the actual triangle side
--    (u,v) and opposite vertex w, prove m ∈ openSegment (coord u) (coord v);
-- 2. use exists_openSegment_to_sameSide_mem_interior_convexHull plus
--    disjoint_int to prove at most one incident triangle on each signed side;
-- 3. use closedness of each triangle hull, finiteness, cover, and
--    frontier_convexHull_triangle_of_doubleArea_ne_zero to show that every
--    triangle covering a sufficiently small point on either side of m is
--    incident with e;
-- 4. use midpoint-in-interior-of-square for ¬ OnSquareBoundary and
--    frontier_unitSquare for OnSquareBoundary to force respectively two
--    incident sides or one incident side.
```

The needed ingredients are now local and proved, but the final packaging and
finite-neighborhood cover argument remain open.

## Round 4 partial update

Added `ProofsInTheBook/Chapter20E2Cover.lean`.

Proved T1 as a standalone general-topology theorem, with the necessary
nonempty hypothesis:

```lean
theorem exists_subset_interior_of_preconnected_covered_closed
    {α : Type*} [TopologicalSpace α] {N : ℕ}
    (C : Fin N → Set α) (S : Set α)
    (hclosed : ∀ k, IsClosed (C k))
    (hdisj : ∀ k l, k ≠ l → Disjoint (interior (C k)) (interior (C l)))
    (hSpre : IsPreconnected S) (hSne : S.Nonempty)
    (hcover : S ⊆ ⋃ k, C k)
    (hfront : ∀ k, Disjoint S (frontier (C k))) :
    ∃ k, S ⊆ interior (C k)
```

The nonempty hypothesis is not optional: the handoff statement is false for
`N = 0`, `S = ∅`.

Also proved the connected part of T2:

```lean
def signedOpenHalfDisk (a b m : ℝ × ℝ) (ε σ : ℝ) : Set (ℝ × ℝ)
lemma doubleArea_affine_combo
lemma convex_signedOpenHalfDisk
lemma isPreconnected_signedOpenHalfDisk
```

New engine-side helpers added and verified:

```lean
triHull
triHull_closed
triHull_subset_unitSquare
exists_triHull_interior_of_preconnected
mem_triAtomicEdges_iff
ne_of_mk_mem_triAtomicEdges
midpoint_mem_openSegment_of_mem_sideAtomicEdges
midpoint_mem_openSegment_of_mem_triAtomicEdges
segment_subset_triHull_of_mem_sideAtomicEdges
segment_subset_triHull_of_mem_triAtomicEdges
segment_subset_unitSquare_of_mem_triAtomicEdges
midpoint_mem_unitSquare_of_mem_triAtomicEdges
segment_subset_frontier_unitSquare_of_midpoint_mem_frontier
```

Verification run:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean -o .lake/build/lib/lean/ProofsInTheBook/Chapter20E2Frontier.olean ProofsInTheBook/Chapter20E2Frontier.lean
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter20E2Cover.lean
PATH=$HOME/.elan/bin:$PATH lake env lean -o .lake/build/lib/lean/ProofsInTheBook/Chapter20E2Cover.olean ProofsInTheBook/Chapter20E2Cover.lean
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter20DissectionEngine.lean
```

`Chapter20E2Cover.lean` passes. `Chapter20DissectionEngine.lean` passes with
the original two E2 `sorry` warnings still present. I did not run `lake build`.

Precise remaining blocker:

The T2 edge-free half-disk step is not formalized. The handoff's key sentence

```text
m is not a vertex, hence no edge of D has m as an endpoint, so near m the only
triangle edges lie on the line L through coord a, coord b.
```

does not by itself rule out a triangle side crossing through `m` in its relative
interior. To close T2 from the current `SquareDissection` fields, the missing
local planar lemma is:

```lean
-- If e = s(a,b) is atomic for triangle i and
-- m ∈ openSegment (coord a) (coord b), then any triangle side of any k
-- whose closed segment contains m is collinear with coord a, coord b.
-- Otherwise the two triangle interiors have a common point near m,
-- contradicting D.disjoint_int.
```

After that lemma, the rest of T2 should follow by finite closed-frontier
avoidance: for triangles whose frontier does not contain `m`, choose a small
ball disjoint from that frontier; for frontiers containing `m`, the classified
collinear sides are avoided by the strict signed half-disk. Then T1 applies to
each half-disk and the two E2 statements reduce to the already proved
`atomicMult_eq_incidentTris_card`.

## Round 5 blocker

I stopped before editing the engine because the no-transversal lemma in
`HANDOFF/TASK_Ch20_E2_r5.md` is false as stated.

The missing hypothesis is that the crossing point `m` is not a vertex of the
second side, equivalently in this use case that the atomic-edge midpoint is not
any `D.coord z`.  The handoff statement only assumes

```lean
m ∈ openSegment ℝ (coord a) (coord b)
m ∈ segment ℝ (coord u) (coord v)
```

for the second side.  If `m` is an endpoint of `(u,v)`, this is a legal
T-junction and does not force interior overlap.

Concrete equal-area square dissection showing the issue:

```text
A = (0,0), E = (1,0), B = (1,1), D = (0,1),
C = (0,1/2), M = (1/2,1/2)

triangles:
  A E M
  E M B
  A B C
  C B D
```

All four triangle areas are `1/4`, and they tile the unit square with disjoint
interiors.  In triangle `A B C`, the side `A B` has `M` in its open segment.
In triangle `E M B`, the side `E M` contains `M` as an endpoint.  But

```text
doubleArea A B M = 0
doubleArea A B E = -1
```

so the side `E M` is not collinear with `A B`.  This directly contradicts the
round-5 no-transversal claim.  I verified the area and double-area arithmetic
with an exact rational-coordinate script:

```text
[1/4, 1/4, 1/4, 1/4], total area 1
M on AB: doubleArea = 0
E not on AB: doubleArea = -1
```

The intended lemma should be strengthened to require either
`m ∈ openSegment ℝ (coord u) (coord v)` or `∀ z : D.vtx, D.coord z ≠ m`.
That strengthened form matches the atomic-midpoint use, but it also requires
first proving the midpoint of an atomic edge is not a dissection vertex.  The
closed-segment version cannot be proved from `disjoint_int`, and using it would
make T2 unsound.

## Round 6 partial update

I proved the requested corrected midpoint lemma and the disjoint-interiors core
of the open-segment no-transversal lemma, but I did not close the two E2 theorem
bodies.

New proved helpers in `ProofsInTheBook/Chapter20DissectionEngine.lean`:

```lean
sideParam_eq_of_lineMap
sideParam_of_onSide
sideParam_left
sideParam_right
sideParam_mem_Icc_of_onSide
sideChain_pairwise
not_key_between_of_mem_consecutiveEdges_pairwise
midpoint_lineMap_average
midpoint_ne_vertex_of_mem_sideAtomicEdges
atomicEdge_midpoint_ne_vertex

no_transversal_openSegments_of_disjoint_int
```

The theorem

```lean
theorem atomicEdge_midpoint_ne_vertex {a b : D.vtx} (i : Fin D.n)
    (hmem : s(a, b) ∈ triAtomicEdges D i) (z : D.vtx) :
    D.coord z ≠ midpoint ℝ (D.coord a) (D.coord b)
```

is Lemma A.  It uses `sideParam` recovery from `lineMap`, pairwise sortedness of
the full side chain, and a generic “adjacent sorted edge has no strict key
between its endpoints” list lemma.

New proved helpers in `ProofsInTheBook/Chapter20E2Frontier.lean`:

```lean
doubleArea_eq_zero_of_mem_segment
doubleArea_direction_combo
doubleArea_direction_combo_uv
exists_common_interior_of_common_sameSide
exists_common_sameSide_of_transversal_directions
```

Together these prove the usable Lemma-B core in the engine:

```lean
lemma no_transversal_openSegments_of_disjoint_int
    {i k : Fin D.n} (hik : i ≠ k)
    {a b c u v w m : ℝ × ℝ}
    (hi : triHull D i = convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)))
    (hk : triHull D k = convexHull ℝ ({u, v, w} : Set (ℝ × ℝ)))
    (habc : doubleArea a b c ≠ 0) (huvw : doubleArea u v w ≠ 0)
    (hmab : m ∈ openSegment ℝ a b) (hmuv : m ∈ openSegment ℝ u v)
    (habuv : doubleArea a b (m + (v - u)) ≠ 0)
    (huvab : doubleArea u v (m + (b - a)) ≠ 0) :
    False
```

This is the open-segment transversal contradiction, expressed with the two
directional nonzero determinant hypotheses.  The proof constructs a point in
the intersection of the two required open half-planes, then uses
`exists_common_interior_of_common_sameSide` and `D.disjoint_int`.

Verification run:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean -o .lake/build/lib/lean/ProofsInTheBook/Chapter20E2Frontier.olean ProofsInTheBook/Chapter20E2Frontier.lean
PATH=$HOME/.elan/bin:$PATH lake env lean -o .lake/build/lib/lean/ProofsInTheBook/Chapter20E2Cover.olean ProofsInTheBook/Chapter20E2Cover.lean
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter20DissectionEngine.lean
```

All three commands pass.  `Chapter20DissectionEngine.lean` still reports exactly
the original two E2 `sorry` warnings.

Remaining gap:

The missing step is still the finite local-incidence/half-disk count, not Lemma
A or the open-transversal contradiction itself.  More concretely, one still has
to prove that, for the atomic midpoint `m`, every triangle frontier meeting a
sufficiently small strict half-disk is absent unless its side is collinear with
the atomic line, then apply `exists_triHull_interior_of_preconnected` to the two
half-disks and convert the resulting one/two local triangles into
`incidentTris` cardinality via `atomicMult_eq_incidentTris_card`.

## Round 8 partial update

Added and verified the Claim 1 layer in
`ProofsInTheBook/Chapter20DissectionEngine.lean`:

```lean
realSign
incidentOppSign
IncidentSideWitness
exists_incidentSideWitness
incidentTris_injOn_oppSign
```

The proof of `incidentTris_injOn_oppSign` follows the intended
`exists_common_interior_of_common_sameSide` + `D.disjoint_int` route.  It
recovers the actual triangle side containing the atomic edge, converts equality
of the atomic-base signs into same-side products, and contradicts disjoint
interiors.

I also added verified finite-frontier infrastructure for Claim 2:

```lean
triSideP
triSideQ
triSideR
triSideSegment
triSide_hull
triSide_nondeg
triSideSegment_closed
triSideSegment_nonempty
exists_triSide_of_mem_frontier_triHull
sideSegmentsNotContaining
minDistToSidesNotContaining
minDistToSidesNotContaining_pos
dist_lt_minDistToSidesNotContaining_not_mem
```

Verification:

```bash
/home/xhuan5/.elan/bin/lake env lean ProofsInTheBook/Chapter20DissectionEngine.lean
```

This passes, still with the two original E2 `sorry` warnings.  I did not run
`lake build`.

---

Round 9 complete.

Closed `Chapter20DissectionEngine.lean`:

```lean
incident_of_midpoint_mem_frontier_triHull
incidentOppSign_eq_of_signedOpenHalfDisk_subset_interior
exists_incident_of_signedOpenHalfDisk_subset_unitSquare
atomicMult_even_of_interior
atomicMult_eq_one_of_boundary
```

The realize-σ proof uses T1 on the signed open half-disk, then gets the
frontier midpoint into `incidentTris` by the overlap with the original
e-incident side.  The sign is transferred through `IncidentSideWitness` using
the interior half-plane product.

Counting is through `incidentTris_card_eq_image_card`, i.e.
`Finset.card_image_of_injOn`.  Interior realizes both signs.  Boundary uses the
same image-counting route, with the square-frontier product lemma showing every
incident opposite vertex has the same sign.

Verification:

```bash
PATH=/data/home/xhuan5/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter20DissectionEngine.lean
grep -n "sorry\|axiom" ProofsInTheBook/Chapter20DissectionEngine.lean || true
```

No `lake build`.
