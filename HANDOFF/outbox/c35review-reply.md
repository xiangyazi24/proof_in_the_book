# Chapter 35 Thomassen design review

Verdict: the proposed route is viable, but two parts of `CH35_DESIGN_ANSWER.md` are too optimistic as stated.

1. The chord split cannot define sides by the full dual graph after only deleting the chord adjacency, because the old outer face touches both boundary arcs and reconnects the two sides. The side construction must split the outer face, or equivalently compute components only among non-outer faces and then add the selected boundary arc by hand.
2. The boundary deletion theorem needs an explicit non-base-case hypothesis. A single triangle is a near-triangulation, but deleting a boundary vertex leaves a one-edge map with Euler characteristic `2` and outer face length `2`, not a near-triangulation.
3. The color bookkeeping in the design answer is wrong/vague in Case 2. The book reserves two colors from `C(v0) \ {alpha}` and deletes those two colors only from the exposed fan vertices `v1, ..., vt`.

## Sources checked

I read:

- `HANDOFF/CH35_DESIGN_ANSWER.md`
- `HANDOFF/CH35_THOMASSEN_ROUTE.md`
- `HANDOFF/BOOK_CH34_FIVECOLOR.txt`
- `ProofsInTheBook/PlanarMap.lean`
- `ProofsInTheBook/PlanarMapEuler.lean`
- `ProofsInTheBook/PlanarMapDelete.lean`
- relevant Mathlib files under `.lake/packages/Mathlib/Mathlib/Combinatorics/SimpleGraph`

I also computed orbit counts for concrete CombMap permutations for:

- the single triangle map,
- deletion of one boundary vertex from that triangle,
- the tetrahedron map with one face chosen outer,
- deletion of one outer-boundary vertex from that tetrahedron.

## Core representation fixes

`NearTriangulation` should include an explicit outer boundary length condition:

```lean
outer_len_ge_three : 3 ≤ outerCycle.length
```

`outerCycle.VertexNodup` alone is not enough. After deleting a vertex from a single triangle, the resulting one-edge map has two distinct boundary vertices and `chi = 2`, but it is not bounded by a graph-theoretic cycle.

The primitive shape should be:

```lean
structure NearTriangulation (M : CombMap D) where
  sphere       : M.IsSphereMap
  simpleGraph  : M.IsSimpleGraph
  outerFace    : Face M
  outerCycle   : BoundaryCycle M outerFace
  outer_simple : outerCycle.VertexNodup
  outer_len    : 3 ≤ outerCycle.length
  inner_tri    : ∀ f : Face M, f ≠ outerFace → faceLen f = 3
```

`BoundaryCycle` should enumerate the face orbit by darts, and should separately expose:

- the cyclic dart list,
- the cyclic boundary vertex list,
- the cyclic boundary edge list,
- proof that the dart list is exactly the selected `phi`-orbit,
- proof that consecutive darts match the map orientation.

This avoids proving every boundary fact from quotient equality each time.

## Chord split: break points and corrected invariant

### Do not use the full dual graph with the old outer face

The design says to define the two sides through face adjacency in the dual after removing the chord edge. That is false if the old outer face remains a dual vertex: the old outer face is adjacent to inner faces along both boundary arcs, so it reconnects the two sides.

Correct construction:

1. Let `e = uv` be a boundary chord.
2. Prove `e` is incident to two distinct non-outer triangular faces, one on each side.
3. Form the face-adjacency graph on `Face M \ {outerFace}`, with adjacency across non-boundary, non-chord edges.
4. Remove only the adjacency across `e`.
5. Let the two non-outer face components seeded by the two chord-incident faces be `Faces₁` and `Faces₂`.
6. Add the chosen boundary arc to each side explicitly.
7. Replace the original chord alpha-pair by a fresh alpha-pair in each side.

The old outer face is not assigned to either side; it becomes two fresh outer faces.

### Duplicated chord darts are right, but face preservation must mention replacement

Duplicating the chord edge is the correct choice. However, the lemma

```lean
chordSplit_faces_preserved_inner
```

must not say inner faces are literally unchanged. The two old triangular faces incident to the chord contain one original chord dart; in the side maps they contain the corresponding fresh chord dart. The correct statement is:

```lean
Every non-outer face of a side is obtained from an old non-outer face of M
by replacing zero or one original chord dart with the fresh side chord dart.
```

### Filtered sigma needs a contiguity theorem

The filtered-rotation construction is the right generic mechanism, but it does not by itself prove the topological side is a disk. Around a vertex, the darts belonging to one side must form one contiguous interval of the old cyclic order, except for the two chord endpoints where the fresh chord dart closes the interval.

Without this, filtering can splice two separated wedges at the same vertex and silently change the boundary walk. The design should add:

```lean
lemma chordSplit_side_darts_contiguous_at_vertex
lemma chordSplit_filtered_sigma_faces_exact
```

These are the real hard lemmas behind "sigma stitching preserves genus".

### Euler counting for chord split

For a proper chord split with duplicated chord edge, the global sums should be:

```text
V₁ + V₂ = V + 2
E₁ + E₂ = E + 1
F₁ + F₂ = F + 1
```

The `+2` in vertices is from duplicating the two chord endpoints across the two side maps. The `+1` in edges is from counting the chord once in each side but once in the original. The `+1` in faces is from replacing the one old outer face by two new outer faces.

Thus `chi₁ + chi₂ = 4` when `chi = 2`. This is not enough inside the current CombMap API unless we also know each side is connected and has the expected face quotient. Do not state `chordSplit_euler_side₁` or `chordSplit_euler_side₂` as a pure count after defining alpha/sigma; it depends on the side face-classification theorem.

### Strictly smaller sides

`chordSplit_smaller` should be stated on graph vertices, not darts. For a proper boundary chord in a simple boundary cycle, both boundary arcs have at least one internal boundary vertex, so each side omits at least one original boundary vertex. Therefore both sides have strictly fewer original vertices than `M`.

The proof should use:

```lean
BoundaryCycle.two_arcs_internally_nonempty_of_chord
```

not only "proper chord" as a word.

## Boundary deletion: break points and corrected invariant

The existing `PlanarMapDelete.lean` already gives the right low-level deletion operation:

- `CombMap.vertexDarts`
- `CombMap.dartVertexDegree`
- `CombMap.deleteVertexSet`
- `CombMap.deleteVertex`
- `CombMap.deleteVertex_E`
- `CombMap.deleteVertex_V_of_orbitEquiv`
- `CombMap.VertexFacesDistinct`
- `CombMap.DeleteVertexFacesMerge`
- `CombMap.deleteVertex_F_of_facesMerge`
- `CombMap.deleteVertex_isSphereMap`

Use this operation. Do not define a parallel deletion operation.

### Single triangle breaks unconditional deletion

Concrete orbit count for a single triangle:

```text
V = 3, E = 3, F = 2, chi = 2.
```

Deleting one boundary vertex removes two incident edges and merges the old outer face with the one inner triangular face:

```text
V' = 2, E' = 1, F' = 1, chi' = 2.
```

The resulting map is a single edge with one face of length `2`. It is a sphere map, but not a near-triangulation if `outer_len ≥ 3` is part of the definition. Therefore:

```lean
deleteBoundaryVertex_nearTriangulation
```

must assume either `3 < M.V` or an equivalent non-base-case/fan-nonempty hypothesis.

The Thomassen induction already has base case `|V| = 3`, so this is not a mathematical problem. It is a statement-design problem.

### Tetrahedron check

For the tetrahedron with an outer triangular face:

```text
V = 4, E = 6, F = 4, chi = 2.
```

Deleting one outer-boundary vertex of degree `3` gives:

```text
V' = 3, E' = 3, F' = 2, chi' = 2.
```

This is the good boundary-length-3 case: `t = 1`, the exposed fan path is `x - z₁ - w`, and the new map is a triangle. Boundary length `3` is not itself bad; the bad case is `t = 0`, which occurs only in the base triangle under chordlessness.

### Fan cases

Let the boundary order near the deleted vertex be:

```text
v0, x, y, ..., w, v0
```

and the neighbors of `v0` in rotation order be:

```text
x, z₁, ..., z_t, w.
```

Correct facts:

- If `t = 0` and the outer boundary length is greater than `3`, then the edge `xw` is a boundary chord. Hence in the chordless non-base case, `t ≥ 1`.
- If the outer boundary length is `3` and `t = 0`, the whole graph is the base triangle and deletion must not be used.
- If the outer boundary length is `3` and `M.V > 3`, then `t ≥ 1`; the tetrahedron is the minimal example.

Add these lemmas explicitly:

```lean
lemma fan_nonempty_of_chordless_of_not_triangle
lemma fan_empty_iff_base_triangle_of_chordless
```

or use a single deletion theorem with `0 < fan.lengthInterior`.

### Chordlessness is used less than the design says

Chordlessness is needed to prove the exposed fan path is simple and meets the old boundary only at `x` and `w`.

It is not necessary to prove that the deleted map is chordless. The recursive induction theorem applies to all near-triangulations; if the deleted map has a chord, the induction handles it through Case 1. Therefore do not spend effort proving:

```lean
deleted outer boundary has no chord
```

It is stronger than needed and likely false in natural examples.

### Euler count for deletion

If `deg(v0) = t + 2`, then the old face classes touched by `v0` are:

```text
old outer face + (t + 1) inner triangular faces
```

so the count is:

```text
V' = V - 1
E' = E - (t + 2)
F' = F - (t + 1)
```

Equivalently, in the existing `PlanarMapDelete.lean` notation:

```text
F' = F - dartVertexDegree(v0) + 1
```

Do not prove a new arithmetic lemma. Prove the near-triangulation hypotheses imply the existing hypotheses:

```lean
NoLoopAt v0
VertexFacesDistinct v0
DeleteVertexFacesMerge v0
vertex quotient equivalence for deleteVertex
Connected (deleteVertex v0)
```

Then reuse `deleteVertex_isSphereMap`.

## Correct Case 2 color bookkeeping

The book's Case 2 invariant is exact and should be copied.

Setup:

- `x,y` are adjacent on the old outer boundary.
- `x` has fixed color `alpha`.
- `y` has fixed color `beta`.
- `v0` is the other boundary neighbor of `x`.
- Neighbors of `v0` in rotation order are:

```text
x, v₁, ..., v_t, w
```

where `v₁, ..., v_t` are the exposed fan vertices. In the chordless non-base case they are interior vertices of the old graph.

Pick two distinct colors:

```text
gamma, delta ∈ C(v0) \ {alpha}
```

This is possible because `|C(v0)| ≥ 3`; even if `alpha ∈ C(v0)`, at least two colors remain.

Define the lists on `G - v0` by:

```text
C'(v_i) = C(v_i) \ {gamma, delta}   for i = 1, ..., t
C'(u)   = C(u)                       for every other remaining vertex u
```

Do not subtract `alpha` from every neighbor. Do not choose colors from `C(w)`. Do not modify `x`, `y`, or `w`.

Why the induction hypotheses hold:

- `x` and `y` stay precolored by singleton lists `{alpha}` and `{beta}`.
- Every old outer-boundary vertex other than `x,y,v0` keeps list size at least `3`.
- Each exposed fan vertex `v_i` was interior before deletion, so `|C(v_i)| ≥ 5`; after deleting two colors, `|C'(v_i)| ≥ 3`, exactly what is needed for new boundary vertices.
- Every remaining interior vertex keeps list size at least `5`.

Extension after coloring `G - v0`:

- `x` has color `alpha`, and `gamma, delta ≠ alpha`.
- Every fan vertex `v_i` was colored from a list with `gamma,delta` removed.
- `w` has one color; choose whichever of `gamma, delta` is not the color of `w`.

Lean-facing lemma:

```lean
lemma deleteBoundaryVertex_thomassenLists
    (hNT : NearTriangulation M)
    (hNoChord : BoundaryChordless hNT.outerCycle)
    (hNotBase : 3 < M.V)
    (hLists : ThomassenLists M hNT x y L alpha beta)
    (hv0 : v0 is the boundary neighbor of x different from y)
    (hgamma : gamma ∈ L v0)
    (hdelta : delta ∈ L v0)
    (hga : gamma ≠ alpha)
    (hda : delta ≠ alpha)
    (hgd : gamma ≠ delta) :
    ThomassenLists (M.deleteVertex v0) hNT_deleted x y
      (deleteFanLists L fan gamma delta) alpha beta
```

and:

```lean
lemma deleteBoundaryVertex_extend_coloring
```

for the final choice of `gamma` or `delta` at `v0`.

## Mathlib graph API inventory

Confirmed in local Mathlib source.

Useful existing names:

- Connectivity:
  - `SimpleGraph.Reachable`
  - `SimpleGraph.Preconnected`
  - `SimpleGraph.Connected`
  - `SimpleGraph.reachable_iff_reflTransGen`
  - `SimpleGraph.Reachable.exists_isPath`
  - `SimpleGraph.Preconnected.exists_isPath`
  - `SimpleGraph.Connected.exists_isPath`
- Connected components:
  - `SimpleGraph.ConnectedComponent`
  - `SimpleGraph.connectedComponentMk`
  - `SimpleGraph.ConnectedComponent.supp`
  - `SimpleGraph.ConnectedComponent.toSimpleGraph`
  - `SimpleGraph.ConnectedComponent.connected_toSimpleGraph`
  - `SimpleGraph.colorable_iff_forall_connectedComponents`
- Subgraphs:
  - `SimpleGraph.Subgraph`
  - `SimpleGraph.Subgraph.Preconnected`
  - `SimpleGraph.Subgraph.Connected`
  - `SimpleGraph.Subgraph.deleteVerts`
  - `SimpleGraph.Subgraph.deleteVerts_adj`
  - `SimpleGraph.Subgraph.coeDeleteVertsIso`
  - `SimpleGraph.Subgraph.connected_sup`
  - `SimpleGraph.ConnectedComponent.toSubgraph`
  - `SimpleGraph.ConnectedComponent.maximal_subgraph_connected_iff`
- Bridges and edge connectivity:
  - `SimpleGraph.IsBridge`
  - `SimpleGraph.isBridge_iff`
  - `SimpleGraph.isBridge_iff_mem_and_forall_cycle_notMem`
  - `SimpleGraph.Connected.connected_delete_edge_of_not_isBridge`
  - `SimpleGraph.IsEdgeReachable`
  - `SimpleGraph.IsEdgeConnected`
  - `SimpleGraph.isEdgeReachable_two`
  - `SimpleGraph.isEdgeConnected_two`
  - `SimpleGraph.isBridge_iff_adj_and_not_isEdgeConnected_two`
- Coloring:
  - `SimpleGraph.Coloring`
  - `SimpleGraph.Coloring.mk`
  - `SimpleGraph.Coloring.valid`
  - `SimpleGraph.Colorable`
  - `SimpleGraph.Colorable.mono`
  - `SimpleGraph.Colorable.of_hom`
- Walk/path/cycle:
  - `G.Walk u v`
  - `G.Path u v`
  - `SimpleGraph.Walk.IsPath`
  - `SimpleGraph.Walk.IsCycle`
  - `SimpleGraph.Walk.toSubgraph`

What I did not find in Mathlib:

- vertex 2-connectivity / biconnectivity;
- `IsCutVertex` or articulation vertices;
- blocks as maximal 2-connected subgraphs;
- block-cut tree;
- ear decomposition;
- graph-theoretic planar embeddings or planar graph API for this purpose.

Important: Mathlib's `IsEdgeConnected` is edge connectivity, not vertex connectivity. It does not give the block layer needed for cut vertices.

## Corrected file plan

Use flat filenames consistent with the existing repo. Each file below should have exactly one writer.

### Near-triangulation core

1. `ProofsInTheBook/PlanarMapSimple.lean`
   - Imports: `PlanarMapEuler`
   - Defines `Vertex M`, `Face M`, edge endpoints from darts, graph adjacency on vertex quotients.
   - Defines `CombMap.IsSimpleGraph` as no loops plus no parallel edges.
   - Proves simple consequences: `NoLoopAt`, triangular face has three distinct vertices, boundary edge uniqueness.

2. `ProofsInTheBook/PlanarMapBoundary.lean`
   - Imports: `PlanarMapSimple`
   - Defines `BoundaryCycle`, `BoundaryPath`, boundary vertex/edge lists, cyclic arcs.
   - Proves face-orbit enumeration, arc decomposition, chord definition, chordless boundary predicate.

3. `ProofsInTheBook/PlanarMapNearTriangulation.lean`
   - Imports: `PlanarMapBoundary`
   - Defines `NearTriangulation`.
   - Includes `outer_len : 3 ≤ outerCycle.length`.
   - Proves basic facts: no boundary loops, boundary vertices have degree at least two, inner triangular faces have distinct vertices, chord endpoints are nonadjacent on boundary.

Build order: `PlanarMapSimple` -> `PlanarMapBoundary` -> `PlanarMapNearTriangulation`.

### Generic rotation and surgeries

4. `ProofsInTheBook/PlanarMapFilteredRotation.lean`
   - Imports: `PlanarMapNearTriangulation`, `PlanarMapDelete`
   - Packages generic filtered cyclic rotations on subtypes and finite sums with fresh darts.
   - Reuses `Equiv.Perm.deleteSet` where possible.
   - Proves alpha/sigma permutation boilerplate for side maps.

5. `ProofsInTheBook/PlanarMapChordSplitData.lean`
   - Imports: `PlanarMapFilteredRotation`
   - Defines chord side data:
     - two boundary arcs,
     - non-outer face components after deleting chord adjacency,
     - side dart sets,
     - fresh chord darts.
   - Proves side partition and endpoint duplication count.

6. `ProofsInTheBook/PlanarMapChordSplit.lean`
   - Imports: `PlanarMapChordSplitData`
   - Defines the two side `CombMap`s.
   - Proves side alpha/sigma valid, face classification, outer boundaries, connectedness, Euler characteristic, near-triangulation, and strict vertex decrease.

7. `ProofsInTheBook/PlanarMapBoundaryFan.lean`
   - Imports: `PlanarMapNearTriangulation`
   - Proves fan existence around a boundary vertex.
   - Proves fan distinctness under chordlessness.
   - Proves `t = 0` is only the base triangle in the chordless case.

8. `ProofsInTheBook/PlanarMapBoundaryDelete.lean`
   - Imports: `PlanarMapBoundaryFan`, `PlanarMapDelete`
   - Reuses `CombMap.deleteVertex`.
   - Proves the near-triangulation hypotheses imply the existing deletion hypotheses:
     `NoLoopAt`, vertex quotient equivalence, `VertexFacesDistinct`, `DeleteVertexFacesMerge`, connectedness.
   - Proves deleted outer boundary and `deleteBoundaryVertex_nearTriangulation`.

Parallel build groups:

- After file 3, files 4 and 7 can proceed in parallel.
- After file 4, file 5 can proceed.
- After files 5 and 7, files 6 and 8 are independent enough for separate writers.

### List coloring and Thomassen induction

9. `ProofsInTheBook/Chapter35ListColoring.lean`
   - Imports: `Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring`
   - Defines list coloring over `SimpleGraph`:
     ```lean
     structure ListColoring (G : SimpleGraph V) (L : V → Finset Color)
     ```
   - Proves restriction, edge-monotonicity, union/glue on overlap, rooted cut-vertex glue.
   - This can start immediately; it does not depend on CombMap surgery.

10. `ProofsInTheBook/Chapter35ThomassenLists.lean`
    - Imports: `PlanarMapChordSplit`, `PlanarMapBoundaryDelete`, `Chapter35ListColoring`
    - Defines `ThomassenLists`.
    - Proves:
      - chord split list validity on side 1,
      - chord split list validity on side 2 after side 1 colors the chord endpoints,
      - deletion list validity with `gamma,delta` removed only from fan vertices,
      - deletion coloring extension.

11. `ProofsInTheBook/Chapter35ThomassenNear.lean`
    - Imports: `Chapter35ThomassenLists`
    - Proves the strengthened near-triangulation list theorem by induction on vertex count.
    - Gives uniform-list corollary for near-triangulations.

Build order: file 9 can be written in parallel with surgery files; file 10 waits for files 6, 8, 9; file 11 waits for file 10.

### Bridge to arbitrary simple sphere maps

Do this after the near-triangulation theorem is stable. This layer is substantial and mostly not supplied by Mathlib.

12. `ProofsInTheBook/SimpleGraphBlocks.lean`
    - Imports: Mathlib SimpleGraph connectivity files.
    - Defines vertex deletion connectivity, cut vertices, rooted blocks, block graph/block-cut tree.
    - Proves decomposition and rooted coloring glue.
    - Must be built from scratch; Mathlib only has connected components, not blocks.

13. `ProofsInTheBook/PlanarMapBlockEmbedding.lean`
    - Imports: `PlanarMapNearTriangulation`, `SimpleGraphBlocks`
    - Shows each block of a simple sphere CombMap inherits a sphere embedding.
    - Proves 2-connected block face boundaries are simple cycles.

14. `ProofsInTheBook/PlanarMapFaceDiagonal.lean`
    - Imports: `PlanarMapBlockEmbedding`
    - Defines diagonal insertion into a simple-cycle face of length at least four.
    - Proves simplicity, Euler preservation, and face-length measure decrease.

15. `ProofsInTheBook/PlanarMapTriangulationCompletion.lean`
    - Imports: `PlanarMapFaceDiagonal`
    - Repeatedly inserts diagonals in each 2-connected block to produce a near-triangulation supergraph.
    - Proves coloring of the supergraph restricts to the original block.

16. `ProofsInTheBook/Chapter35SphereMapFiveColor.lean`
    - Imports: `Chapter35ThomassenNear`, `PlanarMapTriangulationCompletion`
    - Colors each block with prescribed articulation color.
    - Glues along the block-cut tree.
    - Final theorem:
      ```lean
      theorem sphereMap_simple_five_colorable :
        M.IsSphereMap → M.IsSimpleGraph → (underlyingSimpleGraph M).Colorable 5
      ```

Bridge files 12 and 13 can begin in parallel only after the exact underlying graph API in file 1 is stable. Files 14-16 are linear.

## Endpoint recommendation

Keep two endpoints:

```lean
theorem thomassen_nearTriangulation_listColorable
```

for the book-faithful theorem over near-triangulations, and:

```lean
theorem sphereMap_simple_five_colorable
```

for the Chapter 34/35 headline over arbitrary simple sphere maps.

Do not try to make arbitrary simple sphere maps list-colorable through naive block gluing. Rooted list gluing is valid, but the clean final global theorem should be plain `5`-colorability unless we also invest in a fully rooted list-coloring block theorem.
