# Chapter 35 gap probe: abstract planar `SimpleGraph` to five-colorability

Date: 2026-06-17.

Scope checked:

- Read `ProofsInTheBook/Chapter35.lean` and `ProofsInTheBook/ZinanCh35Final.lean`.
- Grepped local Mathlib under `.lake/packages/Mathlib/Mathlib` for planar graph, rotation-system, Euler-planar, and coloring APIs.
- Grepped this repo for `PlaneSimpleGraph`, `CombMap`, `NearTriangulation`, Euler, Kempe, and `FiveColorReducible` surfaces.

## Current endpoints

There are two separate proved endpoints.

1. `ProofsInTheBook.ZinanCh35Final.fiveColor_planar_canonical`:
   for `{M : CombMap D}`, `NearTriangulation M -> M.toSimpleGraph.Colorable 5`.
   This is the strong near-triangulation/Thomassen route endpoint.

2. `ProofsInTheBook.Chapter35.chapter35`:
   for arbitrary finite `SimpleGraph V`, `FiveColorReducible G -> G.Colorable 5`.
   This is a graph-theoretic certificate endpoint, not a planar graph theorem.

The missing theorem is not a small rewrite of either endpoint. It needs a bridge from an
abstract planar `SimpleGraph` statement to one of these certificate/model surfaces.

## Mathlib status

Confirmed by grep:

- No `SimpleGraph.Planar`, `PlanarGraph`, planar embedding, rotation-system, or planar Euler formula API was found in Mathlib's graph directories.
- The only `Planar graphs` hit in `Combinatorics/SimpleGraph/Coloring/VertexColoring.lean` is a TODO/comment section, not a definition or theorem.
- `Euler` hits in `Combinatorics/SimpleGraph` are Eulerian trails/circuits, not Euler's formula for plane graphs.

Useful confirmed Mathlib names:

- `SimpleGraph.Colorable.mono_left` restricts colorability along `G <= G'`.
- `SimpleGraph.Colorable.of_hom` pulls colorability back along graph homomorphisms.
- `SimpleGraph.Embedding` / notation `G ↪g H` exists, but this is abstract graph embedding, not topological/plane embedding.
- `SimpleGraph.sum_degrees_eq_twice_card_edges`, `SimpleGraph.exists_minimal_degree_vertex`, `minDegree`, `maxDegree` exist for finite graph counting, but no planar edge bound feeds them.

## Route A: abstract planar graph -> `NearTriangulation`

Target shape:

```lean
G planar -> exists (D) [Fintype D] [DecidableEq D] (M : CombMap D),
  NearTriangulation M ∧ G <= transported M.toSimpleGraph
```

Then use `fiveColor_planar_canonical` and restrict the coloring back to `G`.

### A1. Planarity predicate for abstract `SimpleGraph`

Status: missing in Mathlib.

No verified Mathlib object exists for `G.Planar` or a topological embedding predicate. This means the first public theorem cannot even be stated using a Mathlib planar predicate today.

Rating: [deep]. This is not a lemma gap; it is a missing theory surface.

### A2. Convert a planar embedding to `CombMap`

Repo status:

- `ProofsInTheBook/PlaneSimpleGraph.lean` defines `PlaneSimpleGraph V D` with fields `G`, `tail`, `head`, `α`, `σ`, dart reversal, `edge_darts`, and vertex rotation data.
- It has `PlaneSimpleGraph.toCombMap`.
- There is no theorem connecting `PlaneSimpleGraph.IsSphereMap` to `PlaneSimpleGraph.toCombMap.IsSphereMap`, no theorem equating `M.G` to `M.toCombMap.toSimpleGraph`, and grep shows no downstream use of `PlaneSimpleGraph` beyond its defining file and imports.

Concrete blocker: `PlaneSimpleGraph.IsSphereMap` is defined as
`numVertices - numEdges + numFaces = 2`, while `CombMap.IsSphereMap` is
`toCombMap.Connected ∧ toCombMap.eulerChar = 2`. The repo lacks bridge lemmas:

- `PlaneSimpleGraph.toCombMap_connected`
- `PlaneSimpleGraph.toCombMap_eulerChar_eq`
- `PlaneSimpleGraph.toCombMap_isSphereMap`
- `PlaneSimpleGraph.graph_iso_toCombMap_toSimpleGraph`

Rating: [medium] if starting from `PlaneSimpleGraph`; [deep] if starting from an external/topological planar embedding because the construction of `PlaneSimpleGraph` itself is absent.

### A3. Extend an arbitrary plane embedded graph to a near-triangulation

Repo status:

- The proved endpoint consumes `NearTriangulation M`.
- Existing near-triangulation structure requires a distinguished simple outer boundary cycle and all non-outer faces length 3.
- I did not find a theorem of the form `PlaneSimpleGraph/CombMap.IsSphereMap -> exists NearTriangulation extension` or "maximal planar supergraph".

Concrete blockers:

- define adding a noncrossing chord/diagonal inside a non-triangular face at `CombMap` level;
- prove it preserves `IsSphereMap`, simple graph, boundary cycle, and embeds the original graph as a subgraph;
- iterate by a well-founded measure on total face excess.

Rating: [deep]. This is a substantial new map-surgery theory, not tactic glue.

### A4. Restrict coloring from supergraph/subgraph

Status: done/trivial.

Mathlib already has `SimpleGraph.Colorable.mono_left`; I added local wrapper
`ProofsInTheBook.Chapter35.colorable_five_of_le`.

Rating: [shallow].

## Route B: abstract planar graph -> `FiveColorReducible`

Target shape:

```lean
G planar -> FiveColorReducible G
```

Then use `chapter35`.

### B1. Planar Euler degree seed

Mathlib status: absent for abstract `SimpleGraph`.

Repo status:

- `CombMap.FaceLengthGe`, `three_F_le_two_E`, `edge_bound`, and
  `CombMap.exists_vertexDegree_le_five` exist in `ProofsInTheBook/PlanarMapEuler.lean`.
- These are for `CombMap`, not arbitrary `SimpleGraph`.
- I added near-triangulation wrappers:
  - `NearTriangulation.faceLengthGe_three`
  - `NearTriangulation.three_le_V`
  - `NearTriangulation.exists_vertexDegree_le_five`

Concrete remaining blocker for route B: even for a `NearTriangulation M`, this degree is `M.vertexDegree v`, not yet bridged to `(M.toSimpleGraph).degree v`. For simple maps this should be provable using `M.IsSimpleGraph.no_parallel`, but the lemma is not present.

Rating:

- [shallow] for `NearTriangulation -> exists vertexDegree <= 5` (done).
- [medium] for `M.vertexDegree v = M.toSimpleGraph.degree v`.
- [deep] for abstract `SimpleGraph` planar `->` Euler seed, because the planar predicate/embedding is missing.

### B2. Degree <= 4 extension

Status: already present.

Confirmed names:

- `FiveColorReducible.step_of_degree_le_four`
- `coloring_extend_of_degree_le_four`
- `coloring_extend_of_neighbor_finset_le_four`

Rating: [done].

### B3. Degree = 5 Kempe step

Status: graph-theoretic Kempe swap core exists, planar separation input absent.

Confirmed names in `Chapter35.lean`:

- `swapColor`
- `swapColor_injective`
- `kempeSwap_proper_abstract`
- `coloring_extend_after_kempe_swap`

What it proves: if a finite set `S` is closed under `c1-c2` adjacency and after swapping colors on `S` the deleted vertex has a free color `c`, then the coloring extends.

What is missing: from a degree-5 planar configuration and a coloring of `G - v`, construct such an `S` and prove the required `hfree`. Classically this uses the cyclic order of the five neighbors around `v` and a Jordan/Kempe-chain separation lemma: not both relevant opposite-color Kempe chains can connect. None of that is available on arbitrary `SimpleGraph`.

Rating:

- [medium] for a purely graph-theoretic component API around `S` once the separation fact is assumed.
- [deep] for the planar separation theorem needed to produce the usable `S`.

### B4. Recursive certificate production

Status: absent.

`FiveColorReducible` is an inductive certificate. To prove it for planar graphs one must show deletion preserves planarity/embedding and recursively choose a vertex and either the degree-<=4 or degree-5 Kempe step. Without an abstract planar predicate and deletion-preservation API, this cannot start.

Rating: [deep] for abstract `SimpleGraph`; [medium/deep] inside `CombMap` depending on whether route uses the existing near-triangulation recursion or reimplements classical Kempe.

## Recommendation

Main attack should stay with route A's existing `NearTriangulation` endpoint, but do not try to start from Mathlib `SimpleGraph planar`; that object is absent. The practical next layer is an internal embedded-graph theorem:

```lean
theorem fiveColor_nearTriangulation_subgraph
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M)
    (G : SimpleGraph M.Vertex) (hG : G <= M.toSimpleGraph) :
    G.Colorable 5
```

This is now landed in `ProofsInTheBook.ZinanCh35Final`. It isolates the "subgraph restriction" end of route A and gives a clean target for future embedding/triangulation work.

After that, the next nontrivial internal lemma is:

```lean
theorem degree_toSimpleGraph_eq_vertexDegree
    {M : CombMap D} (hM : M.IsSimpleGraph) (v : M.Vertex) :
    M.toSimpleGraph.degree v = M.vertexDegree v
```

or a one-sided version enough for Euler:

```lean
theorem toSimpleGraph_degree_le_of_vertexDegree_le
    {M : CombMap D} (hM : M.IsSimpleGraph) {v : M.Vertex} :
    M.vertexDegree v <= 5 -> M.toSimpleGraph.degree v <= 5
```

This is a useful bridge for route B and for any degree-language reporting. The proof should count `σ`-orbit darts at `v` against neighbors, using `IsSimpleGraph.no_loop` and `IsSimpleGraph.no_parallel`.

## Landed shallow work

Added:

- `ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.faceLengthGe_three`
- `ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.three_le_V`
- `ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.exists_vertexDegree_le_five`
- `ProofsInTheBook.Chapter35.colorable_five_of_le`
- `ProofsInTheBook.ZinanCh35Final.fiveColor_nearTriangulation_subgraph`

Verification run:

```text
lake env lean ProofsInTheBook/PlanarMapNearTriangulation.lean
lake env lean ProofsInTheBook/Chapter35.lean
lake env lean ProofsInTheBook/ZinanCh35Final.lean
```

All three passed. The axiom audit for `fiveColor_nearTriangulation_subgraph` reports only
`propext`, `Classical.choice`, and `Quot.sound`. A grep for `sorry`/`axiom`/`admit`/`native_decide`
in the touched Lean files found no code occurrence; the only hit was a docstring in
`ZinanCh35Final.lean`.
