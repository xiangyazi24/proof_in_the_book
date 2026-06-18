Route **A** is the shortest honest path from your already-proven near-triangulation theorem to a general combinatorial-planar theorem. Route **B** is attractive because the graph-theoretic `FiveColorReducible` machinery already exists, but it still needs the degree-5 Kempe separation theorem from the embedding, plus planarity preservation under deletion/induced subgraphs. That is at least as hard as the triangulation route, and it does not reuse your clean Thomassen near-triangulation endpoint as directly.

The repo facts line up this way: `PlaneSimpleGraph` is currently a simple graph plus dart data, edge involution, vertex rotation, edge realization, vertex-cycle facts, and graph connectedness; it forgets to a `CombMap` by keeping only `α` and `σ`, and its own sphere predicate is just `eulerChar = 2`. fileciteturn120file0L18-L39 fileciteturn120file0L45-L67 The lower `CombMap.IsSphereMap` is `Connected ∧ eulerChar = 2`. fileciteturn123file0L24-L79 So the missing bridge is not abstract graph planarity; it is the combinatorial-map extension from an arbitrary sphere embedding to a triangulated sphere supermap.

## 1. Route ranking

**Best: Route A, triangulate the combinatorial sphere map.**  
It has one hard geometric/combinatorial-map theorem: every simple connected sphere map can be extended by adding face diagonals until all faces are triangles, while preserving the old graph as a subgraph. Once you have that, your theorem is basically:

```lean
triangulate P hsphere → hNT : NearTriangulation T
fiveColor_planar_canonical hNT
restrict coloring to P.G
```

**Second: Route B, Kempe reducibility.**  
The repo’s `FiveColorReducible` is ready to consume either a degree-≤4 extension step or an abstract Kempe-swap step. The degree-≤4 constructor is proved. The degree-5 branch still needs a planar Kempe-chain separation theorem: choose a degree-5 vertex, use the cyclic neighbor order from the embedding, show two relevant Kempe chains cannot both connect alternating neighbor pairs, and produce the finite Kempe component satisfying the closure/free-color hypotheses. The `chapter35` theorem explicitly says the missing frontier is the planar instantiation of `FiveColorReducible`. fileciteturn125file0L152-L174 fileciteturn125file0L189-L217

So I would rank:

1. **Route A**: one map-surgery campaign, then direct use of Thomassen.
2. **Route B**: graph induction plus deletion embedding plus degree-5 Kempe separation; more moving parts and less reuse of your `NearTriangulation` theorem.

## 2. Recommended Route A decomposition

### Target interface

Do not try to make `PlaneSimpleGraph.toCombMap` itself a near-triangulation. Instead build a supermap certificate:

```lean
structure PlaneTriangulationExtension
    (P : PlaneSimpleGraph V D) where
  D' : Type*
  instFintypeD' : Fintype D'
  instDecEqD' : DecidableEq D'

  T : CombMap D'
  hNT : NearTriangulation T

  ιV : V → T.Vertex

  -- Every old edge is an edge in the triangulated map.
  adj_embed :
    ∀ {u v : V}, P.G.Adj u v → T.toSimpleGraph.Adj (ιV u) (ιV v)

  -- Optional but useful:
  ιV_inj : Function.Injective ιV
```

Then the final coloring restriction is easy:

```lean
theorem colorable_of_triangulationExtension
    (P : PlaneSimpleGraph V D)
    (E : PlaneTriangulationExtension P) :
    P.G.Colorable 5 := by
  classical
  rcases fiveColor_planar_canonical E.hNT with ⟨C⟩
  refine ⟨SimpleGraph.Coloring.mk (fun v => C (E.ιV v)) ?_⟩
  intro u v huv
  exact C.valid (E.adj_embed huv)
```

This avoids needing a `SimpleGraph.Colorable.mono` lemma. You just pull the coloring back along `ιV`.

### Sphere bridge first

Prove a bridge:

```lean
theorem PlaneSimpleGraph.toCombMap_connected
    (P : PlaneSimpleGraph V D)
    (hNontrivial : Nonempty D) :
    P.toCombMap.Connected := ...
```

Use `P.connected : P.G.Connected`, `P.edge_darts`, and `σ_vertex_cycle`. A dart step lets you move within a vertex orbit by `σ.SameCycle` and across an edge by `α`. Given darts `a b`, connect `tail a` to `tail b` in `P.G`; lift each graph edge on the path to a dart by `edge_darts`; stitch using vertex-cycle moves.

Then prove the count bridge:

```lean
theorem PlaneSimpleGraph.toCombMap_V_eq
    (P : PlaneSimpleGraph V D)
    (hNoIsolated : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.V = Fintype.card V := ...
```

Key map:

```lean
P.toCombMap.Vertex ≃ V
```

defined by lifting `P.tail` over `σ`-orbits; well-defined by `σ_preserves_tail`, injective/surjective by `σ_vertex_cycle` and `hNoIsolated`.

Also:

```lean
P.toCombMap.E = P.numEdges
P.toCombMap.F = P.numFaces
P.toCombMap.eulerChar = P.eulerChar
```

`E = |D|/2` follows from `CombMap.two_mul_E_eq_card` on the `CombMap` side and `PlaneSimpleGraph.numEdges = Fintype.card D / 2` on the `PlaneSimpleGraph` side. The repo already proves every `CombMap` edge has two darts. fileciteturn123file0L107-L135

Then:

```lean
theorem PlaneSimpleGraph.toCombMap_isSphereMap
    (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap)
    (hNontrivial : Nonempty D)
    (hNoIsolated : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.IsSphereMap := by
  exact ⟨P.toCombMap_connected hNontrivial, by
    -- rewrite eulerChar via the count bridge
    simpa [PlaneSimpleGraph.IsSphereMap] using hsphere⟩
```

Small graphs with no darts or isolated vertices should be handled separately by direct coloring; do not force them through `CombMap`.

### Simple-graph bridge

Prove:

```lean
theorem PlaneSimpleGraph.toCombMap_isSimpleGraph
    (P : PlaneSimpleGraph V D) :
    P.toCombMap.IsSimpleGraph := ...
```

Use:

* `dart_edge : P.G.Adj (tail d) (head d)` to rule out loops.
* `edge_darts : G.Adj u v → ∃! d, tail d = u ∧ head d = v` to rule out parallel darts with same endpoints.

`CombMap.IsSimpleGraph` asks for no dart loop and no parallel map edge: no loop and no two darts with the same unordered quotient endpoints unless they are in the same `α`-cycle. fileciteturn127file0L98-L107

This proof is medium, not the bottleneck.

## 3. The hard core: face diagonal insertion

You want a one-step surgery:

```lean
structure FaceDiagonalChoice (M : CombMap D) where
  f : M.Face
  d0 d1 : D
  same_face : M.dartFace d0 = f
  same_face' : M.dartFace d1 = f
  nonadjacent_on_face : ...
  endpoints_distinct : M.tail d0 ≠ M.tail d1
  no_existing_edge :
    ¬ M.toSimpleGraph.Adj (M.tail d0) (M.tail d1)
```

Then:

```lean
def addFaceDiagonal
    (M : CombMap D) (c : FaceDiagonalChoice M) :
    CombMap (D ⊕ Fin 2) := ...
```

Use the repo’s `freshMap` infrastructure as the primitive. It adds two fresh darts, pairs them by a fresh `α`, and splices one fresh dart after each chosen anchor in the vertex rotation. The file describes exactly this construction: `freshAlpha` swaps the two fresh darts, `freshSigma` inserts them after anchors, and `freshMap` packages the resulting `CombMap`. fileciteturn130file0L3-L14 fileciteturn130file0L179-L187

For a face diagonal, the anchors should be the correct darts at the two endpoint vertices so that the new edge is inserted **inside the selected face**. This is the same kind of orientation bookkeeping as chord insertion: if the selected face boundary has cyclic order

```text
... a ... b ...
```

then the two fresh darts must be spliced at the two corners bounding the face arcs so that the old face splits into two face cycles.

### One-step theorem

The one-step theorem should return a structured certificate, not just the new map:

```lean
structure FaceDiagonalInsertion
    (M : CombMap D) (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph)
    (c : FaceDiagonalChoice M) where
  D' : Type*
  instFintypeD' : Fintype D'
  instDecEqD' : DecidableEq D'
  M' : CombMap D'

  includeDart : D → D'
  includeVertex : M.Vertex → M'.Vertex

  sphere : M'.IsSphereMap
  simple : M'.IsSimpleGraph

  old_adj_embed :
    ∀ {u v : M.Vertex}, M.toSimpleGraph.Adj u v →
      M'.toSimpleGraph.Adj (includeVertex u) (includeVertex v)

  -- Count facts
  V_eq : M'.V = M.V
  E_eq : M'.E = M.E + 1
  F_eq : M'.F = M.F + 1

  -- Face-length/excess facts
  faceExcess_decrease :
    faceExcess M' < faceExcess M
```

The count/euler part is the easy part:

```lean
V' = V
E' = E + 1
F' = F + 1
χ' = V - (E+1) + (F+1) = χ
```

For `V' = V`, use the fact fresh darts are inserted into existing vertex rotations, so no new vertex orbit is created. The repo already has a vertex-orbit argument for `freshMap` in the chord Euler layer, but if it is specialized, factor it into a generic `freshMap_V` lemma.

For `E' = E + 1`, `freshAlpha` adds one new α-orbit. The generic `freshMap` edge-count theorem is the same shape as the existing chord-split Euler accounting.

For `F' = F + 1`, this is the real face-split lemma: the selected face orbit splits into two orbits; all other face orbits are unchanged. This is the map-surgery heart.

### Simplicity

`M'.IsSimpleGraph` needs:

1. Old edges remain simple/unique.
2. The fresh edge is not a loop: endpoints distinct.
3. The fresh edge is not parallel to an old edge: `no_existing_edge`.
4. The two fresh darts are paired by `α`, so they are not parallel to each other except as the same edge.

The no-existing-edge condition is why the diagonal choice must be between nonadjacent face vertices.

### Existence of a diagonal choice

For a face of length `k > 3`, you need:

```lean
theorem exists_face_diagonal_choice
    (M : CombMap D) (hSphere : M.IsSphereMap) (hSimple : M.IsSimpleGraph)
    {f : M.Face} (hlen : 3 < M.faceLen f)
    (hFaceSimple : faceBoundarySimple M f) :
    ∃ c : FaceDiagonalChoice M, c.f = f := ...
```

This is where the first Jordan-type fact appears. You need to know a nontriangular face has a pair of nonconsecutive boundary vertices with no existing edge, or at least one valid noncrossing diagonal. In a fully cellular sphere embedding this is true, but formalizing it requires a face-boundary simplicity/no-chord lemma. It is probably the hardest lemma in Route A.

Do not bury it. Name it:

```lean
structure FaceTriangulationOracle (M : CombMap D) where
  face_boundary_simple : ∀ f, FaceBoundarySimple M f
  diagonal_exists :
    ∀ f, 3 < M.faceLen f → ∃ c : FaceDiagonalChoice M, c.f = f
```

Then later prove the oracle from a stronger `PlaneSimpleGraph` embedding contract.

### Measure for recursion

Use total face excess:

```lean
def faceExcess (M : CombMap D) : ℕ :=
  ∑ f : M.Face, M.faceLen f - 3
```

provided you have `3 ≤ M.faceLen f` for all faces. If face boundaries may repeat or have length 1/2 because of bridges, either handle those maps separately or strengthen the input to a 2-cell simple embedding with face length ≥3.

The key theorem:

```lean
theorem faceExcess_eq_zero_iff_all_triangles
    (hLen : ∀ f, 3 ≤ M.faceLen f) :
    faceExcess M = 0 ↔ ∀ f, M.faceLen f = 3 := ...
```

One diagonal insertion into a face of length `k > 3` splits it into lengths `r + 1` and `k - r + 1`, both at least `3`, and the excess changes:

```text
old excess: k - 3
new excess: (r + 1 - 3) + (k - r + 1 - 3) = k - 4
```

so it decreases by exactly `1`.

Then define:

```lean
noncomputable def triangulateByFaceExcess
    (M : CombMap D) (hSphere : M.IsSphereMap) (hSimple : M.IsSimpleGraph)
    (hLen : ∀ f, 3 ≤ M.faceLen f)
    (oracle : FaceTriangulationOracle M) :
    TriangulatedSupermap M
```

by well-founded recursion on `faceExcess`.

At the end, choose any triangular face as the outer face and build a `NearTriangulation`. A `NearTriangulation` requires a sphere map, simple graph, an outer face with a boundary cycle, simple outer boundary, length at least three, and all other faces triangular. The structure fields are exactly these. fileciteturn55file0L20-L30

For the final all-triangle map, building `BoundaryCycle` for a triangular face should be much easier than for arbitrary faces: use `boundaryCycleOfFace` from the face dart list and supply a small `arcSplit` for a 3-cycle. The triangular face vertex distinctness follows from `IsSimpleGraph`; the repo already proves triangular face vertices are pairwise distinct. fileciteturn127file0L140-L174

## 4. Route B skeleton, and why I would not start there

The degree-5 route would need:

```lean
theorem planeSimpleGraph_fiveColorReducible
    (P : PlaneSimpleGraph V D) (hsphere : P.IsSphereMap) :
    FiveColorReducible P.G := ...
```

The induction step requires a vertex `v`. If `degree v ≤ 4`, existing constructor works:

```lean
FiveColorReducible.step_of_degree_le_four
```

which is already proved. fileciteturn125file0L176-L188

For `degree v = 5`, you must produce the second branch of `FiveColorReducible.step` for every coloring `C` of `G - v`:

```lean
∃ c1 c2 c, c1 ≠ c2 ∧
  ∃ S : Finset ({x | x ≠ v}),
    kempe component closed under c1/c2 adjacency
    ∧ after swapping S, color c is free on all neighbors of v
```

The abstract swap preservation is already proved as `coloring_extend_after_kempe_swap`, using `kempeSwap_proper_abstract`. fileciteturn125file0L107-L151

But the missing theorem is the planar separation lemma:

```lean
degree v = 5
neighbors in cyclic order n0 n1 n2 n3 n4
coloring of G - v uses all five colors on neighbors
→ one of the required Kempe pairs is not connected
```

That proof needs:
* deletion of `v` preserving an embedding of `G - v`,
* neighbor cyclic order around `v`,
* Kempe components as embedded subgraphs,
* a Jordan separation argument saying two alternating Kempe chains cannot cross.

This is a full planar-topological argument. Given your current assets, it is not shorter than triangulation.

## 5. Non-vacuity witness

Use the triangle, not the empty graph. The empty graph is trivially colorable but does not validate the rotation-system/face machinery. A triangle exercises:

```text
V = 3, E = 3, F = 2, χ = 2
```

Concrete data:

```lean
abbrev TriV := Fin 3
abbrev TriD := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

def triTail (d : TriD) : TriV := d.1.1
def triHead (d : TriD) : TriV := d.1.2

def triAlpha : Equiv.Perm TriD :=
  -- swap ordered pair (a,b) ↦ (b,a)
  ...

def triSigma : Equiv.Perm TriD :=
  -- at each tail vertex, swap the two outgoing darts
  -- choose the cyclic order compatible with the two triangular faces
  ...
```

Then:

```lean
def trianglePlaneSimpleGraph : PlaneSimpleGraph TriV TriD where
  G := ⊤   -- or the complete graph on Fin 3
  tail := triTail
  head := triHead
  α := triAlpha
  σ := triSigma
  ...
```

Prove:

```lean
example : trianglePlaneSimpleGraph.IsSphereMap := by
  -- V=3, E=3, F=2, so eulerChar=2
  native_decide -- avoid in final theorem if your discipline forbids it;
                -- for witness debugging it is fine, or prove by enumeration.
```

For a clean non-vacuity theorem, avoid `native_decide` and prove by finite enumeration:

```lean
theorem triangle_plane_isSphere :
    trianglePlaneSimpleGraph.IsSphereMap := by
  unfold PlaneSimpleGraph.IsSphereMap PlaneSimpleGraph.eulerChar
  -- simp [numVertices, numEdges, numFaces, trianglePlaneSimpleGraph]
  norm_num
```

Then the final theorem gives:

```lean
example : trianglePlaneSimpleGraph.G.Colorable 5 :=
  fiveColor_planeSimpleGraph trianglePlaneSimpleGraph triangle_plane_isSphere
```

If Route A is finished, the triangulation extension of the triangle is the identity: it is already all triangular.

## Bottom line

Build Route A.

The honest theorem should look like:

```lean
theorem fiveColor_planeSimpleGraph
    (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap)
    (hNoSmall : 3 ≤ Fintype.card V) -- or handle small cases separately
    (hTriangulable : PlaneTriangulable P hsphere) :
    P.G.Colorable 5 := by
  classical
  let E := triangulationExtension P hsphere hTriangulable
  rcases fiveColor_planar_canonical E.hNT with ⟨C⟩
  exact pullbackColoring_along_extension P E C
```

The hard core is:

```lean
face diagonal insertion
+ face-split count/orbit theorem
+ existence of a valid diagonal in every nontriangular face
+ recursion on faceExcess
```

That is still substantial, but it is localized and directly leverages your completed Thomassen near-triangulation proof. Route B would reopen the Kempe-chain/Jordan separation campaign, which is a larger detour.
