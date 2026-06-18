**Decisive answer:** keep `faceDiagonalSupplier_of_simple_sphere` under `IsSphereMap + IsSimpleGraph`. You do **not** need 2-connectedness or 3-connectedness for the theorem. Those hypotheses simplify some intermediate stories, but they are not the honest minimal hypothesis for triangulating an arbitrary simple plane/sphere map.

The right theorem is:

```lean
theorem faceDiagonalSupplier_of_simple_sphere
  (M : CombMap D)
  (hS : M.IsSphereMap)
  (hSimple : M.IsSimpleGraph)
  (f : M.Face)
  (hk : 3 < M.faceLen f) :
  ∃ d0 d1 : D,
    M.dartFace d0 = f ∧
    M.dartFace d1 = f ∧
    M.tail d0 ≠ M.tail d1 ∧
    ¬ M.toSimpleGraph.Adj (M.tail d0) (M.tail d1) ∧
    M.ValidFaceSplit f d0 d1
```

where `ValidFaceSplit` should encode the cyclic-distance condition: the two arcs of the face boundary between the two dart occurrences both have length at least `2`, so after adding the new diagonal the two new faces have lengths at least `3`.

The clean proof is **not** “face boundaries are simple cycles.” That is false without 2-connectedness, as you noted. The clean proof is a **maximal-plane ⇒ triangulated** proof using a local Euler-count contradiction.

## The crux: prove a face-vertex clique is impossible for a long face

Let `W = faceDartList f`, `k = W.length = M.faceLen f`, and let

```lean
S := { v | ∃ d ∈ W, M.tail d = v }
```

be the set/finset of vertices appearing on the face boundary.

Assume, for contradiction, that there is **no** valid addable diagonal in `f`.

Then prove:

```lean
lemma faceVerts_pairwise_adj_of_no_diagonal :
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → M.toSimpleGraph.Adj u v
```

Reason: take occurrences of `u` and `v` on the cyclic face list. If the chosen occurrences are consecutive around the face, adjacency is a boundary edge. If they are nonconsecutive in both cyclic directions, then `u,v` would be a valid diagonal unless they were already adjacent. Since we assumed no diagonal, they must be adjacent. Thus `S` is a clique.

Now form the induced combinatorial submap `H` on the vertices `S`, retaining all edges of `M` whose endpoints lie in `S`. Under the clique conclusion, `H.toSimpleGraph` is a complete graph on `S`. Also, the original face `f` survives as a face of `H` with the same boundary length `k > 3`, because every boundary dart of `f` has both endpoints in `S`.

Then Euler-count `H`.

If `n = |S|` and `E = n(n-1)/2`, then `H` is a complete simple sphere map on `n` vertices. For `n ≥ 3`, it has no bridges, so every face of `H` has length at least `3`. Since one face has length `k ≥ 4`,

```text
2E = sum face lengths
   ≥ k + 3 * (F - 1).
```

Euler gives:

```text
F = 2 - n + E.
```

So:

```text
2E ≥ k + 3(E - n + 1)
E ≤ 3n - 3 - k
E ≤ 3n - 7.
```

But for a complete graph,

```text
E = n(n - 1) / 2,
```

and

```text
n(n - 1) / 2 > 3n - 7
```

for every `n ≥ 3`. The `n ≤ 2` cases are impossible for a simple map face of length `> 3`: with one vertex you would need a loop, and with two vertices a simple graph has at most one edge, hence at most two darts on the face.

Contradiction. Therefore a valid nonadjacent pair of nonconsecutive boundary occurrences exists.

That is the Lean-feasible heart of the proof: **no Jordan curve theorem, no Steinitz, no 3-connectivity.** The only genuinely planar work is packaging the induced “face-vertex submap” and proving the Euler count for it.

## Recommended proof skeleton

I would build it in this order.

### 1. Pure cyclic-list lemmas

These should not mention planarity.

```lean
def CyclicSeparated (L : List D) (d0 d1 : D) : Prop :=
  -- d0,d1 occur in L at cyclic distance δ with 2 ≤ δ and 2 ≤ L.length - δ
```

Then prove:

```lean
lemma split_lengths_ge_three_of_cyclicSeparated :
  CyclicSeparated (M.faceDartList f) d0 d1 →
  -- the two new faces after addFaceDiagonal have lengths ≥ 3
```

This is just arithmetic on cyclic indices.

Also prove:

```lean
lemma adj_of_consecutive_face_darts :
  -- consecutive darts around a face give adjacent tails
```

and:

```lean
lemma exists_occurrences_cyclicSeparated_or_consecutive :
  -- for two distinct face vertices u v, chosen occurrences are either consecutive
  -- or yield a cyclic-separated candidate
```

### 2. “No diagonal implies face vertices form a clique”

This is the first important lemma.

```lean
lemma faceVerts_clique_of_no_valid_diagonal
  (hNoDiag :
    ¬ ∃ d0 d1,
      M.dartFace d0 = f ∧
      M.dartFace d1 = f ∧
      CyclicSeparated (M.faceDartList f) d0 d1 ∧
      M.tail d0 ≠ M.tail d1 ∧
      ¬ M.toSimpleGraph.Adj (M.tail d0) (M.tail d1)) :
  (M.faceVertexFinset f).toSet.Pairwise
    (fun u v => M.toSimpleGraph.Adj u v)
```

This is where the earlier objection “nonconsecutive vertices may already be adjacent” is handled correctly: if they are all already adjacent, the boundary vertices become a clique.

### 3. Build the induced face-vertex submap

This is the main infrastructure lemma.

```lean
def faceVertexSubmap (M : CombMap D) (f : M.Face) : CombMap Df := ...
```

Desired facts:

```lean
lemma faceVertexSubmap_isSphere
  (hS : M.IsSphereMap) :
  (M.faceVertexSubmap f).IsSphereMap

lemma faceVertexSubmap_simple
  (hSimple : M.IsSimpleGraph) :
  (M.faceVertexSubmap f).IsSimpleGraph

lemma faceVertexSubmap_preserves_face_len :
  ∃ f' : (M.faceVertexSubmap f).Face,
    (M.faceVertexSubmap f).faceLen f' = M.faceLen f

lemma faceVertexSubmap_complete_of_faceVerts_clique :
  -- if the face vertices of f are pairwise adjacent in M,
  -- then the submap graph is complete on those vertices
```

This is the only place where deletion/restriction of a combinatorial map is needed. If you do not already have deletion, implement edge/vertex restriction once; it will also be useful later for blocks, bridges, and planar subgraph arguments.

### 4. Euler-count theorem for complete sphere maps

Prove this independently:

```lean
lemma complete_simple_sphere_has_no_long_face
  (H : CombMap DH)
  (hS : H.IsSphereMap)
  (hSimple : H.IsSimpleGraph)
  (hComplete : H.toSimpleGraph = completeGraph H.Vertex) :
  ∀ g : H.Face, H.faceLen g = 3
```

A slightly weaker version is enough:

```lean
lemma complete_simple_sphere_no_faceLen_gt_three
  ... :
  ¬ ∃ g : H.Face, 3 < H.faceLen g
```

Proof is the Euler count above. You need the helper:

```lean
lemma faceLen_ge_three_of_simple_complete
  (hSimple : H.IsSimpleGraph)
  (hComplete : H.toSimpleGraph = completeGraph H.Vertex)
  (hCard : 3 ≤ Fintype.card H.Vertex) :
  ∀ g, 3 ≤ H.faceLen g
```

because complete graphs on at least three vertices have no bridges, no loops, and no parallel edges.

### 5. Finish by contradiction

```lean
theorem faceDiagonalSupplier_of_simple_sphere
  (hS : M.IsSphereMap)
  (hSimple : M.IsSimpleGraph)
  (hk : 3 < M.faceLen f) :
  ∃ d0 d1, ... := by
  by_contra hNo
  have hClique := faceVerts_clique_of_no_valid_diagonal hNo
  let H := M.faceVertexSubmap f
  have hHsphere := faceVertexSubmap_isSphere M f hS
  have hHsimple := faceVertexSubmap_simple M f hSimple
  obtain ⟨fH, hfHlen⟩ := faceVertexSubmap_preserves_face_len M f
  have hComplete := faceVertexSubmap_complete_of_faceVerts_clique M f hClique
  have hNoLong := complete_simple_sphere_no_faceLen_gt_three H hHsphere hHsimple hComplete
  exact hNoLong ⟨fH, by simpa [hfHlen] using hk⟩
```

Then unpack the surviving existential into your existing `addFaceDiagonal` theorem to get the split-face length and preservation facts.

## Why 2-connectedness and 3-connectedness are not the right contract

`2-connected` is enough to make every face boundary a simple cycle, but it is not necessary. A connected simple plane graph with cut vertices can still be triangulated by adding diagonals inside repeated-vertex faces. For example, two triangles sharing a vertex have a repeated outer face boundary, but the outer face still has addable diagonals between vertices in different lobes.

`3-connected` is much stronger. In a 3-connected plane graph, facial cycles are induced, so once you prove that theorem, any two nonconsecutive vertices on a long face give a diagonal. But proving “facial cycles are induced” itself uses the same kind of planar separation content you are trying to avoid. It is overkill for Five Color.

So the honest hierarchy is:

```text
simple connected sphere map        sufficient and minimal for supplier
2-connected simple sphere map      simpler boundary shape, still overkill
3-connected/polyhedral map         much stronger, not needed for FCT triangulation
```

The theorem “maximal planar ⇔ triangulated” is true for simple connected plane graphs, not only for polyhedral/3-connected graphs. Maximality itself forces away cut-vertex obstructions.

## Answer to the step (iii) crux

Use **Euler counting on the face-vertex induced submap**, not Jordan.

Your step (iii) should be replaced by:

```text
Assume every cyclically nonconsecutive distinct pair on the face is already adjacent.
Then all distinct vertices appearing on the face form a clique.
Restrict the sphere map to those vertices. The chosen face remains a face of length > 3.
But a complete simple sphere map cannot have a face of length > 3, by Euler counting.
Contradiction.
```

This is cleaner than an “all diagonals would cross” argument, because the contradiction is algebraic:

```text
2E ≥ k + 3(F - 1)
F = 2 - V + E
k ≥ 4
E = V(V - 1)/2
```

and the resulting inequality is impossible.

## About an “ear” or induction route

There is an ear-style route, but it does not really reduce the work. An ear proof for faces is essentially the theorem that an outerplanar graph has a low-degree boundary vertex / missing diagonal. That theorem is also proved by Euler counting. For repeated face vertices, an ear proof tends to turn into a block-cut decomposition proof, which is more infrastructure than the clique/Euler contradiction above.

So the lowest-friction route is:

```text
no diagonal
⇒ face vertices clique
⇒ complete induced face-vertex submap with a long face
⇒ Euler contradiction
```

That is the route I would formalize.

## Mathlib connectivity API situation

Current Mathlib has ordinary `SimpleGraph.Reachable`, `SimpleGraph.Preconnected`, `SimpleGraph.Connected`, `SimpleGraph.ConnectedComponent`, and bridge-edge API in `Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`; the docs define `Connected` as preconnected plus nonempty, and `Preconnected` as every pair of vertices being reachable. citeturn962261view1

Mathlib also has `SimpleGraph.induce` for induced graphs on a vertex set, which is the API I would use for vertex-deletion definitions. citeturn208630view0 It has `IsBridge` and bridge/deleted-edge reachability API, useful for proving “face length < 3” obstructions. citeturn208630view0

There is a `SimpleGraph.Connectivity.EdgeConnectivity` file defining `IsEdgeReachable` and `IsEdgeConnected`, i.e. **edge** connectivity, not vertex 2/3-connectivity. citeturn819499view0 I would define vertex connectivity yourself rather than trying to force the edge-connectivity API.

A Lean-friendly definition would be:

```lean
def deleteVertsGraph
    [DecidableEq V]
    (G : SimpleGraph V) (s : Finset V) :
    SimpleGraph {v : V // v ∉ (s : Set V)} :=
  SimpleGraph.induce ({v : V | v ∉ (s : Set V)} : Set V) G

def IsVertexKConnected
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
  ∀ s : Finset V, s.card < k →
    (deleteVertsGraph G s).Connected

abbrev IsTwoConnected
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  IsVertexKConnected G 2

abbrev IsThreeConnected
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  IsVertexKConnected G 3
```

But I would **not** put this into the supplier theorem. Use it only if you separately want the derived theorem:

```lean
theorem faceBoundary_nodup_vertices_of_twoConnected :
  IsTwoConnected M.toSimpleGraph →
  (M.faceVertexList f).Nodup
```

That theorem is nice, but it is not needed for the diagonal supplier.

## Final recommendation

Prove the original theorem under:

```text
M.IsSphereMap ∧ M.IsSimpleGraph ∧ 3 < M.faceLen f
```

Do **not** strengthen the supplier to 3-connected. The cleanest provable route is:

```text
no valid diagonal
⇒ face boundary vertex set is a clique
⇒ induced submap on those vertices is a complete simple sphere map
⇒ the same face has length > 3 in that submap
⇒ Euler-count contradiction
⇒ valid diagonal exists
```

That makes the residual supplier disappear without compromising the “general Five Color Theorem unconditional” goal.
