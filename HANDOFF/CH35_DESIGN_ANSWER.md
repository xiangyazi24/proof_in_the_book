Recommendation in one sentence

Use axiomatic NearTriangulation over CombMap as the primitive, not an inductive generated class. Prove chord split and boundary deletion directly as certified surgeries. Use an inductive class only later as an optional constructor library, because it is not the natural induction measure in Thomassen’s proof.

The key reason: Thomassen’s induction is not “built by adding ears”; it is “reduce by chord split or delete one boundary vertex.” So the primitive should make exactly those two reductions cheap to state and verify.

A. Core representation
NearTriangulation

Let M : CombMap.

Define:

lean
structure NearTriangulation (M : CombMap) where
  sphere        : M.IsSphereMap
  simpleGraph   : M.IsSimpleGraph
  outerFace     : M.Face
  outerCycle    : BoundaryCycle M outerFace
  outer_simple   : outerCycle.VertexNodup
  inner_tri      :
    ∀ f : M.Face, f ≠ outerFace → f.card = 3

Here BoundaryCycle M outerFace should be data, not merely existence. It should contain a cyclic list of boundary darts

lean
B = [b₀, b₁, ..., b_{k-1}]

such that:

the darts lie in the outer face orbit of φ = σ * α,

consecutive boundary darts meet at vertices,

the represented boundary vertices are pairwise distinct,

the boundary edges are pairwise distinct,

the cyclic order agrees with the φ-orbit.

For Lean, do not define the outer boundary abstractly as “the face orbit.” Define a normalized finite cyclic list and prove it enumerates the orbit.

B. Why not use an inductive near-triangulation class?

You could define:

lean
inductive GeneratedNearTriangulation : CombMap → Type
| triangle : GeneratedNearTriangulation triangleMap
| glueTriangleOnBoundaryEdge :
    GeneratedNearTriangulation M →
    BoundaryEdge M →
    GeneratedNearTriangulation (glueTriangle M e)
| closeEar :
    GeneratedNearTriangulation M →
    BoundaryPath M a b →
    GeneratedNearTriangulation (addChordOrEar M a b)

But this is the wrong primitive for Thomassen.

It gives easy construction, but hard destruction. Thomassen needs:

if there is a boundary chord, split into two smaller near-triangulations;

if the boundary is chordless, delete one prescribed boundary vertex and get another near-triangulation.

An inductive generated class makes both reductions awkward because after pattern-matching on the last constructor, the chord or deleted vertex need not be related to the last construction step.

So I would prove only the following optional equivalence later:

lean
theorem generated_iff_nearTriangulation :
  GeneratedNearTriangulation M ↔ NearTriangulation M

or, more realistically, two one-way theorems:

lean
theorem generated_to_nearTriangulation :
  GeneratedNearTriangulation M → NearTriangulation M

theorem nearTriangulation_to_generated :
  NearTriangulation M → GeneratedNearTriangulation M

The second direction is nontrivial and essentially requires the same reductions as Thomassen: find either a chord or an ear/deletable boundary vertex. So it is not a simplification.

Verdict: primitive NearTriangulation; no inductive class in the main proof.

C. Chord split

Suppose M is a near-triangulation with outer cycle B, and e = {u,v} is a chord of the outer boundary: both endpoints lie on B, but the edge itself is not a boundary edge.

The chord divides the outer boundary into two boundary arcs:

lean
P₁ : BoundaryPath u v
P₂ : BoundaryPath v u

and the two submaps should have boundaries

lean
B₁ = P₁ ++ [e]
B₂ = P₂ ++ [reverse e]
Do not share chord darts

Use duplicated chord darts, four darts total:

lean
c₁  : chord dart from u to v in side 1
c₁' : chord dart from v to u in side 1

c₂  : chord dart from v to u in side 2
c₂' : chord dart from u to v in side 2

with

lean
α₁ c₁  = c₁'
α₁ c₁' = c₁

α₂ c₂  = c₂'
α₂ c₂' = c₂

This is much cleaner than sharing because each submap must itself be a closed combinatorial map. Sharing darts would make the parts non-disjoint substructures and would force every theorem to talk about partial maps with boundary half-edges. Duplicate.

Exact surgery

Let D₁ be the darts whose embedded side lies weakly inside the closed disk bounded by P₁ ∪ e. Let D₂ be the corresponding set for P₂ ∪ e.

In practice, define them orbit-theoretically:

lean
D₁ := darts reachable from the inner face on side 1 without crossing e
D₂ := darts reachable from the inner face on side 2 without crossing e

But Lean should avoid geometry. Better: define the two sides by the two arcs of the outer boundary plus all faces incident to those arcs, using face adjacency in the dual after removing the chord edge. Since this is a near-triangulation, the chord is incident to exactly two faces, and each side is the set of faces reachable from one of those two faces without crossing the chord.

For each side:

keep all original darts belonging to edges/faces on that side;

replace the original chord alpha-pair by a fresh alpha-pair;

restrict σ at all old vertices to the cyclic subsequence of darts on that side;

insert the fresh chord dart at the place formerly occupied by the original chord dart.

Formally, for side 1:

lean
D_side₁ :=
  {d : M.D // d lies in side₁ and d is not one of the original chord darts}
  ⊕ ChordDart₁

where

lean
ChordDart₁ = {c₁, c₁'}

Define:

lean
α_side₁ d =
  if d = c₁ then c₁'
  else if d = c₁' then c₁
  else image of M.α d

For σ_side₁, at every vertex w:

take the cyclic order of darts around w in M,

delete darts not in side 1,

replace the original chord dart by the fresh chord dart if necessary,

define σ_side₁ as the next dart in this filtered cyclic list.

This “filtered cyclic order” definition is the robust one. It prevents hand-written local case explosions.

Chord split lemma list
lean
lemma chordSplit_side_darts_partition

The two side dart sets are disjoint except for the original chord alpha-pair, and after replacing the chord by fresh copies they become disjoint finite dart sets.

lean
lemma chordSplit_alpha_fpf

The side alpha maps are fixed-point-free involutions.

lean
lemma chordSplit_sigma_perm

The side sigma maps are permutations of the side dart sets.

lean
lemma chordSplit_faces_preserved_inner

Every non-outer face of each side corresponds to a non-outer face of M, hence has size 3.

lean
lemma chordSplit_outerFace_boundary_side₁

The outer face of side 1 has boundary exactly P₁ ++ chord(u,v).

lean
lemma chordSplit_outerFace_boundary_side₂

The outer face of side 2 has boundary exactly P₂ ++ chord(v,u).

lean
lemma chordSplit_connected_side₁
lemma chordSplit_connected_side₂

Each side map is connected.

lean
lemma chordSplit_euler_side₁
lemma chordSplit_euler_side₂

Each side has Euler characteristic 2.

lean
lemma chordSplit_nearTriangulation_side₁
lemma chordSplit_nearTriangulation_side₂

Both side maps are near-triangulations.

lean
lemma chordSplit_vertex_count_decreases

If the chord is proper, both side maps have strictly fewer vertices than M.

This is essential for the induction.

D. Boundary-vertex deletion in the chordless case

Let the outer boundary be

lean
B = [v₀, x₁, x₂, ..., x_m]

where v₀ is the boundary vertex to delete. Its neighbors in clockwise order around v₀ are

lean
x₁ = boundary successor of v₀,
z₁, z₂, ..., z_t,
x_m = boundary predecessor of v₀

where the zᵢ are interior neighbors of v₀.

Because all inner faces are triangles, the faces incident to v₀ along the interior fan are:

lean
(v₀, x₁, z₁),
(v₀, z₁, z₂),
...
(v₀, z_t, x_m).

After deleting v₀, the new outer boundary is:

lean
B' = [x₁, z₁, z₂, ..., z_t, x_m, ...]

followed by the old boundary path from x_m back to x₁ avoiding v₀.

This is the crucial point: deleting v₀ does not merely remove v₀ from the old boundary. It also exposes the interior fan path

lean
x₁ - z₁ - z₂ - ... - z_t - x_m

as part of the new outer boundary.

Exact dart-level surgery

Let

lean
Star(v₀) := {d | origin(d) = v₀ ∨ origin(α d) = v₀}

Remove every dart belonging to an edge incident to v₀:

lean
D' := D \ Star(v₀)

The alpha map is just restriction:

lean
α' d = α d

because no remaining dart is paired with a removed dart.

The sigma map is restriction/filtering at every vertex:

lean
σ'_w = next remaining dart around w

More explicitly, for each remaining vertex w, take the cyclic list of darts around w in M, delete all darts whose alpha-partner points to v₀, and define σ' by the successor in this filtered cyclic list.

This is the same filtered-rotation construction as in chord split.

Faces: all faces not incident to v₀ are unchanged. The t+1 triangular faces incident to v₀ plus the old outer face merge into one new outer face.

Where chordlessness is used

Chordlessness is used in exactly three places.

First, it proves the exposed path

lean
x₁, z₁, z₂, ..., z_t, x_m

has no repeated vertices. Without chordlessness, an interior neighbor of v₀ could coincide with another boundary vertex or create a shortcut, producing a repeated boundary vertex after deletion.

Second, it proves no edge connects two nonconsecutive vertices of the new boundary in a way that was hidden inside the deleted fan. This is needed to keep the induction’s “no boundary chord” branch honest.

Third, it prevents bridge-like face merging pathologies. The old counterexamples for unrestricted star deletion occur when deletion collapses pieces of the map or identifies boundary walks. In a 2-connected chordless near-triangulation, the fan around a boundary vertex is a disk, so deleting it merges exactly the intended faces into one simple outer face.

Boundary deletion lemma list
lean
lemma boundaryVertex_fan_exists

For a boundary vertex v₀ of a near-triangulation, the neighbors of v₀ in cyclic order form a fan

lean
x₁, z₁, ..., z_t, x_m

and the incident non-outer faces are exactly the triangles

lean
(v₀,x₁,z₁), (v₀,z₁,z₂), ..., (v₀,z_t,x_m).
lean
lemma boundaryVertex_fan_vertices_distinct_of_chordless

If the outer boundary is chordless, then

lean
x₁, z₁, ..., z_t, x_m

has pairwise distinct vertices and intersects the old outer boundary only at x₁ and x_m.

lean
lemma deleteBoundaryVertex_alpha_fpf

The restricted alpha map after deleting the star of v₀ is a fixed-point-free involution.

lean
lemma deleteBoundaryVertex_sigma_perm

The filtered sigma rotations define permutations on the remaining darts.

lean
lemma deleteBoundaryVertex_faces_unchanged_or_outer

Every face of the deleted map is either:

an unchanged old inner face not incident to v₀, or

the new outer face obtained by merging the old outer face with the fan triangles incident to v₀.

lean
lemma deleteBoundaryVertex_inner_faces_triangles

Every non-outer face of the deleted map has size 3.

lean
lemma deleteBoundaryVertex_new_outer_boundary

The new outer boundary is the cyclic concatenation of:

lean
x₁ - z₁ - ... - z_t - x_m

with the old boundary path from x_m to x₁ avoiding v₀.

lean
lemma deleteBoundaryVertex_new_outer_simple_of_chordless

The new outer boundary is a simple cycle.

lean
lemma deleteBoundaryVertex_connected

The deleted map remains connected.

This uses the fan path connecting the two old boundary neighbors and the old graph’s 2-connectedness/no-bridge consequence.

lean
lemma deleteBoundaryVertex_euler

The deleted map has Euler characteristic 2.

Best proof: count changes.

If deg(v₀) = t + 2, then:

lean
V' = V - 1
E' = E - (t + 2)
F' = F - (t + 1)

because the t+1 incident inner triangles disappear into the outer face. Therefore

lean
V' - E' + F'
= (V - 1) - (E - (t+2)) + (F - (t+1))
= V - E + F
= 2.
lean
lemma deleteBoundaryVertex_nearTriangulation

The deletion of a chordless boundary vertex in a near-triangulation is again a near-triangulation.

lean
lemma deleteBoundaryVertex_vertex_count_decreases

The vertex count decreases by exactly 1.

E. Thomassen induction theorem

Use the standard strengthened statement.

lean
theorem thomassen_nearTriangulation_listColorable

Let M be a near-triangulation with outer boundary C. Let p q be adjacent vertices on C. Let L : Vertex M → Finset Color. Suppose:

L p = {cp};

L q = {cq};

cp ≠ cq;

every other outer-boundary vertex has list size at least 3;

every interior vertex has list size at least 5.

Then M has a proper list-coloring from L.

Induction structure

Induct on |V|.

Case 1: boundary has a chord

Let chord be u v. Split into M₁ and M₂.

Choose the side M₁ containing the precolored edge p q. By induction, color M₁.

Now u and v are colored, and since u v is an edge, their colors are distinct. In M₂, use u v as the precolored boundary edge, with singleton lists equal to the colors obtained from M₁. Apply induction to M₂.

Glue colorings along u,v.

Needed lemmas:

lean
lemma chordSplit_lists_side₁_valid

The restricted lists on the side containing p q satisfy Thomassen’s list hypotheses.

lean
lemma chordSplit_lists_side₂_valid_after_coloring

After coloring side 1, the induced singleton lists on the chord endpoints satisfy the Thomassen hypotheses on side 2.

lean
lemma chordSplit_colorings_glue

Proper list-colorings of the two sides that agree on the chord endpoints glue to a proper list-coloring of the original map.

Case 2: boundary chordless

Delete one endpoint of the precolored edge, say p.

Let the fan neighbors of p be:

lean
q = x₁, z₁, ..., z_t, x_m = r

where r is the other boundary neighbor of p.

Pick two colors

lean
a ∈ L r \ {color(p)}
b ∈ L r \ {color(p), a}

or, depending on the exact classical proof variant, pick colors to reserve for the exposed fan path. The clean Lean version is:

remove color(p) from the lists of all neighbors of p;

for the other old boundary neighbor r, also choose one color to precolor if needed;

ensure exposed interior fan vertices still have at least 3 colors on the new boundary.

The bookkeeping theorem you want is:

lean
lemma deleteBoundaryVertex_lists_valid

After deleting p and subtracting the color of p from every neighbor’s list, the new near-triangulation satisfies Thomassen’s list hypotheses with precolored edge beginning at q.

The usual reason sizes work:

q was already singleton and adjacent to p; its singleton color is distinct from color(p), so unchanged.

old outer vertices other than p,q had size at least 3; after losing at most one color, those adjacent to p still have at least 2, which is not enough if they become ordinary boundary vertices.

therefore the exact proof must choose the deleted endpoint and the new precolored edge carefully, usually precoloring the other neighbor of p after choosing a color for it, and subtracting that color from the exposed fan.

A Lean-friendly formulation is to use Thomassen’s stronger path version:

lean
theorem thomassen_pathVersion

Outer path P of length 0 or 1 is precolored; vertices on C \ P have lists of size at least 3; interior vertices have lists of size at least 5.

Then in the deletion case, after deleting one precolored endpoint, you choose a color for the opposite boundary neighbor and make the new precolored path the edge between that neighbor and the old second precolored vertex if they are adjacent in the new boundary.

So I recommend stating the induction with a precolored boundary edge, not two arbitrary precolored vertices, and deleting one endpoint of that edge. The new exposed fan makes the other endpoint adjacent along the new boundary to a chosen neighbor, giving the new precolored edge.

F. Bridge from arbitrary sphere maps to near-triangulations

Use path (a): graph-level block decomposition plus 2-connected near-triangulation inside each block.

Do not try to repair arbitrary face-repeated combinatorial maps by adding diagonals directly. Faces with repeated vertices are exactly where the embedding-level operation becomes painful: a “face” may not be a disk boundary, and diagonal insertion can cross the same vertex multiple times or create loops/multiedges.

Also do not use naive list-coloring glue across cut vertices. Your suspicion is correct: list coloring does not glue naively unless the cut vertex’s color is controlled.

Correct glue statement for list coloring

The right statement is rooted/precolored.

lean
lemma listColoring_glue_at_cutvertex_rooted

Let G = G₁ ∪ G₂ and G₁ ∩ G₂ = {v}. Suppose c ∈ L v. If both G₁ and G₂ are list-colorable from the modified lists with v precolored by c, then G is list-colorable from L.

This is true because the two colorings agree at the cut vertex by construction.

The naive statement

lean
G₁ list-colorable from L|G₁
G₂ list-colorable from L|G₂
--------------------------------
G list-colorable from L

is false as a gluing principle, because the two chosen colorings may assign different colors to the cut vertex.

For plain 5-coloring, the glue is easy: color each block with a prescribed color at the articulation vertex. For list coloring, you need Thomassen with a precolored boundary vertex or edge containing that articulation vertex.

Recommended bridge path

Convert the sphere map to its underlying finite simple graph G.

Decompose G into blocks, i.e. maximal 2-connected components plus bridge blocks.

Prove every block of a plane simple graph inherits a plane embedding whose faces are disk-like enough to triangulate.

For each 2-connected block, add noncrossing diagonals inside each face to get a near-triangulation.

Apply Thomassen to the triangulated block.

Remove added edges: a coloring of the supergraph is a coloring of the original block.

Glue block colorings at articulation vertices using rooted color choice.

This avoids doing diagonal insertion inside globally repeated faces.

Bridge lemma list
lean
lemma sphereMap_underlying_graph_planar

The underlying simple graph of a simple sphere map is planar in the graph-theoretic embedding sense.

lean
lemma simple_planar_graph_block_decomposition

Every finite connected simple graph decomposes into blocks whose block-cut incidence graph is a tree.

lean
lemma block_of_plane_graph_has_plane_embedding

Each block of a plane simple graph inherits a plane embedding.

lean
lemma block_embedding_faces_simple_cycles

If the block is 2-connected, each face boundary in the inherited embedding is a simple cycle.

This is the key payoff of block decomposition.

lean
lemma face_simple_cycle_has_non crossing_diagonal_if_length_ge_four

A face boundary cycle of length at least 4 admits a diagonal between two nonconsecutive boundary vertices that can be added inside the face while preserving planarity and simplicity.

lean
lemma triangulate_face_terminates

Repeatedly adding such diagonals strictly decreases the sum

lean
Σ face, max 0 (face.length - 3)

so the process terminates.

lean
lemma block_has_nearTriangulation_supergraph

Every 2-connected plane simple block with at least 3 vertices is a spanning subgraph of a near-triangulation.

lean
lemma coloring_supergraph_restricts

A proper coloring of a graph supergraph restricts to a proper coloring of the original graph.

lean
lemma five_list_colorable_nearTriangulation_plain

Every near-triangulation is 5-list-colorable under uniform lists of size 5.

lean
lemma block_five_colorable_with_prescribed_cutvertex_color

For every block B, every vertex v ∈ B, and every color c : Fin 5, there exists a proper 5-coloring of B with v colored c.

This follows by applying the list theorem with v included in the precolored outer edge. If needed, add a dummy adjacent boundary vertex in the theorem statement or use a one-precolored-vertex corollary.

lean
lemma block_tree_colorings_glue

Given a block-cut tree, if every block can be colored extending the already chosen color of its parent articulation vertex, then the whole graph is 5-colorable.

lean
theorem sphereMap_simple_five_colorable

Every connected simple sphere map with at least one vertex has a proper 5-coloring of its underlying graph.

Handle |V| = 0,1,2 separately.

G. Endpoint choice

Minimal honest endpoint:

lean
theorem thomassen_five_list_nearTriangulation

for near-triangulations, plus

lean
theorem sphereMap_simple_five_colorable

for arbitrary simple sphere maps.

That is the right split.

The book chapter headline is “five-coloring plane graphs,” but Thomassen’s theorem is genuinely stronger and cleaner as an induction theorem. Proving only plain 5-colorability directly through this machinery would be artificial: the induction needs list bookkeeping anyway.

So the honest formalization endpoint should be:

Main technical theorem: Thomassen 5-list-coloring for near-triangulations.

Book headline corollary: every finite simple sphere map is 5-colorable.

Bridge cost after the near-triangulation theorem:

block decomposition,

inherited embeddings for blocks,

triangulation of simple-cycle faces,

restriction from triangulated supergraph,

gluing colorings along articulation vertices.

That is substantial, but it is modular and avoids unsafe dart-level surgery on repeated-face maps.

H. Full dependency-ordered lemma list
Layer 0: map infrastructure
lean
lemma orbit_boundary_cycle_enumerates_face

A normalized boundary cycle enumerates exactly the darts in the corresponding face orbit.

lean
lemma simpleGraph_no_loops_no_parallel_edges

In a simple CombMap, no edge is a loop and no two alpha-pairs connect the same unordered pair of vertices.

lean
lemma nearTriangulation_no_bridges

A near-triangulation with simple outer boundary has no bridges.

lean
lemma nearTriangulation_boundary_vertices_have_degree_ge_two

Every boundary vertex has degree at least 2.

lean
lemma nearTriangulation_inner_face_three_distinct_vertices

Every inner triangular face has three pairwise distinct vertices.

Layer 1: boundary paths and chords
lean
lemma boundary_cycle_two_arcs

For two distinct vertices u v on a simple boundary cycle, the boundary decomposes into two internally disjoint simple paths from u to v.

lean
lemma chord_not_boundary_edge

A chord edge between two boundary vertices is not one of the boundary cycle edges.

lean
lemma chord_separates_boundary

A chord plus the two boundary arcs determines two closed simple boundary cycles.

lean
lemma chord_incident_faces_distinct

In a simple near-triangulation, a chord is incident to two distinct faces.

Layer 2: chord split surgery
lean
lemma chordSplit_alpha_fpf

The duplicated-chord alpha maps on both sides are fixed-point-free involutions.

lean
lemma chordSplit_sigma_perm

Filtered vertex rotations define valid sigma permutations on both sides.

lean
lemma chordSplit_faces_preserved

Each non-outer face of either split side is an old non-outer face of M.

lean
lemma chordSplit_outer_boundary_side₁

The outer boundary of side 1 is boundary arc 1 plus the fresh chord.

lean
lemma chordSplit_outer_boundary_side₂

The outer boundary of side 2 is boundary arc 2 plus the fresh chord.

lean
lemma chordSplit_connected

Both split sides are connected.

lean
lemma chordSplit_euler

Both split sides have Euler characteristic 2.

lean
lemma chordSplit_nearTriangulation

Both split sides are near-triangulations.

lean
lemma chordSplit_smaller

Both split sides have strictly fewer vertices than the original map.

Layer 3: chordless boundary deletion
lean
lemma boundaryVertex_fan_exists

The neighbors of a boundary vertex in a near-triangulation form a triangular fan.

lean
lemma boundaryVertex_fan_faces_exact

The incident inner faces are exactly the consecutive fan triangles.

lean
lemma fan_path_simple_of_chordless

If the outer boundary is chordless, the fan path exposed by deleting the boundary vertex is simple.

lean
lemma fan_path_meets_old_boundary_only_at_ends

In the chordless case, the exposed fan path meets the old boundary only at the two old boundary neighbors.

lean
lemma deleteBoundaryVertex_alpha_fpf

Star deletion preserves fixed-point-free involutive alpha on the remaining darts.

lean
lemma deleteBoundaryVertex_sigma_perm

Filtered rotations after star deletion define valid sigma permutations.

lean
lemma deleteBoundaryVertex_faces_classification

A face after deletion is either an unchanged old inner face or the merged new outer face.

lean
lemma deleteBoundaryVertex_outer_boundary

The new outer boundary is the exposed fan path plus the old boundary path avoiding the deleted vertex.

lean
lemma deleteBoundaryVertex_outer_simple_of_chordless

The new outer boundary is simple.

lean
lemma deleteBoundaryVertex_connected

The deleted map is connected.

lean
lemma deleteBoundaryVertex_euler

The deleted map has Euler characteristic 2.

lean
lemma deleteBoundaryVertex_nearTriangulation

Deleting a boundary vertex from a chordless near-triangulation gives a near-triangulation.

lean
lemma deleteBoundaryVertex_smaller

The vertex count decreases by one.

Layer 4: list-coloring primitives
lean
def ListColoring (G : SimpleGraph V) (L : V → Finset Color) : Prop

A proper coloring c : V → Color such that c v ∈ L v for every vertex.

lean
lemma listColoring_mono_edges

A list-coloring of a supergraph restricts to a list-coloring of a subgraph with the same vertex set.

lean
lemma listColoring_restrict_induced

A list-coloring restricts to an induced subgraph.

lean
lemma listColoring_glue_on_overlap

If two subgraphs cover the graph and their colorings agree on the intersection, then they glue.

lean
lemma listColoring_glue_at_cutvertex_rooted

If two graphs meet only at v and both are list-colorable with v forced to color c, then their union is list-colorable.

Layer 5: Thomassen induction
lean
def ThomassenLists

For a near-triangulation with outer boundary C and distinguished boundary edge p q, the list assignment satisfies:

p and q are singleton lists with distinct colors,

other boundary vertices have list size at least 3,

interior vertices have list size at least 5.

lean
lemma chordSplit_thomassenLists_side₁

If the precolored edge lies on side 1, the restricted lists satisfy ThomassenLists on side 1.

lean
lemma chordSplit_thomassenLists_side₂_after_coloring

After coloring side 1, the lists on side 2 with the chord endpoints forced to their side-1 colors satisfy ThomassenLists.

lean
lemma deleteBoundaryVertex_thomassenLists

In the chordless case, after deleting one precolored boundary endpoint and modifying neighbor lists appropriately, the remaining near-triangulation satisfies ThomassenLists.

lean
theorem thomassen_nearTriangulation_listColorable

Every near-triangulation satisfying ThomassenLists is list-colorable.

lean
corollary nearTriangulation_five_list_colorable

Every near-triangulation is colorable from arbitrary lists of size at least 5.

lean
corollary nearTriangulation_five_colorable

Every near-triangulation is properly colorable with colors Fin 5.

Layer 6: arbitrary sphere maps
lean
lemma simpleSphereMap_underlying_connected_graph

The underlying graph of a connected simple sphere map is connected.

lean
lemma graph_block_cut_tree_exists

Every finite connected graph has a block-cut tree.

lean
lemma plane_block_embedding

Each block of a plane simple graph inherits a plane embedding.

lean
lemma twoConnected_plane_block_faces_simple

Every face boundary in a 2-connected plane block is a simple cycle.

lean
lemma plane_block_triangulable

Every 2-connected plane block with at least three vertices is a spanning subgraph of a near-triangulation.

lean
lemma block_five_colorable_rooted

Every block is 5-colorable while prescribing the color of any chosen articulation vertex.

lean
lemma block_cut_tree_glue_five_colorings

Rooted 5-colorings of all blocks glue along the block-cut tree.

lean
theorem simpleSphereMap_five_colorable

Every finite simple sphere map is 5-colorable.

Final scope

I would formalize the chapter with this headline:

lean
theorem thomassen_nearTriangulation_five_list_colorable

and then present the book’s theorem as the corollary:

lean
theorem five_color_theorem_for_simple_sphere_maps

That is the minimal honest endpoint: the proof machinery is list-theoretic, but the final book-facing statement is ordinary 5-colorability.