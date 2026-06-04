You’re right to reject a bare inductive certificate unless we prove it complete. The revised design below makes “plane” a faithful genus-zero property first, then separately proves the reduction/build lemmas needed for Euler and 5CT.

Yes — revise as follows.
Revised design
Use genus-zero combinatorial maps, not inductive IsPlane certificates.
A. Faithful plane definition
For a connected orientable combinatorial map $M$, define


$$\chi(M)=V(M)-E(M)+F(M).$$


Then:
leandef EulerChar (M : CombMap) : Int :=  (M.V : Int) - (M.E : Int) + (M.F : Int)def IsSphereMap (M : CombMap) : Prop :=  M.Connected ∧ M.EulerChar = 2
This is the right faithful combinatorial definition of a connected cellular embedding on the sphere.
Do not define plane by an inductive build certificate. Instead prove later:
leantheorem sphereMap_reducible :  IsSphereMap M →  M.E ≠ 0 →  ∃ e, Bridge e ∨ NonBridge e
and the deletion/contraction lemmas preserve IsSphereMap.
So Euler is not a deep theorem for IsSphereMap; it is the definition of genus zero. The content becomes:


vertex/edge/face counting,


deletion closure,


$E \le 3V-6$,


degree $\le 5$,


Kempe non-crossing.


That is faithful.

B. Use a graph-with-embedding wrapper for 5CT
For five-coloring, do not work directly with arbitrary multigraph maps. Use a simple graph plus a rotation/cellular embedding.
leanstructure PlaneSimpleGraph where  Vtx : Type  [fintypeV : Fintype Vtx]  [decEqV : DecidableEq Vtx]  G : SimpleGraph Vtx  D : Type  [fintypeD : Fintype D]  [decEqD : DecidableEq D]  tail : D → Vtx  head : D → Vtx  α : Equiv.Perm D  σ : Equiv.Perm D  α_invol : α * α = 1  α_no_fixed : ∀ d, α d ≠ d  reverse_tail : ∀ d, tail (α d) = head d  reverse_head : ∀ d, head (α d) = tail d  dart_edge : ∀ d, G.Adj (tail d) (head d)  edge_darts :    ∀ {u v}, G.Adj u v →      ∃! d, tail d = u ∧ head d = v  σ_preserves_tail :    ∀ d, tail (σ d) = tail d  σ_vertex_cycle :    ∀ v, σ acts cyclically on {d // tail d = v}  connected : G.Connected  sphere :    EulerChar = 2
This is faithful for finite connected simple planar graphs: every finite connected simple graph with a cellular sphere embedding gives such data; conversely such data is a cellular sphere embedding.

C. Vertex deletion closure
Given a vertex $v$, delete all darts incident to $v$:


$$D'=\{d\in D : \operatorname{tail}(d)\ne v \land \operatorname{head}(d)\ne v\}.$$


Restrict:
leanα' d := α dσ' := σ with all deleted darts skipped
The important part is σ': at every remaining vertex, remove from its cyclic order the darts going to $v$, and connect the predecessor/successor around the cycle.
This is the standard “delete entries from a cyclic permutation” operation.
Result:
leantheorem deleteVertex_isSphereMap  (M : PlaneSimpleGraph)  (v : M.Vtx) :  IsSphereMap (M.deleteVertex v).toCombMap
If the graph becomes disconnected, each component is separately planar:
leantheorem deleteVertex_components_sphere :  ∀ C ∈ components (M.G.deleteVertex v),    IsSphereMap (componentEmbedding M v C)
For 5CT induction, color each connected component separately.

D. Degree ≤ 5
For simple connected planar graph with $V \ge 3$:


Euler:




$$V-E+F=2.$$




Face-length sum:




$$\sum_f \ell(f)=2E.$$




In a simple planar graph with $V\ge 3$, every face has length at least $3$:




$$3F \le 2E.$$




Therefore:




$$V-E+F=2,\quad F\le \frac{2E}{3}$$


gives


$$E\le 3V-6.$$




Degree sum:




$$\sum_v \deg(v)=2E\le 6V-12<6V.$$


So some vertex has degree at most $5$.
Lean statements:
leanlemma face_length_sum_eq_two_mul_edges :  ∑ f, faceLength f = 2 * Elemma simple_face_length_ge_three  (hV : 3 ≤ V) :  ∀ f, 3 ≤ faceLength flemma planar_simple_edge_bound  (hV : 3 ≤ V) :  E ≤ 3 * V - 6lemma exists_degree_le_five  (hV : 1 ≤ V) :  ∃ v, degree v ≤ 5

E. Kempe non-crossing from σ
Yes: the cyclic order from σ is exactly what the Kempe proof needs.
At a degree-5 vertex $x$, the five incident darts have a cyclic order:


$$d_1,d_2,d_3,d_4,d_5$$


with neighbors:


$$v_1,v_2,v_3,v_4,v_5.$$


Suppose colors are $1,2,3,4,5$ in cyclic order.
If the $1$-$3$ Kempe chain connects $v_1$ to $v_3$, then together with the two edges $xv_1$, $xv_3$ it forms a simple closed combinatorial cycle separating the sphere into two regions.
Because $v_2$ and $v_4$ lie in different intervals of the cyclic order around $x$, they lie on opposite sides of that cycle. Hence no $2$-$4$ Kempe chain can connect them without crossing the $1$-$3$ cycle.
Combinatorial version: use the face permutation $\phi=\sigma\alpha$. Removing a simple cycle $C$ splits the darts not in $C$ into two face-side regions. The σ-order at $x$ proves $v_2$ and $v_4$ are in different regions. A path from $v_2$ to $v_4$ avoiding $C$ would force them into the same region, contradiction.
Key lemma:
leantheorem kempe_separation  {x v1 v2 v3 v4 : Vtx}  (hcyc : cyclicAround x [v1, v2, v3, v4, ...])  (P13 : SimplePath G v1 v3)  (hP13_colors : pathUsesOnlyColors P13 {1,3})  (hdisjoint : v2 ∉ P13.vertices ∧ v4 ∉ P13.vertices) :  ¬ ∃ P24 : SimplePath G v2 v4,      pathUsesOnlyColors P24 {2,4} ∧      Disjoint P24.vertices P13.vertices
This is the finite replacement for Jordan curve topology.

Final architecture
Use three layers:
Layer 1: raw combinatorial maps
leanCombMapφ = σ * αVertexSet = σ-orbitsEdgeSet = α-orbitsFaceSet = φ-orbitsV, E, FEulerChar = V - E + FConnected
Layer 2: faithful sphere maps
leanIsSphereMap M := M.Connected ∧ M.EulerChar = 2
This is the formal “plane map”.
Layer 3: simple graph embeddings
leanPlaneSimpleGraphtoCombMapsphere : IsSphereMap toCombMap
This is the object used for 5CT.

Ordered lemma list
lean-- raw mapCombMapCombMap.φCombMap.VertexSetCombMap.EdgeSetCombMap.FaceSetCombMap.VCombMap.ECombMap.FCombMap.EulerCharCombMap.Connected-- sphere mapsdef IsSphereMaplemma isSphereMap_euler :  IsSphereMap M → M.EulerChar = 2-- simple embedded graphsPlaneSimpleGraphPlaneSimpleGraph.toCombMapPlaneSimpleGraph.isSphereMap-- deletiondef deleteVertexlemma deleteVertex_rotation_wflemma deleteVertex_toCombMaplemma deleteVertex_components_spherelemma deleteVertex_planar_components-- face lengthsdef faceLengthlemma face_length_sum_eq_two_mul_edgeslemma simple_face_length_ge_threelemma three_mul_faces_le_two_mul_edges-- Euler consequenceslemma planar_simple_edge_bound :  3 ≤ V → E ≤ 3 * V - 6lemma degree_sum_eq_two_mul_edgeslemma exists_degree_le_five-- Kempedef cyclicArounddef KempeSubgraphdef KempeChainlemma cycle_separates_sphere_combinatoriallylemma kempe_non_crossinglemma five_color_extend_degree_le_five
This avoids the certificate-fragment trap, supports vertex deletion, gives the min-degree lemma, and preserves the σ-based finite non-crossing argument needed for Kempe.
