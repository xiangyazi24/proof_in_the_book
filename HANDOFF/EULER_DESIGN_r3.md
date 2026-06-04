I’ll pin the crux as a theorem about deleting the open star of a vertex in a cellular sphere map. The clean proof is not “Euler arithmetic only”; it needs a local face-splicing lemma showing the incident face boundaries collapse from $k$ local corners to one boundary component.

One important correction to the naive count: if deletion disconnects, the face count is not the face count of one restricted disconnected map. For 5CT, use connected components and give each component its own outer face; this duplicates the merged outside face as many times as needed.

Yes: the load-bearing lemma is vertex deletion preserves sphere components. But prove it for the simple embedded graph layer, not bare dart-only maps, because deletion creates isolated vertices.
1. Correct deletion theorem
Let $M$ be a connected simple sphere embedding and let $v$ have degree $k$.
Delete:


$$V' = V \setminus \{v\},
\qquad
D' = \{d\in D : \operatorname{tail}(d)\ne v \land \operatorname{head}(d)\ne v\}.$$


Since the graph is simple, $k$ is exactly the number of incident edges deleted.
Counts:


$$V' = V-1,
\qquad
E' = E-k.$$


If $M-v$ has $c$ connected components, then each component is a sphere map and


$$\sum_i F_i = F + 2c - 1 - k.$$


Indeed,


$$\sum_i (V_i-E_i+F_i)=2c,$$


and


$$\sum_i V_i = V-1,\qquad
\sum_i E_i = E-k.$$


So


$$\sum_i F_i
=2c-(V-1)+(E-k)
=2c-1-k+(E-V)
=2c-1-k+(F-2)
=F+2c-3-k.$$


Careful: using $V-E+F=2$, we have $E-V=F-2$, so:


$$\sum_i F_i = 2c - V + 1 + E - k
= 2c + 1 - k + (E-V)
= 2c + 1 - k + (F-2)
= F + 2c - 1 - k.$$


For connected deletion, $c=1$, hence


$$F' = F-k+1.$$


This is the familiar statement: the $k$ faces incident to $v$ merge into one face.

2. Define deletion precisely
For a simple graph embedding:
leanD' := {d : D // tail d ≠ v ∧ head d ≠ v}
Define:
leanα' d := α d
This is well-defined because:
leantail (α d) = head dhead (α d) = tail d
so if both endpoints of d avoid v, then both endpoints of α d avoid v.
Therefore:
leanlemma deleteVertex_alpha_wf :  d ∈ D' → α d ∈ D'lemma deleteVertex_alpha_invol :  α' * α' = 1lemma deleteVertex_alpha_no_fixed :  ∀ d : D', α' d ≠ d

3. The σ′ operation
This is the hard local operation.
Let $S\subseteq D$ be the deleted dart set:


$$S=\{d : \operatorname{tail}(d)=v \lor \operatorname{head}(d)=v\}.$$


For $d\notin S$, define $\sigma'(d)$ as the first surviving dart encountered by iterating $\sigma$:


$$\sigma'(d)=\sigma^m(d),$$


where $m>0$ is minimal such that $\sigma^m(d)\notin S$.
In Lean, make this a reusable permutation operation:
leandef Perm.deleteSet  (p : Equiv.Perm D)  (S : Finset D) :  Equiv.Perm {d : D // d ∉ S}
Mathematical definition:
leandeleteSet p S x =  first y outside S in the forward p-cycle after x
Inverse:
lean(deleteSet p S)⁻¹ =  deleteSet p⁻¹ S
Main lemmas:
leanlemma deleteSet_apply_sameCycle :  Equiv.Perm.SameCycle p x.val ((Perm.deleteSet p S x).val)lemma deleteSet_orbits_eq_deleted_orbits :  cycles of deleteSet p S are cycles of p with S removedlemma deleteSet_card_orbits :  orbit count changes by deleting empty/nonempty cycle pieces
Then define:
leanσ' := Perm.deleteSet σ deletedDarts
This exactly “splices” cyclic orders at every vertex.

4. Face behavior
Let
leanφ  := σ * αφ' := σ' * α'
Faces are cycles of φ.
Deleting $v$ removes the $k$ darts leaving $v$ and the $k$ darts entering $v$. Around $v$, the incident faces occur cyclically. After deletion, those $k$ local face-corners are spliced into one boundary per affected connected component.
For connected deletion:
leanlemma deleteVertex_faces_connected  (hconn' : (M.deleteVertex v).Connected) :  F (M.deleteVertex v) = F M - degree M.G v + 1
For disconnected deletion:
leanlemma deleteVertex_faces_components  (c : Nat)  (hc : c = numberOfComponents (M.G.deleteVertex v)) :  (∑ C, F (componentEmbedding M v C))    = F M + 2 * c - 1 - degree M.G v
Do not try to make one disconnected map satisfy Euler $=2$. Each connected component satisfies Euler $=2$.

5. Main theorem
leantheorem deleteVertex_isSphereMap_per_component  (M : PlaneSimpleGraph V D)  (v : V)  (hM : IsSphereMap M.toCombMap) :  ∀ C ∈ connectedComponents (M.G.deleteVertex v),    IsSphereMap (M.deleteVertexComponent v C).toCombMap
Proof outline:


α' is restriction of α.


σ' is Perm.deleteSet σ deletedDarts.


Face permutation is compatible:


leanφ' = σ' * α'


Each component inherits a cellular embedding.


The deleted star of $v$ is an open disk in a sphere map.


Removing that open disk leaves a sphere with boundary.


Each connected component can be capped by one outer face.


Therefore each component has Euler characteristic $2$.


This is the exact finite combinatorial substitute for the topology.
The key finite lemma is:
leanlemma deleted_star_boundary_is_one_cycle  (h : IsSphereMap M.toCombMap) :  boundaryCycleOfDeletedStar M v is one cyclic σ/φ boundary
Then capping each component gives one new outer face.

6. Lean encoding recommendation
Use type parameters outside the structure, not fields Vtx : Type and D : Type.
Do this:
leanstructure PlaneSimpleGraph    (V D : Type)    [Fintype V] [DecidableEq V]    [Fintype D] [DecidableEq D] where  G : SimpleGraph V  tail : D → V  head : D → V  α : Equiv.Perm D  σ : Equiv.Perm D  α_invol : α * α = 1  α_no_fixed : ∀ d : D, α d ≠ d  reverse_tail : ∀ d : D, tail (α d) = head d  reverse_head : ∀ d : D, head (α d) = tail d  dart_edge : ∀ d : D, G.Adj (tail d) (head d)  edge_darts :    ∀ {u v : V}, G.Adj u v →      ∃! d : D, tail d = u ∧ head d = v  σ_preserves_tail :    ∀ d : D, tail (σ d) = tail d  σ_vertex_cycle :    ∀ {u : V} {d e : D},      tail d = u →      tail e = u →      Equiv.Perm.SameCycle σ d e  connected : G.Connected
Then separately:
leandef PlaneSimpleGraph.facePerm (M : PlaneSimpleGraph V D) :    Equiv.Perm D :=  M.σ * M.αdef PlaneSimpleGraph.FaceSet (M : PlaneSimpleGraph V D) :=  Quotient (Equiv.Perm.SameCycle.setoid M.facePerm)def PlaneSimpleGraph.numFaces (M : PlaneSimpleGraph V D) : Nat :=  if h : IsEmpty D then 1 else Fintype.card M.FaceSetdef PlaneSimpleGraph.numVertices (M : PlaneSimpleGraph V D) : Nat :=  Fintype.card Vdef PlaneSimpleGraph.numEdges (M : PlaneSimpleGraph V D) : Nat :=  Fintype.card D / 2def PlaneSimpleGraph.eulerChar (M : PlaneSimpleGraph V D) : Int :=  (M.numVertices : Int) - (M.numEdges : Int) + (M.numFaces : Int)def PlaneSimpleGraph.IsSphereMap (M : PlaneSimpleGraph V D) : Prop :=  M.connected ∧ M.eulerChar = 2
This avoids universe/elaboration friction.
Avoid Fin nV / Fin nD initially. Use arbitrary finite types. You can later instantiate with Fin n.

7. Ch12 / Platonic finiteness
For Euler consequences, you do not need the full simple-graph layer.
You need only a connected sphere map with:
leanEulerChar = 2faceLength_sum = 2E∀ f, p ≤ faceLength f∀ v, q ≤ degree v
Then:


$$pF \le 2E,\qquad qV \le 2E,\qquad V-E+F=2.$$


This gives the usual Platonic restriction:


$$\frac1p+\frac1q>\frac12.$$


So Ch12 can be done directly with IsSphereMap plus degree/face-length hypotheses.
For 5CT, use PlaneSimpleGraph, because you need vertex deletion, coloring, adjacency, and Kempe chains.

Final load-bearing lemma list
lean-- permutation deletiondef Perm.deleteSetlemma deleteSet_is_permlemma deleteSet_forward_sameCyclelemma deleteSet_inverselemma deleteSet_cycle_splice-- vertex deletiondef deletedDartsdef deleteVertexDartsdef deleteVertexAlphadef deleteVertexSigmalemma deleteVertex_alpha_wflemma deleteVertex_alpha_invollemma deleteVertex_alpha_no_fixedlemma deleteVertex_sigma_permlemma deleteVertex_sigma_preserves_tail-- countslemma deleteVertex_numVertices :  V' = V - 1lemma deleteVertex_numEdges :  E' = E - degree vlemma deleteVertex_numFaces_connected :  Connected (deleteVertex M v) →  F' = F - degree v + 1lemma deleteVertex_numFaces_components :  ∑ C, F_C = F + 2 * c - 1 - degree v-- sphere preservationtheorem deleteVertex_isSphereMap_connected :  IsSphereMap M →  Connected (deleteVertex M v) →  IsSphereMap (deleteVertex M v)theorem deleteVertex_isSphereMap_per_component :  IsSphereMap M →  ∀ C, IsSphereMap (deleteVertexComponent M v C)
This is the crux. Everything later in 5CT depends on deleteVertex_isSphereMap_per_component.
