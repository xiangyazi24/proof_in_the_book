Below is the route I would implement. The key is not to try to prove the chord side partition directly. Prove one reusable genus-zero “Jordan for a simple cycle” lemma by a finite cut-and-cap dart surgery. Then the chord lemma is a three-line application to the simple cycle:


$$C = \text{chord } e \;+\; \text{one outer-boundary arc between its endpoints}.$$


The assumed interior-dual path from one chord-incident face to the other avoids both the chord and all boundary edges, hence avoids all edges of $C$, contradicting the Jordan lemma.

0. The theorem to prove
Let $M$ be a connected finite orientable combinatorial map with


$$\chi(M) := V(M)-E(M)+F(M)=2.$$


Let $O$ be the distinguished outer face, whose boundary is a simple cycle of length at least $3$. Let $e$ be a chord: a graph edge joining two distinct vertices of $O$, not itself an outer-boundary edge. Let $f_L,f_R$ be the two faces incident with $e$. You already have:


$f_L,f_R\neq O$;


$f_L,f_R$ are inner triangles;


the interior-dual graph has vertices = non-outer faces and adjacency across an edge that is neither an outer-boundary edge nor $e$;


Separates e means $f_L$ and $f_R$ are not connected in that interior dual.


The target is:
leantheorem chord_separates    (M : CombMap)    (hM : NearTriangulation M)    (hsph : M.Connected ∧ M.chi = 2)    (e : Edge M)    (he : IsChord hM.outerCycle e) :    Separates hM e
Equivalently:
lean¬ InteriorDual.ConnectedAvoidingBoundaryAndChord hM e fL fR
The clean proof is:


choose one of the two outer-boundary arcs $A$ between the endpoints of $e$;


form the simple primal cycle


$$C := e \cup A;$$




prove the genus-zero Jordan lemma for simple cycles:

In a connected map with $\chi=2$, if $C$ is a simple primal cycle, then the two faces incident with any edge of $C$ are not connected in the dual after deleting all dual edges crossing $C$.



since the interior-dual path in the negation of Separates avoids $e$ and avoids every boundary edge, it avoids every edge of $C$, contradiction.


So the irreducible wall reduces to the following single general lemma.

1. The reusable Jordan lemma
1.1 Statement
Use directed darts for simple cycles.
Let $C=(d_0,\dots,d_{k-1})$ be a directed simple primal cycle. Write $E(C)$ for its edge-orbit set.
For a dart $d_i\in C$, let $f^+_i$ and $f^-_i$ be the two face orbits incident with the edge $\{d_i,\alpha d_i\}$.
Define the dual graph with all $C$-edges removed:
leandef DualAvoidsCycle (M : CombMap) (C : SimpleCycle M) : SimpleGraph (Face M) :=  -- faces adjacent across primal edges not in C.edgeSet
Then the lemma is:
leantheorem jordan_simple_cycle_of_chi_two    (M : CombMap)    (hconn : M.Connected)    (hchi : M.chi = 2)    (C : SimplePrimalCycle M)    (i : Fin C.length) :    ¬ Reachable (DualAvoidsCycle M C)        (face_left  C i)        (face_right C i)
This is the exact lemma needed. It is fully combinatorial and uses only dart permutations plus Euler inequality.

2. Euler inequality for connected combinatorial maps
You need this first:
leantheorem chi_le_two_of_connected    (M : CombMap)    (hconn : M.Connected) :    M.chi ≤ 2
This is the minimal fragment of Gonthier’s genus theory. You do not need full genus classification. You only need nonnegativity of genus in the form $\chi\le 2$.
A clean proof avoids topology entirely.
2.1 Underlying graph
Let the underlying graph have:
leanVtx M  := Orbits M.sigmaEdge M := Orbits M.alpha
For an edge orbit $e=\{d,\alpha d\}$, its endpoints are:
leansrc e := vertexOrbit dtgt e := vertexOrbit (M.alpha d)
Connectivity of the map implies connectedness of this underlying graph.
Choose a spanning tree $T\subseteq Edge(M)$ of the underlying graph. Since the graph is connected,


$$|T| = V(M)-1.$$


Let $R := Edge(M)\setminus T$. Then


$$|R| = E(M)-V(M)+1.$$


2.2 Restrict the rotation system to the tree
Define restrictEdges M S by deleting all darts whose edge-orbit is not in $S$, splicing the cyclic vertex rotations across the deleted darts.
For $S=T$, the restricted map $M_T$ has:


$$V(M_T)=V(M),\qquad E(M_T)=V(M)-1.$$


The essential lemma is:
leanlemma tree_rotation_has_one_face    (M : CombMap)    (T : Finset (Edge M))    (hT : IsSpanningTree (underlyingGraph M) T) :    (restrictEdges M T).F = 1
Proof
Induct on $|T|$.
Base case: $T$ has one vertex and no edges. The restricted map has one vertex and one face.
Inductive step: a finite tree has a leaf edge $e$. Let $v$ be the leaf vertex and $u$ its neighbor. In the restricted rotation system, the two darts of $e$ are the only darts incident with $v$. Delete $e$ and the leaf vertex. The face permutation before deletion contains a local two-dart excursion through $v$. Removing that excursion does not split or merge face orbits. Therefore $F$ is unchanged.
Formally, the local face permutation calculation is:
If the leaf dart at $v$ is $d$, then the vertex rotation at $v$ is the singleton cycle $(d)$. The opposite dart is $\alpha d$, based at $u$. Since


$$\phi = \sigma\circ\alpha,$$


the face walk enters the leaf through $\alpha d$, applies $\alpha$ to get $d$, then applies $\sigma$ at the leaf vertex, which fixes $d$, and immediately returns across the same edge. After deleting the two darts, the successor in the face cycle is exactly the successor obtained by bypassing this excursion. Thus the number of $\phi$-orbits is unchanged.
So, by induction, $F(M_T)=1$.
2.3 Add non-tree edges one at a time
Order the non-tree edges:


$$R=\{r_1,\dots,r_m\},
\qquad
m=E(M)-V(M)+1.$$


Let


$$M_0 := M_T,\qquad
M_j := restrictEdges M (T\cup\{r_1,\dots,r_j\}).$$


When inserting one edge, two new darts are inserted into the vertex rotations and paired by $\alpha$. At the level of the face permutation $\phi=\sigma\alpha$, this changes the number of face cycles by exactly $\pm 1$. Therefore:
leanlemma face_count_insert_edge_le_succ    (M_old M_new : CombMap)    (hinsert : M_new = insertOneEdge M_old e data) :    M_new.F ≤ M_old.F + 1
The proof is the standard permutation fact:
leanlemma cycles_mul_transposition_change_abs_one    (p : Equiv.Perm α)    (a b : α) (hab : a ≠ b) :    cycleCount (p * Equiv.swap a b) =      cycleCount p + 1 ∨    cycleCount (p * Equiv.swap a b) =      cycleCount p - 1
The edge insertion modifies the face permutation by such a transposition on the relevant successor darts.
Thus


$$F(M)
\le F(M_T)+m
=1+E(M)-V(M)+1.$$


Hence


$$F(M)\le E(M)-V(M)+2,$$


so


$$V(M)-E(M)+F(M)\le 2.$$


This proves:
leantheorem chi_le_two_of_connected    (M : CombMap)    (hconn : M.Connected) :    M.chi ≤ 2
This is the only genus theory you need.

3. Cut-and-cap surgery along a simple cycle
Now define the purely finite dart operation cutCapCycle M C.
Intuitively: cut the map open along $C$, duplicating the cycle vertices and cycle edges, then cap the two new boundary cycles by two fresh faces.
For a simple cycle $C$ of length $k$:


$$V(\operatorname{cutCap}(M,C)) = V(M)+k,$$




$$E(\operatorname{cutCap}(M,C)) = E(M)+k,$$




$$F(\operatorname{cutCap}(M,C)) = F(M)+2.$$


Therefore


$$\chi(\operatorname{cutCap}(M,C))
= \chi(M)+2.$$


Since $\chi(M)=2$, the cut-and-capped map has


$$\chi=4.$$


If it is connected, this contradicts chi_le_two_of_connected.
That is the whole Jordan argument.
3.1 Local construction
Let the directed cycle darts be:


$$d_0,d_1,\dots,d_{k-1}.$$


The source vertex of $d_i$ is $v_i$, and the target vertex is $v_{i+1}$. Thus


$$\operatorname{vtx}(\alpha d_i)=\operatorname{vtx}(d_{i+1}).$$


At vertex $v_i$, the two cycle incidences are:


$$p_i := \alpha d_{i-1},
\qquad
q_i := d_i.$$


Because $C$ is simple, $p_i$ and $q_i$ occur in the same $\sigma$-orbit and no other cycle incidence occurs in that orbit.
The $\sigma$-orbit of $v_i$ is split into two cyclic intervals:


$$[p_i,q_i]_{\sigma},
\qquad
[q_i,p_i]_{\sigma}.$$


These become the two duplicated vertices $v_i^+$ and $v_i^-$.
For every cycle edge $e_i=\{d_i,\alpha d_i\}$, replace it by two edges:


one edge belonging to the $+$-bank;


one edge belonging to the $-$-bank.


Concretely, introduce two fresh cap darts $c_i^+$ and $c_i^-$. Pair the old side-dart on the $+$-bank with $c_i^+$, and the old side-dart on the $-$-bank with $c_i^-$. The fresh cap darts are arranged by the new vertex rotations so that they form two new face cycles:


$$c_0^+,c_1^+,\dots,c_{k-1}^+$$


and


$$c_{k-1}^-,c_{k-2}^-,\dots,c_0^-.$$


The reversal on the second cap is important: it is what preserves orientability and keeps the new map in the same CombMap format with faces still given by $\phi=\sigma\alpha$.
All non-cycle darts are kept. Their vertex assignment is determined by which $\sigma$-interval they lie in at each cycle vertex.
This is a completely finite construction. In Lean I would package it as:
leandef cutCapCycle (M : CombMap) (C : SimplePrimalCycle M) : CombMap
with local simp lemmas for alpha, sigma, and phi.
3.2 Count lemmas
The count lemmas should be proved immediately after defining the surgery.
leanlemma cutCapCycle_vertex_count    (M : CombMap) (C : SimplePrimalCycle M) :    (cutCapCycle M C).V = M.V + C.length
Proof: the only vertex-orbits changed are the $k$ distinct vertices of $C$. Each such $\sigma$-orbit is split into exactly two $\sigma'$-orbits. Thus the vertex count increases by $k$.
leanlemma cutCapCycle_edge_count    (M : CombMap) (C : SimplePrimalCycle M) :    (cutCapCycle M C).E = M.E + C.length
Proof: every non-cycle edge is unchanged. Each of the $k$ cycle edges is replaced by two edges, so the edge count increases by $k$.
leanlemma cutCapCycle_face_count    (M : CombMap) (C : SimplePrimalCycle M) :    (cutCapCycle M C).F = M.F + 2
Proof: every old face survives as a face orbit of the new $\phi'$. Along a cut edge, the old face uses the old side dart and is now bounded by one of the duplicated edge copies, so the old $\phi$-cycle is not destroyed; it is merely routed through the corresponding split vertex. The two new cap-dart cycles are exactly two additional $\phi'$-orbits. No other $\phi'$-orbits exist because every fresh dart belongs to one of those two cap cycles.
Then:
leanlemma cutCapCycle_chi    (M : CombMap) (C : SimplePrimalCycle M) :    (cutCapCycle M C).chi = M.chi + 2
by subtraction:


$$(V+k)-(E+k)+(F+2)=V-E+F+2.$$



4. Connectivity of the cut-cap map from a dual path
This is the crucial finite substitute for topology.
4.1 Statement
Let $C$ be a simple cycle and let $e_i\in C$. Let $f_i^+$ and $f_i^-$ be the two faces incident with $e_i$. Suppose there is a dual path from $f_i^+$ to $f_i^-$ using only edges not in $E(C)$. Then the cut-and-capped map is connected.
leanlemma cutCapCycle_connected_of_dual_path    (M : CombMap)    (hconn : M.Connected)    (C : SimplePrimalCycle M)    (i : Fin C.length)    (hpath :      Reachable (DualAvoidsCycle M C)        (face_left C i)        (face_right C i)) :    (cutCapCycle M C).Connected
4.2 Proof
There are two parts.
Part A: every dart of the cut map reaches one of the two banks of $C$
Because $M$ is connected, every original dart $x$ is connected in the incidence graph generated by $\sigma$ and $\alpha$ to some dart of $C$. Choose a shortest such walk. No internal dart of this walk is a cycle dart.
All steps before the first cycle dart use only non-cycle darts and non-cycle edges. Those steps are unchanged in the cut map. Therefore the corresponding dart in cutCapCycle M C reaches one of the two duplicated banks of $C$.
Fresh cap darts are adjacent by $\alpha'$ to bank darts, so they also reach a bank.
Hence the cut-cap map has at most two connected components: the $+$-bank component and the $-$-bank component.
Formal lemma:
leanlemma cutCapCycle_components_le_two    (M : CombMap)    (hconn : M.Connected)    (C : SimplePrimalCycle M) :    ∀ x : Dart (cutCapCycle M C),      ConnectedTo x (some_plus_bank_dart C) ∨      ConnectedTo x (some_minus_bank_dart C)
Part B: the assumed dual path connects the two banks
A dual adjacency across a primal edge $a\notin E(C)$ means two old faces share the edge $a$. Since $a\notin E(C)$, that edge is not cut. Its two darts and its $\alpha$-pairing are unchanged in the cut-cap map.
Thus each step of the dual path lifts to a dart connectivity step in the cut-cap map.
More explicitly, suppose faces $f$ and $g$ are adjacent across edge $a=\{x,\alpha x\}\notin E(C)$. Then in the cut-cap map:


the dart corresponding to $x$ lies on the old face $f$;


the dart corresponding to $\alpha x$ lies on the old face $g$;


$x$ and $\alpha x$ are still paired by $\alpha'$.


Since face traversal uses $\phi'=\sigma'\alpha'$, darts in the same old face orbit are connected by $\sigma'$ and $\alpha'$. Therefore the two face-boundary dart sets are connected across $a$.
Induct along the dual path. The first face is incident with the $+$-bank of $e_i$, and the last face is incident with the $-$-bank of $e_i$. Therefore the $+$-bank and $-$-bank lie in the same connected component.
Together with Part A, the whole cut-cap map is connected.

5. Jordan lemma proof
Now prove:
leantheorem jordan_simple_cycle_of_chi_two    (M : CombMap)    (hconn : M.Connected)    (hchi : M.chi = 2)    (C : SimplePrimalCycle M)    (i : Fin C.length) :    ¬ Reachable (DualAvoidsCycle M C)        (face_left C i)        (face_right C i)
Proof:
Assume a dual path exists. By cutCapCycle_connected_of_dual_path,
lean(cutCapCycle M C).Connected
By the count lemma,


$$\chi(\operatorname{cutCap}(M,C))
=
\chi(M)+2
=
4.$$


But by Euler inequality for connected maps,


$$\chi(\operatorname{cutCap}(M,C))\le 2.$$


Contradiction.
In Lean shape:
lean  intro hpath  have hconn' :      (cutCapCycle M C).Connected :=    cutCapCycle_connected_of_dual_path M hconn C i hpath  have hchi' :      (cutCapCycle M C).chi = 4 := by    rw [cutCapCycle_chi, hchi]    norm_num  have hle :      (cutCapCycle M C).chi ≤ 2 :=    chi_le_two_of_connected (cutCapCycle M C) hconn'  omega
That is the exact combinatorial Jordan theorem you need.

6. Apply Jordan to a chord of the outer face
Now return to the near-triangulation.
Let the chord endpoints be $u$ and $v$, both vertices on the simple outer cycle $O$. Because $e$ is not an outer-boundary edge, the outer cycle splits into two nonempty boundary arcs between $u$ and $v$:


$$A_{uv},\qquad A_{vu}.$$


Pick one arc, say $A_{vu}$, directed from $v$ back to $u$. Orient the chord dart $d_e$ from $u$ to $v$. Then


$$C := d_e :: A_{vu}$$


is a directed simple primal cycle.
Formal lemma:
leanlemma chord_plus_outer_arc_is_simple_cycle    (M : CombMap)    (hNT : NearTriangulation M)    (e : Edge M)    (he : IsChord hNT.outerCycle e)    (A : OuterArc hNT.outerCycle e.end₁ e.end₂) :    SimplePrimalCycle M (chordConsArc e A)
Proof:


the outer cycle is simple, so the arc has no repeated vertices;


the chord endpoints are exactly the endpoints of the arc;


the chord edge is not an outer-boundary edge, so its edge orbit is not one of the arc edges;


the chord endpoints are distinct;


no interior vertex repetition is introduced.


Thus $C$ is simple.
Now suppose ¬ Separates hNT e. By your equivalence, this gives a path in the interior dual from the two chord-incident faces:
leanhpath :  Reachable (InteriorDualAvoidingBoundaryAndChord hNT e)    fL fR
Every edge used by this path is:


not the chord $e$;


not an outer-boundary edge.


But $C$ consists only of:


the chord $e$;


outer-boundary edges in the chosen arc.


Therefore every edge used by the path is not in $E(C)$. Hence the same path is also a path in DualAvoidsCycle M C.
Formal lemma:
leanlemma interiorDual_path_avoids_chord_cycle    (M : CombMap)    (hNT : NearTriangulation M)    (e : Edge M)    (he : IsChord hNT.outerCycle e)    (C : SimplePrimalCycle M)    (hC : C = chordConsArc e A)    {f g : Face M} :    Reachable (InteriorDualAvoidingBoundaryAndChord hNT e) f g →    Reachable (DualAvoidsCycle M C) f g
Proof by induction on the path. Each adjacency edge $a$ satisfies:
leana ≠ e¬ IsBoundaryEdge hNT.outerCycle a
Since every edge of $C$ is either $e$ or a boundary edge, $a\notin E(C)$.
Finally apply the Jordan lemma to the chord edge of $C$. Its two incident faces as an edge of $C$ are exactly the two chord-incident faces $f_L,f_R$.
leantheorem chord_separates    (M : CombMap)    (hNT : NearTriangulation M)    (hconn : M.Connected)    (hchi : M.chi = 2)    (e : Edge M)    (he : IsChord hNT.outerCycle e) :    Separates hNT e := by  classical  -- choose one boundary arc between endpoints of the chord  obtain ⟨A, hA⟩ := hNT.outerCycle.exists_arc_between_chord_endpoints e he  let C := chordConsArc e A  have hC : SimplePrimalCycle M C :=    chord_plus_outer_arc_is_simple_cycle M hNT e he A  intro hnotsep  -- convert non-separation into an interior-dual path  obtain ⟨p, hp⟩ :=    not_separates_iff_exists_interiorDual_path.mp hnotsep  have hpC :      Reachable (DualAvoidsCycle M C)        (chordFaceLeft hNT e he)        (chordFaceRight hNT e he) :=    interiorDual_path_avoids_chord_cycle      M hNT e he C rfl hp  exact    jordan_simple_cycle_of_chi_two      M hconn hchi C      (chord_edge_index_in_chordConsArc e A)      hpC
That proves Separates.

7. Why the tempting reachable-side double count is insufficient
The pure near-triangulation count


$$3(F_{\mathrm{inner}})=2E_{\mathrm{inner}}+E_{\partial}$$


or equivalently


$$3(F-1)=2E-B$$


is useful, but it does not by itself prove that a chord separates.
If $X$ is the set of inner faces reachable from one chord-incident face in the interior dual after deleting the chord and boundary edges, then under ¬ Separates, both chord-incident faces lie in $X$. Therefore the chord is internal to the patch $X$.
Because $X$ is a whole connected component of the modified interior dual, no non-boundary, non-chord edge crosses from $X$ to its complement. Thus the boundary of the patch consists only of original outer-boundary edges. It is possible, at the level of raw counting, for $X$ to be all inner faces. Then the usual triangulation identity is perfectly consistent:


$$V_X-E_X+F_X=1.$$


So the local double count does not force a contradiction. The missing information is exactly that the chord plus one outer arc is a Jordan cycle. Counting alone cannot distinguish a disk from a surface with a handle unless you import the inequality $\chi\le 2$ and use the cut-and-cap contradiction.
So the right minimal port is not the whole four-color hypermap theory. It is just:


connected maps satisfy $\chi\le 2$;


cutting and capping a simple cycle increases $\chi$ by $2$;


if the two sides of the cycle remain dual-connected after deleting the cycle edges, the cut-and-capped map is connected.


That is the finite-map Jordan fragment.

8. Minimal Gonthier-style fragment to port
If you want to mirror Gonthier’s hypermap development, port only this chain.
8.1 Genus / Euler inequality
Define for connected maps:
leandef genus (M : CombMap) : Nat :=  (2 - M.chi) / 2
Do not depend on division facts initially. Use the inequality version first:
leantheorem genus_nonnegative_as_chi_le_two    (M : CombMap)    (hconn : M.Connected) :    M.chi ≤ 2
Later, if needed, prove parity:
leantheorem chi_parity_connected    (M : CombMap)    (hconn : M.Connected) :    Even (2 - M.chi)
But for the chord lemma, parity is unnecessary.
8.2 Cut along a simple cycle
Port the hypermap operation corresponding to cutting a simple cycle and adding two faces:
leandef cutCapCycle (M : CombMap) (C : SimplePrimalCycle M) : CombMap
with:
leanlemma cutCapCycle_chi :  (cutCapCycle M C).chi = M.chi + 2
8.3 Jordan predicate
Define:
leandef JordanCycle (M : CombMap) (C : SimplePrimalCycle M) : Prop :=  ∀ i,    ¬ Reachable (DualAvoidsCycle M C)        (face_left C i)        (face_right C i)
Then prove:
leantheorem planar_simple_cycle_jordan    (M : CombMap)    (hconn : M.Connected)    (hchi : M.chi = 2)    (C : SimplePrimalCycle M) :    JordanCycle M C
Proof is exactly the cut-cap plus $\chi\le 2$ contradiction.
8.4 Chord application
Finally:
leantheorem chord_jordan_separates    (M : CombMap)    (hNT : NearTriangulation M)    (hconn : M.Connected)    (hchi : M.chi = 2)    (e : Edge M)    (he : IsChord hNT.outerCycle e) :    Separates hNT e
This theorem should be downstream of planar_simple_cycle_jordan, not upstream of the side-map constructions.

9. Final dependency order
I would implement in this order.
Layer J0: finite permutation / orbit lemmas
leancycleCount_mul_swap_eq_add_or_sub_oneorbit_count_restrict_spliceface_count_insert_edge_le_succ
These are generic finite permutation facts.
Layer J1: Euler inequality
leanunderlyingGraph_connected_of_map_connectedexists_spanningTreetree_rotation_has_one_faceface_count_bound_by_cyclomaticchi_le_two_of_connected
Main result:
leantheorem chi_le_two_of_connected :  M.Connected → M.chi ≤ 2
Layer J2: simple cycle cut-cap surgery
leandef cutCapCyclecutCapCycle_valid_alphacutCapCycle_valid_sigmacutCapCycle_vertex_countcutCapCycle_edge_countcutCapCycle_face_countcutCapCycle_chi
Main count:
lean(cutCapCycle M C).chi = M.chi + 2
Layer J3: connectivity of cut-cap from dual path
leandual_step_not_in_cycle_lifts_to_cutCap_connectiondual_path_not_in_cycle_lifts_to_bank_connectioncutCapCycle_components_le_twocutCapCycle_connected_of_dual_path
Main result:
leanReachable (DualAvoidsCycle M C) (face_left C i) (face_right C i)→ (cutCapCycle M C).Connected
Layer J4: Jordan theorem
leantheorem jordan_simple_cycle_of_chi_two :  M.Connected →  M.chi = 2 →  SimplePrimalCycle M C →  ¬ Reachable (DualAvoidsCycle M C) (face_left C i) (face_right C i)
Proof:


$$\chi(\operatorname{cutCap})=4$$


but connected maps have $\chi\le 2$.
Layer J5: outer chord cycle
leanouterCycle_two_arcschord_plus_outer_arc_is_simple_cycleedge_mem_chord_plus_arc_iff :  a ∈ C.edgeSet ↔ a = e ∨ IsBoundaryEdge outerCycle a
Layer J6: chord separates
leaninteriorDual_path_avoids_chord_plus_arcchord_separates
Proof:
Assume an interior-dual path from one chord face to the other. Convert it to a dual path avoiding $C$. Contradict Jordan.

10. The core proof in one paragraph
A chord $e=uv$ together with either outer-boundary arc from $v$ back to $u$ forms a simple primal cycle $C$. If the two chord-incident inner faces were connected in the interior dual after deleting $e$ and the boundary edges, then they would be connected in the full dual after deleting all edges of $C$. Cut the map along $C$ and cap the two resulting boundary cycles. This operation increases $V$ and $E$ by $|C|$, increases $F$ by $2$, and therefore increases Euler characteristic by $2$. Since the original map has $\chi=2$, the cut-and-capped map has $\chi=4$. The assumed dual path connects the two banks of the cut, so the cut-and-capped map is connected. But every connected finite combinatorial map satisfies $\chi\le 2$. Contradiction. Hence no such interior-dual path exists, so the chord separates.