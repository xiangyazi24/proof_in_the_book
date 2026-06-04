Use darts-only combinatorial maps. It is cleaner than a separate vertex set.
0. Critical correction
A finite rotation system alone is not a plane graph. It is an orientable cellular map on some closed orientable surface. Euler $V-E+F=2$ holds only for the sphere / genus-zero subclass.
Counterexample: one vertex, two loops, one face gives $V-E+F=1-2+1=0$, a torus map.
So define raw maps first, then define IsPlane by a reduction/induction certificate.

1. Raw combinatorial map
leanimport Mathlib.Data.Fintype.Basicimport Mathlib.GroupTheory.Perm.Cycle.Typeimport Mathlib.Combinatorics.SimpleGraph.Connectivityopen Equivstructure CombMap where  D : Type  [fintypeD : Fintype D]  [decEqD : DecidableEq D]  -- edge involution on darts  α : Equiv.Perm D  -- vertex rotation  σ : Equiv.Perm D  α_invol : α * α = 1  α_no_fixed : ∀ d : D, α d ≠ d
Add instances:
leanattribute [instance] CombMap.fintypeD CombMap.decEqD
Definitions:
leannamespace CombMapdef φ (M : CombMap) : Equiv.Perm M.D :=  M.σ * M.α-- convention: face permutation = σ ∘ α
Vertices, edges, faces are orbits/cycles:
leandef VertexSet (M : CombMap) :=  Quotient (Equiv.Perm.SameCycle.setoid M.σ)def EdgeSet (M : CombMap) :=  Quotient (Equiv.Perm.SameCycle.setoid M.α)def FaceSet (M : CombMap) :=  Quotient (Equiv.Perm.SameCycle.setoid M.φ)
Cardinal counts:
leannoncomputable def V (M : CombMap) : Nat :=  Fintype.card M.VertexSetnoncomputable def E (M : CombMap) : Nat :=  Fintype.card M.EdgeSetnoncomputable def Fraw (M : CombMap) : Nat :=  Fintype.card M.FaceSet
Because the dart-only face definition gives zero faces for the empty map, use:
leannoncomputable def F (M : CombMap) : Nat :=  if h : IsEmpty M.D then 1 else M.Fraw
For nonempty maps, F = Fraw.
Edges have exactly two darts because α is fixed-point-free involution:
leanlemma edge_orbit_card_two  (M : CombMap) (d : M.D) :  Fintype.card {x : M.D // M.α x = d ∨ x = d} = 2 := by  -- formal proof from α_invol and α_no_fixed  sorry
Then:
leanlemma two_mul_E_eq_card_darts (M : CombMap) :  2 * M.E = Fintype.card M.D := by  -- quotient into α-orbits, each orbit size 2  sorry

2. Connectivity
Define adjacency on vertices by an edge.
Two darts are in the same vertex iff same σ-orbit.
leandef vOf (M : CombMap) (d : M.D) : M.VertexSet :=  Quotient.mk _ ddef edgeRel (M : CombMap) (u v : M.VertexSet) : Prop :=  ∃ d : M.D, M.vOf d = u ∧ M.vOf (M.α d) = v
Connectivity:
leandef Connected (M : CombMap) : Prop :=  ∀ u v : M.VertexSet,    Relation.ReflTransGen M.edgeRel u v
This is graph connectivity of the underlying multigraph.

3. Plane maps
Do not define IsPlane M := V - E + F = 2; that makes Euler tautological.
Define it inductively by sphere-preserving constructions/reductions.
Best Lean-friendly version:
leaninductive IsPlane : CombMap → Prop| oneVertex :    IsPlane emptyOneVertexMap| addBridge :    IsPlane M →    -- attach a new vertex by one new edge in some corner    IsPlane (M.addBridge ...)| addFaceEdge :    IsPlane M →    -- add an edge between two corners of the same face,    -- splitting that face into two faces    IsPlane (M.addFaceEdge ...)
Equivalently, for deletion induction:
leaninductive PlaneReducible : CombMap → Prop| base :    PlaneReducible emptyOneVertexMap| contractBridge_inv :    PlaneReducible M →    PlaneReducible (M.expandBridge ...)| deleteNonBridge_inv :    PlaneReducible M →    PlaneReducible (M.expandFaceEdge ...)
Then define:
leandef IsPlane (M : CombMap) : Prop :=  PlaneReducible M
This is not circular and exactly captures sphere maps generated from one vertex by planar edge insertions.

4. Euler formula
State with integer subtraction:
leantheorem euler_formula  (M : CombMap)  (hconn : M.Connected)  (hplane : IsPlane M) :  (M.V : Int) - (M.E : Int) + (M.F : Int) = 2 := by  -- induction on hplane  sorry
The proof is by induction on the plane construction certificate.

5. Induction proof
Base
emptyOneVertexMap has:
leanV = 1E = 0F = 1
So:
lean1 - 0 + 1 = 2
Bridge expansion
Adding a bridge to a connected plane map:
leanV' = V + 1E' = E + 1F' = F
Therefore:
lean(V + 1) - (E + 1) + F = V - E + F
So Euler is preserved.
The inverse deletion/contraction statement is:
leanlemma contract_bridge_counts :  V M' = V M - 1 ∧  E M' = E M - 1 ∧  F M' = F M
where M' = M.contractBridge e.
Non-bridge / face-edge expansion
Adding an edge inside one face splits that face into two:
leanV' = VE' = E + 1F' = F + 1
Therefore:
leanV - (E + 1) + (F + 1) = V - E + F
The inverse deletion statement is:
leanlemma delete_nonbridge_counts :  V M' = V M ∧  E M' = E M - 1 ∧  F M' = F M - 1
where M' = M.deleteNonBridge e.

6. Tree base alternative
For connected plane maps whose underlying graph is a tree:
leanlemma tree_face_count :  M.IsTree → M.F = 1lemma tree_edge_count :  M.IsTree → M.E = M.V - 1
Then:
leanV - E + F= V - (V - 1) + 1= 2
This is often useful for the five-color proof later.

7. Mathlib pieces that help
Use:
leanEquiv.PermEquiv.Perm.SameCycleEquiv.Perm.cycleTypeFintype.cardFinsetQuotientRelation.ReflTransGen
Useful existing ideas:
leanEquiv.Perm.IsCycleEquiv.Perm.SameCycleEquiv.Perm.cycleType
For graph connectivity, either define your own relation on VertexSet, or later build a SimpleGraph shadow graph and use Mathlib connectivity APIs.

Clean lemma list
Implement in this order:
leanstructure CombMapdef CombMap.φdef CombMap.VertexSetdef CombMap.EdgeSetdef CombMap.FaceSetdef CombMap.Vdef CombMap.Edef CombMap.Frawdef CombMap.Flemma α_orbit_card_twolemma two_mul_E_eq_card_dartsdef CombMap.vOfdef CombMap.edgeReldef CombMap.Connecteddef emptyOneVertexMapdef addBridgelemma addBridge_Vlemma addBridge_Elemma addBridge_Flemma addBridge_connecteddef addFaceEdgelemma addFaceEdge_Vlemma addFaceEdge_Elemma addFaceEdge_Flemma addFaceEdge_connectedinductive IsPlane| oneVertex| addBridge| addFaceEdgetheorem euler_formula :  M.Connected →  IsPlane M →  (M.V : Int) - (M.E : Int) + (M.F : Int) = 2
Main warning: do not state Euler for arbitrary rotation systems. The correct theorem is for IsPlane M, where IsPlane is a genuine inductive genus-zero certificate.
