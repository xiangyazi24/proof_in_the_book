# Ch13 construct-`σ` and the ch35 `PlaneSimpleGraph → CombMap` bridge

## Executive answer

Reusing ch35 helps, but it does **not** make Euler characteristic `2` free.

The current repo bridge

```lean
theorem PlaneSimpleGraph.toCombMap_isSphereMap
    (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.IsSphereMap
```

is a **transport theorem**, not a theorem deriving sphere-ness from geometry or from the raw `PlaneSimpleGraph` fields.  It proves `P.toCombMap.Connected` from `P.connected`, then rewrites the `CombMap` Euler characteristic to `P.eulerChar`; the equality `P.eulerChar = 2` is exactly the input `hsphere`.

So ch35 collapses some bookkeeping:

* connectedness of the dart map from graph connectedness;
* `V` quotient count from a vertex-incidence proof;
* `E` from dart pairing;
* `IsSimpleGraph` from `edge_darts` uniqueness;
* transport from `PlaneSimpleGraph.eulerChar` to `CombMap.eulerChar`.

But it does **not** prove the missing convex-polytope boundary Euler theorem.  The wall becomes:

```lean
P.IsSphereMap  -- i.e. P.eulerChar = 2
```

rather than

```lean
P.toCombMap.IsSphereMap  -- Connected ∧ CombMap.eulerChar = 2
```

That is a useful reduction, not a full sidestep.

## Exact repo facts

`ProofsInTheBook/PlaneSimpleGraph.lean` defines:

```lean
structure PlaneSimpleGraph (V D : Type*) [Fintype V] [DecidableEq V]
    [Fintype D] [DecidableEq D] where
  G : SimpleGraph V
  tail : D → V
  head : D → V
  α : Equiv.Perm D
  σ : Equiv.Perm D
  α_invol : α * α = 1
  α_no_fixed : ∀ d, α d ≠ d
  reverse_tail : ∀ d, tail (α d) = head d
  reverse_head : ∀ d, head (α d) = tail d
  dart_edge : ∀ d, G.Adj (tail d) (head d)
  edge_darts : ∀ {u v : V}, G.Adj u v → ∃! d : D, tail d = u ∧ head d = v
  σ_preserves_tail : ∀ d, tail (σ d) = tail d
  σ_vertex_cycle : ∀ d e : D, tail d = tail e → σ.SameCycle d e
  connected : G.Connected
```

Its own sphere predicate is just an Euler equation:

```lean
def PlaneSimpleGraph.numVertices (M : PlaneSimpleGraph V D) : ℕ := Fintype.card V

def PlaneSimpleGraph.numEdges (M : PlaneSimpleGraph V D) : ℕ := Fintype.card D / 2

def PlaneSimpleGraph.numFaces (M : PlaneSimpleGraph V D) : ℕ := M.toCombMap.F

def PlaneSimpleGraph.eulerChar (M : PlaneSimpleGraph V D) : ℤ :=
  (M.numVertices : ℤ) - (M.numEdges : ℤ) + (M.numFaces : ℤ)

def PlaneSimpleGraph.IsSphereMap (M : PlaneSimpleGraph V D) : Prop :=
  M.eulerChar = 2
```

The bridge file `ProofsInTheBook/PlaneSimpleGraphTriangulate.lean` proves the useful transports:

```lean
theorem PlaneSimpleGraph.toCombMap_V_eq_card
    (P : PlaneSimpleGraph V D)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.V = Fintype.card V

theorem PlaneSimpleGraph.toCombMap_E_eq_numEdges
    (P : PlaneSimpleGraph V D) :
    P.toCombMap.E = P.numEdges

theorem PlaneSimpleGraph.toCombMap_eulerChar_eq
    (P : PlaneSimpleGraph V D)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.eulerChar = P.eulerChar

theorem PlaneSimpleGraph.toCombMap_connected
    (P : PlaneSimpleGraph V D) :
    P.toCombMap.Connected

theorem PlaneSimpleGraph.toCombMap_isSphereMap
    (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.IsSphereMap

theorem PlaneSimpleGraph.toCombMap_isSimpleGraph
    (P : PlaneSimpleGraph V D) :
    P.toCombMap.IsSimpleGraph
```

The proof of `toCombMap_isSphereMap` is exactly:

```lean
theorem toCombMap_isSphereMap (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap) (hincident : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.IsSphereMap := by
  refine ⟨P.toCombMap_connected, ?_⟩
  rw [P.toCombMap_eulerChar_eq hincident]
  exact hsphere
```

So the missing fact is visibly `hsphere`.

## Does `PlaneSimpleGraph` beg the question?

For the ch13 purpose, yes, if the goal is to avoid proving Euler characteristic `2`.

The structure name says “plane,” but the fields do not include a topological embedding into `S²`, a Jordan curve certificate, or a theorem that faces are cells.  It stores a graph plus a rotation system and connectedness.  The actual planarity/sphere condition is the separate predicate:

```lean
P.IsSphereMap : Prop := P.eulerChar = 2
```

Therefore, exhibiting a convex polytope graph as a `PlaneSimpleGraph` gives a strong and useful rotation-system object, but it does not by itself produce `P.toCombMap.IsSphereMap`.  You still need either:

```lean
hsphere : P.IsSphereMap
```

or enough face/count facts to prove it.

## What ch35 really gives ch13

For construct-`σ`, ch35 can replace a custom bridge layer by the following pattern:

```lean
import ProofsInTheBook.PlaneSimpleGraphTriangulate
import ProofsInTheBook.ZinanCh13Euclidean

noncomputable section

open scoped Classical RealInnerProductSpace BigOperators
open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.PlaneSimpleGraph

namespace ProofsInTheBook.Ch13ConstructSigmaPlaneBridge

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Once the geometric construction is packaged as a `PlaneSimpleGraph`, the
existing ch35 bridge supplies the `CombMap` sphere proof, but only from the
plane graph Euler certificate `hsphere`. -/
theorem sphere_for_constructed_combMap
    (P : PlaneSimpleGraph V D)
    (hsphere : P.IsSphereMap)
    (hincident : ∀ v : V, ∃ d : D, P.tail d = v) :
    P.toCombMap.IsSphereMap :=
  P.toCombMap_isSphereMap hsphere hincident

/-- The simple-graph part is genuinely free from the `PlaneSimpleGraph` fields. -/
theorem simple_for_constructed_combMap
    (P : PlaneSimpleGraph V D) :
    P.toCombMap.IsSimpleGraph :=
  P.toCombMap_isSimpleGraph

end ProofsInTheBook.Ch13ConstructSigmaPlaneBridge
```

This is worth using.  It means ch13 does not need to reprove:

* quotient vertices correspond to graph vertices;
* graph connectivity gives dart-map connectivity;
* unique oriented graph darts imply `CombMap.IsSimpleGraph`;
* `CombMap.eulerChar` matches the plane-graph count.

But the ch13 object must still provide or prove `P.IsSphereMap`.

## Concrete reduction for a construct-`σ` convex boundary object

If the ch13 construction is refactored through `PlaneSimpleGraph`, the data should look like this:

```lean
structure Ch13ConstructedPlaneBoundary
    (V D : Type*) [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D] where
  P : PlaneSimpleGraph V D

  /-- Geometric coordinates and convex support data. -/
  pos : V → EuclideanSpace ℝ (Fin 3)

  /-- The constructed rotation agrees with the geometric angular rotation. -/
  sigma_eq_geo : P.σ = globalAngularPermOutward pos   -- schematic name

  /-- No isolated boundary vertex.  Needed to identify graph vertices with
  `P.toCombMap` vertex orbits. -/
  incident : ∀ v : V, ∃ d : D, P.tail d = v

  /-- The still-required Euler/sphere certificate. -/
  sphere : P.IsSphereMap
```

Then the final map obligations are short:

```lean
namespace Ch13ConstructedPlaneBoundary

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]
variable (X : Ch13ConstructedPlaneBoundary V D)

abbrev M : CombMap D := X.P.toCombMap

theorem M_isSphereMap : X.M.IsSphereMap :=
  X.P.toCombMap_isSphereMap X.sphere X.incident

theorem M_isSimpleGraph : X.M.IsSimpleGraph :=
  X.P.toCombMap_isSimpleGraph

end Ch13ConstructedPlaneBoundary
```

This is a good integration layer if `sphere` is accepted as a finite combinatorial input certificate.

## Can `sphere : P.IsSphereMap` be proved from the oriented triangular face list?

Yes, but that is not a ch35 theorem.  For a construct-`σ` object with explicit triangular face list `F`, edge pairing, and `σ = φ_face * α`, the proof of `P.IsSphereMap` reduces to finite counts:

```lean
P.eulerChar =
  (Fintype.card V : ℤ) - (Fintype.card D / 2 : ℤ) + P.toCombMap.F
```

If the face-list proof gives

```lean
P.toCombMap.F = Fintype.card F
```

and the edge pairing gives `Fintype.card D = 2 * E`, then `P.IsSphereMap` becomes the finite cardinal equation

```lean
(Fintype.card V : ℤ) - (E : ℤ) + (Fintype.card F : ℤ) = 2.
```

That is precisely the Euler wall in a smaller form.  You may choose to store that finite equation as a certificate:

```lean
euler_cert :
  (Fintype.card V : ℤ) - (edgeCount : ℤ) + (Fintype.card F : ℤ) = 2
```

or prove it from a convex-polytope boundary theorem.  ch35 does not prove this theorem for convex polytopes.

## Does ch35 contain a hidden general producer of `P.IsSphereMap`?

No general producer appears in the current files.

The triangle witness proves a special finite example:

```lean
theorem triangle_plane_isSphere : trianglePlaneSimpleGraph.IsSphereMap := by
  unfold PlaneSimpleGraph.IsSphereMap PlaneSimpleGraph.eulerChar PlaneSimpleGraph.numVertices
    PlaneSimpleGraph.numEdges
  rw [triangle_numFaces]
  norm_num

theorem triangle_toCombMap_isSphereMap : trianglePlaneSimpleGraph.toCombMap.IsSphereMap :=
  trianglePlaneSimpleGraph.toCombMap_isSphereMap triangle_plane_isSphere triangle_incident
```

That is a direct finite count for the triangle, not a theorem deriving planarity from arbitrary geometry or arbitrary rotation systems.

The five-color endpoint in the same file is also not a sphere producer:

```lean
structure PlaneTriangulationExtension (P : PlaneSimpleGraph V D) where
  D' : Type u'
  T : CombMap D'
  hNT : T.NearTriangulation
  ιV : V → T.Vertex
  adj_embed : ∀ {u v : V}, P.G.Adj u v → T.toSimpleGraph.Adj (ιV u) (ιV v)

theorem fiveColor_planeSimpleGraph_of_extension
    (P : PlaneSimpleGraph V D)
    (E : PlaneTriangulationExtension P) :
    P.G.Colorable 5
```

This consumes a triangulation extension certificate; it is about coloring, not about proving `P.IsSphereMap` for the input plane graph.

## Answer to the three questions

### 1. Can ch13 obtain `IsSphereMap` for free by exhibiting a `PlaneSimpleGraph`?

No.  It obtains `P.toCombMap.IsSphereMap` from `P.IsSphereMap`, not from `PlaneSimpleGraph` alone.

What is free after constructing `P : PlaneSimpleGraph V D`:

```lean
P.toCombMap.Connected
P.toCombMap.IsSimpleGraph
P.toCombMap.eulerChar = P.eulerChar       -- assuming every vertex is incident
```

What is not free:

```lean
P.eulerChar = 2
```

### 2. Does `PlaneSimpleGraph` require a sphere/planarity certificate as input?

The structure itself does not contain `P.IsSphereMap` as a field.  But every theorem that produces `CombMap.IsSphereMap` requires it as an input:

```lean
hsphere : P.IsSphereMap
```

There is no separate topological planarity axiom in the structure.  The effective sphere axiom is the Euler equation `P.eulerChar = 2`.

For a convex polytope’s geometric `σ_geo`, you can construct the rotation-system fields constructively:

```lean
σ_preserves_tail : ∀ d, tail (σ_geo d) = tail d
σ_vertex_cycle : ∀ d e, tail d = tail e → σ_geo.SameCycle d e
```

and the graph fields:

```lean
edge_darts : ∀ {u v}, G.Adj u v → ∃! d, tail d = u ∧ head d = v
connected : G.Connected
```

But these still do not imply `P.IsSphereMap` in the repo API.

### 3. Bottom line

Reusing ch35 **relocates** the Euler wall; it does not remove it.

The concrete reduction is:

```lean
-- construct from geometry/face list
P : PlaneSimpleGraph V D
hincident : ∀ v, ∃ d, P.tail d = v
hsphere : P.IsSphereMap        -- still required

-- get the ch13 map and its global hypotheses
M := P.toCombMap
M.IsSphereMap      := P.toCombMap_isSphereMap hsphere hincident
M.IsSimpleGraph    := P.toCombMap_isSimpleGraph
```

This is still a worthwhile shortcut because it avoids duplicating the `PlaneSimpleGraph → CombMap` transport work.  But if the ch13 objective is truly “derive sphere from raw convex geometry,” the hard missing theorem remains:

```lean
convex_polytope_boundary_face_list_euler_two : P.IsSphereMap
```

or, in finite face-list form:

```lean
(Fintype.card V : ℤ) - (edgeCount : ℤ) + (Fintype.card F : ℤ) = 2.
```

So the recommended path is:

1. Reuse `PlaneSimpleGraph` for the graph/rotation wrapper.
2. Reuse `toCombMap_isSphereMap` and `toCombMap_isSimpleGraph` for the bridge.
3. Treat `P.IsSphereMap` as a named ch13 input certificate initially.
4. Later either prove that certificate from a finite convex-boundary Euler theorem or store it as part of the boundary face-list data.

This turns the multi-month topology wall into a single explicit residue, but it does not eliminate it.