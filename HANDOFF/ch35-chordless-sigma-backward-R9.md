═══ BRIDGE pbook | d8c1197b | 10918 chars 1461 words 272 lines | 273s | prov=network | OK ═══
═══ BRIDGE pbook | d8c1197b | 10918 chars 1461 words 272 lines | 273s | prov=network | OK ═══
**Verdict:** the obstruction is a **fixable convention mismatch**, not a genuine chirality input, provided you are allowed to restate the fan interface and deletion consumer to use the σ-predecessor direction. The existing `BoundaryVertexFan` interface is σ-forward and therefore asks for the wrong local face orientation; your machine-checked “forward forces degree two” result is exactly the diagnosis. The deletion connectivity argument itself is direction-agnostic: it needs a path of neighbor vertices whose consecutive pairs are joined by fan triangles, not the σ-forward orientation specifically.

The current interface hard-codes the mismatch: `NeighborRotationOrder` requires the neighbor list to be the heads of darts in σ-forward order via `consecutive_sigma`, while `IncidentNonOuterFacesExactly` asks for `FanTriangle hNT v0 a b` along consecutive pairs of that same path. fileciteturn154file0L91-L116 The fan-existence file’s own comments describe exactly your finding: the σ-forward spoke-head list gives pairs `(head s_i, head s_{i+1})`, but the actual face between consecutive spokes is oriented as `(v0, head s_{i+1}, head s_i)`, so the natural local triangle is σ-predecessor-facing, not σ-forward-facing. fileciteturn93file0L52-L74

## 1. Why σ-backward is the right formal orientation

Let `e` be an inner spoke at `v0`. You proved:

```lean
M.head (M.φ e) = M.head (M.σ.symm e)
```

Since `M.φ e` is the next dart in the triangular face of `e`, the natural fan triangle is:

```lean
FanTriangle hNT v0 (M.head e) (M.head (M.σ.symm e))
```

So the correct neighbor path is the σ-inverse head list:

```lean
[head e₀, head (σ⁻¹ e₀), head (σ⁻² e₀), ...]
```

not the σ-forward head list:

```lean
[head e₀, head (σ e₀), head (σ² e₀), ...].
```

That exactly matches the tetrahedron trace in the repo comment: with σ-spokes `[s₀,s₁,s₂]`, the real fan path is `[head s₂, head s₁, head s₀]`, and consecutive pairs correspond to the faces `face(s₂)` and `face(s₁)`. fileciteturn93file0L52-L57

So the σ-backward version is not choosing arbitrary handedness. It is the handedness already encoded by:

```lean
φ = σ * α
```

and by the chosen orientation of the outer face.

## 2. The deletion consumer is direction-agnostic

The deletion connectivity proof only needs that the neighbors of `v0` are connected through the surviving fan path. Its local predicate is:

```lean
DeleteVertexNeighborsConnected M v
```

which says neighbor-survivor darts are connected after deleting the closed star. The file comments describe it as the fan-path content `x, z₁, …, z_t, w`: consecutive fan triangles supply surviving edges `z_i z_{i+1}` joining the neighbors. fileciteturn155file0L30-L40

The proof machinery makes the direction irrelevance explicit. It defines a symmetric vertex-connection relation `VConn`, and proves `VConn.symm`. fileciteturn156file0L19-L28 Then `vconn_head_of_pairs` chains along `consecutivePairs` of the path to connect every path vertex to the head. Reversing the path still gives a valid chain, just in the opposite direction, and symmetry supplies the same connectivity. fileciteturn156file0L50-L98

The final consumer:

```lean
deleteVertex_neighborsConnected_of_fan
```

uses only:

```lean
fan.path
fan.incident_faces_exact.triangle_of_pair
neighbor_tail_mem_path fan ...
```

It does not inspect whether `fan.path` came from σ or σ⁻¹. fileciteturn156file0L133-L178 The σ-forward dependence enters only through the current `BoundaryVertexFan.rotation_order` field, not through the graph-theoretic deletion argument.

## 3. Restate the interface with σ⁻¹

Introduce a backward rotation order:

```lean
structure NeighborRotationOrderPred
    (M : CombMap D) (v0 : M.Vertex)
    (neighbors : List M.Vertex) where
  darts : List D
  darts_nodup : darts.Nodup
  darts_nonempty : 0 < darts.length
  tails_eq : darts.map M.tail = List.replicate darts.length v0
  heads_eq : darts.map M.head = neighbors
  consecutive_sigma_inv :
    ∀ i : Fin darts.length,
      darts.get (cyclicNext darts_nonempty i) =
        M.σ.symm (darts.get i)
```

Then define the backward fan certificate:

```lean
structure BoundaryVertexFanPred
    (hNT : NearTriangulation M) (v0 : M.Vertex) where
  x : M.Vertex
  interior : List M.Vertex
  w : M.Vertex

  v0_boundary : hNT.outerCycle.IsBoundaryVertex v0
  x_boundary : hNT.outerCycle.IsBoundaryVertex x
  w_boundary : hNT.outerCycle.IsBoundaryVertex w

  rotation_order_pred :
    NeighborRotationOrderPred M v0 (fanPath x interior w)

  incident_faces_exact :
    IncidentNonOuterFacesExactly hNT v0 (fanPath x interior w)

  path_nodup_of_chordless :
    BoundaryChordless hNT.outerCycle → (fanPath x interior w).Nodup

  interior_not_boundary_of_chordless :
    BoundaryChordless hNT.outerCycle →
      ∀ z : M.Vertex, z ∈ interior → ¬ hNT.outerCycle.IsBoundaryVertex z

  empty_iff_base_triangle_of_chordless :
    BoundaryChordless hNT.outerCycle → (interior = [] ↔ hNT.IsBaseTriangle)
```

The `IncidentNonOuterFacesExactly` structure itself does **not** need to change. It already says that each consecutive pair of the path has a `FanTriangle`, and that every non-outer face incident with `v0` appears exactly once. fileciteturn154file0L105-L117 What changes is the path order fed into it.

## 4. The σ-derived face theorem you should prove

For a σ-backward dart list:

```lean
backDarts := (M.σ.symm).toList start
backHeads := backDarts.map M.head
```

prove:

```lean
theorem backward_incident_faces_exact
    :
    IncidentNonOuterFacesExactly hNT v0 backHeads
```

The key constructor is:

```lean
lemma fanTriangle_of_spoke_pred
    {e : D}
    (htail : M.tail e = v0)
    (hinner : M.dartFace e ≠ hNT.outerFace) :
    FanTriangle hNT v0 (M.head e) (M.head (M.σ.symm e))
```

This is exactly your `spokeFace_head_eq` packaged with `hNT.inner_face_isFaceTriangle`.

Then `triangle_of_pair` follows because consecutive pairs in `backHeads` have the form:

```lean
(M.head e, M.head (M.σ.symm e)).
```

The `exact_faces` field follows by the usual orbit argument: every non-outer face incident at `v0` has a unique dart `e` with `tail e = v0`, and since it is non-outer, it is not the unique outer-face dart at that boundary vertex. The local triangle is exactly the one supplied by `fanTriangle_of_spoke_pred`.

This proof is σ-algebraic plus the already-landed facts:

```lean
dart_eq_of_same_face_same_tail
inner_face_isFaceTriangle
BoundaryCycle.mem_darts_iff
outer vertex nodup
```

No extra handedness input is needed.

## 5. Refactor the deletion theorem to a direction-free core

Rather than duplicating all of `deleteVertex_neighborsConnected_of_fan`, factor it through a smaller path certificate:

```lean
structure FanPathConnectivityData
    (hNT : NearTriangulation M) (v0 : M.Vertex)
    (path : List M.Vertex) where
  faces_exact :
    IncidentNonOuterFacesExactly hNT v0 path

  neighbor_tail_mem_path :
    ∀ {d0 : D} (htail0 : M.tail d0 = v0)
      {x : {d : D // d ∉ M.deleteVertexSet d0}},
      (∃ e ∈ M.deleteVertexSet d0, M.σ.SameCycle e x.1) →
        M.tail x.1 ∈ path

  path_has_edge :
    ∃ a b rest, path = a :: b :: rest
```

Then prove:

```lean
theorem deleteVertex_neighborsConnected_of_fanPath
    (data : FanPathConnectivityData hNT v0 path)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    M.DeleteVertexNeighborsConnected d0
```

This is just the existing proof of `deleteVertex_neighborsConnected_of_fan`, with `fan.path`, `fan.incident_faces_exact`, and `neighbor_tail_mem_path` abstracted. The current proof already has that shape: it builds `htri` from `incident_faces_exact.triangle_of_pair`, connects path vertices to the head with `vconn_head_of_pairs`, and uses `neighbor_tail_mem_path` to put neighbor-survivors on the path. fileciteturn156file0L136-L178

Then both old and new fan directions can feed the same theorem.

For the backward fan, prove:

```lean
lemma neighbor_tail_mem_path_pred
    (fan : BoundaryVertexFanPred hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0)
    {x : {d : D // d ∉ M.deleteVertexSet d0}}
    (hx : ∃ e ∈ M.deleteVertexSet d0, M.σ.SameCycle e x.1) :
    M.tail x.1 ∈ fan.path
```

The proof is the same as the current `neighbor_tail_mem_path`, except that `rotation_order_pred` enumerates the same σ-orbit using σ⁻¹. Since σ and σ⁻¹ have the same cycles, the vertex-dart-set enumeration lemma is identical in substance.

## 6. Is there a global consistency requirement?

There is a global consistency requirement only in the weak sense that you must use **one convention consistently**. You cannot mix σ-forward fan triangles at some vertices with σ-backward triangles at others unless the rest of the deletion/reconstruction code knows how to interpret them.

But there is no additional “chirality oracle” needed. The correct convention is determined by the map algebra:

```lean
φ = σ * α
```

and the chosen orientation of the outer face. The natural local fan is σ-predecessor-oriented everywhere. If the deleted outer boundary later needs the opposite cyclic orientation, you reverse the boundary cycle certificate correspondingly; a `BoundaryCycle` can be represented in either cyclic direction only if its `consecutive_phi` field matches the chosen map’s face permutation, so the reconstruction must choose the direction that the deleted `φ` actually follows. That is bookkeeping, not a new topological chirality input.

## 7. What is impossible without refactoring

The current `BoundaryVertexFan` interface probably cannot be filled for nontrivial fans if it insists on:

```lean
rotation_order : NeighborRotationOrder M v0 (fanPath x interior w)
```

with `consecutive_sigma`, and simultaneously:

```lean
incident_faces_exact :
  IncidentNonOuterFacesExactly hNT v0 (fanPath x interior w)
```

using σ-forward consecutive pairs. Your theorem

```lean
forward_fanTriangle_forces_degree_two
```

shows exactly that.

So:

```text
Existing forward BoundaryVertexFan API: needs a genuine, impossible/mis-oriented certificate.
Backward/refactored API: σ-derivable.
Deletion connectivity consumer: direction-agnostic.
```

## Final answer

Yes: the forward-vs-backward problem is a **convention mismatch**. The chordless fan can be made σ-derivable by restating the fan path in σ-predecessor order:

```lean
neighbors = (σ⁻¹-star darts).map head
```

and using the natural triangles:

```lean
FanTriangle hNT v0 (head e) (head (σ⁻¹ e)).
```

The Thomassen deletion connectivity proof only needs a path of surviving neighbor vertices connected by fan triangles; it does not care which direction the path is traversed. To close this in Lean, introduce `NeighborRotationOrderPred` or a direction-free `FanPathConnectivityData`, then adapt `deleteVertex_neighborsConnected_of_fan` to consume that. The existing σ-forward `BoundaryVertexFan` structure is the source of the false obligation, not the mathematics of the deletion step.
