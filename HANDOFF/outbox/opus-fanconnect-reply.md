# Fan connectivity reply: `ProofsInTheBook/PlanarMapFanConnectivity.lean`

## Status: the `connected` field is now PROVEN UNCONDITIONALLY from the fan

`deleteVertex_connected_of_fan` discharges the `connected` field of
`FanSurgeryReconstruction` with **no certificate hypothesis** — only a
`BoundaryVertexFan hNT v0` and a dart `d0` representing `v0`
(`M.tail d0 = v0`).  It is not a conditional/isolated reduction: the
fan-geometric predicate that the reduction needs is itself proved from the fan.

```
theorem deleteVertex_connected_of_fan (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) :
    (M.deleteVertex d0).Connected
```

## Verification

* `lake env lean ProofsInTheBook/PlanarMapFanConnectivity.lean` — EXIT 0.
* `lake build ProofsInTheBook.PlanarMapFanConnectivity` — Build completed
  successfully (8428 jobs), no error/warning.
* `#print axioms` on all three headline results returns exactly
  `[propext, Classical.choice, Quot.sound]`:
  - `deleteVertex_connected_of_fan`
  - `deleteVertex_connected_of_neighborsConnected`
  - `deleteVertex_neighborsConnected_of_fan`
* 0 `sorry` / `admit` / `axiom` / `native_decide` in code (only the word
  "sorry-free" appears, in a docstring).
* Imports only `ProofsInTheBook.PlanarMapFanSurgery`; touches no other file.
  515 lines.

## Proof architecture (two independent layers, both unconditional)

### 1. The reduction (`deleteVertex_connected_of_neighborsConnected`)

`CombMap.Connected` is the dart-level
`∀ a b, ReflTransGen dartStep a b`, `dartStep a b := σ.SameCycle a b ∨ b = α a`.
Two facts make the deleted-map step relation transparent:

* `deleteVertex_sigma_sameCycle_iff` (existing): a deleted-map σ-step between
  survivors is exactly an `M`-σ-step (an *iff*, not coarser);
* `deleteVertex_alpha_apply_coe` (existing): `(deleteVertex).α x` is `M.α x.1`,
  and `α` preserves survival (`alpha_mem_deleteVertexSet_iff`), so an α-step
  *never* leaves the survivors.

Hence the only way an `M`-`dartStep` walk can leave the survivors is a σ-step
into the deleted star of `v0`.  I fix a base survivor and prove every survivor
reaches it, by a single backward `ReflTransGen.head_induction_on` over an
`M`-walk (from `M.Connected`) carrying the invariant

```
Inv r c := (c ∉ S → Rel ⟨c⟩ r) ∧ (c ∈ S → ∀ neighbour-survivor a, Rel a r)
```

The σ-into-deleted gap and the deleted-region bookkeeping both close using the
predicate `DeleteVertexNeighborsConnected M v0` — "any two surviving darts whose
vertices are neighbours of `v0` are deleted-map-connected".  This predicate is
strictly weaker than the conclusion (it constrains only neighbour darts), is
satisfiable (true for any real chordless boundary deletion, e.g. the
tetrahedron `t = 1`), and is genuinely load-bearing — it is exactly the local
fact the `TwoEdgePathObstruction` shows fails when the fan is absent.

### 2. Discharging the predicate from the fan (`deleteVertex_neighborsConnected_of_fan`)

The fan path `x, z₁, …, z_t, w` reconnects all neighbours of `v0` among the
survivors:

* `fanTriangle_edge_dart_survives` — for a fan triangle `(v0, a, b)`, its middle
  dart `T.d1` (tail `a`, head `b`) survives deletion (both endpoints `≠ v0`).
* `fanTriangle_connects` / `fanTriangle_vconn` — that surviving edge dart plus
  its reverse `α T.d1` give a deleted-map path joining any survivor at vertex
  `a` to any survivor at vertex `b`.
* `vconn_head_of_pairs` — a `consecutivePairs` list induction chaining the fan
  triangles, maintaining a surviving witness dart at the running head, so every
  fan-path vertex is connected to the head `fan.x`.
* `neighbor_tail_mem_path` — a neighbour-survivor's vertex is the head of a
  rotation dart (`vertexDarts_eq` + `heads_eq`), hence lies on the fan path.

Two neighbour-survivors therefore both connect to `fan.x`, and through a witness
at `fan.x` to each other.

## Net result

The headline `(M.deleteVertex d0).Connected` is obtained as
`deleteVertex_connected_of_neighborsConnected M d0 hNT.sphere.1
   (deleteVertex_neighborsConnected_of_fan fan htail0)` —
`M.Connected` from the ambient sphere map, the reconnection from the fan.  The
`connected` field is fully closed; nothing is left as a certificate.

## Public API (`…PlanarMap.CombMap` / `…CombMap.NearTriangulation`)

```
deleteVertex_dartStep_of_alpha / _of_sigma / _symm        -- step lifting/symmetry
deleteVertex_reachable_symm
DeleteVertexNeighborsConnected (M v) : Prop               -- fan-geometric residue (now discharged)
deleteVertex_connected_of_neighborsConnected             -- the reduction (unconditional)
NearTriangulation.deleteVertex_neighborsConnected_of_fan -- predicate proved from the fan
NearTriangulation.deleteVertex_connected_of_fan          -- headline: connected, unconditional
```

## Suggested wiring (for the owner of PlanarMapFanSurgery.lean, not done here)

The `connected` field of `FanSurgeryReconstruction` (and the `connected` field
of `BoundaryDeletionData`) can now be supplied by
`hNT.deleteVertex_connected_of_fan fan htail0` instead of being carried as
surgery output, reducing the reconstruction's four residual fields to three
(`vertexQuotient`, `facesMerge`, `outerCycle`).
