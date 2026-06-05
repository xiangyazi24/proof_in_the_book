# opus-delbound reply — PlanarMapDeletedBoundary.lean

## Status: DONE, verified clean (0 sorry / 0 axiom / clean-3)

New file `ProofsInTheBook/PlanarMapDeletedBoundary.lean` (389 lines), imports only
the **stable** `ProofsInTheBook.PlanarMapFanFaces` (built successfully, 8431-job
full build). It does NOT import `PlanarMapFanMergedOrbit.lean` because that file is
currently being rewritten by a parallel agent and is mid-edit / broken on disk
(genuine build error at the relocated `survivor_on_fanTriangle_eq_d1` call,
~line 480 — see note below); my module is fully independent of it.

## Verification

```
rsync … PlanarMapDeletedBoundary.lean uisai1:…
ssh uisai1 'lake env lean ProofsInTheBook/PlanarMapDeletedBoundary.lean'   → EXIT=0, no errors/warnings
ssh uisai1 'lake build ProofsInTheBook.PlanarMapDeletedBoundary'          → Build completed successfully (8431 jobs)
#print axioms (all 4 headline decls)  → [propext, Classical.choice, Quot.sound]  (no sorryAx / ofReduceBool / trustCompiler)
grep sorry|admit|^axiom|native_decide  → none (only the word "sorry-free" in a docstring)
```

## What was built (substantive, not a wrapper)

1. **Explicit normalized boundary-cycle constructor `CombMap.boundaryCycleOfFace`.**
   The cyclic dart list of any face is the concrete `M.φ.toList root =
   [root, φ root, φ² root, …]`. ALL orbit-algebraic `BoundaryCycle` fields are
   PROVEN from the Mathlib `Equiv.Perm.toList` API (no certificate):
   - `NormalizedCyclicDartList` (head = root, root_face, nodup via `nodup_toList`,
     length_pos, `toFinset = faceOrbitFinset` via `mem_toList_iff` ↔ same `φ`-cycle);
   - `consecutive_phi`: `darts[(i+1)%n] = φ darts[i]`, proved via `getElem_toList`
     (`darts[k] = φ^k root`) + `φ^n root = root` (`pow_mod_card_support_cycleOf`)
     + the `n*q + r` split — pure orbit algebra;
   - `consecutive_vertex` from `consecutive_phi` + `tail_phi`;
   - `vertices_eq`, `edges_eq` definitional.
   The ONLY input left to `boundaryCycleOfFace` is the `arcSplit` function — the
   genuinely planar Jordan-curve pairing, which the whole `PlanarMap` layer treats
   as data (`hNT.outerCycle` is itself a `NearTriangulation` field; there is no
   generic `BoundaryCycle` derivation anywhere in the repo).

2. **`DeletedOuterBoundary.ofMergedFace`** — assembles the EXACT input structure of
   `fanSurgeryReconstruction` for the deleted map's merged outer face, using
   `boundaryCycleOfFace` on `(M.deleteVertex d0)`. `φ'` nontriviality at the root is
   discharged from `deleteVertex_isSimpleGraph` (`phi_ne_self_of_isSimpleGraph`), so
   the explicit list `[root, φ' root, φ'² root, …]` is the new boundary cycle. The
   remaining inputs are exactly the planar residues: `arcSplit`, the vertex-list
   simplicity `outer_simple` (= the fan-path-simple ∪ old-boundary-arc Nodup),
   `outer_len_ge_three`, and `inner_tri`.

3. **The single isolated certificate `DeletedMergedBoundaryCertificate`** (the
   "at most ONE isolated Prop" allowance) bundles exactly the two residues the
   orbit-algebra fan layer cannot produce:
   - `mergedOrbit : DeleteVertexMergedFaceSingleOrbit M d0` (the φ-seam single-orbit
     fact — already a named Prop in `PlanarMapFanFaces`, satisfiable on the
     tetrahedron, strictly about incident survivors; the parallel
     `PlanarMapFanMergedOrbit` discharges it from the fan + outer-arc residue);
   - `boundary : DeletedOuterBoundary hNT d0` (now constructible via #2).

4. **End-to-end endpoint** `deleteBoundaryVertex_nearTriangulation_final` and the
   inductive-step / vertex-decrease / Euler-count corollaries, all assembled from
   `fan + htail0 + cert` through `fanSurgeryReconstruction` →
   `FanSurgeryReconstruction.nearTriangulation`. The three dart-rotation surgery
   fields (`vertexQuotient`, `facesMerge`, `connected`) and the local `NoLoopAt` /
   `VertexFacesDistinct` are all discharged UNCONDITIONALLY upstream.

## Faithfulness (§3.3 self-audit)

- Neither certificate field is the deletion goal `NearTriangulation (M.deleteVertex
  d0)`; both are strictly weaker planar data. Not vacuous (both hold for the
  tetrahedron `t=1`). The headline returns real `NearTriangulation` data, not `True`.
- The three `:= rfl` are legitimate (a `cyclicNext` index value used in a proof, and
  the definitional `vertices_eq`/`edges_eq` fields).

## Note for the parallel merged-orbit agent

`PlanarMapFanMergedOrbit.lean` does NOT build on `uisai1` right now (Type mismatch at
the relocated `survivor_on_fanTriangle_eq_d1`/`fanTriangle_edge_dart_sameCycle_ref`
calls, ~L480). My file consumes only `DeleteVertexMergedFaceSingleOrbit` (the Prop)
as the `mergedOrbit` certificate field, so once that agent lands a clean
`deleteVertexMergedFaceSingleOrbit_of_fan`, the `mergedOrbit` field can be discharged
from the fan + the outer-arc reconnection with zero changes to my file.

## Not committed (per repo policy; remote is on a different branch with a dirty tree).
Local file: `/Users/huangx/repos/proof_in_the_book/ProofsInTheBook/PlanarMapDeletedBoundary.lean`
