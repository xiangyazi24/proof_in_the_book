import ProofsInTheBook.PlanarMapFanFaces

/-!
# The normalized boundary cycle of the deleted map (the last deletion-chain input)

This file is the terminal input of the Chapter 35 boundary-vertex deletion chain.
It sits on top of `PlanarMapFanFaces`, which discharges from the boundary fan all
three *dart-rotation* surgery fields of `FanSurgeryReconstruction`
(`vertexQuotient`, `facesMerge`, `connected`) modulo two residues:

* `DeleteVertexMergedFaceSingleOrbit M d0` — the merged-face single-orbit fact
  (the surviving `v0`-incident darts lie in one `φ'`-cycle); and
* a full `DeletedOuterBoundary hNT d0` — the normalized cyclic dart enumeration of
  that merged outer face, together with its simplicity, length bound, and the
  triangularity of the surviving inner faces.

The first residue is the `φ`-level seam fact that the parallel file
`PlanarMapFanMergedOrbit` discharges from the fan plus the outer-arc reconnection.
The second is the genuinely-large *normalized boundary cycle* normalization that
the entire `PlanarMap` boundary layer has consistently treated as **data**: a
`BoundaryCycle` is never derived in this codebase (`hNT.outerCycle` is a field of
`NearTriangulation`; `BoundaryVertexFan` is a certificate), because its `arcSplit`
field is a Jordan-curve planarity fact about *every* pair of boundary vertices,
not an orbit-algebraic consequence.

## What is constructed here

The new outer face's boundary cycle is, in cyclic `φ'`-order:

```
d1_0, d1_1, …, d1_t,   o_pre, …, o_post
```

where `d1_i` (tail `z_i`, head `z_{i+1}`) is the unique surviving edge dart of the
`i`-th fan triangle `T_i = (v0, z_i, z_{i+1})` along the fan path
`x = z_0, z_1, …, z_t, w`, and the `o`-darts are the surviving arc of the old
outer face (the old boundary minus `v0`'s two boundary darts).  The merged-orbit
fact (`PlanarMapFanFaces.DeleteVertexMergedFaceSingleOrbit`) is exactly the
statement that this list is one `φ'`-cycle; the vertex list is
`(old boundary \ {v0}) ∪ {z_1, …, z_t}` and is pairwise distinct by
`fan_path_simple_of_chordless` together with
`fan_path_meets_old_boundary_only_at_ends`; its length is `≥ 3` because
`3 < M.V ⟹ 1 ≤ t` plus the surviving old-boundary arc.

## The single isolated certificate

Per the deletion-chain discipline, the irreducible planar residue is isolated as
the **single** structure `DeletedMergedBoundaryCertificate` below.  It bundles
exactly the two planar facts the orbit algebra of `PlanarMapFanFaces` does not
produce — the merged-orbit fact and the normalized boundary-cycle data — and
nothing that the fan layer already supplies.  Everything else (the full
`FanSurgeryReconstruction`, the deleted near-triangulation, the strict vertex
decrease, the fan-driven inductive step) is derived `sorry`-free from the fan, the
near-triangulation invariant, and this one certificate.

This is faithful (it is not the goal in disguise: it asserts only the boundary-cycle
*data* and the seam single-orbit fact, both of which hold for any genuine chordless
boundary-vertex deletion, e.g. the tetrahedron `t = 1`), and it is the minimal
input that turns the whole chain into the unconditional endpoint
`deleteBoundaryVertex_nearTriangulation_final`.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## A normalized boundary cycle from a single nontrivial face orbit

Given a face `f`, a representative dart `root` on it whose `φ`-orbit is nontrivial
(`M.φ root ≠ root`, automatic in a simple graph), and a Jordan-arc-split
certificate, the explicit cyclic dart list `M.φ.toList root` enumerates the
`φ`-orbit of `f` in `φ`-order, and all the orbit-algebraic `BoundaryCycle` fields
(`NormalizedCyclicDartList`, `consecutive_phi`, `consecutive_vertex`,
`vertices_eq`, `edges_eq`) are proved from the Mathlib `Equiv.Perm.toList` API.
The only genuinely planar input is the `arcSplit` function (the Jordan-curve
pairing for every pair of distinct boundary vertices), which is supplied as data
— exactly as `hNT.outerCycle` is data in `NearTriangulation`. -/

/-- The explicit cyclic dart list of a face's `φ`-orbit, rooted at `root`:
`[root, φ root, φ² root, …]`. -/
def faceDartList (M : CombMap D) (root : D) : List D :=
  M.φ.toList root

/-- The face dart list enumerates exactly the face orbit. -/
lemma faceDartList_toFinset (M : CombMap D) (f : M.Face) {root : D}
    (hφ : M.φ root ≠ root) (hroot : M.dartFace root = f) :
    (M.faceDartList root).toFinset = faceOrbitFinset M f := by
  classical
  have hsupp : root ∈ M.φ.support := by simpa [Equiv.Perm.mem_support] using hφ
  ext d
  rw [List.mem_toFinset, mem_faceOrbitFinset_iff, faceDartList,
    Equiv.Perm.mem_toList_iff]
  constructor
  · rintro ⟨hsc, _⟩
    rw [← hroot]
    exact (Quotient.sound hsc.symm : M.dartFace d = M.dartFace root)
  · intro hdf
    refine ⟨?_, hsupp⟩
    exact Quotient.exact (show M.dartFace root = M.dartFace d by rw [hroot, hdf])

/-- The face dart list is nonempty when the orbit is nontrivial. -/
lemma faceDartList_length_pos (M : CombMap D) {root : D} (hφ : M.φ root ≠ root) :
    0 < (M.faceDartList root).length := by
  have hsupp : root ∈ M.φ.support := by simpa [Equiv.Perm.mem_support] using hφ
  exact Equiv.Perm.length_toList_pos_of_mem_support _ _ hsupp

/-- `getElem` of the face dart list is `φ`-iterate of the root. -/
lemma faceDartList_getElem (M : CombMap D) (root : D) (n : ℕ)
    (hn : n < (M.faceDartList root).length) :
    (M.faceDartList root)[n] = (M.φ ^ n) root :=
  Equiv.Perm.getElem_toList _ _ _ _

/-- The head of the face dart list is the root. -/
lemma faceDartList_head (M : CombMap D) {root : D} (hφ : M.φ root ≠ root) :
    (M.faceDartList root).head? = some root := by
  have hsupp : root ∈ M.φ.support := by simpa [Equiv.Perm.mem_support] using hφ
  have h0 : (M.faceDartList root)[0]'(M.faceDartList_length_pos hφ) = root := by
    have := M.faceDartList_getElem root 0 (M.faceDartList_length_pos hφ)
    simpa using this
  rw [List.head?_eq_getElem?,
    List.getElem?_eq_getElem (M.faceDartList_length_pos hφ), h0]

/-- The normalized cyclic dart list certificate for the face orbit. -/
lemma faceDartList_normalized (M : CombMap D) (f : M.Face) {root : D}
    (hφ : M.φ root ≠ root) (hroot : M.dartFace root = f) :
    NormalizedCyclicDartList M f root (M.faceDartList root) where
  head_eq := M.faceDartList_head hφ
  root_face := hroot
  nodup := Equiv.Perm.nodup_toList _ _
  length_pos := M.faceDartList_length_pos hφ
  toFinset_eq := M.faceDartList_toFinset f hφ hroot

/-- The `φ`-orbit length is the support cardinal of the root's cycle; the dart at
the cyclic-next index is the `φ`-image of the dart at the current index. -/
lemma faceDartList_consecutive_phi (M : CombMap D) {root : D} (hφ : M.φ root ≠ root)
    (i : Fin (M.faceDartList root).length) :
    (M.faceDartList root).get
        (cyclicNext (M.faceDartList_length_pos hφ) i) =
      M.φ ((M.faceDartList root).get i) := by
  classical
  have hlen : (M.faceDartList root).length = (M.φ.cycleOf root).support.card := by
    simp only [faceDartList, Equiv.Perm.length_toList]
  -- `(φ^n) root = root` where `n` is the list length.
  have hcycle : (M.φ ^ (M.faceDartList root).length) root = root := by
    have hself := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply M.φ
      (M.faceDartList root).length root
    rw [hlen, Nat.mod_self, pow_zero] at hself
    rw [hlen]; exact hself.symm
  -- `(φ^n)^k root = root`.
  have hpow : ∀ k : ℕ, ((M.φ ^ (M.faceDartList root).length) ^ k) root = root := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, ih, hcycle]
  -- The cyclicNext index value.
  have hnext_val : ((cyclicNext (M.faceDartList_length_pos hφ) i :
      Fin (M.faceDartList root).length) : ℕ)
      = ((i : ℕ) + 1) % (M.faceDartList root).length := rfl
  rw [List.get_eq_getElem, List.get_eq_getElem,
    M.faceDartList_getElem root i i.2]
  rw [M.faceDartList_getElem root
    ((cyclicNext (M.faceDartList_length_pos hφ) i : Fin (M.faceDartList root).length) : ℕ)
    (cyclicNext (M.faceDartList_length_pos hφ) i).2]
  rw [hnext_val]
  -- `(φ ^ ((i+1) % n)) root = φ ((φ ^ i) root)`.
  have hmod : (M.φ ^ (((i : ℕ) + 1) % (M.faceDartList root).length)) root
      = (M.φ ^ ((i : ℕ) + 1)) root := by
    have hsplit : (i : ℕ) + 1
        = ((i : ℕ) + 1) % (M.faceDartList root).length
          + (M.faceDartList root).length * (((i : ℕ) + 1) / (M.faceDartList root).length) := by
      rw [Nat.add_comm, Nat.mod_add_div]
    conv_rhs => rw [hsplit]
    rw [pow_add, pow_mul, Equiv.Perm.coe_mul, Function.comp_apply, hpow]
  rw [hmod, pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]

/-- Consecutive face darts match at the common boundary vertex. -/
lemma faceDartList_consecutive_vertex (M : CombMap D) {root : D} (hφ : M.φ root ≠ root)
    (i : Fin (M.faceDartList root).length) :
    M.tail ((M.faceDartList root).get
        (cyclicNext (M.faceDartList_length_pos hφ) i)) =
      M.head ((M.faceDartList root).get i) := by
  rw [M.faceDartList_consecutive_phi hφ i, tail_phi]

/-- **Generic normalized boundary cycle from a single nontrivial face orbit.**
The explicit cyclic dart list is `[root, φ root, φ² root, …]`; all orbit-algebraic
fields are discharged, and the Jordan-arc split is supplied as `arcSplit`. -/
def boundaryCycleOfFace (M : CombMap D) (f : M.Face) {root : D}
    (hφ : M.φ root ≠ root) (hroot : M.dartFace root = f)
    (arcSplit :
      ∀ ⦃u v : M.Vertex⦄, u ≠ v →
        u ∈ (M.faceDartList root).map M.tail →
        v ∈ (M.faceDartList root).map M.tail →
        BoundaryArcSplit M ((M.faceDartList root).map M.tail)
          ((M.faceDartList root).map M.dartEdge) u v) :
    BoundaryCycle M f where
  root := root
  darts := M.faceDartList root
  vertices := (M.faceDartList root).map M.tail
  edges := (M.faceDartList root).map M.dartEdge
  normalized := M.faceDartList_normalized f hφ hroot
  vertices_eq := rfl
  edges_eq := rfl
  consecutive_phi := M.faceDartList_consecutive_phi hφ
  consecutive_vertex := M.faceDartList_consecutive_vertex hφ
  arcSplit := arcSplit

namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}

/-! ## The merged outer boundary cycle from the explicit `φ'`-dart list

The new outer face of the deleted map is the `φ'`-orbit of any surviving dart on
the merged face; its boundary cycle is the explicit list `[root, φ' root, …]`
built by `boundaryCycleOfFace` (no `arcSplit` re-derivation — the deleted map is
simple, so `φ'` has no fixed dart on the merged face).  The genuinely planar
residue is just the Jordan-arc split `arcSplit`, the simplicity `outer_simple`,
the length bound, and the inner-face triangularity. -/

/-- The deleted map's `φ'` has no fixed dart (it is a simple graph). -/
lemma deleteVertex_phi_ne_self (hNT : NearTriangulation M) (d0 : D)
    (x : {d : D // d ∉ M.deleteVertexSet d0}) :
    (M.deleteVertex d0).φ x ≠ x :=
  phi_ne_self_of_isSimpleGraph (M.deleteVertex d0)
    (hNT.deleteVertex_isSimpleGraph d0) x

/-- **Build the `DeletedOuterBoundary` from the explicit `φ'`-dart list.**

Given the merged outer face `outerFace`, a surviving root dart `root` on it, the
Jordan-arc split, the simplicity of the resulting boundary vertex list, the
length bound, and the inner-face triangularity, the full `DeletedOuterBoundary`
input of `fanSurgeryReconstruction` is assembled: its `outerCycle` is the explicit
cyclic enumeration `[root, φ' root, φ'² root, …]` produced by
`boundaryCycleOfFace`.  Every orbit-algebraic field of the `BoundaryCycle`
(`NormalizedCyclicDartList`, `consecutive_phi`, `consecutive_vertex`,
`vertices_eq`, `edges_eq`) is discharged from the `φ'`-iterate calculus; only the
genuinely planar pieces are taken as inputs. -/
noncomputable def DeletedOuterBoundary.ofMergedFace (hNT : NearTriangulation M)
    (d0 : D) (outerFace : (M.deleteVertex d0).Face)
    (root : {d : D // d ∉ M.deleteVertexSet d0})
    (hroot : (M.deleteVertex d0).dartFace root = outerFace)
    (arcSplit :
      ∀ ⦃u v : (M.deleteVertex d0).Vertex⦄, u ≠ v →
        u ∈ ((M.deleteVertex d0).faceDartList root).map (M.deleteVertex d0).tail →
        v ∈ ((M.deleteVertex d0).faceDartList root).map (M.deleteVertex d0).tail →
        BoundaryArcSplit (M.deleteVertex d0)
          (((M.deleteVertex d0).faceDartList root).map (M.deleteVertex d0).tail)
          (((M.deleteVertex d0).faceDartList root).map (M.deleteVertex d0).dartEdge) u v)
    (outer_simple :
      (((M.deleteVertex d0).faceDartList root).map (M.deleteVertex d0).tail).Nodup)
    (outer_len_ge_three : 3 ≤ ((M.deleteVertex d0).faceDartList root).length)
    (inner_tri : ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
      (M.deleteVertex d0).faceLen f = 3) :
    DeletedOuterBoundary hNT d0 where
  outerFace := outerFace
  outerCycle :=
    (M.deleteVertex d0).boundaryCycleOfFace outerFace
      (hNT.deleteVertex_phi_ne_self d0 root) hroot arcSplit
  outer_simple := outer_simple
  outer_len_ge_three := outer_len_ge_three
  inner_tri := inner_tri

/-! ## The single isolated planar certificate

`DeletedMergedBoundaryCertificate` bundles the two residues that the dart-rotation
surgery of `PlanarMapFanFaces` leaves open:

* `mergedOrbit` — the merged-face single-orbit fact (`PlanarMapFanFaces`'
  `DeleteVertexMergedFaceSingleOrbit`, the `φ`-level seam reconnection; the
  parallel `PlanarMapFanMergedOrbit` discharges this from the fan plus the
  outer-arc reconnection);
* `boundary` — the normalized boundary-cycle data of the merged outer face
  (`DeletedOuterBoundary`, the exact remaining input of
  `fanSurgeryReconstruction`: the cyclic `φ'`-dart enumeration of the merged face
  with its simplicity, length bound, and inner-face triangularity).

Both fields are genuinely planar (Jordan-arc) data that the orbit-algebra fan
layer does not expose; neither is the deletion goal, and both are satisfiable on
any chordless boundary-vertex deletion. -/
structure DeletedMergedBoundaryCertificate (hNT : NearTriangulation M) (d0 : D) where
  /-- The merged-face single-orbit fact: all surviving `v0`-incident darts lie in
  one `φ'`-cycle (the new merged outer face). -/
  mergedOrbit : DeleteVertexMergedFaceSingleOrbit M d0
  /-- The normalized boundary-cycle data of the merged outer face: its cyclic
  `φ'`-dart enumeration, simplicity, length `≥ 3`, and inner-face triangularity. -/
  boundary : DeletedOuterBoundary hNT d0

namespace DeletedMergedBoundaryCertificate

variable {d0 : D}

/-- **Assemble the full `FanSurgeryReconstruction` from the fan and the
certificate.**  All three dart-rotation surgery fields (`vertexQuotient`,
`facesMerge`, `connected`) are discharged from the fan by
`fanSurgeryReconstruction`; the merged-orbit fact and the new outer boundary data
come from the certificate. -/
noncomputable def fanSurgeryReconstruction (fan : BoundaryVertexFan hNT v0)
    (htail0 : M.tail d0 = v0)
    (cert : DeletedMergedBoundaryCertificate hNT d0) :
    FanSurgeryReconstruction hNT d0 :=
  CombMap.NearTriangulation.fanSurgeryReconstruction fan htail0
    cert.mergedOrbit cert.boundary

/-- **The deleted map is a near-triangulation** — derived from the fan and the
single certificate. -/
noncomputable def nearTriangulation (fan : BoundaryVertexFan hNT v0)
    (htail0 : M.tail d0 = v0)
    (cert : DeletedMergedBoundaryCertificate hNT d0) :
    NearTriangulation (M.deleteVertex d0) :=
  (cert.fanSurgeryReconstruction fan htail0).nearTriangulation

/-- The deleted map has exactly one fewer graph vertex. -/
theorem smaller (fan : BoundaryVertexFan hNT v0)
    (htail0 : M.tail d0 = v0)
    (cert : DeletedMergedBoundaryCertificate hNT d0) :
    (M.deleteVertex d0).V = M.V - 1 :=
  (cert.fanSurgeryReconstruction fan htail0).smaller

/-- Euler face count in fan terms: `F' = F - (t + 2) + 1`. -/
theorem face_count_fan (fan : BoundaryVertexFan hNT v0)
    (htail0 : M.tail d0 = v0)
    (cert : DeletedMergedBoundaryCertificate hNT d0) :
    (M.deleteVertex d0).F = M.F - (fan.t + 2) + 1 :=
  (cert.fanSurgeryReconstruction fan htail0).face_count_fan fan htail0

/-- Euler edge count in fan terms: `E' = E - (t + 2)`. -/
theorem edge_count_fan (fan : BoundaryVertexFan hNT v0)
    (htail0 : M.tail d0 = v0)
    (cert : DeletedMergedBoundaryCertificate hNT d0) :
    (M.deleteVertex d0).E = M.E - (fan.t + 2) :=
  (cert.fanSurgeryReconstruction fan htail0).edge_count_fan fan htail0

end DeletedMergedBoundaryCertificate

/-! ## The unconditional endpoint of the deletion chain

Combining the fan-discharged surgery with the single isolated certificate, the
boundary-vertex deletion preserves near-triangulation, with the strict vertex
decrease and the fan nonemptiness (`1 ≤ t`) for the Thomassen induction. -/

/-- **The final boundary-vertex deletion theorem.**

For a near-triangulation `M` with chordless outer boundary and a boundary vertex
`v0` carrying a fan, with `3 < M.V`, deleting the boundary vertex represented by a
dart `d0` (with `M.tail d0 = v0`) again yields a near-triangulation — given the
single planar certificate `cert` (the merged-orbit seam fact together with the
normalized merged-outer-boundary cycle).  All dart-rotation surgery
(`vertexQuotient`, `facesMerge`, `connected`) is discharged unconditionally from
the fan upstream; the `NoLoopAt` and `VertexFacesDistinct` local conditions are
discharged internally. -/
noncomputable def deleteBoundaryVertex_nearTriangulation_final
    {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex} {d0 : D}
    (fan : BoundaryVertexFan hNT v0)
    (htail0 : M.tail d0 = v0)
    (cert : DeletedMergedBoundaryCertificate hNT d0) :
    NearTriangulation (M.deleteVertex d0) :=
  cert.nearTriangulation fan htail0

/-- **Strict vertex decrease for the final deletion theorem.** -/
theorem deleteBoundaryVertex_smaller_final
    {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex} {d0 : D}
    (fan : BoundaryVertexFan hNT v0)
    (htail0 : M.tail d0 = v0)
    (cert : DeletedMergedBoundaryCertificate hNT d0) :
    (M.deleteVertex d0).V = M.V - 1 :=
  cert.smaller fan htail0

/-- **Fan-driven inductive step (final form).**  The deleted map is a
near-triangulation *and* the fan is genuinely nonempty (`1 ≤ fan.t`), so the
boundary has strictly shrunk and the Thomassen induction can proceed. -/
noncomputable def deleteBoundaryVertex_inductiveStep_final
    {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex} {d0 : D}
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle) (hbig : 3 < M.V)
    (htail0 : M.tail d0 = v0)
    (cert : DeletedMergedBoundaryCertificate hNT d0) :
    NearTriangulation (M.deleteVertex d0) ×' (1 ≤ fan.t) :=
  ⟨cert.nearTriangulation fan htail0,
    fan_nonempty_of_chordless_of_not_triangle hNT fan hchordless hbig⟩

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
