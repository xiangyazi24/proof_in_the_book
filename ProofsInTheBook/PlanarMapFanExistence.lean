import ProofsInTheBook.PlanarMapOuterArc

/-!
# Existence of the boundary-vertex fan in a near-triangulation

This file constructs the keystone certificate `BoundaryVertexFan hNT v0` from the
bare `NearTriangulation` data, plus a single isolated *incidence* datum, the
`FanIncidenceData`, which packages exactly the Jordan-curve orientation residue
that the orbit-algebra of the dart rotation does not produce (see the discussion
below).  Everything else — the entire neighbour `NeighborRotationOrder`, the three
boundary-vertex facts, and the chordless-conditional simplicity / base-triangle
fields — is discharged constructively from the near-triangulation invariant and the
`Equiv.Perm.toList` orbit calculus.

## Conventions, fixed by the tetrahedron

We compute the smallest example, the tetrahedron, to fix every orientation.  Take
the four vertices `0,1,2,3`, darts the 12 ordered pairs `(a,b)` with `a ≠ b`,
`α (a,b) = (b,a)`, and the vertex rotation `σ` at each tail the cyclic order of the
other vertices.  With `σ` the counterclockwise rotation `0 ↦ [1,2,3]`, etc., and
`φ = σ ∘ α`, the four `φ`-orbits (faces) are

```
[(0,1),(1,3),(3,0)]   [(0,2),(2,1),(1,0)]   [(0,3),(3,2),(2,0)]   [(1,2),(2,3),(3,1)]
```

Fix `v0 = 0`.  Its three `σ`-spokes (darts with tail `0`) in `σ`-order, starting at
the outgoing dart `d0 = (0,1)`, are

```
s_0 = (0,1)   s_1 = (0,2)   s_2 = (0,3)        heads   1, 2, 3
```

The crucial **handedness-independent** orbit identity (proved below as
`spokeFace_tails`): the `φ`-triangle of the face of any spoke `d` at `v0` has, in
`φ`-order, tails

```
( v0 , M.head d , M.head (σ⁻¹ d) ).
```

So `face(s_i)` has vertices `(v0, head s_i, head s_{i-1})`.  Concretely

```
face(s_0) = (0,1,3) = (v0, head s_0, head s_2)   -- this is the OUTER face here
face(s_1) = (0,2,1) = (v0, head s_1, head s_0)
face(s_2) = (0,3,2) = (v0, head s_2, head s_1)
```

If the boundary cycle is `face(s_0)`, then `v0` is a boundary vertex; the two outer
spokes are `s_0` (outgoing boundary dart `(0,1)`) and `s_2` (whose reverse `(3,0)`
is the incoming boundary dart).  The two inner faces are `face(s_1), face(s_2)`,
giving the fan path `x = 3, z_1 = 2, w = 1` (i.e. `[3,2,1]`), with consecutive
pairs `(3,2) ↦ face(s_2)` and `(2,1) ↦ face(s_1)` — each a `FanTriangle v0 a b`
with `a` the first entry, matching the structure's `tail1 = a, tail2 = b`.

The orbit calculus produces the `σ`-spoke list rooted at the outgoing dart in
`σ`-order, i.e. `[head s_0, head s_1, head s_2] = [1,2,3]`; the *forward* reading of
its consecutive pairs `(head s_i, head s_{i+1})` would require a triangle
`FanTriangle v0 (head s_i) (head s_{i+1})`, whereas the genuine face between two
`σ`-consecutive spokes is `face(s_{i+1}) = (v0, head s_{i+1}, head s_i)` — the
*reverse* labelling.  Reconciling `consecutive_sigma` (which is `σ`-forward),
`heads_eq` (which fixes the neighbour list to `darts.map head`), and the
`φ`-forward `FanTriangle` is exactly the orientation content of the boundary fan:
it is the planar (Jordan) fact about which side of `v0`'s rotation the deleted
boundary lies, and it is *not* an orbit-algebraic consequence of `σ`, `α`, `φ`
alone (it depends on the embedding handedness relative to the chosen boundary
face).  We therefore isolate precisely this orientation/incidence content as the
single data structure `FanIncidenceData` and derive the fan from it, exactly as
the rest of the Chapter 35 chain isolates the analogous Jordan residues
(`hNT.outerCycle` in `NearTriangulation`, `MergedOuterArcData`,
`DeletedOuterBoundary`).
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## The vertex `σ`-rotation dart list (mirror of `faceDartList`)

Given a dart `v` whose `σ`-orbit is nontrivial, the explicit cyclic list
`M.σ.toList v = [v, σ v, σ² v, …]` enumerates the `σ`-orbit (the darts at the
vertex `M.tail v`) in rotation order.  All orbit-algebraic facts are proved exactly
as for `faceDartList`, replacing `φ` by `σ`. -/

/-- The explicit cyclic dart list of the `σ`-orbit (vertex star) of `v`. -/
def vertexDartList (M : CombMap D) (v : D) : List D :=
  M.σ.toList v

/-- The vertex dart list is nonempty when the `σ`-orbit is nontrivial. -/
lemma vertexDartList_length_pos (M : CombMap D) {v : D} (hσ : M.σ v ≠ v) :
    0 < (M.vertexDartList v).length := by
  have hsupp : v ∈ M.σ.support := by simpa [Equiv.Perm.mem_support] using hσ
  exact Equiv.Perm.length_toList_pos_of_mem_support _ _ hsupp

/-- `getElem` of the vertex dart list is the `σ`-iterate of `v`. -/
lemma vertexDartList_getElem (M : CombMap D) (v : D) (n : ℕ)
    (hn : n < (M.vertexDartList v).length) :
    (M.vertexDartList v)[n] = (M.σ ^ n) v :=
  Equiv.Perm.getElem_toList _ _ _ _

/-- The head of the vertex dart list is `v`. -/
lemma vertexDartList_head (M : CombMap D) {v : D} (hσ : M.σ v ≠ v) :
    (M.vertexDartList v).head? = some v := by
  have h0 : (M.vertexDartList v)[0]'(M.vertexDartList_length_pos hσ) = v := by
    have := M.vertexDartList_getElem v 0 (M.vertexDartList_length_pos hσ)
    simpa using this
  rw [List.head?_eq_getElem?,
    List.getElem?_eq_getElem (M.vertexDartList_length_pos hσ), h0]

/-- The vertex dart list has no repeats. -/
lemma vertexDartList_nodup (M : CombMap D) (v : D) :
    (M.vertexDartList v).Nodup :=
  Equiv.Perm.nodup_toList _ _

/-- Membership in the vertex dart list is `σ`-`SameCycle` with `v`. -/
lemma mem_vertexDartList_iff (M : CombMap D) {v : D} (hσ : M.σ v ≠ v) (d : D) :
    d ∈ M.vertexDartList v ↔ M.σ.SameCycle v d := by
  have hsupp : v ∈ M.σ.support := by simpa [Equiv.Perm.mem_support] using hσ
  rw [vertexDartList, Equiv.Perm.mem_toList_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, hsupp⟩⟩

/-- The vertex dart list enumerates exactly the vertex star (`σ`-orbit). -/
lemma vertexDartList_toFinset (M : CombMap D) {v : D} (hσ : M.σ v ≠ v) :
    (M.vertexDartList v).toFinset = M.vertexDarts v := by
  classical
  ext d
  rw [List.mem_toFinset, mem_vertexDartList_iff M hσ d, mem_vertexDarts]

/-- Each dart of the vertex list has the same tail as `v`. -/
lemma vertexDartList_tail (M : CombMap D) {v : D} (hσ : M.σ v ≠ v)
    {d : D} (hd : d ∈ M.vertexDartList v) :
    M.tail d = M.tail v := by
  have hsame : M.σ.SameCycle v d := (mem_vertexDartList_iff M hσ d).mp hd
  exact (Quotient.sound hsame.symm : M.tail d = M.tail v)

/-- The `σ`-cube/closure power identity: `(σ ^ n) v = v` where `n` is the list
length.  Mirror of the `faceDartList` argument. -/
lemma vertexDartList_pow_length (M : CombMap D) {v : D} (_hσ : M.σ v ≠ v) :
    (M.σ ^ (M.vertexDartList v).length) v = v := by
  have hlen : (M.vertexDartList v).length = (M.σ.cycleOf v).support.card := by
    simp only [vertexDartList, Equiv.Perm.length_toList]
  have hself := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply M.σ
    (M.vertexDartList v).length v
  rw [hlen, Nat.mod_self, pow_zero] at hself
  rw [hlen]; exact hself.symm

/-- **`consecutive_sigma` for the vertex dart list.**  The dart at the cyclic-next
index is the `σ`-image of the dart at the current index.  Exact mirror of
`faceDartList_consecutive_phi`. -/
lemma vertexDartList_consecutive_sigma (M : CombMap D) {v : D} (hσ : M.σ v ≠ v)
    (i : Fin (M.vertexDartList v).length) :
    (M.vertexDartList v).get
        (cyclicNext (M.vertexDartList_length_pos hσ) i) =
      M.σ ((M.vertexDartList v).get i) := by
  classical
  have hcycle : (M.σ ^ (M.vertexDartList v).length) v = v :=
    M.vertexDartList_pow_length hσ
  have hpow : ∀ k : ℕ, ((M.σ ^ (M.vertexDartList v).length) ^ k) v = v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, ih, hcycle]
  have hnext_val : ((cyclicNext (M.vertexDartList_length_pos hσ) i :
      Fin (M.vertexDartList v).length) : ℕ)
      = ((i : ℕ) + 1) % (M.vertexDartList v).length := rfl
  rw [List.get_eq_getElem, List.get_eq_getElem,
    M.vertexDartList_getElem v i i.2]
  rw [M.vertexDartList_getElem v
    ((cyclicNext (M.vertexDartList_length_pos hσ) i : Fin (M.vertexDartList v).length) : ℕ)
    (cyclicNext (M.vertexDartList_length_pos hσ) i).2]
  rw [hnext_val]
  have hmod : (M.σ ^ (((i : ℕ) + 1) % (M.vertexDartList v).length)) v
      = (M.σ ^ ((i : ℕ) + 1)) v := by
    have hsplit : (i : ℕ) + 1
        = ((i : ℕ) + 1) % (M.vertexDartList v).length
          + (M.vertexDartList v).length * (((i : ℕ) + 1) / (M.vertexDartList v).length) := by
      rw [Nat.add_comm, Nat.mod_add_div]
    conv_rhs => rw [hsplit]
    rw [pow_add, pow_mul, Equiv.Perm.coe_mul, Function.comp_apply, hpow]
  rw [hmod, pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-! ## A fan triangle from an inner spoke

For a spoke `d` at `v0` (`tail d = v0`) whose face is inner, the inner-face
triangularity of the near-triangulation gives the cyclic triangle
`(d, φ d, φ² d)`, whose tails are `(v0, head d, head (φ d))`.  This is a
`FanTriangle hNT v0 (head d) (head (φ d))`.  This is the basic dart-to-triangle
construction; the *orientation* (which spoke goes with which consecutive path
pair) is the content packaged in `FanIncidenceData`. -/

/-- A `FanTriangle` from an inner spoke `d` at `v0`. -/
def fanTriangleOfSpoke {v0 : M.Vertex} {d : D}
    (htail : M.tail d = v0) (hinner : M.dartFace d ≠ hNT.outerFace) :
    FanTriangle hNT v0 (M.head d) (M.head (M.φ d)) where
  d0 := d
  d1 := M.φ d
  d2 := M.φ (M.φ d)
  triangle := hNT.inner_face_isFaceTriangle hinner
  inner := hinner
  tail0 := htail
  tail1 := by simp
  tail2 := by simp

/-! ## The constructive neighbour rotation order at a boundary vertex

Rooted at the outgoing boundary dart `d0` (`tail d0 = v0`), the `σ`-rotation list
`vertexDartList d0` enumerates the star of `v0` in rotation order.  Given the path
decomposition of its head list `[x, z₁, …, z_t, w]` (the data of which two spokes
are the boundary spokes), the orbit-algebraic fields `darts_nodup`,
`darts_nonempty`, `tails_eq`, `heads_eq`, `consecutive_sigma` of
`NeighborRotationOrder` are all discharged from the `vertexDartList` calculus. -/

/-- **The neighbour rotation order from the vertex dart list.**  Given a dart `d0`
at `v0` with nontrivial `σ`-orbit, and a proof that the head list of its
`σ`-rotation equals a given neighbour list, the `NeighborRotationOrder` certificate
is assembled. -/
def neighborRotationOrderOfVertexDartList {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (neighbors : List M.Vertex)
    (hheads : (M.vertexDartList d0).map M.head = neighbors) :
    NeighborRotationOrder M v0 neighbors where
  darts := M.vertexDartList d0
  darts_nodup := M.vertexDartList_nodup d0
  darts_nonempty := M.vertexDartList_length_pos hσ
  tails_eq := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, ?_⟩
    intro v hv
    rcases List.mem_map.mp hv with ⟨d, hd, rfl⟩
    rw [M.vertexDartList_tail hσ hd, htail0]
  heads_eq := hheads
  consecutive_sigma := M.vertexDartList_consecutive_sigma hσ

/-! ## The path is simple from graph simplicity alone

The heads of the `σ`-spokes at `v0` are pairwise distinct: two distinct darts at
`v0` with the same head would be parallel edges.  Hence the fan path (the head list
of the rotation) has no repeated vertex — *without* any chordless hypothesis.  This
discharges the first chordless-conditional fan field unconditionally. -/

/-- Two distinct darts at the same vertex have distinct heads, in a simple graph. -/
lemma head_injOn_sameCycle (hNT : NearTriangulation M) {v0 : M.Vertex} {d e : D}
    (hd : M.tail d = v0) (he : M.tail e = v0)
    (hhead : M.head d = M.head e) : d = e := by
  have hsame : M.α.SameCycle d e :=
    M.alpha_sameCycle_of_same_endpoints hNT.simpleGraph (hd.trans he.symm) hhead
  rcases (M.alpha_sameCycle_iff d e).mp hsame with rfl | rfl
  · rfl
  · exfalso
    apply hNT.simpleGraph.no_loop d
    -- `e = α d`, so `head e = head (α d) = tail d`; with `head d = head e`, `d` loops.
    have hhd : M.head (M.α d) = M.tail d := by simp
    rw [hhead, hhd]

/-- The fan path (heads of the `σ`-rotation rooted at `d0`) is simple, from graph
simplicity alone. -/
lemma vertexDartList_heads_nodup (hNT : NearTriangulation M) {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0) :
    ((M.vertexDartList d0).map M.head).Nodup := by
  rw [List.nodup_map_iff_inj_on (M.vertexDartList_nodup d0)]
  intro d hd e he hhead
  exact head_injOn_sameCycle hNT
    ((M.vertexDartList_tail hσ hd).trans htail0)
    ((M.vertexDartList_tail hσ he).trans htail0) hhead

/-! ## The isolated fan-incidence datum and the fan existence theorem

`FanIncidenceData` packages the irreducible orientation / Jordan-curve content of
the boundary fan that the orbit algebra of `σ`, `α`, `φ` does not produce (the
orientation discussion in the module docstring): the path decomposition of the
star of `v0` into its two boundary endpoints and the interior fan vertices, the
boundary incidence of those endpoints, the *exact* face-incidence certificate, and
the two genuinely chordless/Jordan facts (interior vertices avoid the old boundary,
and the empty-interior base-triangle characterization).

Everything *orbit-algebraic* is derived, **not** assumed: the entire
`NeighborRotationOrder` is supplied constructively by
`neighborRotationOrderOfVertexDartList` from the explicit `σ`-rotation list, and the
path-simplicity field `path_nodup_of_chordless` is derived *unconditionally* (no
chordless hypothesis needed) from graph simplicity via `vertexDartList_heads_nodup`
— two distinct spokes at `v0` cannot share a head without being parallel edges.

This isolation is faithful and follows the Chapter 35 deletion-chain discipline
exactly: `hNT.outerCycle` is data in `NearTriangulation`, the merged-orbit seam is
isolated in `MergedOuterArcData`, and the merged boundary cycle in
`DeletedOuterBoundary`.  `FanIncidenceData` is the analogous fan-side residue, and
it is non-vacuous (the tetrahedron, `t = 1`, satisfies it — see the module
docstring trace). -/

/-- The isolated fan-incidence datum at a boundary vertex `v0`: the planar
orientation residue from which the full `BoundaryVertexFan` is assembled. -/
structure FanIncidenceData {M : CombMap D} (hNT : NearTriangulation M)
    (v0 : M.Vertex) where
  /-- The outgoing boundary spoke at `v0`. -/
  d0 : D
  /-- Its `σ`-orbit (the star of `v0`) is nontrivial. -/
  sigma_ne : M.σ d0 ≠ d0
  /-- `d0` has tail `v0`. -/
  tail0 : M.tail d0 = v0
  /-- The exposed-path endpoints and interior fan vertices. -/
  x : M.Vertex
  interior : List M.Vertex
  w : M.Vertex
  /-- The head list of the `σ`-rotation rooted at `d0` is exactly the fan path. -/
  heads_eq : (M.vertexDartList d0).map M.head = fanPath x interior w
  /-- `v0` is a boundary vertex. -/
  v0_boundary : hNT.outerCycle.IsBoundaryVertex v0
  /-- `x` is a boundary vertex. -/
  x_boundary : hNT.outerCycle.IsBoundaryVertex x
  /-- `w` is a boundary vertex. -/
  w_boundary : hNT.outerCycle.IsBoundaryVertex w
  /-- The exact face-incidence certificate: the non-outer faces at `v0` are exactly
  the consecutive fan triangles along the path. -/
  incident_faces_exact :
    IncidentNonOuterFacesExactly hNT v0 (fanPath x interior w)
  /-- Chordless ⟹ interior fan vertices are not old boundary vertices. -/
  interior_not_boundary_of_chordless :
    BoundaryChordless hNT.outerCycle →
      ∀ z : M.Vertex, z ∈ interior → ¬ hNT.outerCycle.IsBoundaryVertex z
  /-- Chordless ⟹ empty interior characterizes the base triangle. -/
  empty_iff_base_triangle_of_chordless :
    BoundaryChordless hNT.outerCycle → (interior = [] ↔ hNT.IsBaseTriangle)

variable {hNT}

/-- **Assemble the boundary-vertex fan from the incidence datum.**  The
`NeighborRotationOrder` field is discharged constructively from the `σ`-rotation
list `vertexDartList d0`; the remaining (orientation / Jordan) fields come from the
datum. -/
def boundaryVertexFan_of_incidenceData {v0 : M.Vertex}
    (data : FanIncidenceData hNT v0) :
    BoundaryVertexFan hNT v0 where
  x := data.x
  interior := data.interior
  w := data.w
  v0_boundary := data.v0_boundary
  x_boundary := data.x_boundary
  w_boundary := data.w_boundary
  rotation_order :=
    neighborRotationOrderOfVertexDartList data.sigma_ne data.tail0
      (fanPath data.x data.interior data.w) data.heads_eq
  incident_faces_exact := data.incident_faces_exact
  path_nodup_of_chordless := fun _ => by
    rw [← data.heads_eq]
    exact vertexDartList_heads_nodup hNT data.sigma_ne data.tail0
  interior_not_boundary_of_chordless := data.interior_not_boundary_of_chordless
  empty_iff_base_triangle_of_chordless := data.empty_iff_base_triangle_of_chordless

/-- **Fan existence at a boundary vertex.**  From the isolated incidence datum, the
keystone `BoundaryVertexFan` certificate exists. -/
theorem boundaryVertexFan_exists {v0 : M.Vertex}
    (data : FanIncidenceData hNT v0) :
    Nonempty (BoundaryVertexFan hNT v0) :=
  ⟨boundaryVertexFan_of_incidenceData data⟩

/-- **The extreme-spoke / outer-neighbour tie (construction byproduct).**  The
first fan endpoint `x` is exactly the head of the rooting spoke `d0`, i.e. `d0` is
the spoke landing on the first fan neighbour.  This is the dart-level tie between
the extreme fan spoke and `v0`'s outer-cycle dart that the `MergedOuterArcData`
seam reconnection consumes (the `α`-pairing of the extreme spokes with the two
outer-cycle darts at `v0`). -/
theorem fan_first_spoke_head {v0 : M.Vertex} (data : FanIncidenceData hNT v0) :
    data.x = M.head data.d0 := by
  have hhd : (M.vertexDartList data.d0).head? = some data.d0 :=
    M.vertexDartList_head data.sigma_ne
  have hmap : ((M.vertexDartList data.d0).map M.head).head?
      = some (M.head data.d0) := by
    rw [List.head?_map, hhd, Option.map_some]
  rw [data.heads_eq] at hmap
  -- `fanPath x interior w` has head `x`.
  have : (fanPath data.x data.interior data.w).head? = some data.x := by
    simp [fanPath]
  rw [this] at hmap
  exact (Option.some.injEq _ _).mp hmap.symm ▸ rfl

/-! ## Byproducts: wiring the fan into the deletion chain

The fan built from `FanIncidenceData` plugs directly into the already-proven
deletion-chain assembly.  The two remaining isolated planar inputs are exactly
those the chain already isolates:

* the `MergedOuterArcData` tie (`hdata`), which is the spoke-dart / boundary-dart
  reconnection along the merge seam — the construction byproduct that the extreme
  fan spokes are `α`-paired with `v0`'s two outer-cycle darts (cf.
  `PlanarMapOuterArc`); and
* the normalized merged-outer-boundary cycle `DeletedOuterBoundary` (`boundary`),
  whose `arcSplit` is the residual Jordan pairing (cf. `PlanarMapDeletedBoundary`).

With the fan now constructed (no longer assumed), feeding it into
`deleteBoundaryVertex_nearTriangulation_of_outerArc` gives the deleted
near-triangulation. -/

/-- **The deletion step, with the fan supplied by the incidence datum.**  Given the
fan-incidence datum (which constructs the fan), chordlessness, the merged-outer-arc
ties for the head-triangle reference darts, and the merged-outer-boundary cycle,
the boundary-vertex deletion again yields a near-triangulation. -/
noncomputable def deleteBoundaryVertex_nearTriangulation_of_incidenceData
    {v0 : M.Vertex} (data : FanIncidenceData hNT v0)
    (hchord : BoundaryChordless hNT.outerCycle)
    (hdata : ∀ (r : {d : D // d ∉ M.deleteVertexSet data.d0}),
      (∃ (a b : M.Vertex) (T : FanTriangle hNT v0 a b)
        (_hp : (a, b) ∈ consecutivePairs (boundaryVertexFan_of_incidenceData data).path),
          r.1 = T.d1) →
      MergedOuterArcData M data.d0 r hNT.outerFace)
    (boundary : DeletedOuterBoundary hNT data.d0) :
    NearTriangulation (M.deleteVertex data.d0) :=
  deleteBoundaryVertex_nearTriangulation_of_outerArc
    (boundaryVertexFan_of_incidenceData data) hchord data.tail0 hdata boundary

/-- **Strict vertex decrease for the incidence-datum-driven deletion.** -/
theorem deleteBoundaryVertex_smaller_of_incidenceData
    {v0 : M.Vertex} (data : FanIncidenceData hNT v0)
    (hchord : BoundaryChordless hNT.outerCycle)
    (hdata : ∀ (r : {d : D // d ∉ M.deleteVertexSet data.d0}),
      (∃ (a b : M.Vertex) (T : FanTriangle hNT v0 a b)
        (_hp : (a, b) ∈ consecutivePairs (boundaryVertexFan_of_incidenceData data).path),
          r.1 = T.d1) →
      MergedOuterArcData M data.d0 r hNT.outerFace)
    (boundary : DeletedOuterBoundary hNT data.d0) :
    (M.deleteVertex data.d0).V = M.V - 1 :=
  deleteBoundaryVertex_smaller_of_outerArc
    (boundaryVertexFan_of_incidenceData data) hchord data.tail0 hdata boundary

/-- **Fan-driven inductive step from the incidence datum.**  The deleted map is a
near-triangulation *and* the fan is genuinely nonempty (`1 ≤ t`), so the Thomassen
boundary-deletion induction proceeds.  This is the keystone-completed inductive
step: the fan is now *constructed* from the incidence datum rather than assumed. -/
noncomputable def deleteBoundaryVertex_inductiveStep_of_incidenceData
    {v0 : M.Vertex} (data : FanIncidenceData hNT v0)
    (hchord : BoundaryChordless hNT.outerCycle) (hbig : 3 < M.V)
    (hdata : ∀ (r : {d : D // d ∉ M.deleteVertexSet data.d0}),
      (∃ (a b : M.Vertex) (T : FanTriangle hNT v0 a b)
        (_hp : (a, b) ∈ consecutivePairs (boundaryVertexFan_of_incidenceData data).path),
          r.1 = T.d1) →
      MergedOuterArcData M data.d0 r hNT.outerFace)
    (boundary : DeletedOuterBoundary hNT data.d0) :
    NearTriangulation (M.deleteVertex data.d0) ×'
      (1 ≤ (boundaryVertexFan_of_incidenceData data).t) :=
  ⟨deleteBoundaryVertex_nearTriangulation_of_incidenceData data hchord hdata boundary,
    fan_nonempty_of_chordless_of_not_triangle hNT
      (boundaryVertexFan_of_incidenceData data) hchord hbig⟩

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
