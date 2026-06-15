import ProofsInTheBook.ZinanCh35BoundaryAssembler

/-!
# Chapter 35 — the foundation vacuity obstruction (FOUND AND FIXED, historical record)

**Status: FIXED (2026-06-15).**  This file documents a vacuity bug that was found and
repaired in the same session; the proof below is preserved *as a comment* because it no
longer compiles (by design — the repair removed the lemma it depended on).

## The bug (pre-fix)

`NearTriangulation M` was **uninhabited for every finite `M`** with a boundary of length
`≥ 3`.  Root cause: `BoundaryArcSplit` (`PlanarMapBoundary.lean`) carried *two* fields

  `path₁_internal_iff_proper : path₁.HasInternalVertex ↔ s(u,v) ∉ boundaryEdges`
  `path₂_internal_iff_proper : path₂.HasInternalVertex ↔ s(u,v) ∉ boundaryEdges`

as **`↔`**.  For a *consecutive* pair `u,v` (so `s(u,v)` IS a boundary edge) on a cycle
with a third vertex `w`, the long complementary arc must contain `w` internally
(`boundary_vertices_covered` + `w ∉ {u,v}`), forcing `HasInternalVertex`; but the `↔`
then forces `s(u,v) ∉ edges`, contradicting that it is a boundary edge.  Hence
`BoundaryArcSplit` was unsatisfiable for consecutive pairs.  Since `BoundaryCycle.arcSplit`
quantifies over **all** distinct pairs and `NearTriangulation` carries `outer_simple`
(Nodup) + `outer_len ≥ 3`, every `hNT` supplied the killer configuration from its own
fields, so `(hNT : NearTriangulation M) → …` theorems — including the headline
`ZinanCh35Final.fiveColor_planar_of_recursionResiduals` — were all vacuously true.  This
is the §3.3 vacuity that `#print axioms` cannot detect.

## The fix

`PlanarMapBoundary.lean`: the two fields are now **one-directional**
(`s(u,v) ∉ boundaryEdges → pathᵢ.HasInternalVertex`).  A *proper* (non-adjacent) pair
still forces both arcs nontrivial (all that any consumer needs, via `path*_internal_of_chord`);
a *consecutive* pair is no longer forced to have a trivial long arc, so `BoundaryArcSplit` —
hence `BoundaryCycle` and `NearTriangulation` — is inhabited again.  The now-false
`boundaryArcSplit_consecutive_unsatisfiable` (and its deleted-map mirror
`mergedFaceSingleOrbit_not_from_genusSlack_alone`) were removed.

## The historical refutation proof (no longer compiles — preserved for the record)

The proof below derived `False` from `hNT : NearTriangulation M` using
`boundaryArcSplit_consecutive_unsatisfiable`, which has since been deleted.  It is kept
verbatim, commented out, as the machine-checked evidence (clean-3 at the time) of the bug.
-/

/-
open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ZinanCh35BoundaryAssembler

universe u

theorem nearTriangulation_uninhabited {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M) : False := by
  classical
  set C := hNT.outerCycle with hC
  have hlen : 3 ≤ C.darts.length := hNT.outer_len
  have hLpos : 0 < C.darts.length := by omega
  have h0 : (0 : ℕ) < C.darts.length := by omega
  have h1 : (1 : ℕ) < C.darts.length := by omega
  have h2 : (2 : ℕ) < C.darts.length := by omega
  set d0 := C.darts[0]'h0 with hd0
  set d1 := C.darts[1]'h1 with hd1
  set d2 := C.darts[2]'h2 with hd2
  set u := M.tail d0 with hu
  set v := M.tail d1 with hv
  set w := M.tail d2 with hw
  have hVN : (C.darts.map M.tail).Nodup := by
    have := hNT.outer_simple
    rwa [BoundaryCycle.VertexNodup, C.vertices_eq] at this
  have hcv := C.consecutive_vertex ⟨0, h0⟩
  have hcyc : (cyclicNext C.normalized.length_pos ⟨0, h0⟩ : Fin C.darts.length) = ⟨1, h1⟩ := by
    apply Fin.ext; show (0 + 1) % C.darts.length = 1; rw [Nat.zero_add]; exact Nat.mod_eq_of_lt h1
  rw [hcyc] at hcv
  have hvhead : M.head d0 = v := by
    rw [show C.darts.get ⟨1, h1⟩ = d1 from rfl, show C.darts.get ⟨0, h0⟩ = d0 from rfl] at hcv
    rw [hv]; exact hcv.symm
  have humem : u ∈ C.vertices := by
    rw [C.vertices_eq]; exact List.mem_map_of_mem (List.getElem_mem h0)
  have hvmem : v ∈ C.vertices := by
    rw [C.vertices_eq]; exact List.mem_map_of_mem (List.getElem_mem h1)
  have hwmem : w ∈ C.vertices := by
    rw [C.vertices_eq]; exact List.mem_map_of_mem (List.getElem_mem h2)
  have hdn := C.darts_nodup
  have hd01 : d0 ≠ d1 := by
    rw [hd0, hd1]; intro h
    have := (List.Nodup.getElem_inj_iff hdn (i := 0) (hi := h0) (j := 1) (hj := h1)).mp h
    simp at this
  have hd20 : d2 ≠ d0 := by
    rw [hd2, hd0]; intro h
    have := (List.Nodup.getElem_inj_iff hdn (i := 2) (hi := h2) (j := 0) (hj := h0)).mp h
    simp at this
  have hd21 : d2 ≠ d1 := by
    rw [hd2, hd1]; intro h
    have := (List.Nodup.getElem_inj_iff hdn (i := 2) (hi := h2) (j := 1) (hj := h1)).mp h
    simp at this
  have hti := fun {d e : D} hd he ht =>
    C.tail_injective_on_darts hNT.outer_simple (d := d) (e := e) hd he ht
  have huv : u ≠ v := fun h =>
    hd01 (hti (List.getElem_mem h0) (List.getElem_mem h1) h)
  have huw : w ≠ u := fun h =>
    hd20 (hti (List.getElem_mem h2) (List.getElem_mem h0) h)
  have hvw : w ≠ v := fun h =>
    hd21 (hti (List.getElem_mem h2) (List.getElem_mem h1) h)
  have hbe : C.IsBoundaryEdge s(u, v) := by
    show s(u, v) ∈ C.edges
    rw [C.edges_eq]
    have : M.dartEdge d0 = s(u, v) := by rw [dartEdge, hu, hvhead]
    rw [← this]
    exact List.mem_map_of_mem (List.getElem_mem h0)
  have S := C.arcSplit huv humem hvmem
  exact boundaryArcSplit_consecutive_unsatisfiable C hbe huw hvw hwmem S
-/
