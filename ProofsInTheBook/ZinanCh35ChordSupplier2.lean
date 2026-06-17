import ProofsInTheBook.ZinanCh35ChordSupplier

/-!
# Chapter 35 chord supplier, side-2 Thomassen-list closure

This file keeps the side-2 boundary transport and forced-list producer out of
`ZinanCh35ChordSupplier.lean`.  It mirrors the already-closed side-1 transport in
that file, but for the swapped canonical side-2 map rooted at `inr 0`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordSupplier2

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation
open ProofsInTheBook.ZinanCh35Regions
open ProofsInTheBook.ZinanCh35Side2Confine
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35Side2Anchors
open ProofsInTheBook.ZinanCh35OuterTrace
open ProofsInTheBook.ZinanCh35OuterTraceProof
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ZinanCh35ChordSupplier

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v p q : M.Vertex}

@[simp] lemma sideVertexToM₂_tail_inr_zero_apply
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep a₀ a₁ hne
        ((data.sideMap₂ hsep a₀ a₁ hne).tail (Sum.inr (0 : Fin 2)))
      = M.tail a₀.1 := by
  simpa using ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_tail_inr data hsep a₀ a₁ hne
    (0 : Fin 2)

@[simp] lemma sideVertexToM₂_head_inr_zero_apply
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep a₀ a₁ hne
        ((data.sideMap₂ hsep a₀ a₁ hne).head (Sum.inr (0 : Fin 2)))
      = M.tail a₁.1 := by
  simpa using ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_head_inr data hsep a₀ a₁ hne
    (0 : Fin 2)

@[simp] lemma sideVertexToM₂_tail_inl_apply
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₂}) :
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep a₀ a₁ hne
        ((data.sideMap₂ hsep a₀ a₁ hne).tail (Sum.inl k))
      = M.tail k.1 := by
  exact ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_inl data hsep a₀ a₁ hne k

@[simp] lemma sideVertexToM₂_head_inl_apply
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₂}) :
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep a₀ a₁ hne
        ((data.sideMap₂ hsep a₀ a₁ hne).head (Sum.inl k))
      = M.head k.1 := by
  exact ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_head_inl data hsep a₀ a₁ hne k

/-- The swapped-root canonical side-2 near-triangulation. -/
noncomputable def canonicalSide₂NT (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    NearTriangulation
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm) :=
  ProofsInTheBook.ZinanCh35Side2.chordSideNearTriangulation₂_of_share data hsep
    (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
    (ProofsInTheBook.ChordSideClose.side₂IsDisk_unconditional data hsep)
    (side₂AnchorsShareFace_canonical_swapped (hNT := hNT) data hsep)
    (contiguousInterval₂_direct_canonical_swapped_uncond hNT data hsep)

@[simp] theorem canonicalSide₂NT_outerCycle_darts
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.darts =
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0) :=
  rfl

theorem canonicalSide₂_boundary_tail_of_faceDartList_mem
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {x : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2}
    (hx : x ∈ (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0)) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
      ((data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).tail x) := by
  rw [BoundaryCycle.IsBoundaryVertex,
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.vertices_eq]
  exact List.mem_map_of_mem hx

theorem canonicalSide₂_boundary_head_of_faceDartList_mem
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {x : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2}
    (hx : x ∈ (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0)) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
      ((data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).head x) := by
  exact boundaryCycle_head_mem_vertices_of_mem_darts
    ((canonicalSide₂NT (hNT := hNT) data hsep).outerCycle)
    (by simpa [canonicalSide₂NT_outerCycle_darts (hNT := hNT) data hsep] using hx)

theorem canonicalSide₂_boundary_edge_of_faceDartList_mem
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {x : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2}
    (hx : x ∈ (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0)) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryEdge
      ((data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).dartEdge x) := by
  rw [BoundaryCycle.IsBoundaryEdge,
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.edges_eq]
  exact List.mem_map_of_mem hx

theorem canonicalSide₂_root0_mem_faceDartList
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (Sum.inr (0 : Fin 2) : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) ∈
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0) :=
  (ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_side₂_outer_orbit_mem_iff_swapped_root0
    hNT data hsep (Sum.inr (0 : Fin 2))).2 (Or.inl rfl)

theorem canonicalSide₂_boundary_vertex_parent_boundary
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (htu : M.tail data.dart = u)
    (W : (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).Vertex)
    (hW : (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W) :
    hNT.outerCycle.IsBoundaryVertex
      (ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm W) := by
  classical
  rw [BoundaryCycle.IsBoundaryVertex,
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.vertices_eq,
    canonicalSide₂NT_outerCycle_darts (hNT := hNT) data hsep] at hW
  rw [List.mem_map] at hW
  obtain ⟨x, hx, hxW⟩ := hW
  rcases (canonical_side₂_outer_orbit_mem_iff_swapped_root0 hNT data hsep x).1 hx with
    hroot | ⟨k, hxk, hτ⟩
  · rw [← hxW, hroot]
    rw [sideVertexToM₂_tail_inr_zero_apply]
    rw [canonicalSide₂Anchor₁_tail hNT data hsep, htu]
    exact data.chord.left_boundary
  · have H := side₂EndpointBoundaryAlignment_uncond hNT data hsep
    have hTA := canonicalTracePhiArc₂_fwdArc_of_alignment hNT data hsep H.1 H.2
    have hτorig :
        (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
            (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
          ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) k := by
      simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)] using hτ
    rcases (hTA.mem_iff k).1 hτorig with ⟨i, hk⟩
    rw [← hxW, hxk]
    rw [sideVertexToM₂_tail_inl_apply]
    rw [hk]
    exact boundaryCycle_tail_mem_vertices_of_mem_darts hNT.outerCycle
      ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).boundary i)

theorem fwdArc_arcDart_mem_outerArc₂
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (i : Fin (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).len) :
    (ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart i ∈ data.outerArc₂ := by
  constructor
  · exact (hNT.outerCycle.mem_darts_iff _).mp
      ((ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).boundary i)
  · exact ProofsInTheBook.ZinanCh35ArcSide.fwdArc_reverse_face_mem_side₂ data i

theorem canonicalSide₂_faceDartList_mem_of_outerArc₂
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₂}) (hk : k.1 ∈ data.outerArc₂) :
    (Sum.inl k : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) ∈
      (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm).faceDartList (Sum.inr 0) := by
  classical
  obtain ⟨i, hi⟩ := outerArc₂_mem_fwdArc_canonical hNT data hsep hk
  have H := side₂EndpointBoundaryAlignment_uncond hNT data hsep
  have hTA := canonicalTracePhiArc₂_fwdArc_of_alignment hNT data hsep H.1 H.2
  have hkArc :
      k =
        ⟨(ProofsInTheBook.ZinanCh35ArcSide.fwdArc data).arcDart i,
          fwdArc_arcDart_notMem_keptDel₂ hNT data hsep i⟩ := by
    apply Subtype.ext
    exact hi
  have hτ :
      (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)).SameCycle
        ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) k :=
    (hTA.mem_iff k).2 ⟨i, hkArc⟩
  have hτswapped :
      (tracePhi (data.sideAlpha₂ hsep) data.sideSigma₂
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)).SameCycle
        ((data.sideAlpha₂ hsep) (side₂Anchor₁ data hsep)) k := by
    simpa [tracePhi_swap_anchors (data.sideAlpha₂ hsep) data.sideSigma₂
        (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep)] using hτ
  exact (canonical_side₂_outer_orbit_mem_iff_swapped_root0
    hNT data hsep (Sum.inl k)).2 (Or.inr ⟨k, rfl, hτswapped⟩)

theorem canonicalSide₂_boundary_of_outerArc_tail_eq
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {W : (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).Vertex}
    {b : D} (hb : b ∈ data.outerArc₂)
    (htail : M.tail b =
      ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm W) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W := by
  classical
  let k : {d : D // d ∉ data.keptDel₂} :=
    ⟨b, ProofsInTheBook.ChordSideClose.outerArc_notMem_keptDel₂ data hb.1 hb.2⟩
  let S := data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  let Wb : S.Vertex := S.tail (Sum.inl k)
  have hWb :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex Wb :=
    canonicalSide₂_boundary_tail_of_faceDartList_mem (hNT := hNT) data hsep
      (canonicalSide₂_faceDartList_mem_of_outerArc₂ (hNT := hNT) data hsep k hb)
  have hι :
      ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm Wb =
        ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm W := by
    dsimp [Wb, S, k]
    rw [sideVertexToM₂_tail_inl_apply]
    exact htail
  have hEq : Wb = W :=
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_injective_canonical data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm hι
  simpa [hEq] using hWb

theorem canonicalSide₂_boundary_of_parent_eq_tail
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {W : (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).Vertex}
    (htu : M.tail data.dart = u)
    (hW : ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm W = u) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W := by
  classical
  let S := data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  let Wb : S.Vertex := S.tail (Sum.inr (0 : Fin 2))
  have hx := canonicalSide₂_root0_mem_faceDartList (hNT := hNT) data hsep
  have hWb :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex Wb :=
    canonicalSide₂_boundary_tail_of_faceDartList_mem (hNT := hNT) data hsep hx
  have hι :
      ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm Wb =
        ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm W := by
    dsimp [Wb, S]
    rw [sideVertexToM₂_tail_inr_zero_apply, canonicalSide₂Anchor₁_tail hNT data hsep, htu, hW]
  have hEq : Wb = W :=
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_injective_canonical data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm hι
  simpa [hEq] using hWb

theorem canonicalSide₂_boundary_of_parent_eq_head
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {W : (data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm).Vertex}
    (hhv : M.head data.dart = v)
    (hW : ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm W = v) :
    (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex W := by
  classical
  let S := data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  let Wb : S.Vertex := S.head (Sum.inr (0 : Fin 2))
  have hx := canonicalSide₂_root0_mem_faceDartList (hNT := hNT) data hsep
  have hWb :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex Wb :=
    canonicalSide₂_boundary_head_of_faceDartList_mem (hNT := hNT) data hsep hx
  have hι :
      ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm Wb =
        ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm W := by
    dsimp [Wb, S]
    rw [sideVertexToM₂_head_inr_zero_apply, canonicalSide₂Anchor₀_tail hNT data hsep, hhv, hW]
  have hEq : Wb = W :=
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_injective_canonical data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm hι
  simpa [hEq] using hWb

theorem canonicalSide₂_parent_boundary_vertex_side_boundary_normalized
    {h : hNT.outerCycle.Chord u v}
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v)
    (W : ((normalizedChordSplitData h).sideMap₂ hsep
      (side₂Anchor₁ (normalizedChordSplitData h) hsep)
      (side₂Anchor₀ (normalizedChordSplitData h) hsep)
      (side₂Anchors_ne hNT (normalizedChordSplitData h) hsep).symm).Vertex)
    (hparent : hNT.outerCycle.IsBoundaryVertex
      (ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ (normalizedChordSplitData h) hsep
        (side₂Anchor₁ (normalizedChordSplitData h) hsep)
        (side₂Anchor₀ (normalizedChordSplitData h) hsep)
        (side₂Anchors_ne hNT (normalizedChordSplitData h) hsep).symm W)) :
    (canonicalSide₂NT (hNT := hNT) (normalizedChordSplitData h) hsep).outerCycle.IsBoundaryVertex W := by
  classical
  let data := normalizedChordSplitData h
  let ι := ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
    (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  have hWside : ι W ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data :=
    ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_mem data hsep
      (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm W
  have hparentι : hNT.outerCycle.IsBoundaryVertex (ι W) := by
    simpa [ι, data] using hparent
  let R := normalizedRuns h
  rcases R.covering hparentι with hUV | hVU | hWu | hWv
  · obtain ⟨i, hi⟩ := hUV
    have hB : M.dartFace (M.α ((ZinanCh35Aligned.daCast R.arcUV htu.symm hhv.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcUV htu.symm hhv.symm).symm i))) ∈ data.side₁ :=
      bwdRun_reverse_face_mem_side₁ data (ZinanCh35Aligned.daCast R.arcUV htu.symm hhv.symm)
        (by rw [ZinanCh35Aligned.daCast_len]; exact R.lenUV) _
    have hsame : (ZinanCh35Aligned.daCast R.arcUV htu.symm hhv.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcUV htu.symm hhv.symm).symm i)
          = R.arcUV.arcDart i := by
      rw [ZinanCh35Aligned.daCast_arcDart_eq]; congr 1
    rw [hsame] at hB
    have hchord : M.dartEdge (R.arcUV.arcDart i) ≠ s(u, v) := by
      intro he
      apply h.not_boundary_edge
      rw [← he]
      show M.dartEdge (R.arcUV.arcDart i) ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq]
      exact List.mem_map_of_mem (R.arcUV.boundary i)
    have hWside₁ : ι W ∈ sideRegion₁ data := by
      have hchordα : M.dartEdge (M.α (R.arcUV.arcDart i)) ≠ s(u, v) := by
        rw [M.dartEdge_alpha]
        exact hchord
      obtain ⟨_, htail⟩ :=
        endpoints_mem_sideRegion₁_of_face data hsep hchordα hB
      rw [M.head_alpha] at htail
      rw [hi] at htail
      exact htail
    rcases ProofsInTheBook.ZinanCh35StarConn.sideRegionInterChordEnds_holds data hsep hWside₁ hWside with hWu' | hWv'
    · exact canonicalSide₂_boundary_of_parent_eq_tail (hNT := hNT) data hsep (W := W) htu (by
        simpa [ι] using hWu')
    · exact canonicalSide₂_boundary_of_parent_eq_head (hNT := hNT) data hsep (W := W) hhv (by
        simpa [ι] using hWv')
  · obtain ⟨i, hi⟩ := hVU
    have hF : M.dartFace (M.α ((ZinanCh35Aligned.daCast R.arcVU hhv.symm htu.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcVU hhv.symm htu.symm).symm i))) ∈ data.side₂ :=
      fwdRun_reverse_face_mem_side₂ data (ZinanCh35Aligned.daCast R.arcVU hhv.symm htu.symm)
        (by rw [ZinanCh35Aligned.daCast_len]; exact R.lenVU) _
    have hsame : (ZinanCh35Aligned.daCast R.arcVU hhv.symm htu.symm).arcDart
        (Fin.cast (ZinanCh35Aligned.daCast_len R.arcVU hhv.symm htu.symm).symm i)
          = R.arcVU.arcDart i := by
      rw [ZinanCh35Aligned.daCast_arcDart_eq]; congr 1
    rw [hsame] at hF
    have hb : R.arcVU.arcDart i ∈ data.outerArc₂ := by
      constructor
      · exact (hNT.outerCycle.mem_darts_iff _).mp (R.arcVU.boundary i)
      · exact hF
    exact canonicalSide₂_boundary_of_outerArc_tail_eq (hNT := hNT) data hsep hb (by
      simpa [ι] using hi)
  · exact canonicalSide₂_boundary_of_parent_eq_tail (hNT := hNT) data hsep (W := W) htu (by
      simpa [ι] using hWu)
  · exact canonicalSide₂_boundary_of_parent_eq_head (hNT := hNT) data hsep (W := W) hhv (by
      simpa [ι] using hWv)

theorem canonicalSide₂ThomassenLists_forced_normalized
    {α : Type u} [DecidableEq α] {h : hNT.outerCycle.Chord u v}
    {L : M.Vertex → Finset α} {cp cq : α}
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v)
    (hTL : ThomassenLists hNT p q L cp cq)
    (hp : p ∈ sideRegion₁ (normalizedChordSplitData h))
    (hq : q ∈ sideRegion₁ (normalizedChordSplitData h))
    (regions : ChordSplitRegions hNT u v p q L cp cq)
    (c₁ : M.Vertex → α) (hcuv : c₁ u ≠ c₁ v) :
    ThomassenLists
      (canonicalSide₂NT (hNT := hNT) (normalizedChordSplitData h) hsep)
      (((normalizedChordSplitData h).sideMap₂ hsep
        (side₂Anchor₁ (normalizedChordSplitData h) hsep)
        (side₂Anchor₀ (normalizedChordSplitData h) hsep)
        (side₂Anchors_ne hNT (normalizedChordSplitData h) hsep).symm).tail (Sum.inr 0))
      (((normalizedChordSplitData h).sideMap₂ hsep
        (side₂Anchor₁ (normalizedChordSplitData h) hsep)
        (side₂Anchor₀ (normalizedChordSplitData h) hsep)
        (side₂Anchors_ne hNT (normalizedChordSplitData h) hsep).symm).head (Sum.inr 0))
      (fun x => regions.forcedLists c₁ L
        (ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ (normalizedChordSplitData h) hsep
          (side₂Anchor₁ (normalizedChordSplitData h) hsep)
          (side₂Anchor₀ (normalizedChordSplitData h) hsep)
          (side₂Anchors_ne hNT (normalizedChordSplitData h) hsep).symm x))
      (c₁ u) (c₁ v) := by
  classical
  let data := normalizedChordSplitData h
  let S := data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  let ι := ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂ data hsep
    (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
    (side₂Anchors_ne hNT data hsep).symm
  have hx : (Sum.inr (0 : Fin 2) : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) ∈
      S.faceDartList (Sum.inr 0) :=
    canonicalSide₂_root0_mem_faceDartList (hNT := hNT) data hsep
  have hpbd :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
        (S.tail (Sum.inr (0 : Fin 2))) :=
    canonicalSide₂_boundary_tail_of_faceDartList_mem (hNT := hNT) data hsep hx
  have hqbd :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryVertex
        (S.head (Sum.inr (0 : Fin 2))) :=
    canonicalSide₂_boundary_head_of_faceDartList_mem (hNT := hNT) data hsep hx
  have hpqbd :
      (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryEdge
        (S.dartEdge (Sum.inr (0 : Fin 2))) :=
    canonicalSide₂_boundary_edge_of_faceDartList_mem (hNT := hNT) data hsep hx
  refine
    { p_boundary := by simpa [data, S] using hpbd
      q_boundary := by simpa [data, S] using hqbd
      pq_boundary_edge := by
        change (canonicalSide₂NT (hNT := hNT) data hsep).outerCycle.IsBoundaryEdge
          (S.dartEdge (Sum.inr (0 : Fin 2)))
        exact hpqbd
      colors_ne := hcuv
      list_p := ?_
      list_q := ?_
      boundary_ge_three := ?_
      interior_ge_five := ?_ }
  · have hιp : ι (S.tail (Sum.inr (0 : Fin 2))) = u := by
      dsimp [ι, S]
      rw [sideVertexToM₂_tail_inr_zero_apply, canonicalSide₂Anchor₁_tail hNT data hsep, htu]
    simpa [ι, data, S, hιp] using regions.forcedLists_u c₁ L
  · have hιq : ι (S.head (Sum.inr (0 : Fin 2))) = v := by
      dsimp [ι, S]
      rw [sideVertexToM₂_head_inr_zero_apply, canonicalSide₂Anchor₀_tail hNT data hsep, hhv]
    have huv : u ≠ v := h.endpoints_ne
    simpa [ι, data, S, hιq] using regions.forcedLists_v huv c₁ L
  · intro W hW hWp hWq
    have hparent :
        hNT.outerCycle.IsBoundaryVertex (ι W) :=
      canonicalSide₂_boundary_vertex_parent_boundary (hNT := hNT) data hsep htu W hW
    have hWside₂ : ι W ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data :=
      ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_mem data hsep
        (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
        (side₂Anchors_ne hNT data hsep).symm W
    have hWu : ι W ≠ u := by
      intro hιu
      have hEq : W = S.tail (Sum.inr (0 : Fin 2)) :=
        ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_injective_canonical data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm (by
            dsimp [ι, S] at hιu ⊢
            rw [sideVertexToM₂_tail_inr_zero_apply, canonicalSide₂Anchor₁_tail hNT data hsep,
              htu]
            exact hιu)
      exact hWp hEq
    have hWv : ι W ≠ v := by
      intro hιv
      have hEq : W = S.head (Sum.inr (0 : Fin 2)) :=
        ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_injective_canonical data hsep
          (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
          (side₂Anchors_ne hNT data hsep).symm (by
            dsimp [ι, S] at hιv ⊢
            rw [sideVertexToM₂_head_inr_zero_apply, canonicalSide₂Anchor₀_tail hNT data hsep,
              hhv]
            exact hιv)
      exact hWq hEq
    have hWp_parent : ι W ≠ p := by
      intro hιp
      have hp₂ : p ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data := by
        simpa [hιp] using hWside₂
      rcases ProofsInTheBook.ZinanCh35StarConn.sideRegionInterChordEnds_holds data hsep hp hp₂ with
        hpu | hpv
      · exact hWu (hιp.trans hpu)
      · exact hWv (hιp.trans hpv)
    have hWq_parent : ι W ≠ q := by
      intro hιq
      have hq₂ : q ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data := by
        simpa [hιq] using hWside₂
      rcases ProofsInTheBook.ZinanCh35StarConn.sideRegionInterChordEnds_holds data hsep hq hq₂ with
        hqu | hqv
      · exact hWu (hιq.trans hqu)
      · exact hWv (hιq.trans hqv)
    rw [regions.forcedLists_other hWu hWv c₁ L]
    exact hTL.boundary_ge_three (ι W) hparent hWp_parent hWq_parent
  · intro W hWint
    have hparentInt : ¬ hNT.outerCycle.IsBoundaryVertex (ι W) := by
      intro hparent
      exact hWint
        (canonicalSide₂_parent_boundary_vertex_side_boundary_normalized
          (hNT := hNT) (h := h) hsep htu hhv W (by simpa [data, ι] using hparent))
    have hWu : ι W ≠ u := by
      intro hιu
      exact hWint
        (canonicalSide₂_boundary_of_parent_eq_tail (hNT := hNT) data hsep (W := W) htu
          (by simpa [ι] using hιu))
    have hWv : ι W ≠ v := by
      intro hιv
      exact hWint
        (canonicalSide₂_boundary_of_parent_eq_head (hNT := hNT) data hsep (W := W) hhv
          (by simpa [ι] using hιv))
    rw [regions.forcedLists_other hWu hWv c₁ L]
    exact hTL.interior_ge_five (ι W) hparentInt

noncomputable def canonicalChordBranchResidualData
    {α : Type u} [DecidableEq α] {h : hNT.outerCycle.Chord u v}
    {L : M.Vertex → Finset α} {cp cq : α}
    (hTL : ThomassenLists hNT p q L cp cq)
    (hp : p ∈ sideRegion₁ (normalizedChordSplitData h))
    (hq : q ∈ sideRegion₁ (normalizedChordSplitData h)) :
    ProofsInTheBook.ZinanCh35ChordBranch.ChordBranchResidualData h p q L cp cq := by
  classical
  let data := normalizedChordSplitData h
  let hsep := ProofsInTheBook.ZinanCh35ChordResidue.normSep h
  have htu : M.tail data.dart = u := by
    simpa [data] using normalizedChordSplitData_dart_tail (hNT := hNT) h
  have hhv : M.head data.dart = v := by
    simpa [data] using normalizedChordSplitData_dart_head (hNT := hNT) h
  have hSide₁ :
      ∃ pₛ qₛ : (data.sideMap₁ hsep
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).Vertex,
        ThomassenLists
          (canonicalSide₁NT (hNT := hNT) data hsep)
          pₛ qₛ
          (fun x => L (sideVertexToM₁ data hsep
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep) x))
          cp cq :=
    canonicalSide₁ThomassenLists_exists_normalized (hNT := hNT) (h := h)
      hsep htu hhv hTL hp hq
  let p₁ := Classical.choose hSide₁
  let hSide₁' := Classical.choose_spec hSide₁
  let q₁ := Classical.choose hSide₁'
  have hL₁ := Classical.choose_spec hSide₁'
  let res := chordSplitRegionsResidue_of_precolored data hsep hp hq
  let regions :=
    ProofsInTheBook.ZinanCh35ChordResidue.chordSplitRegions_of_residue
      data hsep htu hhv res (L := L) (cp := cp) (cq := cq)
  refine canonicalChordBranchResidualData_of_fuel (hNT := hNT) (h := h)
    L cp cq htu hhv hp hq p₁ q₁ cp cq ?_
    (fun _ _ => data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm |>.tail (Sum.inr (0 : Fin 2)))
    (fun _ _ => data.sideMap₂ hsep (side₂Anchor₁ data hsep) (side₂Anchor₀ data hsep)
      (side₂Anchors_ne hNT data hsep).symm |>.head (Sum.inr (0 : Fin 2)))
    (fun c₁ _ => c₁ u) (fun c₁ _ => c₁ v) ?_
  · simpa [canonicalSide₁NT, data, hsep] using hL₁
  · intro c₁ hcuv
    simpa [canonicalSide₂NT, data, hsep, res, regions] using
      canonicalSide₂ThomassenLists_forced_normalized (hNT := hNT) (h := h)
        hsep htu hhv hTL hp hq regions c₁ hcuv

noncomputable def canonicalChordBranchResidualSupplier
    (α : Type u) [DecidableEq α] :
    ProofsInTheBook.ZinanCh35ChordBranch.ChordBranchResidualSupplier α where
  supply := by
    intro D _ _ M hNT p q L cp cq hTL hchord
    let u := Classical.choose hchord
    let hchord' := Classical.choose_spec hchord
    let v := Classical.choose hchord'
    let h := Classical.choose_spec hchord'
    obtain ⟨u', v', h', hpq⟩ :=
      orientChordForPreedge (hNT := hNT) (h := h) hTL
    exact ⟨u', v', h',
      canonicalChordBranchResidualData (hNT := hNT) (h := h') hTL hpq.1 hpq.2⟩

end ProofsInTheBook.ZinanCh35ChordSupplier2

/-! ## Axiom audit. -/
