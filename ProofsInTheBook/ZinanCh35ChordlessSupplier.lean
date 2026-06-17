import ProofsInTheBook.ZinanCh35ChordlessSite
import ProofsInTheBook.ZinanCh35DeletedAssembly
import ProofsInTheBook.ZinanCh35DeletedBoundary
import ProofsInTheBook.ZinanCh35ChordlessOracle

/-!
# Chordless supplier assembly

This file is the final Phase-C supplier layer.  It starts by exposing the
deleted-boundary classification API needed by the Thomassen-list transport.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35ChordlessSupplier

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {α : Type u} [DecidableEq α]
variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}

/-- Boundary-cycle vertices are exactly tails of listed boundary darts. -/
theorem boundary_vertex_iff_exists_dart_tail {K : CombMap D} {f : K.Face}
    (C : BoundaryCycle K f) (W : K.Vertex) :
    C.IsBoundaryVertex W ↔ ∃ d : D, d ∈ C.darts ∧ K.tail d = W := by
  constructor
  · intro hW
    rw [BoundaryCycle.IsBoundaryVertex, C.vertices_eq] at hW
    simpa [List.mem_map] using hW
  · rintro ⟨d, hd, rfl⟩
    rw [BoundaryCycle.IsBoundaryVertex, C.vertices_eq]
    exact List.mem_map_of_mem hd

/-- Boundary-cycle edges are exactly dart edges of listed boundary darts. -/
theorem boundary_edge_iff_exists_dart_edge {K : CombMap D} {f : K.Face}
    (C : BoundaryCycle K f) (e : Sym2 K.Vertex) :
    C.IsBoundaryEdge e ↔ ∃ d : D, d ∈ C.darts ∧ K.dartEdge d = e := by
  constructor
  · intro he
    rw [BoundaryCycle.IsBoundaryEdge, C.edges_eq] at he
    simpa [List.mem_map] using he
  · rintro ⟨d, hd, rfl⟩
    rw [BoundaryCycle.IsBoundaryEdge, C.edges_eq]
    exact List.mem_map_of_mem hd

/-- An endpoint of a listed boundary edge is a boundary vertex. -/
lemma boundary_vertex_of_boundary_edge_left {K : CombMap D} {f : K.Face}
    (C : BoundaryCycle K f) {x y : K.Vertex}
    (he : C.IsBoundaryEdge s(x, y)) :
    C.IsBoundaryVertex x := by
  classical
  obtain ⟨d, hd, hdedge⟩ := (boundary_edge_iff_exists_dart_edge C s(x, y)).1 he
  rw [CombMap.dartEdge, Sym2.eq_iff] at hdedge
  rcases hdedge with ⟨htail, _hhead⟩ | ⟨_htail, hhead⟩
  · exact (boundary_vertex_iff_exists_dart_tail C x).2 ⟨d, hd, htail⟩
  · have hφd : K.φ d ∈ C.darts := C.phi_mem_darts hd
    exact (boundary_vertex_iff_exists_dart_tail C x).2
      ⟨K.φ d, hφd, by rw [K.tail_phi, hhead]⟩

/-- Consecutive in/out darts at a simple boundary vertex have distinct other
endpoints. -/
lemma boundary_neighbors_distinct_public {bin bout : D}
    (hbin_mem : bin ∈ hNT.outerCycle.darts) (hbout_mem : bout ∈ hNT.outerCycle.darts)
    (hbin_phi : M.φ bin = bout) :
    M.tail bin ≠ M.head bout := by
  intro hxy
  have hφbout_mem : M.φ bout ∈ hNT.outerCycle.darts :=
    hNT.outerCycle.phi_mem_darts hbout_mem
  have htail : M.tail bin = M.tail (M.φ bout) := by
    rw [tail_phi, hxy]
  have hbin_eq_phi_bout : bin = M.φ bout :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hbin_mem hφbout_mem htail
  have hφ2 : M.φ (M.φ bout) = bout := by
    rw [← hbin_eq_phi_bout, hbin_phi]
  have hφ : M.φ bout ≠ bout :=
    phi_ne_self_of_isSimpleGraph M hNT.simpleGraph bout
  have hcard2 :
      (M.φ.cycleOf bout).support.card = 2 :=
    card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
  have hbout_face : M.dartFace bout = hNT.outerFace :=
    (hNT.outerCycle.mem_darts_iff bout).mp hbout_mem
  have hface2 : M.faceLen hNT.outerFace = 2 := by
    have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
    rw [hbout_face, hcard2] at hsupport
    exact hsupport
  have hlen2 : hNT.outerCycle.length = 2 :=
    hNT.outerCycle.faceLen_eq_length.symm.trans hface2
  have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
  omega

/-- Any old boundary vertex that survives a vertex deletion has an old boundary
edge incident with it whose other endpoint also survives. -/
lemma old_boundary_vertex_has_surviving_boundary_edge
    {d0 : D} (htail0 : M.tail d0 = v0)
    {u : M.Vertex}
    (hu_old : hNT.outerCycle.IsBoundaryVertex u)
    (hu_ne : u ≠ M.tail d0) :
    ∃ w : M.Vertex, w ≠ M.tail d0 ∧ hNT.outerCycle.IsBoundaryEdge s(u, w) := by
  classical
  obtain ⟨bin, bout, hbin, _hbin_unique, hbout, _hbout_unique, hbin_phi⟩ :=
    hNT.outer_v0_darts_consecutive hu_old
  rcases hbin with ⟨hbin_mem, hbin_head⟩
  rcases hbout with ⟨hbout_mem, hbout_tail⟩
  by_cases hsucc_ne : M.head bout ≠ M.tail d0
  · refine ⟨M.head bout, hsucc_ne, ?_⟩
    show s(u, M.head bout) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hedge : M.dartEdge bout = s(u, M.head bout) := by
      simp [CombMap.dartEdge, hbout_tail]
    rw [← hedge]
    exact List.mem_map_of_mem hbout_mem
  · have hsucc_eq : M.head bout = M.tail d0 := by simpa using not_not.mp hsucc_ne
    have hpred_ne : M.tail bin ≠ M.tail d0 := by
      intro hpred_eq
      exact boundary_neighbors_distinct_public (hNT := hNT) hbin_mem hbout_mem hbin_phi
        (by rw [hpred_eq, hsucc_eq])
    refine ⟨M.tail bin, hpred_ne, ?_⟩
    show s(u, M.tail bin) ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    have hedge : M.dartEdge bin = s(u, M.tail bin) := by
      simp [CombMap.dartEdge, hbin_head, Sym2.eq_swap]
    rw [← hedge]
    exact List.mem_map_of_mem hbin_mem

/-- The second vertex of a fan consecutive pair is either exposed-interior or
the terminal endpoint. -/
lemma consecutivePair_second_mem_interior_or_w
    (fan : BoundaryVertexFan hNT v0) {a b : M.Vertex}
    (hp : (a, b) ∈ consecutivePairs fan.path) :
    b ∈ fan.interior ∨ b = fan.w := by
  have hb_tail : b ∈ fan.path.tail := by
    rw [consecutivePairs] at hp
    exact (List.of_mem_zip hp).2
  rw [BoundaryVertexFan.path, fanPath] at hb_tail
  simpa using hb_tail

/-- Any listed interior fan vertex has a predecessor in the fan path. -/
lemma fan_interior_exists_predecessor_pair
    (fan : BoundaryVertexFan hNT v0) {z : M.Vertex}
    (hz : z ∈ fan.interior) :
    ∃ a : M.Vertex, (a, z) ∈ consecutivePairs fan.path := by
  classical
  have aux : ∀ (x : M.Vertex) (l : List M.Vertex),
      z ∈ l → ∃ a : M.Vertex, (a, z) ∈ consecutivePairs (x :: l ++ [fan.w]) := by
    intro x l
    induction l generalizing x with
    | nil =>
        intro hz
        simp at hz
    | cons y ys ih =>
        intro hz
        rw [List.mem_cons] at hz
        rcases hz with rfl | hz
        · refine ⟨x, ?_⟩
          simp [consecutivePairs]
        · obtain ⟨a, ha⟩ := ih y hz
          refine ⟨a, ?_⟩
          simp [consecutivePairs] at ha ⊢
          exact Or.inr ha
  rw [BoundaryVertexFan.path, fanPath]
  exact aux fan.x fan.interior hz

/-- Fan interior vertices are old-map interior vertices in the chordless case. -/
theorem fan_interior_old_interior
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    {z : M.Vertex} (hz : z ∈ fan.interior.toFinset) :
    ¬ hNT.outerCycle.IsBoundaryVertex z := by
  rw [List.mem_toFinset] at hz
  exact fan_interior_vertices_not_boundary_of_chordless hNT fan hchordless z hz

/-- A surviving dart whose old face was incident with the deleted vertex has its
tail over either an old boundary vertex or an exposed fan-interior vertex. -/
theorem incident_survivor_tail_oldBoundary_or_fanInterior
    (fan : BoundaryVertexFan hNT v0) {d0 : D} (htail0 : M.tail d0 = v0)
    (y : {d : D // d ∉ M.deleteVertexSet d0})
    (hyinc : M.dartFace y.1 ∈ M.vertexFaces d0) :
    hNT.outerCycle.IsBoundaryVertex (M.tail y.1) ∨
      M.tail y.1 ∈ fan.interior.toFinset := by
  classical
  by_cases hyouter : M.dartFace y.1 = hNT.outerFace
  · left
    exact ProofsInTheBook.ZinanCh35DeletedAssembly.isBoundaryVertex_tail_of_outer_dart
      (hNT := hNT) hyouter
  ·
    obtain ⟨a, b, hp, hy_eq⟩ :=
      ProofsInTheBook.ZinanCh35DeletedAssembly.incident_nonouter_survivor_eq_fan_edge
        fan htail0 y hyinc hyouter
    have htail_b : M.tail y.1 = b := by
      rw [hy_eq]
      exact (fan.incident_faces_exact.triangle_of_pair hp).tail1
    rcases consecutivePair_second_mem_interior_or_w fan hp with hbint | hbw
    · right
      simpa [htail_b] using hbint
    · left
      rw [htail_b, hbw]
      exact fan.w_boundary

/-- Forward half of deleted-boundary classification, abstracted over any deleted
boundary cycle whose darts are known to be old faces incident with the deleted
vertex. -/
theorem deleted_boundary_vertex_oldBoundary_or_fanInterior_of_incident_darts
    (fan : BoundaryVertexFan hNT v0) {d0 : D} (htail0 : M.tail d0 = v0)
    {outerFace : (M.deleteVertex d0).Face}
    (C : BoundaryCycle (M.deleteVertex d0) outerFace)
    (hinc : ∀ y : {d : D // d ∉ M.deleteVertexSet d0},
      y ∈ C.darts → M.dartFace y.1 ∈ M.vertexFaces d0)
    {u' : (M.deleteVertex d0).Vertex}
    (hu' : C.IsBoundaryVertex u') :
    hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∨
      deletedVertexToM M d0 u' ∈ fan.interior.toFinset := by
  classical
  obtain ⟨y, hy, hy_tail⟩ := (boundary_vertex_iff_exists_dart_tail C u').1 hu'
  have hclass := incident_survivor_tail_oldBoundary_or_fanInterior fan htail0 y (hinc y hy)
  have htoM : deletedVertexToM M d0 u' = M.tail y.1 := by
    rw [← hy_tail]
    exact deletedVertexToM_tail M d0 y
  simpa [htoM] using hclass

/-- Darts on the produced fan-pair deleted outer cycle are exactly old faces
incident with the deleted vertex, forward direction. -/
theorem fan_pair_deleted_outerCycle_dart_incident
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (y : {d : D // d ∉ M.deleteVertexSet d0})
    (hy : y ∈
      ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.darts)) :
    M.dartFace y.1 ∈ M.vertexFaces d0 := by
  classical
  let root : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩
  let hmerge : DeleteVertexMergedFaceSingleOrbit M d0 :=
    ProofsInTheBook.ZinanCh35MergedArc.deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
      fan hchordless htail0 hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
  have hroot_inc : M.dartFace root.1 ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.fanPairSeamEdge_incident fan htail0 hp
  change y ∈ (M.deleteVertex d0).faceDartList root at hy
  exact (ProofsInTheBook.ZinanCh35DeletedAssembly.mem_faceDartList_root_iff_incident
    hNT htail0 root y hroot_inc hmerge).1 hy

/-- Any survivor whose old face is incident with the deleted vertex is listed on
the produced fan-pair deleted outer cycle. -/
theorem fan_pair_incident_survivor_mem_deleted_outerCycle
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (y : {d : D // d ∉ M.deleteVertexSet d0})
    (hyinc : M.dartFace y.1 ∈ M.vertexFaces d0) :
    y ∈
      ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.darts) := by
  classical
  let root : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩
  let hmerge : DeleteVertexMergedFaceSingleOrbit M d0 :=
    ProofsInTheBook.ZinanCh35MergedArc.deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
      fan hchordless htail0 hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
  have hroot_inc : M.dartFace root.1 ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.fanPairSeamEdge_incident fan htail0 hp
  change y ∈ (M.deleteVertex d0).faceDartList root
  exact (ProofsInTheBook.ZinanCh35DeletedAssembly.mem_faceDartList_root_iff_incident
    hNT htail0 root y hroot_inc hmerge).2 hyinc

/-- Forward half of `DeletedBoundaryClassification.boundary_iff` for the closed
fan-pair seam assembly. -/
theorem fan_pair_deleted_boundary_vertex_oldBoundary_or_fanInterior
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu' :
      ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u')) :
    hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∨
      deletedVertexToM M d0 u' ∈ fan.interior.toFinset := by
  exact deleted_boundary_vertex_oldBoundary_or_fanInterior_of_incident_darts
    fan htail0
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle)
    (fun y hy => fan_pair_deleted_outerCycle_dart_incident
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi y hy)
    hu'

/-- A deleted vertex whose old image is an exposed fan-interior vertex is on the
produced deleted outer boundary. -/
theorem fan_pair_fanInterior_deleted_boundary_vertex
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu'fan : deletedVertexToM M d0 u' ∈ fan.interior.toFinset) :
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u') := by
  classical
  rw [List.mem_toFinset] at hu'fan
  obtain ⟨a₀, hp₀⟩ := fan_interior_exists_predecessor_pair fan hu'fan
  let T := fan.incident_faces_exact.triangle_of_pair hp₀
  let y : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨T.d1, ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
      T htail0⟩
  have hyinc : M.dartFace y.1 ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.fanPairSeamEdge_incident fan htail0 hp₀
  have hy_mem := fan_pair_incident_survivor_mem_deleted_outerCycle
    fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
    hoPre_surv hoPre_phi y hyinc
  have htail_old : M.tail y.1 = deletedVertexToM M d0 u' := by
    dsimp [y, T]
    rw [(fan.incident_faces_exact.triangle_of_pair hp₀).tail1]
  have htail_deleted : (M.deleteVertex d0).tail y = u' := by
    apply deletedVertexToM_injective M d0
    rw [deletedVertexToM_tail, htail_old]
  exact (boundary_vertex_iff_exists_dart_tail
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle) u').2
    ⟨y, hy_mem, htail_deleted⟩

/-- The canonical section is the unique deleted vertex with the prescribed old
image. -/
lemma deleted_vertex_eq_sectionToDeleted_of_toM_eq
    {d0 : D} (R : FanSurgeryReconstruction hNT d0)
    {W : (M.deleteVertex d0).Vertex} {x : M.Vertex}
    (hx : x ≠ M.tail d0)
    (hW : deletedVertexToM M d0 W = x) :
    W = sectionToDeleted R x hx := by
  apply deletedVertexToM_injective M d0
  rw [hW, deletedVertexToM_sectionToDeleted]

/-- Old boundary edges whose endpoints survive the deletion remain boundary
edges of the produced deleted outer cycle. -/
theorem fan_pair_old_boundary_edge_survives
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {x y : M.Vertex}
    (hx : x ≠ M.tail d0) (hy : y ≠ M.tail d0)
    (hedge : hNT.outerCycle.IsBoundaryEdge s(x, y)) :
    let R :=
      (ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon
    R.nearTriangulation.outerCycle.IsBoundaryEdge
      s(sectionToDeleted R x hx, sectionToDeleted R y hy) := by
  classical
  intro R
  obtain ⟨e, he_mem, he_edge⟩ :=
    (boundary_edge_iff_exists_dart_edge hNT.outerCycle s(x, y)).1 hedge
  have he_face : M.dartFace e = hNT.outerFace :=
    hNT.outerCycle.dartFace_of_mem_darts he_mem
  have htail_ne : M.tail e ≠ M.tail d0 := by
    rw [CombMap.dartEdge, Sym2.eq_iff] at he_edge
    rcases he_edge with ⟨ht, _hh⟩ | ⟨ht, _hh⟩
    · rw [ht]; exact hx
    · rw [ht]; exact hy
  have hhead_ne : M.head e ≠ M.tail d0 := by
    rw [CombMap.dartEdge, Sym2.eq_iff] at he_edge
    rcases he_edge with ⟨_ht, hh⟩ | ⟨_ht, hh⟩
    · rw [hh]; exact hy
    · rw [hh]; exact hx
  have hsurv : e ∉ M.deleteVertexSet d0 :=
    dart_notMem_deleteVertexSet_of_endpoints_ne M d0 htail_ne hhead_ne
  let e' : {d : D // d ∉ M.deleteVertexSet d0} := ⟨e, hsurv⟩
  have houter_inc : hNT.outerFace ∈ M.vertexFaces d0 :=
    ProofsInTheBook.ZinanCh35DeletedAssembly.oldOuterFace_incident_of_seam
      htail0 hbin_mem hbin_head hbout
  have he_inc : M.dartFace e'.1 ∈ M.vertexFaces d0 := by
    dsimp [e']
    rw [he_face]
    exact houter_inc
  have he'_mem := fan_pair_incident_survivor_mem_deleted_outerCycle
    fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
    hoPre_surv hoPre_phi e' he_inc
  refine (boundary_edge_iff_exists_dart_edge R.nearTriangulation.outerCycle
    s(sectionToDeleted R x hx, sectionToDeleted R y hy)).2 ⟨e', he'_mem, ?_⟩
  have he_edge_saved : M.dartEdge e = s(x, y) := he_edge
  rw [CombMap.dartEdge, Sym2.eq_iff] at he_edge_saved ⊢
  rcases he_edge_saved with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · left
    constructor
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hx (by
        rw [deletedVertexToM_tail]
        exact ht)
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hy (by
        rw [deletedVertexToM_head]
        exact hh)
  · right
    constructor
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hy (by
        rw [deletedVertexToM_tail]
        exact ht)
    · exact deleted_vertex_eq_sectionToDeleted_of_toM_eq R hx (by
        rw [deletedVertexToM_head]
        exact hh)

/-- Old boundary vertices that survive the deletion lie on the produced deleted
outer boundary. -/
theorem fan_pair_oldBoundary_deleted_boundary_vertex
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu_old : hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u')) :
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u') := by
  classical
  let R :=
    (ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi).chordlessRecon
  let u := deletedVertexToM M d0 u'
  have hu_ne : u ≠ M.tail d0 := by
    dsimp [u]
    exact deletedVertexToM_ne_v0 M d0 u'
  obtain ⟨w, hw_ne, hedge⟩ :=
    old_boundary_vertex_has_surviving_boundary_edge
      (hNT := hNT) (v0 := v0) htail0 hu_old hu_ne
  have hedge' :
      R.nearTriangulation.outerCycle.IsBoundaryEdge
        s(sectionToDeleted R u hu_ne, sectionToDeleted R w hw_ne) := by
    simpa [R] using
      (fan_pair_old_boundary_edge_survives
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hu_ne hw_ne hedge)
  have hsec_boundary :
      R.nearTriangulation.outerCycle.IsBoundaryVertex
        (sectionToDeleted R u hu_ne) :=
    boundary_vertex_of_boundary_edge_left R.nearTriangulation.outerCycle hedge'
  have hu'_eq : u' = sectionToDeleted R u hu_ne :=
    deleted_vertex_eq_sectionToDeleted_of_toM_eq R hu_ne (by rfl)
  simpa [R, hu'_eq]
    using hsec_boundary

/-- Full vertex-level deleted-boundary classification for the produced
fan-pair seam assembly. -/
theorem fan_pair_deleted_boundary_iff_oldBoundary_or_fanInterior
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (u' : (M.deleteVertex d0).Vertex) :
    ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u') ↔
      hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∨
        deletedVertexToM M d0 u' ∈ fan.interior.toFinset := by
  constructor
  · intro hu'
    exact fan_pair_deleted_boundary_vertex_oldBoundary_or_fanInterior
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi hu'
  · intro hclass
    rcases hclass with hold | hfan
    · exact fan_pair_oldBoundary_deleted_boundary_vertex
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hold
    · exact fan_pair_fanInterior_deleted_boundary_vertex
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi hfan

/-- Deleted non-boundary vertices map to old non-boundary vertices and are not
exposed fan-interior vertices. -/
theorem fan_pair_deleted_nonboundary_old_interior
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hp : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    {u' : (M.deleteVertex d0).Vertex}
    (hu' :
      ¬ ((ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
        fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
        hoPre_surv hoPre_phi).chordlessRecon.nearTriangulation.outerCycle.IsBoundaryVertex u')) :
    ¬ hNT.outerCycle.IsBoundaryVertex (deletedVertexToM M d0 u') ∧
      deletedVertexToM M d0 u' ∉ fan.interior.toFinset := by
  constructor
  · intro hold
    exact hu' (fan_pair_oldBoundary_deleted_boundary_vertex
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi hold)
  · intro hfan
    exact hu' (fan_pair_fanInterior_deleted_boundary_vertex
      fan hchordless hbig htail0 hbin_mem hbin_head hp hbin_tail hbout
      hoPre_surv hoPre_phi hfan)

end ProofsInTheBook.ZinanCh35ChordlessSupplier
