import ProofsInTheBook.ZinanCh35MergedArc
import ProofsInTheBook.ZinanCh35DeletedBoundary
import ProofsInTheBook.PlanarMapDeletedBoundary

/-!
# Chordless deleted-boundary assembly helpers

This file keeps the remaining Phase-C boundary assembly helpers out of the heavy
chordless supplier files.  The lemmas here are non-circular: in particular,
`cleanFaceClass_of_mergedOrbit_root` consumes only an independently proved merged
orbit and a chosen incident root of the merged outer face, not a `DeletedSeamData`.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35DeletedAssembly

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordlessFinal

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}

/-- A small list-cardinality repackaging used by the route-(b) itinerary: three
pairwise distinct listed elements force length at least three. -/
lemma three_le_length_of_three_mem {α : Type u} [DecidableEq α] {L : List α}
    {a b c : α} (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ L.length := by
  classical
  let S : Finset α := {a, b, c}
  have hSsub : S ⊆ L.toFinset := by
    intro x hx
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
    rw [List.mem_toFinset]
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hcardS : S.card = 3 := by
    simp [S, hab, hac, hbc]
  have hle_card : 3 ≤ L.toFinset.card := by
    rw [← hcardS]
    exact Finset.card_le_card hSsub
  exact hle_card.trans (List.toFinset_card_le L)

/-- The fan path has a first consecutive pair starting at `fan.x`. -/
lemma exists_head_fan_pair (fan : BoundaryVertexFan hNT v0) :
    ∃ b : M.Vertex, (fan.x, b) ∈ consecutivePairs fan.path := by
  set L : List M.Vertex := fan.interior ++ [fan.w] with hL
  have hpath : fan.path = fan.x :: L := by
    rw [BoundaryVertexFan.path, fanPath, hL, List.cons_append]
  obtain ⟨b, l', hLb⟩ : ∃ b l', L = b :: l' := by
    rw [hL]
    cases fan.interior with
    | nil => exact ⟨fan.w, [], rfl⟩
    | cons c t => exact ⟨c, t ++ [fan.w], rfl⟩
  refine ⟨b, ?_⟩
  rw [hpath, hLb, consecutivePairs]
  simp

/-- The fan path has a terminal consecutive pair ending at `fan.w`. -/
lemma exists_terminal_fan_pair (fan : BoundaryVertexFan hNT v0) :
    ∃ a : M.Vertex, (a, fan.w) ∈ consecutivePairs fan.path := by
  classical
  have hterm : ∀ (x : M.Vertex) (l : List M.Vertex),
      ∃ a : M.Vertex, (a, fan.w) ∈ consecutivePairs (x :: l ++ [fan.w]) := by
    intro x l
    induction l generalizing x with
    | nil =>
        refine ⟨x, ?_⟩
        simp [consecutivePairs]
    | cons z zs ih =>
        rcases ih z with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        simp [consecutivePairs] at ha ⊢
        exact Or.inr ha
  rw [BoundaryVertexFan.path, fanPath]
  exact hterm fan.x fan.interior

/-- Pure vertex-list part of the deleted outer-boundary simplicity proof.
The eventual itinerary supplies `oldArcVertices`, its old-boundary sublist proof,
and the half-open endpoint fact `fan.x ∉ oldArcVertices`; the fan/chordless layer
then proves the appended list is nodup. -/
theorem deleted_outer_vertices_nodup_M
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (oldArcVertices : List M.Vertex)
    (hold_sub : List.Sublist oldArcVertices hNT.outerCycle.vertices)
    (hx_not_oldArc : fan.x ∉ oldArcVertices) :
    ((fan.x :: fan.interior) ++ oldArcVertices).Nodup := by
  classical
  let fanPrefix : List M.Vertex := fan.x :: fan.interior
  have hpath : (fanPrefix ++ [fan.w]).Nodup := by
    simpa [fanPrefix, BoundaryVertexFan.path, fanPath] using
      fan_path_simple_of_chordless hNT fan hchordless
  have hfanPrefix : fanPrefix.Nodup :=
    List.Nodup.of_append_left hpath
  have holdBoundaryNodup : hNT.outerCycle.vertices.Nodup := by
    simpa [BoundaryCycle.VertexNodup] using hNT.outer_simple
  have holdArc : oldArcVertices.Nodup :=
    holdBoundaryNodup.sublist hold_sub
  have hdisj : List.Disjoint fanPrefix oldArcVertices := by
    rw [List.disjoint_left]
    intro y hyfan hyold
    have hy_old_boundary : hNT.outerCycle.IsBoundaryVertex y := by
      have hy_old : y ∈ hNT.outerCycle.vertices := hold_sub.subset hyold
      simpa [BoundaryCycle.IsBoundaryVertex] using hy_old
    rcases List.mem_cons.mp hyfan with hyx | hyint
    · subst hyx
      exact hx_not_oldArc hyold
    · exact
        (fan_interior_vertices_not_boundary_of_chordless
          hNT fan hchordless y hyint) hy_old_boundary
  simpa [fanPrefix] using hfanPrefix.append holdArc hdisj

/-- The old outer face is incident with the deleted vertex when `bin` is the
incoming outer dart and `bout = φ bin` is the outgoing outer dart at `v0`. -/
lemma oldOuterFace_incident_of_seam {d0 bin bout : D}
    (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin) :
    hNT.outerFace ∈ M.vertexFaces d0 := by
  classical
  rw [vertexFaces, Finset.mem_image]
  refine ⟨bout, ?_, ?_⟩
  · rw [mem_vertexDarts]
    have hbout_tail : M.tail bout = v0 := by
      rw [hbout, tail_phi, hbin_head]
    exact Quotient.exact (show M.tail d0 = M.tail bout by rw [htail0, hbout_tail])
  · have hbout_face : M.dartFace bout = hNT.outerFace := by
      rw [hbout, dartFace_phi]
      exact hNT.outerCycle.dartFace_of_mem_darts hbin_mem
    exact hbout_face

/-- A canonical fan-pair seam edge lies on a face incident with the deleted vertex. -/
lemma fanPairSeamEdge_incident
    (fan : BoundaryVertexFan hNT v0) {d0 : D} (htail0 : M.tail d0 = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path) :
    M.dartFace (fan.incident_faces_exact.triangle_of_pair hp).d1 ∈
      M.vertexFaces d0 := by
  classical
  set T := fan.incident_faces_exact.triangle_of_pair hp
  rw [vertexFaces, Finset.mem_image]
  refine ⟨T.d0, ?_, ?_⟩
  · rw [mem_vertexDarts]
    exact Quotient.exact (show M.tail d0 = M.tail T.d0 by rw [htail0, T.tail0])
  · have hface : M.dartFace T.d1 = M.dartFace T.d0 := by
      rw [← T.triangle.1, dartFace_phi]
    exact hface.symm

/-- Incident-with-`v0` is invariant along deleted-map `φ'` cycles.  This is the
public form needed for the route-(b) orbit classifier. -/
lemma incident_invariant_of_sameCycle {d0 : D} (htail0 : M.tail d0 = v0)
    {x y : {d : D // d ∉ M.deleteVertexSet d0}}
    (hxy : (M.deleteVertex d0).φ.SameCycle x y) :
    M.dartFace x.1 ∈ M.vertexFaces d0 ↔ M.dartFace y.1 ∈ M.vertexFaces d0 := by
  constructor
  · intro hx
    by_contra hy
    have hMsc : M.φ.SameCycle y.1 x.1 :=
      (cleanSameCycle_iff htail0 y hy x).1 hxy.symm
    have hface : M.dartFace y.1 = M.dartFace x.1 :=
      Quotient.sound hMsc
    exact hy (by rw [hface]; exact hx)
  · intro hy
    by_contra hx
    have hMsc : M.φ.SameCycle x.1 y.1 :=
      (cleanSameCycle_iff htail0 x hx y).1 hxy
    have hface : M.dartFace x.1 = M.dartFace y.1 :=
      Quotient.sound hMsc
    exact hx (by rw [hface]; exact hy)

/-- Any incident survivor lies on the `faceDartList` of an incident root once the
merged-orbit theorem is available. -/
lemma incident_survivor_mem_faceDartList_of_mergedOrbit
    (hNT : NearTriangulation M) {d0 : D}
    (r y : {d : D // d ∉ M.deleteVertexSet d0})
    (hr_incident : M.dartFace r.1 ∈ M.vertexFaces d0)
    (hy_incident : M.dartFace y.1 ∈ M.vertexFaces d0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    y ∈ (M.deleteVertex d0).faceDartList r := by
  rw [CombMap.faceDartList, Equiv.Perm.mem_toList_iff]
  exact ⟨hmerge r y hr_incident hy_incident,
    Equiv.Perm.mem_support.2
      (phi_ne_self_of_isSimpleGraph (M.deleteVertex d0)
        (ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.deleteVertex_isSimpleGraph
          hNT d0) r)⟩

/-- Conversely, every dart listed in the merged root's `faceDartList` is incident
with the deleted vertex. -/
lemma incident_of_mem_faceDartList_root {d0 : D} (htail0 : M.tail d0 = v0)
    (r y : {d : D // d ∉ M.deleteVertexSet d0})
    (hr_incident : M.dartFace r.1 ∈ M.vertexFaces d0)
    (hy : y ∈ (M.deleteVertex d0).faceDartList r) :
    M.dartFace y.1 ∈ M.vertexFaces d0 := by
  rw [CombMap.faceDartList, Equiv.Perm.mem_toList_iff] at hy
  exact (incident_invariant_of_sameCycle htail0 hy.1).1 hr_incident

/-- Route-(b) membership classifier for the merged root's explicit face dart
list: it is exactly the list of surviving darts whose old `M`-face is incident
with the deleted vertex. -/
theorem mem_faceDartList_root_iff_incident
    (hNT : NearTriangulation M) {d0 : D} (htail0 : M.tail d0 = v0)
    (r y : {d : D // d ∉ M.deleteVertexSet d0})
    (hr_incident : M.dartFace r.1 ∈ M.vertexFaces d0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    y ∈ (M.deleteVertex d0).faceDartList r ↔
      M.dartFace y.1 ∈ M.vertexFaces d0 :=
  ⟨fun hy => incident_of_mem_faceDartList_root htail0 r y hr_incident hy,
    fun hy => incident_survivor_mem_faceDartList_of_mergedOrbit hNT r y
      hr_incident hy hmerge⟩

lemma fanTriangle_edge_face {a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    M.dartFace T.d1 = M.dartFace T.d0 := by
  rw [← T.triangle.1, dartFace_phi]

lemma fanTriangle_edge_ne_outer_dart {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d : D}
    (hdouter : M.dartFace d = hNT.outerFace) :
    T.d1 ≠ d := by
  intro h
  exact T.inner (by
    rw [← hdouter, ← h]
    exact (fanTriangle_edge_face T).symm)

lemma old_outer_predecessor_face {bin oPre : D}
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hoPre_phi : M.φ oPre = bin) :
    M.dartFace oPre = hNT.outerFace := by
  rw [← hNT.outerCycle.dartFace_of_mem_darts hbin_mem, ← hoPre_phi, dartFace_phi]

/-- The head of the surviving fan-triangle edge dart. -/
lemma fanTriangle_head1 {a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    M.head T.d1 = b := by
  have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
  have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
  rw [hh, T.tail2]

/-- The last fan-triangle dart points back to the apex. -/
lemma fanTriangle_head2 {a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    M.head T.d2 = v0 := by
  have hphi : M.φ T.d2 = T.d0 := T.triangle.2.2
  have hh : M.head T.d2 = M.tail T.d0 := by rw [← tail_phi, hphi]
  rw [hh, T.tail0]

/-- The last dart of a fan triangle is deleted by closed-star deletion at the
fan apex. -/
lemma fanTriangle_d2_deleted {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d2 ∈ M.deleteVertexSet d0 := by
  rw [mem_deleteVertexSet_iff]; right
  rw [mem_vertexDarts]
  exact Quotient.exact (show M.tail d0 = M.tail (M.α T.d2) by
    rw [tail_alpha, fanTriangle_head2, htail0])

/-- A surviving dart on a fan-triangle face is the triangle's surviving edge dart. -/
lemma survivor_on_fanTriangle_eq_d1 {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hface : M.dartFace x.1 = T.face) :
    x.1 = T.d1 := by
  have hdf1 : M.dartFace T.d1 = T.face := by
    rw [FanTriangle.face, ← T.triangle.1, dartFace_phi]
  have hlen : M.faceLen (M.dartFace T.d1) = 3 := by
    rw [hdf1]; exact T.faceLen_eq_three
  have hsame : M.φ.SameCycle T.d1 x.1 :=
    Quotient.exact (show M.dartFace T.d1 = M.dartFace x.1 by rw [hdf1, hface])
  have hφ : M.φ T.d1 ≠ T.d1 := phi_ne_self_of_isSimpleGraph M hNT.simpleGraph T.d1
  have hsupp : T.d1 ∈ M.φ.support := by simpa [Equiv.Perm.mem_support] using hφ
  have hcard : (M.φ.cycleOf T.d1).support.card = 3 := by
    rw [← faceLen_dartFace_eq_card_support_cycleOf M hφ, hlen]
  obtain ⟨i, hi, hpow⟩ := hsame.exists_pow_eq_of_mem_support hsupp
  rw [hcard] at hi
  have h01 : M.φ T.d1 = T.d2 := T.triangle.2.1
  have h12 : M.φ T.d2 = T.d0 := T.triangle.2.2
  interval_cases i
  · simpa using hpow.symm
  · exfalso
    have : x.1 = T.d2 := by simpa [h01] using hpow.symm
    exact x.2 (this ▸ fanTriangle_d2_deleted T htail0)
  · exfalso
    have hx0 : x.1 = T.d0 := by
      have h2 : (M.φ ^ 2) T.d1 = T.d0 := by
        rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ', pow_one]
        simp only [Equiv.Perm.coe_mul, Function.comp_apply, h01, h12]
      rw [h2] at hpow
      exact hpow.symm
    have hd0del : T.d0 ∈ M.deleteVertexSet d0 := by
      rw [mem_deleteVertexSet_iff]; left
      rw [mem_vertexDarts]
      exact Quotient.exact (show M.tail d0 = M.tail T.d0 by rw [htail0, T.tail0])
    exact x.2 (hx0 ▸ hd0del)

/-- Convert membership in `vertexFaces d0` into ordinary face incidence at `v0`. -/
lemma faceIncidentAtVertex_of_incident {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hx : M.dartFace x.1 ∈ M.vertexFaces d0) :
    FaceIncidentAtVertex M (M.dartFace x.1) v0 := by
  rw [vertexFaces, Finset.mem_image] at hx
  obtain ⟨e, he, hef⟩ := hx
  rw [mem_vertexDarts] at he
  refine ⟨e, hef, ?_⟩
  have : M.tail d0 = M.tail e := Quotient.sound he
  exact this ▸ htail0

/-- Every non-outer incident survivor is one of the canonical fan-triangle edge
darts. -/
lemma incident_nonouter_survivor_eq_fan_edge
    (fan : BoundaryVertexFan hNT v0) {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hxinc : M.dartFace x.1 ∈ M.vertexFaces d0)
    (hxnonouter : M.dartFace x.1 ≠ hNT.outerFace) :
    ∃ a b : M.Vertex, ∃ hp : (a, b) ∈ consecutivePairs fan.path,
      x.1 = (fan.incident_faces_exact.triangle_of_pair hp).d1 := by
  have hinc : FaceIncidentAtVertex M (M.dartFace x.1) v0 :=
    faceIncidentAtVertex_of_incident htail0 x hxinc
  obtain ⟨a, b, hp, hface⟩ :=
    (fan.incident_faces_exact.exact_faces (M.dartFace x.1) hxnonouter).1 hinc
  refine ⟨a, b, hp, ?_⟩
  exact survivor_on_fanTriangle_eq_d1
    (fan.incident_faces_exact.triangle_of_pair hp) htail0 x hface.symm

/-- In a nodup path, a vertex has at most one predecessor in the consecutive-pair
list. -/
lemma consecutivePairs_left_eq_of_same_right {α : Type u} {xs : List α}
    (hnodup : xs.Nodup) {a c b : α}
    (hab : (a, b) ∈ consecutivePairs xs)
    (hcb : (c, b) ∈ consecutivePairs xs) :
    a = c := by
  obtain ⟨i, hi, hai, hbi⟩ :=
    (ProofsInTheBook.ZinanCh35FanBackward.mem_consecutivePairs_iff xs a b).1 hab
  obtain ⟨j, hj, hcj, hbj⟩ :=
    (ProofsInTheBook.ZinanCh35FanBackward.mem_consecutivePairs_iff xs c b).1 hcb
  have hidx : i + 1 = j + 1 := by
    exact (List.getElem_inj hnodup).1 (by rw [hbi, hbj])
  have hij : i = j := by omega
  have hget : xs[i] = xs[j] := by
    subst hij
    rfl
  exact hai.symm.trans (hget.trans hcj)

/-- Equality of deleted-map vertices lifts to equality of old-map tails for
surviving darts. -/
lemma M_tail_eq_of_deleted_tail_eq {d0 : D}
    (x y : {d : D // d ∉ M.deleteVertexSet d0})
    (hxy : (M.deleteVertex d0).tail x = (M.deleteVertex d0).tail y) :
    M.tail x.1 = M.tail y.1 := by
  have hsc' : (M.deleteVertex d0).σ.SameCycle x y := Quotient.exact hxy
  have hsc : M.σ.SameCycle x.1 y.1 :=
    (deleteVertex_sigma_sameCycle_iff M d0 x y).1 hsc'
  exact Quotient.sound hsc

/-- Tail injectivity on the fan-triangle part of the merged deleted boundary. -/
lemma incident_nonouter_survivor_eq_of_deleted_tail_eq
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (x y : {d : D // d ∉ M.deleteVertexSet d0})
    (hxinc : M.dartFace x.1 ∈ M.vertexFaces d0)
    (hyinc : M.dartFace y.1 ∈ M.vertexFaces d0)
    (hxnonouter : M.dartFace x.1 ≠ hNT.outerFace)
    (hynonouter : M.dartFace y.1 ≠ hNT.outerFace)
    (hxy : (M.deleteVertex d0).tail x = (M.deleteVertex d0).tail y) :
    x = y := by
  obtain ⟨a, b, hp, hxval⟩ :=
    incident_nonouter_survivor_eq_fan_edge fan htail0 x hxinc hxnonouter
  obtain ⟨c, d, hq, hyval⟩ :=
    incident_nonouter_survivor_eq_fan_edge fan htail0 y hyinc hynonouter
  have hMtail : M.tail x.1 = M.tail y.1 :=
    M_tail_eq_of_deleted_tail_eq x y hxy
  have hbd : b = d := by
    have hxb : M.tail x.1 = b := by
      rw [hxval]
      exact (fan.incident_faces_exact.triangle_of_pair hp).tail1
    have hyd : M.tail y.1 = d := by
      rw [hyval]
      exact (fan.incident_faces_exact.triangle_of_pair hq).tail1
    rw [hxb, hyd] at hMtail
    exact hMtail
  subst hbd
  have hac : a = c :=
    consecutivePairs_left_eq_of_same_right
      (fan_path_simple_of_chordless hNT fan hchordless) hp hq
  subst hac
  have hhp : hp = hq := Subsingleton.elim _ _
  subst hhp
  exact Subtype.ext (hxval.trans hyval.symm)

/-- Tail injectivity on the surviving old-outer-arc part. -/
lemma old_outer_survivor_eq_of_deleted_tail_eq {d0 : D}
    (x y : {d : D // d ∉ M.deleteVertexSet d0})
    (hxouter : M.dartFace x.1 = hNT.outerFace)
    (hyouter : M.dartFace y.1 = hNT.outerFace)
    (hxy : (M.deleteVertex d0).tail x = (M.deleteVertex d0).tail y) :
    x = y := by
  have hxmem : x.1 ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff x.1).2 hxouter
  have hymem : y.1 ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff y.1).2 hyouter
  have hMtail : M.tail x.1 = M.tail y.1 :=
    M_tail_eq_of_deleted_tail_eq x y hxy
  exact Subtype.ext
    (hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hxmem hymem hMtail)

/-- In the chordless fan path, the second endpoint of a consecutive pair cannot
be the head endpoint `fan.x`; if it is an old boundary vertex, it is `fan.w`. -/
lemma consecutivePair_second_eq_w_of_boundary
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hb_boundary : hNT.outerCycle.IsBoundaryVertex b) :
    b = fan.w := by
  have hb_path : b ∈ fan.path := by
    obtain ⟨i, hi, _ha, hb⟩ :=
      (ProofsInTheBook.ZinanCh35FanBackward.mem_consecutivePairs_iff
        fan.path a b).1 hp
    exact List.mem_iff_getElem.2 ⟨i + 1, hi, hb⟩
  rcases fan_path_meets_old_boundary_only_at_ends hNT fan hchordless b hb_path
      hb_boundary with hbx | hbw
  · exfalso
    obtain ⟨i, hi, _ha, hb⟩ :=
      (ProofsInTheBook.ZinanCh35FanBackward.mem_consecutivePairs_iff
        fan.path a b).1 hp
    have hpath0 : fan.path[0] = fan.x := by
      simp [BoundaryVertexFan.path, fanPath]
    have hidx : i + 1 = 0 := by
      exact (List.getElem_inj (fan_path_simple_of_chordless hNT fan hchordless)).1
        (by rw [hb, hbx, hpath0])
    omega
  · exact hbw

/-- The tail of any old-outer dart is an old boundary vertex. -/
lemma isBoundaryVertex_tail_of_outer_dart {d : D}
    (hdouter : M.dartFace d = hNT.outerFace) :
    hNT.outerCycle.IsBoundaryVertex (M.tail d) := by
  have hdmem : d ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff d).2 hdouter
  have hmem : M.tail d ∈ hNT.outerCycle.darts.map M.tail :=
    List.mem_map.2 ⟨d, hdmem, rfl⟩
  simpa [BoundaryCycle.IsBoundaryVertex, hNT.outerCycle.vertices_eq] using hmem

/-- A non-outer fan-edge survivor and an old-outer survivor cannot represent the
same deleted boundary vertex. -/
lemma incident_nonouter_not_old_outer_same_deleted_tail
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    {d0 bin : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hpₛ : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (x y : {d : D // d ∉ M.deleteVertexSet d0})
    (hxinc : M.dartFace x.1 ∈ M.vertexFaces d0)
    (hxnonouter : M.dartFace x.1 ≠ hNT.outerFace)
    (hyouter : M.dartFace y.1 = hNT.outerFace)
    (hxy : (M.deleteVertex d0).tail x = (M.deleteVertex d0).tail y) :
    False := by
  obtain ⟨a, b, hp, hxval⟩ :=
    incident_nonouter_survivor_eq_fan_edge fan htail0 x hxinc hxnonouter
  have hMtail : M.tail x.1 = M.tail y.1 :=
    M_tail_eq_of_deleted_tail_eq x y hxy
  have hxb : M.tail x.1 = b := by
    rw [hxval]
    exact (fan.incident_faces_exact.triangle_of_pair hp).tail1
  have hyb : M.tail y.1 = b := hMtail.symm.trans hxb
  have hb_boundary : hNT.outerCycle.IsBoundaryVertex b := by
    rw [← hyb]
    exact isBoundaryVertex_tail_of_outer_dart hyouter
  have hb_w : b = fan.w :=
    consecutivePair_second_eq_w_of_boundary fan hchordless hp hb_boundary
  have hbin_boundary : hNT.outerCycle.IsBoundaryVertex bₛ := by
    rw [← hbin_tail]
    exact isBoundaryVertex_tail_of_outer_dart
      (hNT.outerCycle.dartFace_of_mem_darts hbin_mem)
  have hbs_w : bₛ = fan.w :=
    consecutivePair_second_eq_w_of_boundary fan hchordless hpₛ hbin_boundary
  have hy_tail_bin : M.tail y.1 = M.tail bin := by
    rw [hyb, hb_w, hbin_tail, hbs_w]
  have hymem : y.1 ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff y.1).2 hyouter
  have hy_eq_bin : y.1 = bin :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hymem hbin_mem hy_tail_bin
  have hbin_deleted : bin ∈ M.deleteVertexSet d0 :=
    mem_deleteVertexSet_of_head (M := M) (v0 := v0) htail0 hbin_head
  exact y.2 (hy_eq_bin ▸ hbin_deleted)

/-- Route-(b) boundary simplicity for the merged deleted face rooted at the
actual fan-pair seam edge. -/
theorem deleted_outer_simple_of_fan_pair_seam
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {aₛ bₛ : M.Vertex} (hpₛ : (aₛ, bₛ) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = bₛ)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin) :
    ((((M.deleteVertex d0).faceDartList
        (⟨(fan.incident_faces_exact.triangle_of_pair hpₛ).d1,
          ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
            (fan.incident_faces_exact.triangle_of_pair hpₛ) htail0⟩ :
          {d : D // d ∉ M.deleteVertexSet d0})).map
        (M.deleteVertex d0).tail).Nodup) := by
  classical
  let root : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨(fan.incident_faces_exact.triangle_of_pair hpₛ).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hpₛ) htail0⟩
  let hmerge : DeleteVertexMergedFaceSingleOrbit M d0 :=
    ProofsInTheBook.ZinanCh35MergedArc.deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
      fan hchordless htail0
      hbin_mem hbin_head hpₛ hbin_tail hbout hoPre_surv hoPre_phi
  have hroot_inc : M.dartFace root.1 ∈ M.vertexFaces d0 :=
    fanPairSeamEdge_incident fan htail0 hpₛ
  change (((M.deleteVertex d0).faceDartList root).map
      (M.deleteVertex d0).tail).Nodup
  have hL : ((M.deleteVertex d0).faceDartList root).Nodup := by
    rw [ProofsInTheBook.PlanarMap.CombMap.faceDartList]
    exact Equiv.Perm.nodup_toList _ _
  rw [List.nodup_map_iff_inj_on hL]
  intro x hx y hy htail
  have hxinc : M.dartFace x.1 ∈ M.vertexFaces d0 :=
    (mem_faceDartList_root_iff_incident hNT htail0 root x hroot_inc hmerge).1 hx
  have hyinc : M.dartFace y.1 ∈ M.vertexFaces d0 :=
    (mem_faceDartList_root_iff_incident hNT htail0 root y hroot_inc hmerge).1 hy
  by_cases hxouter : M.dartFace x.1 = hNT.outerFace
  · by_cases hyouter : M.dartFace y.1 = hNT.outerFace
    · exact old_outer_survivor_eq_of_deleted_tail_eq x y hxouter hyouter htail
    · exfalso
      exact incident_nonouter_not_old_outer_same_deleted_tail fan hchordless htail0
        hbin_mem hbin_head hpₛ hbin_tail y x hyinc hyouter hxouter htail.symm
  · by_cases hyouter : M.dartFace y.1 = hNT.outerFace
    · exfalso
      exact incident_nonouter_not_old_outer_same_deleted_tail fan hchordless htail0
        hbin_mem hbin_head hpₛ hbin_tail x y hxinc hxouter hyouter htail
    · exact incident_nonouter_survivor_eq_of_deleted_tail_eq fan hchordless htail0
        x y hxinc hyinc hxouter hyouter htail

/-- Route-(b) `outer_len` for any chosen incident root of the merged deleted
outer face.  It avoids a literal `faceDartList` itinerary: the merged-orbit
classifier puts two fan-edge darts and one surviving old-outer dart in the root
orbit, and they are pairwise distinct. -/
theorem deleted_root_faceDartList_len_ge_three
    (fan : BoundaryVertexFan hNT v0)
    (hchordless : BoundaryChordless hNT.outerCycle)
    (hbig : 3 < M.V)
    {d0 bin bout oPre : D} (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet d0)
    (hoPre_phi : M.φ oPre = bin)
    (r : {d : D // d ∉ M.deleteVertexSet d0})
    (hr_incident : M.dartFace r.1 ∈ M.vertexFaces d0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    3 ≤ ((M.deleteVertex d0).faceDartList r).length := by
  classical
  have hfan_nonempty : 1 ≤ fan.t :=
    fan_nonempty_of_chordless_of_not_triangle (hNT := hNT) fan hchordless hbig
  obtain ⟨b0, bs, hInterior⟩ : ∃ b bs, fan.interior = b :: bs := by
    have hne : fan.interior ≠ [] := by
      intro hnil
      have ht0 : fan.t = 0 := by simp [BoundaryVertexFan.t, hnil]
      omega
    cases h : fan.interior with
    | nil => exact False.elim (hne h)
    | cons b bs => exact ⟨b, bs, rfl⟩
  have hpath_head : fan.path = fan.x :: b0 :: (bs ++ [fan.w]) := by
    rw [BoundaryVertexFan.path, fanPath, hInterior]
    rfl
  have hp0 : (fan.x, b0) ∈ consecutivePairs fan.path := by
    rw [hpath_head, consecutivePairs]
    simp
  obtain ⟨aT, hpT⟩ := exists_terminal_fan_pair fan
  set T0 := fan.incident_faces_exact.triangle_of_pair hp0
  set TT := fan.incident_faces_exact.triangle_of_pair hpT
  let y0 : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨T0.d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        T0 htail0⟩
  let yT : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨TT.d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        TT htail0⟩
  let yO : {d : D // d ∉ M.deleteVertexSet d0} := ⟨oPre, hoPre_surv⟩
  have hinc0 : M.dartFace y0.1 ∈ M.vertexFaces d0 := by
    exact fanPairSeamEdge_incident fan htail0 hp0
  have hincT : M.dartFace yT.1 ∈ M.vertexFaces d0 := by
    exact fanPairSeamEdge_incident fan htail0 hpT
  have hoPre_face : M.dartFace oPre = hNT.outerFace :=
    old_outer_predecessor_face (hNT := hNT) hbin_mem hoPre_phi
  have hincO : M.dartFace yO.1 ∈ M.vertexFaces d0 := by
    dsimp [yO]
    rw [hoPre_face]
    exact oldOuterFace_incident_of_seam htail0 hbin_mem hbin_head hbout
  have hmem0 : y0 ∈ (M.deleteVertex d0).faceDartList r :=
    (mem_faceDartList_root_iff_incident hNT htail0 r y0 hr_incident hmerge).2 hinc0
  have hmemT : yT ∈ (M.deleteVertex d0).faceDartList r :=
    (mem_faceDartList_root_iff_incident hNT htail0 r yT hr_incident hmerge).2 hincT
  have hmemO : yO ∈ (M.deleteVertex d0).faceDartList r :=
    (mem_faceDartList_root_iff_incident hNT htail0 r yO hr_incident hmerge).2 hincO
  have hb0_ne_w : b0 ≠ fan.w := by
    have hnodup : fan.path.Nodup :=
      fan_path_simple_of_chordless hNT fan hchordless
    rw [hpath_head] at hnodup
    intro hbw
    subst hbw
    have htail_nodup : (fan.w :: bs ++ [fan.w]).Nodup :=
      (List.nodup_cons.mp hnodup).2
    have hw_not_tail : fan.w ∉ bs ++ [fan.w] :=
      (List.nodup_cons.mp htail_nodup).1
    exact hw_not_tail (by simp)
  have hy0_ne_yT : y0 ≠ yT := by
    intro h
    have htail : M.tail T0.d1 = M.tail TT.d1 := by
      exact congrArg (fun z : {d : D // d ∉ M.deleteVertexSet d0} => M.tail z.1) h
    have hT0_tail : M.tail T0.d1 = b0 := by
      dsimp [T0]
      exact (fan.incident_faces_exact.triangle_of_pair hp0).tail1
    have hTT_tail : M.tail TT.d1 = fan.w := by
      dsimp [TT]
      exact (fan.incident_faces_exact.triangle_of_pair hpT).tail1
    exact hb0_ne_w (by rw [← hT0_tail, htail, hTT_tail])
  have hy0_ne_yO : y0 ≠ yO := by
    intro h
    exact (fanTriangle_edge_ne_outer_dart T0 hoPre_face)
      (Subtype.ext_iff.mp h)
  have hyT_ne_yO : yT ≠ yO := by
    intro h
    exact (fanTriangle_edge_ne_outer_dart TT hoPre_face)
      (Subtype.ext_iff.mp h)
  exact three_le_length_of_three_mem hmem0 hmemT hmemO hy0_ne_yT hy0_ne_yO hyT_ne_yO

/-- Clean-face classification from an independently proved merged orbit.  The
root `r` must be on an old face incident with the deleted vertex, and the selected
`outerFace` must be its deleted-map face. -/
theorem cleanFaceClass_of_mergedOrbit_root {d0 : D}
    (r : {d : D // d ∉ M.deleteVertexSet d0})
    (outerFace : (M.deleteVertex d0).Face)
    (hroot : (M.deleteVertex d0).dartFace r = outerFace)
    (hr_incident : M.dartFace r.1 ∈ M.vertexFaces d0)
    (houter_incident : hNT.outerFace ∈ M.vertexFaces d0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    CleanFaceClass (hNT := hNT) outerFace := by
  intro f hf
  obtain ⟨x, rfl⟩ := f.exists_rep
  by_cases hxinc : M.dartFace x.1 ∈ M.vertexFaces d0
  · have hsc : (M.deleteVertex d0).φ.SameCycle r x :=
      hmerge r x hr_incident hxinc
    have hface_eq :
        (M.deleteVertex d0).dartFace r = (M.deleteVertex d0).dartFace x :=
      Quotient.sound hsc
    have hxouter : (M.deleteVertex d0).dartFace x = outerFace := by
      rw [← hface_eq, hroot]
    exact False.elim (hf hxouter)
  · refine ⟨x, rfl, hxinc, ?_⟩
    intro hMouter
    exact hxinc (hMouter ▸ houter_incident)

/-- The clean-face classifier specialized to a canonical fan-pair seam root. -/
theorem cleanFaceClass_of_fan_pair_mergedOrbit
    (fan : BoundaryVertexFan hNT v0) {d0 bin bout : D}
    (htail0 : M.tail d0 = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    CleanFaceClass (hNT := hNT)
      ((M.deleteVertex d0).dartFace
        (⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
          ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
            (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩ :
          {d : D // d ∉ M.deleteVertexSet d0})) :=
  cleanFaceClass_of_mergedOrbit_root
    (r := ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩)
    _ rfl
    (fanPairSeamEdge_incident fan htail0 hp)
    (oldOuterFace_incident_of_seam htail0 hbin_mem hbin_head hbout)
    hmerge

/-- Assemble the current Phase-C seam bundle from the proved seam/orbit pieces,
leaving only the route-(b) boundary simplicity (`outer_simple`) as an explicit
input.  The length and clean-face fields are discharged in this file. -/
noncomputable def deletedSeamData_of_fan_pair_seam_of_outer_simple
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
    (houter_simple :
      ((((M.deleteVertex d0).faceDartList
          (⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
            ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
              (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩ :
            {d : D // d ∉ M.deleteVertexSet d0})).map
          (M.deleteVertex d0).tail).Nodup)) :
    ProofsInTheBook.ZinanCh35DeletedBoundary.DeletedSeamData fan hchordless htail0 := by
  classical
  let root : {d : D // d ∉ M.deleteVertexSet d0} :=
    ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htail0⟩
  let outerFace : (M.deleteVertex d0).Face := (M.deleteVertex d0).dartFace root
  let hmerge : DeleteVertexMergedFaceSingleOrbit M d0 :=
    ProofsInTheBook.ZinanCh35MergedArc.deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
      fan hchordless htail0
      hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
  refine
    { seamEdge := root
      seamEdge_fan :=
        ProofsInTheBook.ZinanCh35MergedArc.fanPairSeamEdge_is_fan_edge fan htail0 hp
      mergedArc :=
        ProofsInTheBook.ZinanCh35MergedArc.mergedOuterArcData_of_fan_pair_seam
          fan htail0 hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
      outerFace := outerFace
      outerCycle :=
        (M.deleteVertex d0).boundaryCycleOfFace outerFace
          (hNT.deleteVertex_phi_ne_self d0 root) rfl ?_
      outer_simple := ?_
      outer_len_ge_three := ?_
      cleanFaceClass := ?_ }
  · exact houter_simple
  · change ((((M.deleteVertex d0).faceDartList root).map
        (M.deleteVertex d0).tail).Nodup)
    exact houter_simple
  · change 3 ≤ ((M.deleteVertex d0).faceDartList root).length
    exact deleted_root_faceDartList_len_ge_three fan hchordless hbig htail0
      hbin_mem hbin_head hbout hoPre_surv hoPre_phi root
      (fanPairSeamEdge_incident fan htail0 hp) hmerge
  · exact cleanFaceClass_of_fan_pair_mergedOrbit fan htail0 hbin_mem hbin_head
      hbout hp hmerge

/-- PHASE C seam-data closure: the actual fan-pair seam data now supplies the
merged orbit, the route-(b) boundary simplicity, the length bound, and the
clean-face classifier. -/
noncomputable def deletedSeamData_of_fan_pair_seam
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
    (hoPre_phi : M.φ oPre = bin) :
    ProofsInTheBook.ZinanCh35DeletedBoundary.DeletedSeamData fan hchordless htail0 :=
  deletedSeamData_of_fan_pair_seam_of_outer_simple fan hchordless hbig htail0
    hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi
    (deleted_outer_simple_of_fan_pair_seam fan hchordless htail0
      hbin_mem hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi)

/-- The corresponding full fan-surgery reconstruction obtained from the closed
seam data.  This is the `ChordlessOracle.recon` field before the list-bookkeeping
stage. -/
noncomputable def chordlessRecon_of_fan_pair_seam
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
    (hoPre_phi : M.φ oPre = bin) :
    FanSurgeryReconstruction hNT d0 :=
  (deletedSeamData_of_fan_pair_seam fan hchordless hbig htail0 hbin_mem
    hbin_head hp hbin_tail hbout hoPre_surv hoPre_phi).chordlessRecon

end ProofsInTheBook.ZinanCh35DeletedAssembly

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35DeletedAssembly.deleted_outer_vertices_nodup_M
#print axioms ProofsInTheBook.ZinanCh35DeletedAssembly.exists_head_fan_pair
#print axioms ProofsInTheBook.ZinanCh35DeletedAssembly.exists_terminal_fan_pair
#print axioms ProofsInTheBook.ZinanCh35DeletedAssembly.mem_faceDartList_root_iff_incident
#print axioms ProofsInTheBook.ZinanCh35DeletedAssembly.deleted_root_faceDartList_len_ge_three
#print axioms ProofsInTheBook.ZinanCh35DeletedAssembly.cleanFaceClass_of_mergedOrbit_root
#print axioms ProofsInTheBook.ZinanCh35DeletedAssembly.cleanFaceClass_of_fan_pair_mergedOrbit
#print axioms ProofsInTheBook.ZinanCh35DeletedAssembly.deleted_outer_simple_of_fan_pair_seam
#print axioms ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam_of_outer_simple
#print axioms ProofsInTheBook.ZinanCh35DeletedAssembly.deletedSeamData_of_fan_pair_seam
#print axioms ProofsInTheBook.ZinanCh35DeletedAssembly.chordlessRecon_of_fan_pair_seam
