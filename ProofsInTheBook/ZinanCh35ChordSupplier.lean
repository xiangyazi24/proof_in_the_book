import ProofsInTheBook.ZinanCh35Side2Confine
import ProofsInTheBook.ZinanCh35Aligned
import ProofsInTheBook.ZinanCh35Regions

/-!
# Chapter 35 chord-branch supplier plumbing

This file contains the Phase-B recursion-supplier facts that are not part of the
planar/discrete-Schoenflies closure itself.  We keep them separate from the large
outer-trace file so the remaining recursion fuel can be audited locally.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordSupplier

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation
open ProofsInTheBook.ZinanCh35Regions
open ProofsInTheBook.ZinanCh35Side2Confine
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v p q : M.Vertex}

/-- If a boundary dart on `outerArc₁` carries the precoloured edge `pq`, then both endpoints of
`pq` lie in the side-1 region.  The only extra hypothesis is that `pq` is not the chord edge; the
orientation-choice layer supplies that from the chord/precoloured-edge separation. -/
theorem precolored_endpoints_mem_sideRegion₁_of_outerArc₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) {b : D}
    (hb : b ∈ data.outerArc₁) (hedge : M.dartEdge b = s(p, q))
    (hpq_ne_chord : s(p, q) ≠ s(u, v)) :
    p ∈ sideRegion₁ data ∧ q ∈ sideRegion₁ data := by
  have hbchord : M.dartEdge b ≠ s(u, v) := by
    intro h
    exact hpq_ne_chord (hedge.symm.trans h)
  have hαchord : M.dartEdge (M.α b) ≠ s(u, v) := by
    rwa [M.dartEdge_alpha]
  have hface : M.dartFace (M.α b) ∈ data.side₁ := hb.2
  obtain ⟨hαtail, hαhead⟩ :=
    endpoints_mem_sideRegion₁_of_face data hsep hαchord hface
  have htail : M.tail b ∈ sideRegion₁ data := by
    simpa [M.head_alpha] using hαhead
  have hhead : M.head b ∈ sideRegion₁ data := by
    simpa [M.tail_alpha] using hαtail
  have hedge' : (s(M.tail b, M.head b) : Sym2 M.Vertex) = s(p, q) := hedge
  rcases Sym2.eq_iff.mp hedge' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ htail, h2 ▸ hhead⟩
  · exact ⟨h2 ▸ hhead, h1 ▸ htail⟩

@[simp] theorem normalizedChordSplitData_dart_tail (h : hNT.outerCycle.Chord u v) :
    M.tail (normalizedChordSplitData h).dart = u := by
  simpa [normalizedChordSplitData, ChordSplitData.dart] using hNT.chordDart_tail h

@[simp] theorem normalizedChordSplitData_dart_head (h : hNT.outerCycle.Chord u v) :
    M.head (normalizedChordSplitData h).dart = v := by
  simpa [normalizedChordSplitData, ChordSplitData.dart] using hNT.chordDart_head h

theorem normalizedChordSplitData_chord_symm_dart
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).dart =
      M.α (normalizedChordSplitData h).dart := by
  let d := (normalizedChordSplitData h).dart
  let d' := (normalizedChordSplitData (chord_symm h)).dart
  have ht : M.tail d = u := normalizedChordSplitData_dart_tail h
  have hh : M.head d = v := normalizedChordSplitData_dart_head h
  have ht' : M.tail d' = v := normalizedChordSplitData_dart_tail (chord_symm h)
  have hh' : M.head d' = u := normalizedChordSplitData_dart_head (chord_symm h)
  have hsame : M.α.SameCycle d' d :=
    M.alpha_sameCycle_of_same_endpoints_symm hNT.simpleGraph (ht'.trans hh.symm) (hh'.trans ht.symm)
  rcases (M.alpha_sameCycle_iff d' d).mp hsame with hsame_d | hα
  · exfalso
    exact h.endpoints_ne (ht.symm.trans (hsame_d.symm ▸ ht'))
  · change d' = M.α d
    calc
      d' = M.α (M.α d') := by rw [M.alpha_alpha]
      _ = M.α d := by rw [← hα]

theorem chordSplitAdj_swap_iff {f g : M.Face} :
    hNT.ChordSplitAdj v u f g ↔ hNT.ChordSplitAdj u v f g := by
  constructor
  · rintro ⟨d, hdf, hdg, hb, hch⟩
    refine ⟨d, hdf, hdg, hb, ?_⟩
    rwa [Sym2.eq_swap]
  · rintro ⟨d, hdf, hdg, hb, hch⟩
    refine ⟨d, hdf, hdg, hb, ?_⟩
    rwa [Sym2.eq_swap]

theorem normalizedChordSplitData_chord_symm_face₁
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).face₁ =
      (normalizedChordSplitData h).face₂ := by
  unfold ChordSplitData.face₁ ChordSplitData.face₂
  rw [normalizedChordSplitData_chord_symm_dart]

theorem normalizedChordSplitData_chord_symm_face₂
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).face₂ =
      (normalizedChordSplitData h).face₁ := by
  unfold ChordSplitData.face₂ ChordSplitData.face₁
  rw [normalizedChordSplitData_chord_symm_dart, M.alpha_alpha]

theorem normalizedChordSplitData_chord_symm_side₁
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).side₁ =
      (normalizedChordSplitData h).side₂ := by
  ext f
  constructor
  · intro hf
    change Relation.ReflTransGen (hNT.ChordSplitAdj v u)
      (normalizedChordSplitData (chord_symm h)).face₁ f at hf
    rw [normalizedChordSplitData_chord_symm_face₁ h] at hf
    exact hf.mono (fun _ _ hstep => (chordSplitAdj_swap_iff (hNT := hNT)).1 hstep)
  · intro hf
    change Relation.ReflTransGen (hNT.ChordSplitAdj u v)
      (normalizedChordSplitData h).face₂ f at hf
    rw [← normalizedChordSplitData_chord_symm_face₁ h] at hf
    exact hf.mono (fun _ _ hstep => (chordSplitAdj_swap_iff (hNT := hNT)).2 hstep)

theorem normalizedChordSplitData_chord_symm_sideDarts₁
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).sideDarts₁ =
      (normalizedChordSplitData h).sideDarts₂ := by
  ext d
  change M.dartFace d ∈ (normalizedChordSplitData (chord_symm h)).side₁ ↔
    M.dartFace d ∈ (normalizedChordSplitData h).side₂
  rw [normalizedChordSplitData_chord_symm_side₁ h]

theorem normalizedChordSplitData_chord_symm_outerArc₁
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).outerArc₁ =
      (normalizedChordSplitData h).outerArc₂ := by
  ext d
  change (M.dartFace d = hNT.outerFace ∧
      M.dartFace (M.α d) ∈ (normalizedChordSplitData (chord_symm h)).side₁) ↔
    (M.dartFace d = hNT.outerFace ∧
      M.dartFace (M.α d) ∈ (normalizedChordSplitData h).side₂)
  rw [normalizedChordSplitData_chord_symm_side₁ h]

theorem normalizedChordSplitData_chord_symm_keptSet₁
    (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData (chord_symm h)).keptSet₁ =
      (normalizedChordSplitData h).keptSet₂ := by
  ext d
  change d ∈ ((normalizedChordSplitData (chord_symm h)).sideDarts₁ ∪
      (normalizedChordSplitData (chord_symm h)).outerArc₁) \
        {(normalizedChordSplitData (chord_symm h)).dart} ↔
    d ∈ ((normalizedChordSplitData h).sideDarts₂ ∪
      (normalizedChordSplitData h).outerArc₂) \ {M.α (normalizedChordSplitData h).dart}
  rw [normalizedChordSplitData_chord_symm_sideDarts₁ h,
    normalizedChordSplitData_chord_symm_outerArc₁ h,
    normalizedChordSplitData_chord_symm_dart h]

theorem normalizedChordSplitData_chord_symm_sideRegion₁
    (h : hNT.outerCycle.Chord u v) :
    sideRegion₁ (normalizedChordSplitData (chord_symm h)) =
      ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ (normalizedChordSplitData h) := by
  ext w
  constructor
  · rintro ⟨d, hd, htail⟩
    have hkept₁ :
        d ∈ (normalizedChordSplitData (chord_symm h)).keptSet₁ :=
      ((normalizedChordSplitData (chord_symm h)).mem_keptDel₁_iff d).1 hd
    have hkept₂ : d ∈ (normalizedChordSplitData h).keptSet₂ := by
      rwa [normalizedChordSplitData_chord_symm_keptSet₁ h] at hkept₁
    exact ⟨d, ((normalizedChordSplitData h).mem_keptDel₂_iff d).2 hkept₂, htail⟩
  · rintro ⟨d, hd, htail⟩
    have hkept₂ : d ∈ (normalizedChordSplitData h).keptSet₂ :=
      ((normalizedChordSplitData h).mem_keptDel₂_iff d).1 hd
    have hkept₁ : d ∈ (normalizedChordSplitData (chord_symm h)).keptSet₁ := by
      rwa [normalizedChordSplitData_chord_symm_keptSet₁ h]
    exact ⟨d, ((normalizedChordSplitData (chord_symm h)).mem_keptDel₁_iff d).2 hkept₁, htail⟩

/-- The parent precoloured boundary edge is confined to one of the two chord sides. -/
theorem precolored_edge_confined_to_one_side
    {α : Type u} [DecidableEq α] (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {L : M.Vertex → Finset α} {cp cq : α}
    (hTL : ThomassenLists hNT p q L cp cq) :
    (p ∈ sideRegion₁ data ∧ q ∈ sideRegion₁ data) ∨
      (p ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data ∧
        q ∈ ProofsInTheBook.ZinanCh35EdgeCore.sideRegion₂ data) := by
  classical
  have hadj : M.toSimpleGraph.Adj p q := by
    have hpq_boundary := hTL.pq_boundary_edge
    change s(p, q) ∈ hNT.outerCycle.edges at hpq_boundary
    rw [hNT.outerCycle.edges_eq, List.mem_map] at hpq_boundary
    obtain ⟨d, _hd, hedge⟩ := hpq_boundary
    exact ⟨hTL.p_ne_q, d, hedge⟩
  exact edge_confined_holds data hsep hadj

theorem precolored_edge_side₁_or_swapped_side₁
    {α : Type u} [DecidableEq α] (h : hNT.outerCycle.Chord u v)
    {L : M.Vertex → Finset α} {cp cq : α}
    (hTL : ThomassenLists hNT p q L cp cq) :
    (p ∈ sideRegion₁ (normalizedChordSplitData h) ∧
        q ∈ sideRegion₁ (normalizedChordSplitData h)) ∨
      (p ∈ sideRegion₁ (normalizedChordSplitData (chord_symm h)) ∧
        q ∈ sideRegion₁ (normalizedChordSplitData (chord_symm h))) := by
  have hconf :=
    precolored_edge_confined_to_one_side (normalizedChordSplitData h)
      (ProofsInTheBook.ZinanCh35ChordResidue.normSep h) hTL
  rcases hconf with h₁ | h₂
  · exact Or.inl h₁
  · right
    rwa [normalizedChordSplitData_chord_symm_sideRegion₁ h]

/-- Choose the chord orientation whose side-1 region contains the precoloured edge. -/
noncomputable def orientChordForPreedge
    {α : Type u} [DecidableEq α] (h : hNT.outerCycle.Chord u v)
    {L : M.Vertex → Finset α} {cp cq : α}
    (hTL : ThomassenLists hNT p q L cp cq) :
    Σ' (u' v' : M.Vertex) (h' : hNT.outerCycle.Chord u' v'),
      p ∈ sideRegion₁ (normalizedChordSplitData h') ∧
        q ∈ sideRegion₁ (normalizedChordSplitData h') := by
  classical
  exact Classical.choice (show Nonempty
    (Σ' (u' v' : M.Vertex) (h' : hNT.outerCycle.Chord u' v'),
      p ∈ sideRegion₁ (normalizedChordSplitData h') ∧
        q ∈ sideRegion₁ (normalizedChordSplitData h')) from by
      rcases precolored_edge_side₁_or_swapped_side₁ h hTL with h₁ | h₂
      · exact ⟨⟨u, v, h, h₁⟩⟩
      · exact ⟨⟨v, u, chord_symm h, h₂⟩⟩)

end ProofsInTheBook.ZinanCh35ChordSupplier
