import ProofsInTheBook.ZinanCh35ChordResidue
import ProofsInTheBook.ZinanCh35Side2Confine
import ProofsInTheBook.ZinanCh35Schoenflies2
import ProofsInTheBook.ZinanCh35ArcSide

/-!
# Chapter 35: discharging `ChordSplitRegionsResidue` (the discrete-Schoenflies residue).

`ZinanCh35ChordResidue.lean` isolated the chord-branch's structural residue as
`ChordSplitRegionsResidue data p q`, carrying the vertex-level region-glue data of
`ThomassenLists.ChordSplitRegions`.  At the time that file was written the repository documented
*no producer* for these fields.  This file proves that the **structural** fields all follow
unconditionally (modulo the separately-dischargeable `data.Separates`) from the now-proven planar
bridges:

* `cover` — every `M`-vertex lies in `sideRegion₁ ∪ sideRegion₂`
  (`cover_holds`): via `boundedFacePartition_uncond` + `alpha_dartFace_ne_outer_of_outer`.
* `edge_confined` — a graph edge between two vertices stays inside one side region
  (`edge_confined_holds`): via `boundedFacePartition_uncond` +
  `endpoints_mem_sideRegion₁_of_face` / `endpoints_mem_sideRegion₂_of_face`.
* `u_s₂ / v_s₂` — the chord endpoints lie in `sideRegion₂`
  (`tailDart_mem_sideRegion₂` / `headDart_mem_sideRegion₂`): via the side-2 forward-run arc
  (`ZinanCh35ArcSide.fwdArc_tail_mem_sideRegion₂` and the head-variant per-dart bridge).

The remaining two fields `p_s₁ / q_s₁` — the **precolored** endpoints lie in `sideRegion₁` — are
NOT structural facts of the chord split: `p, q` are arbitrary external vertices (the precolored
boundary edge supplied by `ThomassenLists`), and their placement on side 1 is the recursion's
*choice* (Thomassen picks the chord so the precolored edge is on side 1), not a consequence of the
chord-split geometry.  They are therefore genuinely recursion-supplied and are carried as the two
remaining inputs of `chordSplitRegionsResidue_of_precolored`.

`#print axioms` clean-3 (`propext`, `Classical.choice`, `Quot.sound`).  No `sorry` / `axiom` /
`admit` / `native_decide`; no posited conclusion.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Regions

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.ZinanCh35Side2Confine
open ProofsInTheBook.ZinanCh35Schoenflies2
open ProofsInTheBook.ZinanCh35ChordResidue
open ProofsInTheBook.ZinanCh35ArcSide

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## Section 1.  The chord-endpoint memberships in `sideRegion₂`.

The forward-run arc `fwdArc data : DartArc M outerCycle (head dart) (tail dart)` traverses the
side-2 boundary arc from `v = head dart` to `u = tail dart`.  Every arc dart's tail is in
`sideRegion₂` (`fwdArc_tail_mem_sideRegion₂`, unconditional); the FIRST arc dart's tail is
`head dart = v`, and the LAST arc dart's head is `tail dart = u` (reached by the head-variant of the
per-dart side-2 bridge, since the arc's reverse faces are in `side₂`). -/

/-- **The chord endpoint `v = head dart` lies in `sideRegion₂`.**  The first forward-run arc dart
has tail `v` and lies in `sideRegion₂`. -/
theorem headDart_mem_sideRegion₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.head data.dart ∈ sideRegion₂ data := by
  have h := fwdArc_tail_mem_sideRegion₂ data hsep (fwdArc data).firstIdx
  rwa [(fwdArc data).tail_firstIdx] at h

/-- **The chord endpoint `u = tail dart` lies in `sideRegion₂`.**  The last forward-run arc dart has
head `u`; its reverse face is in `side₂`, so the head-variant bridge places `u` in `sideRegion₂`. -/
theorem tailDart_mem_sideRegion₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail data.dart ∈ sideRegion₂ data := by
  have h :=
    ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.dartRun_head_mem_sideRegion₂_of_face
      data hsep (fwdArc_dartEdge_ne_chord data (fwdArc data).lastIdx)
      (fwdArc_reverse_face_mem_side₂ data (fwdArc data).lastIdx)
  rwa [(fwdArc data).head_lastIdx] at h

/-! ## Section 2.  Every vertex has a non-outer incident dart, and the vertex cover. -/

/-- **Every vertex is the tail of a non-outer dart.**  Pick any dart `d₀` with `tail d₀ = w`; if its
face is outer, `M.σ d₀` shares the tail (`tail_sigma`) and is non-outer (its face equals
`dartFace (M.α d₀)`, non-outer by `alpha_dartFace_ne_outer_of_outer`). -/
theorem exists_nonouter_dart_tail (w : M.Vertex) :
    ∃ d : D, M.tail d = w ∧ M.dartFace d ≠ hNT.outerFace := by
  obtain ⟨d₀, hd₀⟩ := Quotient.exists_rep w
  have htail₀ : M.tail d₀ = w := hd₀
  by_cases ho : M.dartFace d₀ = hNT.outerFace
  · refine ⟨M.σ d₀, ?_, ?_⟩
    · rw [M.tail_sigma]; exact htail₀
    · rw [ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha d₀]
      exact alpha_dartFace_ne_outer_of_outer hNT ho
  · exact ⟨d₀, htail₀, ho⟩

/-- **The vertex cover** (the `cover` field of `ChordSplitRegions`).  Every `M`-vertex lies in
`sideRegion₁ ∪ sideRegion₂`. -/
theorem cover_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ w : M.Vertex, w ∈ sideRegion₁ data ∨ w ∈ sideRegion₂ data := by
  intro w
  obtain ⟨d, htail, hnonouter⟩ := exists_nonouter_dart_tail (hNT := hNT) w
  rcases boundedFacePartition_uncond data hnonouter with hs₁ | hs₂
  · left
    by_cases hd : d = data.dart
    · subst hd; rw [← htail]; exact tailDart_mem_sideRegion₁ data hsep
    · have hkept : d ∈ data.keptSet₁ := ⟨Or.inl hs₁, by simp only [Set.mem_singleton_iff]; exact hd⟩
      rw [← htail]; exact ⟨d, (data.mem_keptDel₁_iff d).2 hkept, rfl⟩
  · right
    by_cases hd : d = M.α data.dart
    · subst hd; rw [← htail, M.tail_alpha]; exact headDart_mem_sideRegion₂ data hsep
    · have hkept : d ∈ data.keptSet₂ := ⟨Or.inl hs₂, by simp only [Set.mem_singleton_iff]; exact hd⟩
      rw [← htail]; exact ⟨d, (data.mem_keptDel₂_iff d).2 hkept, rfl⟩

/-! ## Section 3.  The vertex-level edge confinement. -/

/-- A non-outer dart whose two endpoints we wish to confine: `boundedFacePartition` places its face
in `side₁` or `side₂`, and the matching `endpoints_mem_sideRegionₛ_of_face` lemma confines BOTH
endpoints to that side region.  (Non-chord hypothesis needed for the kept-set membership.) -/
theorem nonouter_dart_confined (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hnonouter : M.dartFace e ≠ hNT.outerFace) :
    (M.tail e ∈ sideRegion₁ data ∧ M.head e ∈ sideRegion₁ data) ∨
      (M.tail e ∈ sideRegion₂ data ∧ M.head e ∈ sideRegion₂ data) := by
  rcases boundedFacePartition_uncond data hnonouter with hs₁ | hs₂
  · exact Or.inl (endpoints_mem_sideRegion₁_of_face data hsep hchord hs₁)
  · exact Or.inr (endpoints_mem_sideRegion₂_of_face data hsep hchord hs₂)

/-- **Edge confinement at the level of a single dart's two endpoints.**  Both `tail e` and `head e`
are confined to one common side region: if `e` is the chord they are `u, v ∈ sideRegion₁`; otherwise
the non-outer representative (`e` or `M.α e`) confines both via `nonouter_dart_confined`. -/
theorem dart_endpoints_confined (data : hNT.ChordSplitData u v) (hsep : data.Separates) (e : D) :
    (M.tail e ∈ sideRegion₁ data ∧ M.head e ∈ sideRegion₁ data) ∨
      (M.tail e ∈ sideRegion₂ data ∧ M.head e ∈ sideRegion₂ data) := by
  by_cases hchord : M.dartEdge e = s(u, v)
  · -- chord edge: `{tail e, head e} = {u, v}`, both in `sideRegion₁`.
    left
    have hu₁ : M.tail data.dart ∈ sideRegion₁ data := tailDart_mem_sideRegion₁ data hsep
    have hv₁ : M.head data.dart ∈ sideRegion₁ data := headDart_mem_sideRegion₁ data hsep
    have hdartedge : M.dartEdge data.dart = s(u, v) := hNT.chordDart_edge data.chord
    have he2 : (s(M.tail e, M.head e) : Sym2 M.Vertex)
        = s(M.tail data.dart, M.head data.dart) := by
      have h1 : (s(M.tail e, M.head e) : Sym2 M.Vertex) = s(u, v) := hchord
      have h2 : (s(M.tail data.dart, M.head data.dart) : Sym2 M.Vertex) = s(u, v) := hdartedge
      rw [h1, h2]
    rcases Sym2.eq_iff.mp he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ hu₁, h2 ▸ hv₁⟩
    · exact ⟨h1 ▸ hv₁, h2 ▸ hu₁⟩
  · -- non-chord: pick the non-outer representative dart of the edge.
    by_cases ho : M.dartFace e = hNT.outerFace
    · have hαnonouter : M.dartFace (M.α e) ≠ hNT.outerFace :=
        alpha_dartFace_ne_outer_of_outer hNT ho
      have hαchord : M.dartEdge (M.α e) ≠ s(u, v) := by rwa [M.dartEdge_alpha]
      rcases nonouter_dart_confined data hsep hαchord hαnonouter with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · rw [M.tail_alpha] at ht; rw [M.head_alpha] at hh; exact Or.inl ⟨hh, ht⟩
      · rw [M.tail_alpha] at ht; rw [M.head_alpha] at hh; exact Or.inr ⟨hh, ht⟩
    · exact nonouter_dart_confined data hsep hchord ho

/-- **The vertex-level edge confinement** (the `edge_confined` field).  A graph edge between two
vertices keeps both inside one side region. -/
theorem edge_confined_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ∀ ⦃a b : M.Vertex⦄, M.toSimpleGraph.Adj a b →
      (a ∈ sideRegion₁ data ∧ b ∈ sideRegion₁ data) ∨
        (a ∈ sideRegion₂ data ∧ b ∈ sideRegion₂ data) := by
  intro a b hab
  obtain ⟨hne, e, hedge⟩ := hab
  -- `dartEdge e = s(a,b)`; so `(tail e = a ∧ head e = b) ∨ (tail e = b ∧ head e = a)`.
  have hedge' : (s(M.tail e, M.head e) : Sym2 M.Vertex) = s(a, b) := hedge
  rcases dart_endpoints_confined data hsep e with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · -- both endpoints of `e` in `sideRegion₁`; transfer to `a, b` by the Sym2 equality.
    left
    rcases Sym2.eq_iff.mp hedge' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ ht, h2 ▸ hh⟩
    · exact ⟨h2 ▸ hh, h1 ▸ ht⟩
  · right
    rcases Sym2.eq_iff.mp hedge' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ ht, h2 ▸ hh⟩
    · exact ⟨h2 ▸ hh, h1 ▸ ht⟩

/-! ## Section 4.  Assembling the residue.

The four STRUCTURAL fields (`cover`, `edge_confined`, `u_s₂`, `v_s₂`) are unconditional.  The two
PRECOLORED fields (`p_s₁`, `q_s₁`) are the recursion's choice (Thomassen places the precolored edge
on side 1); we take them as the only inputs. -/

/-- **The chord-split-regions residue, from the precolored placement alone.**  The four structural
fields are produced unconditionally; the only inputs are the recursion-supplied precolored
memberships `p, q ∈ sideRegion₁`. -/
theorem chordSplitRegionsResidue_of_precolored
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) {p q : M.Vertex}
    (hp : p ∈ sideRegion₁ data) (hq : q ∈ sideRegion₁ data) :
    ChordSplitRegionsResidue data p q where
  cover := cover_holds data hsep
  edge_confined := edge_confined_holds data hsep
  u_s₂ := tailDart_mem_sideRegion₂ data hsep
  v_s₂ := headDart_mem_sideRegion₂ data hsep
  p_s₁ := hp
  q_s₁ := hq

/-! ## Section 5.  §3.3 non-vacuity / faithfulness audit.

* The four structural fields are genuine producers (real proofs through
  `boundedFacePartition_uncond`, `endpoints_mem_sideRegion₁/₂_of_face`,
  `alpha_dartFace_ne_outer_of_outer`, the forward-run side-2 arc), not posited.
* The two precolored fields `p_s₁ / q_s₁` are taken as hypotheses because for *arbitrary* external
  `p, q` they are not chord-split-structural (the precolored edge is placed on side 1 by the
  recursion's chord choice).  They are exactly the recursion fuel, not Jordan/structural residue.
* Non-vacuity of the structural fields: `cover` is total over `M.Vertex`; `u_s₂`/`v_s₂` exhibit
  concrete kept side-2 darts (the forward-run arc endpoints), so the side-2 region is inhabited at
  both chord ends; `edge_confined` is the genuine per-edge dichotomy. -/

-- The side-2 region genuinely contains both chord endpoints (non-vacuity of `u_s₂`/`v_s₂`).
example (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail data.dart ∈ sideRegion₂ data ∧ M.head data.dart ∈ sideRegion₂ data :=
  ⟨tailDart_mem_sideRegion₂ data hsep, headDart_mem_sideRegion₂ data hsep⟩

end ProofsInTheBook.ZinanCh35Regions

/-! ## Axiom audit (expect clean-3: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35Regions.headDart_mem_sideRegion₂
#print axioms ProofsInTheBook.ZinanCh35Regions.tailDart_mem_sideRegion₂
#print axioms ProofsInTheBook.ZinanCh35Regions.exists_nonouter_dart_tail
#print axioms ProofsInTheBook.ZinanCh35Regions.cover_holds
#print axioms ProofsInTheBook.ZinanCh35Regions.edge_confined_holds
#print axioms ProofsInTheBook.ZinanCh35Regions.chordSplitRegionsResidue_of_precolored
