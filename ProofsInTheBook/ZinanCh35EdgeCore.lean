import ProofsInTheBook.ZinanCh35Schoenflies

/-!
# Chapter 35 discrete-Schoenflies: the corrected (bounded) `edge_core`, via closure-intersection

This file PROVES the corrected `edge_core` field of `Side₁StarConfinement`
(`ZinanCh35Schoenflies.lean`) — now restricted to **bounded** darts (`dartFace e ≠ outerFace`),
the §3.3 repair of the formerly-false too-strong field — via the **closure-intersection** route
(NOT vertex rotation).

## The route (ChatGPT design, §3.3 repair)

`edge_core` asks: a non-chord, **bounded** dart `e` whose two endpoints are both side-1-region
vertices has its own face in `side₁`.  The closure-intersection argument:

1. **`bounded_face_partition`** (the coverage bridge): every non-outer face is in `side₁` or
   `side₂`.  Disjointness `side₁ ∩ side₂ = ∅` is the proven separation
   (`separates_iff_sidesDisjoint`); *coverage* is the genuine missing planar bridge
   (the cut-component ↔ `ChordSplitAdj`-reachability identification — `numCyclesCutPhi2`
   counts the dual face partition, but its identification with the two `Side` reachability
   closures is not landed).  Isolated as a named hypothesis.

2. **`sideRegion_inter_subset_chordEnds`** (the vertex-level Schoenflies bridge): a vertex in
   *both* side regions is a chord endpoint (`= u ∨ = v`).  The two closed side disks meet only
   at the chord ends.  Genuine boundary-incidence content; isolated as a named hypothesis.

3. **`endpoints_mem_sideRegion₂_of_face`** (UNCONDITIONAL): if `dartFace e ∈ side₂` then both
   endpoints of `e` are in `sideRegion₂`.  Proven from the `keptSet₂` structure
   (`e ∈ sideDarts₂ ⊆ keptSet₂`, and `α`-closure for the head).

4. **`edge_eq_chord_of_endpoints_chordEnds`** (UNCONDITIONAL): if both endpoints are in `{u, v}`
   and `e` is a non-loop, then `dartEdge e = s(u, v)` (simple map: two distinct endpoints in
   `{u, v}` are exactly `u, v`).

5. **`edge_core_holds`**: assume for contradiction `dartFace e ∈ side₂`; by (3) both endpoints are
   in `sideRegion₂`, and by hypothesis both are in `sideRegion₁`, so by (2) both are chord ends;
   by (4) `e` is the chord, contradicting `dartEdge e ≠ s(u, v)`.  Hence (by (1) coverage)
   `dartFace e ∈ side₁`.

The two genuinely-missing planar bridges (coverage + the vertex-region intersection) are isolated
SHARPLY as the named hypotheses `BoundedFacePartition` and `SideRegionInterChordEnds`; everything
else is proven unconditionally, axiom-clean.  `edge_core_holds` is clean-3 conditional on exactly
those two bridges.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35EdgeCore

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Schoenflies

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## 1. The side-2 region (the `side₂` analogue of `sideRegion₁`) -/

/-- **The side-2 region.**  The set of `M`-vertices that are the tail of some kept side-2 dart
(`d ∉ keptDel₂`); the `side₂`-analogue of `sideRegion₁`. -/
def sideRegion₂ (data : hNT.ChordSplitData u v) : Set M.Vertex :=
  {w : M.Vertex | ∃ d : D, d ∉ data.keptDel₂ ∧ M.tail d = w}

/-- A kept side-2 dart's tail is in the side-2 region. -/
lemma tail_mem_sideRegion₂ (data : hNT.ChordSplitData u v) {d : D}
    (hd : d ∉ data.keptDel₂) : M.tail d ∈ sideRegion₂ data :=
  ⟨d, hd, rfl⟩

/-! ## 2. The two missing planar bridges, isolated sharply

These two propositions are the *only* genuinely-open planar facts the closure-intersection route
needs.  Each is a sharp, non-vacuous statement; neither is derivable from the landed combinatorial
substrate (see the module header). -/

/-- **Bridge 1 — bounded-face coverage.**  Every non-outer face lies in `side₁` or `side₂`.
This is the coverage half of the face partition; disjointness is the proven separation.  Coverage
is the missing cut-component ↔ `ChordSplitAdj`-reachability identification. -/
def BoundedFacePartition (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {f : M.Face}, f ≠ hNT.outerFace → f ∈ data.side₁ ∨ f ∈ data.side₂

/-- **Bridge 2 — vertex-region intersection (vertex-level Schoenflies).**  A vertex lying in both
side regions is a chord endpoint.  The two closed side disks meet only at the chord ends `{u, v}`. -/
def SideRegionInterChordEnds (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {w : M.Vertex}, w ∈ sideRegion₁ data → w ∈ sideRegion₂ data → w = u ∨ w = v

/-! ## 3. `endpoints_mem_sideRegion₂_of_face` (unconditional)

If `dartFace e ∈ side₂` and `e` is non-chord, both endpoints of `e` lie in `sideRegion₂`: `e` is a
side-2 face-dart, hence in `keptSet₂` (it is not the side-2 seam dart `α dart`, since that has
chord edge), so its tail is in the region; the `α`-closure of `keptSet₂` puts `head e = tail (α e)`
in the region too. -/

/-- The side-2 seam dart `α dart` has chord edge `s(u, v)`. -/
lemma alpha_dart_edge (data : hNT.ChordSplitData u v) :
    M.dartEdge (M.α data.dart) = s(u, v) := by
  rw [M.dartEdge_alpha]; exact hNT.chordDart_edge data.chord

/-- **Both endpoints of a non-chord side-2 face-dart are in `sideRegion₂`** (unconditional in
`hsep`-free combinatorics apart from the `α`-closure, which needs `Separates`). -/
theorem endpoints_mem_sideRegion₂_of_face (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hface : M.dartFace e ∈ data.side₂) :
    M.tail e ∈ sideRegion₂ data ∧ M.head e ∈ sideRegion₂ data := by
  -- `e ≠ α dart` (else its edge would be the chord).
  have hne : e ≠ M.α data.dart := by
    intro h; exact hchord (by rw [h]; exact alpha_dart_edge data)
  -- `e ∈ sideDarts₂ ⊆ keptSet₂`.
  have hkept : e ∈ data.keptSet₂ := by
    refine ⟨Or.inl hface, ?_⟩
    simp only [Set.mem_singleton_iff]; exact hne
  have htail : M.tail e ∈ sideRegion₂ data :=
    tail_mem_sideRegion₂ data ((data.mem_keptDel₂_iff e).2 hkept)
  -- head `e = tail (α e)`; `α e ∈ keptSet₂` by the `α`-closure.
  have hkeptα : M.α e ∈ data.keptSet₂ := (data.mem_keptSet₂_alpha_iff hsep e).2 hkept
  have hhead : M.head e ∈ sideRegion₂ data :=
    tail_mem_sideRegion₂ data ((data.mem_keptDel₂_iff (M.α e)).2 hkeptα)
  exact ⟨htail, hhead⟩

/-! ## 4. `edge_eq_chord_of_endpoints_chordEnds` (unconditional)

Two distinct endpoints (non-loop) both in `{u, v}` force the edge to be the chord. -/

/-- **A non-loop edge with both endpoints in `{u, v}` is the chord.**  The simple-map no-loop
fact gives `tail e ≠ head e`; two distinct members of `{u, v}` are exactly `u, v` (in some order),
so `dartEdge e = s(tail e, head e) = s(u, v)`. -/
theorem edge_eq_chord_of_endpoints_chordEnds (data : hNT.ChordSplitData u v) {e : D}
    (htail : M.tail e = u ∨ M.tail e = v) (hhead : M.head e = u ∨ M.head e = v) :
    M.dartEdge e = s(u, v) := by
  have hloop : M.tail e ≠ M.head e := hNT.simpleGraph.no_loop e
  show s(M.tail e, M.head e) = s(u, v)
  rcases htail with ht | ht <;> rcases hhead with hh | hh
  · -- both `= u`: contradicts non-loop.
    exact absurd (ht.trans hh.symm) hloop
  · rw [ht, hh]
  · rw [ht, hh, Sym2.eq_swap]
  · -- both `= v`: contradicts non-loop.
    exact absurd (ht.trans hh.symm) hloop

/-! ## 5. `edge_core_holds` — the corrected (bounded) `edge_core`, conditional on the two bridges -/

/-- **The corrected (bounded) `edge_core`, via closure-intersection.**  For a non-chord, bounded
dart `e` (`dartFace e ≠ outerFace`) whose two endpoints are both in `sideRegion₁`, the face of `e`
lies in `side₁`.

Proof: `bounded_face_partition` places `dartFace e` in `side₁` or `side₂`.  In the `side₂` case,
`endpoints_mem_sideRegion₂_of_face` puts both endpoints in `sideRegion₂`; combined with the
`sideRegion₁` hypotheses, `sideRegion_inter_subset_chordEnds` forces both endpoints into `{u, v}`,
whence `edge_eq_chord_of_endpoints_chordEnds` makes `e` the chord — contradicting non-chordness.
So `dartFace e ∈ side₁`.

Clean-3 conditional on exactly the two isolated planar bridges. -/
theorem edge_core_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hpart : BoundedFacePartition data) (hinter : SideRegionInterChordEnds data)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (houter : M.dartFace e ≠ hNT.outerFace)
    (htail : M.tail e ∈ sideRegion₁ data) (hhead : M.head e ∈ sideRegion₁ data) :
    M.dartFace e ∈ data.side₁ := by
  rcases hpart houter with hside₁ | hside₂
  · exact hside₁
  · -- `dartFace e ∈ side₂`: derive `e = chord`, contradiction.
    exfalso
    obtain ⟨htail₂, hhead₂⟩ := endpoints_mem_sideRegion₂_of_face data hsep hchord hside₂
    have htchord : M.tail e = u ∨ M.tail e = v := hinter htail htail₂
    have hhchord : M.head e = u ∨ M.head e = v := hinter hhead hhead₂
    exact hchord (edge_eq_chord_of_endpoints_chordEnds data htchord hhchord)

/-! ## 6. Packaging: the `Side₁StarConfinement.edge_core` field, from the bridges

`edge_core_holds` is exactly the bounded `edge_core` field shape; we expose it as such so a
downstream `Side₁StarConfinement` can be assembled once the two bridges are supplied. -/

/-- **The bounded `edge_core` field, supplied by the two bridges.**  Exactly the shape of
`Side₁StarConfinement.edge_core` / `Side₁StarBankAnchor.edge_core` / `OppArcStarSeed.edge_core`. -/
theorem edge_core_field (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hpart : BoundedFacePartition data) (hinter : SideRegionInterChordEnds data) :
    ∀ {e : D},
      M.dartEdge e ≠ s(u, v) →
      M.dartFace e ≠ hNT.outerFace →
      M.tail e ∈ sideRegion₁ data →
      M.head e ∈ sideRegion₁ data →
        M.dartFace e ∈ data.side₁ :=
  fun hchord houter htail hhead => edge_core_holds data hsep hpart hinter hchord houter htail hhead

end ProofsInTheBook.ZinanCh35EdgeCore

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35EdgeCore.endpoints_mem_sideRegion₂_of_face
#print axioms ProofsInTheBook.ZinanCh35EdgeCore.edge_eq_chord_of_endpoints_chordEnds
#print axioms ProofsInTheBook.ZinanCh35EdgeCore.edge_core_holds
#print axioms ProofsInTheBook.ZinanCh35EdgeCore.edge_core_field
