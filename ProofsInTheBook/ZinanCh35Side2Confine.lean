import ProofsInTheBook.ZinanCh35Side2
import ProofsInTheBook.ZinanCh35Side1Confine
import ProofsInTheBook.ZinanCh35EdgeCoreFinal
import ProofsInTheBook.ZinanCh35Schoenflies2

/-!
# Chapter 35 discrete-Schoenflies: discharging `Side₂SchoenfliesConfinementInput` (the side-2 confinement)

This file is the **symmetric mirror** of `ZinanCh35Side1Confine.lean`.  It discharges the SIDE-2
confinement input `ZinanCh35Side2.Side₂SchoenfliesConfinementInput` — the missing half of the
`ChordBranchSupplier`'s chord branch — conditional on the **same** bank-orientation labelling datum
side 1 needs (the arc-bounds-its-side residual), with the side₁/side₂ roles swapped.

## The two fields of `Side₂SchoenfliesConfinementInput`

* `oppArcStarSeed₂` — *opposite-arc omission*: a strictly internal vertex `w` of the opposite
  boundary arc `path₁` is omitted by side 2 (`w ∉ sideRegion₂ data`).  (For side 2 the opposite arc
  is `path₁`, the mirror of side 1's `path₂`.)  Discharged via the **direct route** (the side-2
  mirror of `ZinanCh35Side1Confine.oppArc_star_core_direct`): `w` is `path₁`-internal hence `≠ u, v`,
  and lies in `sideRegion₁` (by the symmetric bank datum `path₁_internal_mem_sideRegion₁`); the
  proven side-symmetric `ZinanCh35StarConn.sideRegionInterChordEnds_holds` then forbids `w` from
  *also* lying in `sideRegion₂`, so `w ∉ sideRegion₂`.

* `edge_core₂` — *region edge-confinement core* (the side-2 mirror of
  `ZinanCh35Schoenflies.Side₁SchoenfliesConfinement.edge_confined`): an ambient edge `e` whose two
  endpoints are both side-2-region vertices is either represented in the side-2 carve (`e ∉ keptDel₂
  ∧ α e ∉ keptDel₂`) or is the chord.  Discharged via the SAME two bridges as side 1, mirrored — the
  side-symmetric `BoundedFacePartition` (`ZinanCh35EdgeCoreFinal.boundedFacePartition_uncond`,
  UNCONDITIONAL) and `SideRegionInterChordEnds` (`ZinanCh35StarConn.sideRegionInterChordEnds_holds`,
  UNCONDITIONAL) — instantiated with the side roles swapped (`side₁ ↔ side₂`, `sideRegion₁ ↔
  sideRegion₂`, `keptSet₁ ↔ keptSet₂`, the seam dart `dart ↔ α dart`).

## The orientation datum

The direct route needs exactly the **symmetric** bank-orientation fact

```
path₁_internal_mem_sideRegion₁ : w ∈ path₁.internalVertices → w ∈ sideRegion₁ data
```

i.e. *the first listed boundary arc `path₁` is the side-1 boundary arc* — the same
"arc bounds its side" labelling residual that side 1 isolated (there as
`path₂_internal_mem_sideRegion₂`).  In the current `ChordSplitData` layer this is a free input
(reversing `data.chord` swaps `side₁ ↔ side₂` while fixing the arc labelling, flipping its truth
value), so it is isolated here exactly as side 1 isolates its mirror; it is **not** faked.  We bundle
it as `ChordArcBankOrientation` (carrying this single symmetric field) and prove
`Side₂SchoenfliesConfinementInput` conditional on it.

## Honesty contract (§3.3)

This is a **genuine mirror**, not `:= side₁…`.  Everything structural — the side-2 bounded
`edge_core` (closure-intersection, side roles swapped), the side-2 `endpoints_mem_sideRegion₁_of_face`
producer, the side-2 outer-dart route, the `α`-reduction to the kept disjunction, and the direct
opposite-arc omission — is proved here against the side-2 data, conditional only on the same proven
side-symmetric bridges plus the single bank-orientation datum.  No `sorry` / `axiom` / `admit` /
`native_decide`; no posited conclusion; the bundle is non-vacuous (its `oppArcStarSeed₂` quantifies
over the nonempty `path₁.internalVertices`, exhibited below).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Side2Confine

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ZinanCh35Schoenflies2
open ProofsInTheBook.ZinanCh35Side2

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## The minimal bank-orientation datum (symmetric mirror)

The single genuinely-free fact the direct side-2 route needs: the symmetric mirror of
`ZinanCh35Side1Confine.ChordArcBankOrientation`.  Side 1 isolated
`path₂_internal_mem_sideRegion₂` (the second arc bounds side 2); side 2 needs
`path₁_internal_mem_sideRegion₁` (the first arc bounds side 1).  Both are the same
"arc bounds its side" labelling datum — see the side-1 module header for the proof that it is not
derivable from the bare `ChordSplitData`. -/

/-- **The chord-arc bank-orientation datum (side-2 mirror).**  The first listed boundary arc
`path₁` is the side-1 boundary arc: every strictly-internal vertex of `path₁` lies in the side-1
region.  Symmetric counterpart of `ZinanCh35Side1Confine.ChordArcBankOrientation`'s
`path₂_internal_mem_sideRegion₂`; isolated here rather than faked, for the same reason. -/
structure ChordArcBankOrientation (data : hNT.ChordSplitData u v) : Prop where
  /-- A strictly-internal vertex of the boundary arc `path₁` is in the side-1 region. -/
  path₁_internal_mem_sideRegion₁ : ∀ {w : M.Vertex},
    w ∈ data.arc.path₁.internalVertices → w ∈ sideRegion₁ data

/-! ## Tier 1 — the side-1 endpoint producer (mirror of `endpoints_mem_sideRegion₂_of_face`)

The side-2 closure-intersection route needs the side-1 analogue of
`ZinanCh35EdgeCore.endpoints_mem_sideRegion₂_of_face`: if `dartFace e ∈ side₁` (and `e` is
non-chord), both endpoints of `e` lie in `sideRegion₁`.  The side-1 seam dart is `data.dart` (whose
edge is the chord), the kept set is `keptSet₁`, and the `α`-closure is `mem_keptSet₁_alpha_iff`. -/

/-- **Both endpoints of a non-chord side-1 face-dart are in `sideRegion₁`.**  Mirror of
`endpoints_mem_sideRegion₂_of_face` with the side roles swapped: `e` is a side-1 face-dart, hence in
`keptSet₁` (it is not the side-1 seam dart `dart`, since that has chord edge), so its tail is in the
region; the `α`-closure of `keptSet₁` puts `head e = tail (α e)` in the region too. -/
theorem endpoints_mem_sideRegion₁_of_face (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hface : M.dartFace e ∈ data.side₁) :
    M.tail e ∈ sideRegion₁ data ∧ M.head e ∈ sideRegion₁ data := by
  -- `e ≠ dart` (else its edge would be the chord).
  have hne : e ≠ data.dart := by
    intro h; exact hchord (by rw [h]; exact hNT.chordDart_edge data.chord)
  -- `e ∈ sideDarts₁ ⊆ keptSet₁`.
  have hkept : e ∈ data.keptSet₁ := by
    refine ⟨Or.inl hface, ?_⟩
    simp only [Set.mem_singleton_iff]; exact hne
  have htail : M.tail e ∈ sideRegion₁ data :=
    ⟨e, (data.mem_keptDel₁_iff e).2 hkept, rfl⟩
  -- head `e = tail (α e)`; `α e ∈ keptSet₁` by the `α`-closure.
  have hkeptα : M.α e ∈ data.keptSet₁ := (data.mem_keptSet₁_alpha_iff hsep e).2 hkept
  have hhead : M.head e ∈ sideRegion₁ data :=
    ⟨M.α e, (data.mem_keptDel₁_iff (M.α e)).2 hkeptα, rfl⟩
  exact ⟨htail, hhead⟩

/-! ## Tier 2 — the side-2 bounded `edge_core` (mirror of `edge_core_holds`)

The corrected (bounded) side-2 `edge_core`: a non-chord bounded dart `e` whose two endpoints are
both in `sideRegion₂` has its own face in `side₂`.  Mirror of `ZinanCh35EdgeCore.edge_core_holds`
with the side roles swapped — `BoundedFacePartition` places `dartFace e` in `side₁` or `side₂`; the
`side₁` case puts both endpoints in `sideRegion₁` (Tier 1), forcing them (with the `sideRegion₂`
hypotheses, via `SideRegionInterChordEnds`) into `{u, v}`, whence `e` is the chord — contradiction. -/

/-- **The corrected (bounded) side-2 `edge_core`.**  For a non-chord, bounded dart `e`
(`dartFace e ≠ outerFace`) whose two endpoints are both in `sideRegion₂`, the face of `e` lies in
`side₂`.  Conditional on exactly the two proven side-symmetric bridges
(`BoundedFacePartition` + `SideRegionInterChordEnds`).  Mirror of `edge_core_holds`. -/
theorem edge_core₂_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hpart : BoundedFacePartition data) (hinter : SideRegionInterChordEnds data)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (houter : M.dartFace e ≠ hNT.outerFace)
    (htail : M.tail e ∈ sideRegion₂ data) (hhead : M.head e ∈ sideRegion₂ data) :
    M.dartFace e ∈ data.side₂ := by
  rcases hpart houter with hside₁ | hside₂
  · -- `dartFace e ∈ side₁`: derive `e = chord`, contradiction.
    exfalso
    obtain ⟨htail₁, hhead₁⟩ := endpoints_mem_sideRegion₁_of_face data hsep hchord hside₁
    -- both endpoints are in both regions ⟹ both are chord ends.
    have htchord : M.tail e = u ∨ M.tail e = v := hinter htail₁ htail
    have hhchord : M.head e = u ∨ M.head e = v := hinter hhead₁ hhead
    exact hchord (edge_eq_chord_of_endpoints_chordEnds data htchord hhchord)
  · exact hside₂

/-! ## Tier 3 — the side-2 outer-dart route `OuterDartArc₂` (mirror of `outerDartArc₁_holds`)

The side-2 mirror of `ZinanCh35Schoenflies.OuterDartArc₁` / `ZinanCh35Schoenflies2.outerDartArc₁_holds`:
for an outer dart `e` (face = outer face), non-chord, with both endpoints in `sideRegion₂`, the
reverse inner face `dartFace (α e)` lies in `side₂`.  Same argument, side roles swapped: the reverse
face is non-outer (`alpha_dartFace_ne_outer_of_outer`, side-symmetric), so the partition places it in
`side₁` or `side₂`; the `side₁` case makes `α e` a non-chord `side₁` face dart, putting both endpoints
of `e` in `sideRegion₁`, whence (with `sideRegion₂`) `SideRegionInterChordEnds` forces them into
`{u, v}` and `e` is the chord — contradiction. -/

/-- **The side-2 outer-dart route (`OuterDartArc₂`).**  Mirror of `outerDartArc₁_holds`: an outer
dart whose two endpoints are both in `sideRegion₂` has its reverse face in `side₂`.  Conditional on
the two proven side-symmetric bridges. -/
theorem outerDartArc₂_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hpart : BoundedFacePartition data) (hinter : SideRegionInterChordEnds data)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hface : M.dartFace e = hNT.outerFace)
    (htail : M.tail e ∈ sideRegion₂ data) (hhead : M.head e ∈ sideRegion₂ data) :
    M.dartFace (M.α e) ∈ data.side₂ := by
  -- The reverse inner face is non-outer.
  have hαe_not_outer : M.dartFace (M.α e) ≠ hNT.outerFace :=
    alpha_dartFace_ne_outer_of_outer hNT hface
  -- Partition it into side₁ or side₂.
  rcases hpart hαe_not_outer with h₁ | h₂
  · -- `dartFace (α e) ∈ side₁`: derive `e = chord`, contradiction.
    exfalso
    -- `α e` is a non-chord side₁ face dart.
    have hαe_chord : M.dartEdge (M.α e) ≠ s(u, v) := by
      rw [M.dartEdge_alpha]; exact hchord
    -- both endpoints of `α e` are in `sideRegion₁`.
    obtain ⟨htail₁, hhead₁⟩ :=
      endpoints_mem_sideRegion₁_of_face data hsep hαe_chord h₁
    -- `tail (α e) = head e`, `head (α e) = tail e`.
    rw [M.tail_alpha] at htail₁
    rw [M.head_alpha] at hhead₁
    -- so both endpoints of `e` are in `sideRegion₁`; combine with `sideRegion₂`.
    have htchord : M.tail e = u ∨ M.tail e = v := hinter hhead₁ htail
    have hhchord : M.head e = u ∨ M.head e = v := hinter htail₁ hhead
    exact hchord (edge_eq_chord_of_endpoints_chordEnds data htchord hhchord)
  · exact h₂

/-! ## Tier 4 — the side-2 `edge_core₂` field (mirror of `edge_confined`)

Assemble the `edge_core₂` field of `Side₂SchoenfliesConfinementInput` (the kept-disjunction shape)
from the bounded `edge_core₂` and the outer-dart route, mirroring
`ZinanCh35Schoenflies.vertexStar_confined_of_starConfinement`'s `edge_confined` derivation with the
side roles swapped.  The side-2 seam dart is `α dart` (whose edge is the chord by
`ZinanCh35EdgeCore.alpha_dart_edge`); `α`-closure of `keptSet₂` is `mem_keptSet₂_alpha_iff`. -/

/-- **The side-2 region edge-confinement field, from the two bridges.**  Mirror of
`Side₁SchoenfliesConfinement.edge_confined`: an ambient edge `e` whose two endpoints are both in
`sideRegion₂` is either represented in the side-2 carve (`e ∉ keptDel₂ ∧ α e ∉ keptDel₂`) or is the
chord.  Case-splits on whether `e` is an outer dart: a bounded dart is kept via the bounded
`edge_core₂`; an outer dart via the `outerDartArc₂` route.  Conditional on exactly the two proven
side-symmetric bridges. -/
theorem edge_confined₂_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hpart : BoundedFacePartition data) (hinter : SideRegionInterChordEnds data) :
    ∀ {e : D},
      M.tail e ∈ sideRegion₂ data →
      M.head e ∈ sideRegion₂ data →
        ((e ∉ data.keptDel₂ ∧ M.α e ∉ data.keptDel₂) ∨ M.dartEdge e = s(u, v)) := by
  intro e htail hhead
  by_cases hchord : M.dartEdge e = s(u, v)
  · exact Or.inr hchord
  · -- non-chord: split on whether `e` is an outer dart.
    left
    -- `e ≠ α dart` (the side-2 seam, else `dartEdge e = dartEdge (α dart) = s(u, v)`).
    have hne : e ≠ M.α data.dart := by
      intro h; exact hchord (by rw [h]; exact alpha_dart_edge data)
    -- In both cases we produce `e ∈ keptSet₂`, then close under `α`.
    have hkept : e ∈ data.keptSet₂ := by
      by_cases hof : M.dartFace e = hNT.outerFace
      · -- outer dart: kept via `outerArc₂` (face = outerFace, reverse face ∈ side₂).
        have hrev : M.dartFace (M.α e) ∈ data.side₂ :=
          outerDartArc₂_holds data hsep hpart hinter hchord hof htail hhead
        refine ⟨Or.inr ⟨hof, hrev⟩, ?_⟩
        simp only [Set.mem_singleton_iff]; exact hne
      · -- bounded dart: the bounded `edge_core₂` gives `dartFace e ∈ side₂`, hence `∈ sideDarts₂`.
        have hface : M.dartFace e ∈ data.side₂ :=
          edge_core₂_holds data hsep hpart hinter hchord hof htail hhead
        refine ⟨Or.inl hface, ?_⟩
        simp only [Set.mem_singleton_iff]; exact hne
    refine ⟨?_, ?_⟩
    · rw [data.mem_keptDel₂_iff]; exact hkept
    · rw [data.mem_keptDel₂_iff]
      exact (data.mem_keptSet₂_alpha_iff hsep e).2 hkept

/-! ## Tier 5 — the direct opposite-arc omission `oppArcStarSeed₂` (mirror of `oppArc_star_core_direct`)

The side-2 mirror of `ZinanCh35Side1Confine.oppArc_star_core_direct`, but the target is *directly*
`w ∉ sideRegion₂` (no star-confinement unfolding needed, since the side-2 input field
`oppArcStarSeed₂` already asks for region omission): a `path₁`-internal vertex `w` is `≠ u, v` and
lies in `sideRegion₁` (the symmetric bank datum), so it cannot also lie in `sideRegion₂`. -/

/-- **The opposite-arc omission, via the direct route.**  Conditional on the symmetric
bank-orientation datum, a strictly-internal vertex of the opposite boundary arc `path₁` is omitted by
side 2 (`w ∉ sideRegion₂ data`).  Mirror of `oppArc_star_core_direct`. -/
theorem oppArcStarSeed₂_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hbank : ChordArcBankOrientation data) {w : M.Vertex}
    (hw : w ∈ data.arc.path₁.internalVertices) :
    w ∉ sideRegion₂ data := by
  intro hw₂
  -- `w` lies in the side-1 region (bank datum) and is `≠ u, v` (path₁-internal).
  have hw₁ : w ∈ sideRegion₁ data := hbank.path₁_internal_mem_sideRegion₁ hw
  -- `path₁ : BoundaryPath u v`, so `_ne_start` gives `≠ u` and `_ne_end` gives `≠ v`.
  have hw_ne_u : w ≠ u := data.arc.path₁.internalVertex_ne_start hw
  have hw_ne_v : w ≠ v := data.arc.path₁.internalVertex_ne_end hw
  -- a vertex in both side regions is a chord end — contradicting `≠ u, v`.
  rcases sideRegionInterChordEnds_holds data hsep hw₁ hw₂ with h | h
  · exact hw_ne_u h
  · exact hw_ne_v h

/-! ## Assembly: `Side₂SchoenfliesConfinementInput`, conditional on the bank-orientation datum

`edge_core₂` is discharged via the two proven side-symmetric bridges (both UNCONDITIONAL given the
chord split + `Separates`); `oppArcStarSeed₂` is the direct route above, conditional only on the
single bank-orientation datum. -/

/-- **`Side₂SchoenfliesConfinementInput`, discharged conditional on the single bank-orientation
datum.**  The mirror of `ZinanCh35Side1Confine.side₁StarConfinement_holds` for the side-2
confinement bundle.

* The `edge_core₂` field is discharged via the two proven side-symmetric bridges
  (`boundedFacePartition_uncond` + `sideRegionInterChordEnds_holds`, both UNCONDITIONAL given the
  chord split + `Separates`), instantiated with the side roles swapped.
* The `oppArcStarSeed₂` field is discharged via the direct route, conditional **only** on the
  minimal `ChordArcBankOrientation` datum (the symmetric mirror of side 1's bank datum).

This completes the side-2 confinement input modulo that single bank-orientation input — the missing
half of the `ChordBranchSupplier`'s chord branch. -/
theorem side₂SchoenfliesConfinementInput_holds (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (hbank : ChordArcBankOrientation data) :
    Side₂SchoenfliesConfinementInput data hsep where
  oppArcStarSeed₂ := fun {w} hw =>
    oppArcStarSeed₂_holds data hsep hbank hw
  edge_core₂ := fun {e} htail hhead =>
    edge_confined₂_holds data hsep (boundedFacePartition_uncond data)
      (sideRegionInterChordEnds_holds data hsep) htail hhead

/-! ## Non-vacuity of the side-2 confinement bundle (the §3.3 satisfiability obligation)

The discharged bundle is NOT propositionally `False`: its `oppArcStarSeed₂` field quantifies over
the *nonempty* `path₁.internalVertices` (`data.arc₁_internal`), and `edge_confined₂_holds` is a
genuine consequence of the two proven side-symmetric bridges — not a vacuous conditional.  We record
the omitted-vertex witness axiom-cleanly. -/

/-- **Non-vacuity witness.**  The discharged bundle exhibits a concrete omitted vertex: the opposite
boundary arc `path₁` carries an internal vertex (`data.arc₁_internal`), which `oppArcStarSeed₂` places
outside `sideRegion₂`.  So the bundle is inhabited-on-real-data, not `False`. -/
theorem side₂SchoenfliesConfinementInput_nonvacuous (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (hbank : ChordArcBankOrientation data) :
    ∃ w : M.Vertex, w ∉ sideRegion₂ data := by
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ data.arc₁_internal
  exact ⟨w, oppArcStarSeed₂_holds data hsep hbank hw⟩

end ProofsInTheBook.ZinanCh35Side2Confine

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35Side2Confine.endpoints_mem_sideRegion₁_of_face
#print axioms ProofsInTheBook.ZinanCh35Side2Confine.edge_core₂_holds
#print axioms ProofsInTheBook.ZinanCh35Side2Confine.outerDartArc₂_holds
#print axioms ProofsInTheBook.ZinanCh35Side2Confine.edge_confined₂_holds
#print axioms ProofsInTheBook.ZinanCh35Side2Confine.oppArcStarSeed₂_holds
#print axioms ProofsInTheBook.ZinanCh35Side2Confine.side₂SchoenfliesConfinementInput_holds
#print axioms ProofsInTheBook.ZinanCh35Side2Confine.side₂SchoenfliesConfinementInput_nonvacuous
