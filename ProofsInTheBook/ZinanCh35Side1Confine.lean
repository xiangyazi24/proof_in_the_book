import ProofsInTheBook.ZinanCh35Schoenflies
import ProofsInTheBook.ZinanCh35StarConn
import ProofsInTheBook.ZinanCh35EdgeCoreFinal

/-!
# Chapter 35 discrete-Schoenflies: discharging `Side₁StarConfinement` (the side-1 confinement)

This file closes the two-field residual `Side₁StarConfinement`
(`ZinanCh35Schoenflies.lean`) — the single genuinely-open vertex-star anchoring fact of the
discrete-Schoenflies star-rotation design — down to **one** minimal datum.

## The two fields

* `edge_core` — the **region edge-confinement core**.  Discharged **unconditionally** (clean-3)
  by `ZinanCh35EdgeCoreFinal.edge_core_uncond`, whose two planar bridges
  (`BoundedFacePartition` from the coverage atom, `SideRegionInterChordEnds` from the σ-star
  connectivity argument) are both proven.

* `oppArc_star_core` — the **opposite-arc vertex-star confinement**: every dart `d` tailed at a
  strictly internal vertex `w` of the opposite boundary arc `path₂` is deleted by side 1.
  Discharged via the **direct route** (ChatGPT Pro R7, bypassing the dead orientation-false
  `OppArcSeedReach` seed): both conjuncts close through the proven
  `ZinanCh35StarConn.sideRegionInterChordEnds_holds`
  (`w ∈ sideRegion₁ → w ∈ sideRegion₂ → w = u ∨ v`) once we know
  `w ∈ sideRegion₂`.  The vertex `w` is `path₂`-internal hence `≠ u, v`, so being in both
  side regions is impossible — therefore `w ∉ sideRegion₁`, which (by the proven star-witness
  producers) forces every `tail`-incident non-chord dart to be deleted by side 1.

## The one real input: `ChordArcBankOrientation`

The direct route needs exactly one fact:

```
path₂_internal_mem_sideRegion₂ : w ∈ path₂.internalVertices → w ∈ sideRegion₂ data
```

i.e. *the second listed boundary arc `path₂` is the side-2 boundary arc*.

**This is genuinely free in the current `ChordSplitData` layer**, not a provable consequence.
INVESTIGATION (recorded for audit):

* `ChordSplitData` (`PlanarMapChordSplitData.lean:208`) bundles a chord, a
  `BoundaryArcSplit`, and two internality fields.  The faces are *dart*-derived:
  `face₁ := dartFace data.dart`, `face₂ := dartFace (α data.dart)`
  (`PlanarMapChordSplitData.lean:227–232`), and `side₁/side₂` are the reachability closures from
  `face₁/face₂`.
* `BoundaryArcSplit` (`PlanarMapBoundary.lean:92`) stores `path₁ : BoundaryPath u v`,
  `path₂ : BoundaryPath v u`, together with covering / internal-disjointness / properness
  fields phrased **only** in terms of `boundaryVertices` / `boundaryEdges`.  **No field ties
  `path₁`/`path₂` to `face₁`/`face₂` or to `data.dart`.**  The chord dart and the arc labelling
  are chosen independently.
* Consequently, **reversing** `data.chord`'s dart swaps `face₁ ↔ face₂` (hence `side₁ ↔ side₂`)
  while leaving `path₁`/`path₂` fixed — flipping the truth value of
  `path₂_internal_mem_sideRegion₂`.  This is precisely the orientation mismatch that made the
  dead `OppArcSeedReach` seed false (R7 §4).
* Corroborating evidence that this is a *free input*, not derivable: the side-2 mirror bundle
  `ZinanCh35Side2.Side₂SchoenfliesConfinementInput` takes the symmetric statement
  (`path₁`-internal ⟹ `∉ sideRegion₂`) as an **unproven hypothesis field** `oppArcStarSeed₂`;
  it is nowhere discharged from the construction either.

We therefore isolate it as the minimal clean residual `ChordArcBankOrientation` (R7 §5) and
prove `Side₁StarConfinement` **conditional on it**.  We do **not** fake it.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Side1Confine

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Schoenflies
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## The minimal bank-orientation datum

The single genuinely-free fact the direct route needs (R7 §5).  See the module header for the
proof that this is *not* derivable from the bare `ChordSplitData` (the arc labelling and the
dart-derived face labelling are construction-independent, and reversing the chord dart flips it). -/

/-- **The chord-arc bank-orientation datum.**  The second listed boundary arc `path₂` is the
side-2 boundary arc: every strictly-internal vertex of `path₂` lies in the side-2 region.

This is the weakest honest orientation statement the direct `oppArc_star_core` route needs; in
the current `ChordSplitData` layer it is a free input (reversing `data.chord` swaps
`side₁ ↔ side₂` while fixing `path₂`, flipping its truth value), so it is isolated here rather
than faked. -/
structure ChordArcBankOrientation (data : hNT.ChordSplitData u v) : Prop where
  /-- A strictly-internal vertex of the opposite boundary arc `path₂` is in the side-2 region. -/
  path₂_internal_mem_sideRegion₂ : ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices → w ∈ sideRegion₂ data

/-! ## The direct `oppArc_star_core` route (R7 §3)

Both conjuncts close by contradiction through `sideRegionInterChordEnds_holds`: a `path₂`-internal
vertex `w` is `≠ u, v`, lies in `sideRegion₂` (by the bank datum), so it cannot also lie in
`sideRegion₁`.  Then the proven star-witness producers turn "`w ∉ sideRegion₁`" into "every
non-chord dart tailed at `w` is deleted by side 1". -/

/-- **The opposite-arc vertex-star confinement, via the direct route.**  Conditional on the single
bank-orientation datum, every dart `d` tailed at a `path₂`-internal vertex `w` is the chord dart,
or its face is outside `side₁` and it is not a side-1 boundary dart. -/
theorem oppArc_star_core_direct (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hbank : ChordArcBankOrientation data) {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices) (d : D) (htail : M.tail d = w) :
    d = data.dart ∨
      (M.dartFace d ∉ data.side₁ ∧
        ¬ (M.dartFace d = hNT.outerFace ∧ M.dartFace (M.α d) ∈ data.side₁)) := by
  by_cases hd : d = data.dart
  · exact Or.inl hd
  · right
    -- `w` lies in the side-2 region (bank datum) and is `≠ u, v` (path₂-internal).
    have hw₂ : w ∈ sideRegion₂ data := hbank.path₂_internal_mem_sideRegion₂ hw
    -- `path₂ : BoundaryPath v u`, so `_ne_start` gives `≠ v` and `_ne_end` gives `≠ u`.
    have hw_ne_v : w ≠ v := data.arc.path₂.internalVertex_ne_start hw
    have hw_ne_u : w ≠ u := data.arc.path₂.internalVertex_ne_end hw
    -- Hence `w ∉ sideRegion₁`: otherwise it is a chord endpoint, contradicting `≠ u, v`.
    have no_sideRegion₁ : w ∉ sideRegion₁ data := by
      intro hw₁
      rcases sideRegionInterChordEnds_holds data hsep hw₁ hw₂ with h | h
      · exact hw_ne_u h
      · exact hw_ne_v h
    refine ⟨?_, ?_⟩
    · -- Conjunct 1: if `dartFace d ∈ side₁`, then `d` is a kept inner side-1 dart, so
      -- `w ∈ sideRegion₁` — contradiction.
      intro hface1
      exact no_sideRegion₁ (mem_sideRegion₁_of_star_side₁ data htail hd hface1)
    · -- Conjunct 2: if `d` is an outer dart with reverse face in `side₁`, it is a kept side-1
      -- boundary dart, so `w ∈ sideRegion₁` — contradiction.
      rintro ⟨hd_outer, hα_side1⟩
      exact no_sideRegion₁ (mem_sideRegion₁_of_star_outerArc₁ data htail hd hd_outer hα_side1)

/-! ## Assembly: `Side₁StarConfinement`, conditional on the bank-orientation datum

`edge_core` is unconditional (`edge_core_uncond`); `oppArc_star_core` is the direct route above. -/

/-- **`Side₁StarConfinement`, discharged conditional on the single bank-orientation datum.**

* The `edge_core` field is **unconditional** clean-3 (`edge_core_uncond`).
* The `oppArc_star_core` field is discharged via the direct R7 route, conditional **only** on the
  minimal `ChordArcBankOrientation` datum (the one genuinely-free orientation fact; see the module
  header for why it is not derivable from the bare `ChordSplitData`).

This completes the side-1 confinement modulo that single bank-orientation input. -/
theorem side₁StarConfinement_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hbank : ChordArcBankOrientation data) :
    Side₁StarConfinement data where
  edge_core := fun {e} hchord houter htail hhead =>
    edge_core_uncond data hsep hchord houter htail hhead
  oppArc_star_core := fun {w} hw d htail =>
    oppArc_star_core_direct data hsep hbank hw d htail

end ProofsInTheBook.ZinanCh35Side1Confine

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35Side1Confine.oppArc_star_core_direct
#print axioms ProofsInTheBook.ZinanCh35Side1Confine.side₁StarConfinement_holds
