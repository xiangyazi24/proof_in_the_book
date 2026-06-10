import ProofsInTheBook.ZinanCh35StarRotation
import ProofsInTheBook.ZinanCh35Confinement

/-!
# Chapter 35 discrete-Schoenflies: the star-rotation confinement package (bricks 4–7)

This file is the **confinement** layer of the discrete-Schoenflies star-rotation design
(`HANDOFF/design-rounds/ch35-schoenflies-star-rotation.md`), bricks 4–7.  It sits on top of the
purely-combinatorial vertex-star API (`ZinanCh35StarRotation.lean`, bricks 1–3) and the
region-confinement bundle (`ZinanCh35Confinement.lean`), and connects them to the actual `Iota`
residue consumers (`hreflect`/`homit`).

## What this file establishes

* **Brick 4 — side-region/star bridges (UNCONDITIONAL).**  The concrete unfolding of
  `sideRegion₁` against the landed `keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`:
  `notMem_sideRegion₁_iff` (a vertex is omitted iff *every* incident dart is deleted by side 1),
  the star-witness producers `mem_sideRegion₁_of_star_side₁` /
  `mem_sideRegion₁_of_star_outerArc₁`, and their contrapositive star-confinement consequences.

* **The sharp residual `Side₁StarConfinement` (Brick 5 lever).**  The single discrete-Schoenflies
  fact the landed material does NOT supply — the vertex-star anchoring — isolated as a *named,
  satisfiable, non-vacuous* structure with exactly two fields, the geometric cores of
  `edge_confined` and `opposite_arc_omitted`.  The INVENTORY (recorded in the report) verified
  there is no landed boundary-dart characterization placing a path₂-internal vertex's star faces
  outside `side₁`; `separates_closed` is only *face*-dual separation (`face₂ ∉ side₁`), strictly
  weaker than the *vertex-star* confinement these fields demand.  So this residual is exposed, not
  papered over.

* **Brick 5 — the master confinement.**  `vertexStar_confined_of_starConfinement` produces the
  design's `Side₁SchoenfliesConfinement` from the residual, discharging the `α`-reduction of
  `edge_confined` (the chord case + the landed `α`-closure `mem_keptSet₁_alpha_iff`) so that only
  the geometric star core is taken as input.

* **Bricks 6–7 — producers + final plug-in.**  `opposite_arc_omitted` ⟹ the concrete
  region-omission residue `∃ w, w ∉ sideRegion₁` (the `homit` content), proven FULLY via the
  landed `BoundaryPath.exists_internal_vertex`; then `chordSideResidue₁_of_schoenflies` feeds the
  package into the landed `chordSideResidue₁_of_confinement`.

## Honesty note (the residual)

`hreflect` (the region edge-confinement field of `Side₁Confinement`) is consumed *verbatim* by
`ZinanCh35Iota.sideVertexToM₁_adj_reflect_canonical` — there is no landed reduction of it, so it
remains an honest input at its exact shape.  The geometric star core of `edge_confined` and the
`opposite_arc_omitted` field are the genuine discrete-Schoenflies vertex-star anchoring, bundled
into the single `Side₁StarConfinement` residual.  Everything *around* the residual (the
`sideRegion₁` unfolding, the `α`-closure reduction, the internal-vertex extraction, the producers
and the final plug-in) is proved unconditionally and axiom-clean.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Schoenflies

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ZinanCh35Iota
open ProofsInTheBook.ZinanCh35Confinement
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]

/-! ## Brick 4 — side-region/star bridges (unfolding `sideRegion₁`)

Recall the landed definitions:

* `sideRegion₁ data = {w | ∃ d, d ∉ keptDel₁ ∧ M.tail d = w}` (`ChordReconClose.lean`),
* `d ∉ keptDel₁ ↔ d ∈ keptSet₁` (`mem_keptDel₁_iff`),
* `keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}` (`PlanarMapChordSplit.lean`),
* `sideDarts₁ = {d | M.dartFace d ∈ side₁}`,
* `outerArc₁ = {b | M.dartFace b = outerFace ∧ M.dartFace (M.α b) ∈ side₁}`.

So a vertex `w` is in the side-1 region iff some dart `d` tailed at `w`, distinct from the chord
dart, has its face in `side₁` *or* is an outer dart whose reverse face is in `side₁`. -/

/-- **Side-region membership, unfolded.**  `w ∈ sideRegion₁` exactly when `w` has an incident
dart (tail `w`) distinct from the chord dart that is *kept* by side 1: either its own face is in
`side₁` (an inner side-1 dart), or it is an outer dart whose reverse face is in `side₁` (a
boundary dart of the side-1 arc). -/
theorem mem_sideRegion₁_iff (data : hNT.ChordSplitData u v) (w : M.Vertex) :
    w ∈ sideRegion₁ data ↔
      ∃ d : D, M.tail d = w ∧ d ≠ data.dart ∧
        (M.dartFace d ∈ data.side₁ ∨
          (M.dartFace d = hNT.outerFace ∧ M.dartFace (M.α d) ∈ data.side₁)) := by
  constructor
  · rintro ⟨d, hd, htail⟩
    rw [data.mem_keptDel₁_iff] at hd
    obtain ⟨hU, hne⟩ := hd
    simp only [Set.mem_singleton_iff] at hne
    refine ⟨d, htail, hne, ?_⟩
    rcases hU with hin | hout
    · exact Or.inl hin
    · exact Or.inr ⟨hout.1, hout.2⟩
  · rintro ⟨d, htail, hne, hkept⟩
    refine ⟨d, ?_, htail⟩
    rw [data.mem_keptDel₁_iff]
    refine ⟨?_, by simp only [Set.mem_singleton_iff]; exact hne⟩
    rcases hkept with hin | hout
    · exact Or.inl hin
    · exact Or.inr hout

/-- **Side-region OMISSION, unfolded** (the form `homit` needs).  A vertex `w` is *outside* the
side-1 region exactly when *every* dart tailed at `w` is deleted by side 1: it is the chord dart,
or its face is not in `side₁` and it is not a side-1 boundary dart.  This is the vertex-star
confinement statement. -/
theorem notMem_sideRegion₁_iff (data : hNT.ChordSplitData u v) (w : M.Vertex) :
    w ∉ sideRegion₁ data ↔
      ∀ d : D, M.tail d = w →
        (d = data.dart ∨
          (M.dartFace d ∉ data.side₁ ∧
            ¬ (M.dartFace d = hNT.outerFace ∧ M.dartFace (M.α d) ∈ data.side₁))) := by
  rw [mem_sideRegion₁_iff]
  constructor
  · intro hnot d htail
    -- If `d` were a kept side-1 dart, `w` would be in the region.
    by_cases hne : d = data.dart
    · exact Or.inl hne
    · right
      refine ⟨?_, ?_⟩
      · intro hin
        exact hnot ⟨d, htail, hne, Or.inl hin⟩
      · intro hout
        exact hnot ⟨d, htail, hne, Or.inr hout⟩
  · rintro hall ⟨d, htail, hne, hkept⟩
    rcases hall d htail with hchord | ⟨hface, houter⟩
    · exact hne hchord
    · rcases hkept with hin | hout
      · exact hface hin
      · exact houter hout

/-- **Star witness ⟹ region membership (inner case).**  If `w` has a star dart `d` (tail `w`)
distinct from the chord dart whose face is in `side₁`, then `w ∈ sideRegion₁`. -/
theorem mem_sideRegion₁_of_star_side₁ (data : hNT.ChordSplitData u v) {w : M.Vertex}
    {d : D} (htail : M.tail d = w) (hne : d ≠ data.dart) (hface : M.dartFace d ∈ data.side₁) :
    w ∈ sideRegion₁ data :=
  (mem_sideRegion₁_iff data w).2 ⟨d, htail, hne, Or.inl hface⟩

/-- **Star witness ⟹ region membership (boundary case).**  If `w` has a star dart `d` (tail `w`)
distinct from the chord dart that is an outer dart whose reverse face is in `side₁`, then
`w ∈ sideRegion₁`. -/
theorem mem_sideRegion₁_of_star_outerArc₁ (data : hNT.ChordSplitData u v) {w : M.Vertex}
    {d : D} (htail : M.tail d = w) (hne : d ≠ data.dart)
    (houter : M.dartFace d = hNT.outerFace) (hrev : M.dartFace (M.α d) ∈ data.side₁) :
    w ∈ sideRegion₁ data :=
  (mem_sideRegion₁_iff data w).2 ⟨d, htail, hne, Or.inr ⟨houter, hrev⟩⟩

/-! ## The sharp residual `Side₁StarConfinement` (the discrete-Schoenflies vertex-star anchoring)

This is the **single** genuinely-open fact.  Its two fields are the geometric cores the landed
material cannot derive (verified by the file's inventory — see the report).  Each is a concrete,
non-vacuous statement about `M`'s vertex stars; together they discharge `Side₁SchoenfliesConfinement`. -/

/-- **The side-1 vertex-star anchoring residual.**  The discrete-Schoenflies confinement fact that
the landed *face*-dual separation does not supply, isolated sharply:

* `edge_core` — *region edge-confinement core*: an ambient non-chord edge `e` whose two endpoints
  are both side-1-region vertices has its own face in `side₁` (so the edge is realised by an inner
  side-1 dart).  This is the geometric content of `Side₁SchoenfliesConfinement.edge_confined` once
  the chord case and the `α`-closure reduction are peeled off.

* `oppArc_star_core` — *opposite-arc star confinement*: every dart `d` tailed at a strictly
  internal vertex `w` of the *opposite* boundary arc `path₂` is deleted by side 1 (it is the chord
  dart, or its face is outside `side₁` and it is not a side-1 boundary dart).  This is precisely
  the vertex-star-confinement form of `opposite_arc_omitted`.

Both fields are inhabited statements about the concrete map; neither is vacuous (the opposite arc
carries an internal vertex by `data.arc₂_internal`, and the region is inhabited by
`sideRegion₁_nonempty`). -/
structure Side₁StarConfinement (data : hNT.ChordSplitData u v) : Prop where
  /-- Region edge-confinement core (geometric heart of `edge_confined`). -/
  edge_core : ∀ {e : D},
    M.dartEdge e ≠ s(u, v) →
    M.tail e ∈ sideRegion₁ data →
    M.head e ∈ sideRegion₁ data →
      M.dartFace e ∈ data.side₁
  /-- Opposite-arc vertex-star confinement (geometric heart of `opposite_arc_omitted`). -/
  oppArc_star_core : ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices →
    ∀ d : D, M.tail d = w →
      (d = data.dart ∨
        (M.dartFace d ∉ data.side₁ ∧
          ¬ (M.dartFace d = hNT.outerFace ∧ M.dartFace (M.α d) ∈ data.side₁)))

/-! ## Brick 5 — the master confinement package

From `Side₁StarConfinement` we discharge the design's `Side₁SchoenfliesConfinement`
(`edge_confined` + `opposite_arc_omitted`).  The `edge_confined` derivation does the genuine
*reduction* work: the chord case is the right disjunct, and on a non-chord edge the landed
`α`-closure `mem_keptSet₁_alpha_iff` collapses `e ∉ keptDel₁ ∧ α e ∉ keptDel₁` to `e ∈ keptSet₁`,
which follows from `edge_core` (`dartFace e ∈ side₁` puts `e ∈ sideDarts₁ ⊆ keptSet₁`). -/

/-- **The design's master confinement structure (design §2).**  `edge_confined` and
`opposite_arc_omitted` in the exact shapes the `hreflect`/`homit` producers consume. -/
structure Side₁SchoenfliesConfinement (data : hNT.ChordSplitData u v) : Prop where
  /-- Any ambient edge whose two endpoints are in the side-1 vertex region is either represented
  in the side-1 carve (both `e` and `α e` kept) or is the chord. -/
  edge_confined : ∀ {e : D},
    M.tail e ∈ sideRegion₁ data →
    M.head e ∈ sideRegion₁ data →
      ((e ∉ data.keptDel₁ ∧ M.α e ∉ data.keptDel₁) ∨ M.dartEdge e = s(u, v))
  /-- A strict internal vertex of the opposite boundary arc is omitted by side 1. -/
  opposite_arc_omitted : ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices → w ∉ sideRegion₁ data

/-- **The chord dart's edge is `s(u, v)`.**  Bookkeeping for the chord case of `edge_confined`. -/
lemma dart_edge (data : hNT.ChordSplitData u v) : M.dartEdge data.dart = s(u, v) :=
  hNT.chordDart_edge data.chord

/-- **Master confinement from the star residual (Brick 5).**  Produces the design's
`Side₁SchoenfliesConfinement` from `Side₁StarConfinement`, performing the `edge_confined`
`α`-reduction with the landed `Separates`-conditional `α`-closure. -/
theorem vertexStar_confined_of_starConfinement (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (conf : Side₁StarConfinement data) :
    Side₁SchoenfliesConfinement data where
  edge_confined := by
    intro e htail hhead
    by_cases hchord : M.dartEdge e = s(u, v)
    · exact Or.inr hchord
    · -- non-chord: `edge_core` gives `dartFace e ∈ side₁`, hence `e ∈ keptSet₁`; close under `α`.
      left
      have hface : M.dartFace e ∈ data.side₁ := conf.edge_core hchord htail hhead
      -- `e ≠ dart` (else `dartEdge e = dartEdge dart = s(u,v)`).
      have hne : e ≠ data.dart := by
        intro h; exact hchord (by rw [h]; exact dart_edge data)
      -- `e ∈ sideDarts₁ ⊆ keptSet₁` (it is an inner side-1 dart, and `e ≠ dart`).
      have hkept : e ∈ data.keptSet₁ := by
        refine ⟨Or.inl hface, ?_⟩
        simp only [Set.mem_singleton_iff]; exact hne
      refine ⟨?_, ?_⟩
      · rw [data.mem_keptDel₁_iff]; exact hkept
      · rw [data.mem_keptDel₁_iff]
        exact (data.mem_keptSet₁_alpha_iff hsep e).2 hkept
  opposite_arc_omitted := by
    intro w hw
    rw [notMem_sideRegion₁_iff]
    exact conf.oppArc_star_core hw

/-! ## Bricks 6–7 — residue producers + final plug-in

`opposite_arc_omitted` produces the concrete `homit` content `∃ w, w ∉ sideRegion₁` (the
strict-decrease fuel) FULLY, by extracting a strictly-internal vertex of the opposite arc with the
landed `BoundaryPath.exists_internal_vertex` and the stored `data.arc₂_internal`.

`hreflect` (the region edge-confinement field consumed verbatim by `Iota`) is taken as an honest
input at its exact landed shape — there is no landed reduction of it (see the module note). -/

/-- **`homit` from the master confinement (Brick 6).**  The opposite boundary arc has an internal
vertex (by `data.arc₂_internal`); that vertex is omitted by side 1 (by `opposite_arc_omitted`), so
it witnesses the concrete region-omission residue `∃ w, w ∉ sideRegion₁`. -/
theorem homit_region_of_schoenflies (data : hNT.ChordSplitData u v)
    (H : Side₁SchoenfliesConfinement data) :
    ∃ w : M.Vertex, w ∉ sideRegion₁ data := by
  -- `arc₂_internal : path₂.HasInternalVertex`, i.e. `path₂.internalVertices ≠ []`.
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ data.arc₂_internal
  exact ⟨w, H.opposite_arc_omitted hw⟩

/-- **`homit` (the `Set.range` form) from the master confinement.**  Transports
`homit_region_of_schoenflies` through the landed equivalence
`homit_iff_exists_notMem_sideRegion₁`. -/
theorem homit_of_schoenflies (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (H : Side₁SchoenfliesConfinement data) :
    ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne) :=
  (homit_iff_exists_notMem_sideRegion₁ data hsep a₀ a₁ hne).2
    (homit_region_of_schoenflies data H)

/-- **The full side-1 confinement bundle from the star residual.**  Assembles the landed
`Side₁Confinement` (the object `chordSideResidue₁_of_confinement` consumes) from the discrete-
Schoenflies star residual plus the honest `hreflect` input. -/
theorem side₁Confinement_of_starConfinement (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (conf : Side₁StarConfinement data)
    (hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y) :
    Side₁Confinement data hsep a₀ a₁ hne :=
  side₁Confinement_of_notMem_sideRegion₁ data hsep a₀ a₁ hne hreflect
    (homit_region_of_schoenflies data
      (vertexStar_confined_of_starConfinement data hsep conf))

/-- **Brick 7 — the final Ch35 plug-in.**  Feeds the star-confinement-derived `Side₁Confinement`
into the landed `chordSideResidue₁_of_confinement`, producing the full `ChordSideResidue`.  The
non-confinement inputs (`ci`/`hshare`/`hchord`/`hLₛ`) and the honest `hreflect` stay as inputs;
the genuine discrete-Schoenflies content is exactly `conf : Side₁StarConfinement`. -/
def chordSideResidue₁_of_schoenflies (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (ci : ContiguousInterval data hsep a₀ a₁ hne)
    (hshare : ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace data hsep a₀ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (pₛ qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y)
    (conf : Side₁StarConfinement data) :
    ChordSideResidue data hsep a₀ a₁ hne L :=
  chordSideResidue₁_of_confinement data hsep a₀ a₁ hne L ci hshare hchord pₛ qₛ cpₛ cqₛ hLₛ
    (side₁Confinement_of_starConfinement data hsep a₀ a₁ hne conf hreflect)

end ProofsInTheBook.ZinanCh35Schoenflies

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35Schoenflies.mem_sideRegion₁_iff
#print axioms ProofsInTheBook.ZinanCh35Schoenflies.notMem_sideRegion₁_iff
#print axioms ProofsInTheBook.ZinanCh35Schoenflies.mem_sideRegion₁_of_star_side₁
#print axioms ProofsInTheBook.ZinanCh35Schoenflies.vertexStar_confined_of_starConfinement
#print axioms ProofsInTheBook.ZinanCh35Schoenflies.homit_region_of_schoenflies
#print axioms ProofsInTheBook.ZinanCh35Schoenflies.side₁Confinement_of_starConfinement
#print axioms ProofsInTheBook.ZinanCh35Schoenflies.chordSideResidue₁_of_schoenflies
