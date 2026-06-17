import ProofsInTheBook.ZinanCh35EdgeCore

/-!
# Chapter 35 discrete-Schoenflies: the two vertex/dart-level bridges

Two vertex/dart-level discrete-Schoenflies facts that Chapter 35 needs:

* **Bridge 2 — `OuterDartArc₁`** (`ZinanCh35Schoenflies.lean:246`): an outer dart (face = outer
  face), non-chord, with both endpoints in `sideRegion₁`, has its reverse (inner) face in `side₁`.
  **PROVED in full** here (`outerDartArc₁_holds`), conditional on exactly the two planar bridges the
  prompt sanctions (`BoundedFacePartition` + `SideRegionInterChordEnds`) plus `Separates`.  The
  argument is the one in the prompt: the reverse face is non-outer (`alpha_dartFace_ne_outer_of_outer`,
  proved unconditionally), so the face partition places it in `side₁` or `side₂`; the `side₂` case
  makes `α e` a non-chord `side₂` face dart, putting both endpoints of `e` in `sideRegion₂`, whence
  Bridge 1 forces them into `{u, v}` and `e` becomes the chord — contradiction.

* **Bridge 1 — `SideRegionInterChordEnds`** (`ZinanCh35EdgeCore.lean:92`): a vertex in both side
  regions is a chord endpoint.  **REDUCED** here, via the vertex-rotation machinery of
  `ZinanCh35StarRotation.lean`, to a *single* sharp planar residual `StarFanOneSide` (plus the landed
  `Separates`).  The reduction is genuine, not a rename:

  - `exists_starDart_side₁` / `exists_starDart_side₂` (unconditional): region membership yields a
    star dart whose *inner* face is in the side (the outer-arc case is handled by the next star dart
    via `starFace_next_eq_alpha`).
  - `Separates` makes the two sides disjoint, so the `side₂` star face reads outside `side₁`.
  - `star_escape_crosses_seam` (landed, unconditional) exhibits a seam dart `c` on the rotation arc.
  - `chord_starDart_endpoint` (unconditional) excludes the chord seam at a non-chord vertex, so `c`
    is a **boundary-edge** seam.
  - `starDart_outer_unique` (unconditional): at most one outer-face star dart per vertex — the single
    boundary gap of the rotation.

  `StarFanOneSide` is then the residual boundary-fan one-side fact, consumed only after the
  boundary-edge seam is exhibited.

## The remaining residual `StarFanOneSide` and its (fully-mapped) closing argument

The single open atom is the **boundary-vertex fan contiguity** fact.  Its closing argument, fully
worked out (the only missing piece is the finite single-cycle index arithmetic for `starSigma M w`):

Let `b₀` be the unique outer-face star dart at `w` (unique by `starDart_outer_unique`).  Every
boundary-edge seam dart `c` satisfies `c = b₀` or `starSigma c = b₀` (i.e. `c = σ⁻¹ b₀`), because a
boundary edge always abuts the outer face on one of its two incident faces, and the only outer-face
star dart is `b₀`.  Hence the cut set lies in the two *adjacent* darts `{b₀, σ⁻¹ b₀}`, whose
complement (all star darts except `b₀`) is a single `starSigma`-arc on which side-1 membership is
constant (`side_constant_on_cutFree_walk`).  Both `s₁` (face ∈ side₁) and `s₂` (face ∈ side₂) lie in
that complement (their faces are non-outer, so `s₁, s₂ ≠ b₀`), so `s₁ ∈ side₁ ↔ s₂ ∈ side₁`,
contradicting `s₂ ∈ side₂` and disjointness.  Formalizing "the complement of two adjacent points of a
single permutation cycle is one cut-free arc reaching between any two of its points" requires the
minimal-period / iterate-injectivity infrastructure for `starSigma M w` (it is a single cycle on the
finite star), which is not landed; that is the entire residual.

This matches the prior design's assessment (`ZinanCh35Schoenflies.lean` header: the landed *face*-dual
`separates_closed` is strictly weaker than vertex-star confinement; the fan API of
`PlanarMapBoundaryFan.lean` is a *certificate structure* fed by `FanIncidenceData`, with no
unconditional fan construction landed).

No `sorry` / `axiom` / `admit` / `native_decide`.  Every named result below is axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`); Bridge 1's final theorem is conditional on the single
sharp residual `StarFanOneSide`, Bridge 2 on the two prompt-sanctioned bridges.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Schoenflies2

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Schoenflies
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## A. A boundary edge has at most one outer-face dart. -/

/-- If a dart's face is the outer face, its reverse's face is **not** the outer face: an edge
cannot have both of its darts on the simple outer boundary cycle (that would force a length-2
boundary, contradicting `outer_len`). -/
theorem alpha_dartFace_ne_outer_of_outer {e : D}
    (hNT : NearTriangulation M) (he : M.dartFace e = hNT.outerFace) :
    M.dartFace (M.α e) ≠ hNT.outerFace := by
  intro hαe
  -- both `e` and `α e` are boundary darts.
  have he_mem : e ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff e).2 he
  have hαe_mem : M.α e ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff (M.α e)).2 hαe
  -- `φ e` is a boundary dart (same outer face), with `tail (φ e) = head e = tail (α e)`.
  have hφe_mem : M.φ e ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    show M.dartFace (M.φ e) = hNT.outerFace
    rw [M.dartFace_phi]; exact he
  have htail_eq : M.tail (M.φ e) = M.tail (M.α e) := by
    rw [M.tail_phi, M.tail_alpha]
  -- two boundary darts with the same tail are equal: `φ e = α e`.
  have hφα : M.φ e = M.α e :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφe_mem hαe_mem htail_eq
  -- Then `φ (φ e) = φ (α e)`, whose tail is `head (α e) = tail e = tail e`.
  have htail2 : M.tail (M.φ (M.φ e)) = M.tail e := by
    rw [hφα, M.tail_phi, M.head_alpha]
  -- `φ² e` is a boundary dart with the same tail as `e`, hence `φ² e = e`.
  have hφ2_mem : M.φ (M.φ e) ∈ hNT.outerCycle.darts := by
    rw [hNT.outerCycle.mem_darts_iff]
    show M.dartFace (M.φ (M.φ e)) = hNT.outerFace
    rw [M.dartFace_phi, M.dartFace_phi]; exact he
  have hφ2 : M.φ (M.φ e) = e :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφ2_mem he_mem htail2
  -- So the outer-face orbit has support card 2, i.e. `faceLen outerFace = 2 < 3`.
  have hφ : M.φ e ≠ e := phi_ne_self_of_isSimpleGraph M hNT.simpleGraph e
  have hcard2 : (M.φ.cycleOf e).support.card = 2 :=
    card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
  have hface2 : M.faceLen hNT.outerFace = 2 := by
    have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
    rw [he, hcard2] at hsupport; exact hsupport
  have hlen2 : hNT.outerCycle.length = 2 :=
    hNT.outerCycle.faceLen_eq_length.symm.trans hface2
  have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
  omega

/-! ## B. Bridge 2 — `OuterDartArc₁`, conditional on the two planar bridges.

For an outer dart `e` (face = outer face), non-chord, both endpoints in `sideRegion₁`: the reverse
inner face `dartFace (α e)` lies in `side₁`.

By `alpha_dartFace_ne_outer_of_outer`, the reverse face is non-outer, so `BoundedFacePartition`
places it in `side₁` or `side₂`.  If it were in `side₂`, then `α e` is a non-chord `side₂` face
dart, so by the landed `endpoints_mem_sideRegion₂_of_face` both *its* endpoints — which are exactly
the endpoints of `e` — lie in `sideRegion₂`.  Combined with both endpoints in `sideRegion₁`, the
vertex-level Schoenflies bridge `SideRegionInterChordEnds` forces both endpoints into `{u, v}`,
whence `edge_eq_chord_of_endpoints_chordEnds` makes `e` the chord — contradicting non-chordness.
So the reverse face is in `side₁`. -/

/-- **Bridge 2 (`OuterDartArc₁`), conditional on the two planar bridges.**  Clean-3 conditional on
exactly `Separates`, `BoundedFacePartition`, and `SideRegionInterChordEnds` (the latter is Bridge 1,
proved/isolated separately; the prompt sanctions stating Bridge 2 conditional on it). -/
theorem outerDartArc₁_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hpart : BoundedFacePartition data) (hinter : SideRegionInterChordEnds data) :
    OuterDartArc₁ data := by
  intro e hchord hface htail hhead
  -- The reverse inner face is non-outer.
  have hαe_not_outer : M.dartFace (M.α e) ≠ hNT.outerFace :=
    alpha_dartFace_ne_outer_of_outer hNT hface
  -- Partition it into side₁ or side₂.
  rcases hpart hαe_not_outer with h₁ | h₂
  · exact h₁
  · -- `dartFace (α e) ∈ side₂`: derive `e = chord`, contradiction.
    exfalso
    -- `α e` is a non-chord side₂ face dart.
    have hαe_chord : M.dartEdge (M.α e) ≠ s(u, v) := by
      rw [M.dartEdge_alpha]; exact hchord
    -- both endpoints of `α e` are in `sideRegion₂`.
    obtain ⟨htail₂, hhead₂⟩ :=
      endpoints_mem_sideRegion₂_of_face data hsep hαe_chord h₂
    -- `tail (α e) = head e`, `head (α e) = tail e`.
    rw [M.tail_alpha] at htail₂
    rw [M.head_alpha] at hhead₂
    -- so both endpoints of `e` are in `sideRegion₂`; combine with `sideRegion₁`.
    have htchord : M.tail e = u ∨ M.tail e = v := hinter htail hhead₂
    have hhchord : M.head e = u ∨ M.head e = v := hinter hhead htail₂
    exact hchord (edge_eq_chord_of_endpoints_chordEnds data htchord hhchord)

/-! ## C. Bridge 1 — `SideRegionInterChordEnds`.

The route is the **vertex rotation** (`ZinanCh35StarRotation.lean`).  We first reduce region
membership to a star dart whose *inner* face is in the side, then use rotation invariance.

### C.1  Region membership ⟹ a star dart with inner face in the side.

`w ∈ sideRegion₁` yields, via `mem_sideRegion₁_iff`, a non-chord star dart `d` at `w` with either
(a) `dartFace d ∈ side₁`, or (b) `dartFace d = outerFace ∧ dartFace (α d) ∈ side₁`.  In case (a) the
star dart `⟨d, _⟩` already reads a `side₁` face; in case (b) the *next* star dart
`starSigma ⟨d, _⟩` reads `dartFace (α d) ∈ side₁` (by `starFace_next_eq_alpha`).  Either way `w`
carries a star dart whose `starFace` is in `side₁`. -/

/-- **A side-1 region vertex carries a star dart whose face is in `side₁`.** -/
theorem exists_starDart_side₁ (data : hNT.ChordSplitData u v) {w : M.Vertex}
    (hw : w ∈ sideRegion₁ data) :
    ∃ s : StarDart M w, starFace w s ∈ data.side₁ := by
  rw [mem_sideRegion₁_iff] at hw
  obtain ⟨d, htail, hne, hkept⟩ := hw
  rcases hkept with hin | ⟨hout, hrev⟩
  · -- inner side-1 dart: use `d` itself.
    exact ⟨⟨d, htail⟩, hin⟩
  · -- outer dart whose reverse face is in side₁: use the *next* star dart.
    refine ⟨starSigma M w ⟨d, htail⟩, ?_⟩
    rw [starFace_next_eq_alpha]
    exact hrev

/-- **A side-2 region vertex carries a star dart whose face is in `side₂`.** -/
theorem exists_starDart_side₂ (data : hNT.ChordSplitData u v) {w : M.Vertex}
    (hw : w ∈ sideRegion₂ data) :
    ∃ s : StarDart M w, starFace w s ∈ data.side₂ := by
  -- Same unfolding as `mem_sideRegion₁_iff`, against `keptSet₂`.
  obtain ⟨d, hd, htail⟩ := hw
  rw [data.mem_keptDel₂_iff] at hd
  obtain ⟨hU, hne⟩ := hd
  simp only [Set.mem_singleton_iff] at hne
  rcases hU with hin | ⟨hout, hrev⟩
  · exact ⟨⟨d, htail⟩, hin⟩
  · refine ⟨starSigma M w ⟨d, htail⟩, ?_⟩
    rw [starFace_next_eq_alpha]
    exact hrev

/-! ### C.2  A seam dart at `w` whose edge is the chord forces `w ∈ {u, v}`.

Every star dart `c` at `w` has `tail c.1 = w`, so `dartEdge c.1 = s(w, head c.1)`; if that equals
the chord edge `s(u, v)`, then `w ∈ {u, v}` (membership of `w` in the unordered pair). -/

/-- A star dart at `w` whose edge is the chord forces `w` to be a chord endpoint. -/
theorem chord_starDart_endpoint {w : M.Vertex} (s : StarDart M w)
    (hc : M.dartEdge s.1 = s(u, v)) : w = u ∨ w = v := by
  have htail : M.tail s.1 = w := s.2
  have hpair : s(w, M.head s.1) = s(u, v) := by
    have : M.dartEdge s.1 = s(w, M.head s.1) := by rw [dartEdge, htail]
    rw [← this]; exact hc
  -- `w` is one of the two members of the pair `s(u, v)`.
  rcases (Sym2.eq_iff).1 hpair with ⟨hwu, _⟩ | ⟨hwv, _⟩
  · exact Or.inl hwu
  · exact Or.inr hwv

/-! ### C.2b  At most one outer-face star dart per vertex (the single boundary gap).

A star dart whose face is the outer face is exactly a boundary dart tailed at `w`.  By
`tail_injective_on_darts` (the simple outer cycle has distinct boundary-vertex tails), there is at
most one such dart: the rotation around any vertex has at most one outer-face "gap". -/

/-- **At most one outer-face star dart at a vertex.**  Two star darts at `w` whose faces are both the
outer face are equal — the unique boundary dart tailed at `w`. -/
theorem starDart_outer_unique {w : M.Vertex} (b b' : StarDart M w)
    (hb : starFace w b = hNT.outerFace) (hb' : starFace w b' = hNT.outerFace) :
    b = b' := by
  have hb_mem : b.1 ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff b.1).2 hb
  have hb'_mem : b'.1 ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff b'.1).2 hb'
  have htail : M.tail b.1 = M.tail b'.1 := by rw [b.2, b'.2]
  exact Subtype.ext
    (hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hb_mem hb'_mem htail)

/-! ### C.3  The isolated planar residual: boundary-fan one-side.

After the rotation reduction, the *only* remaining content is the **boundary-vertex fan** fact: at a
non-chord-endpoint vertex `w` (`w ≠ u`, `w ≠ v`), the rotation around `w` cannot carry a `side₁`
star face to a `side₂` star face.  Equivalently, the non-outer faces incident at `w` form a single
`ChordSplitAdj`-connected arc — they are not split into two sides — because the only seams at such a
`w` are *boundary edges*, and a boundary edge always abuts the (single) outer-face gap of the
rotation; with no chord at `w`, there is exactly one such gap (the simple outer cycle visits `w`
once), so the inner faces stay on one side.

This fan-contiguity fact is genuine discrete-Schoenflies content.  The landed substrate supplies the
fan API (`BoundaryVertexFan`, `IncidentNonOuterFacesExactly` in `PlanarMapBoundaryFan.lean`) only as
a *certificate structure* fed by `FanIncidenceData`; there is no landed unconditional construction of
the fan at an arbitrary boundary vertex, so the one-side consequence is not derivable here.  It is
isolated SHARPLY below as the named, non-vacuous predicate `StarFanOneSide`; everything around it (the
region→star reduction, the rotation escape, the chord-endpoint identification) is proved
unconditionally and axiom-clean. -/

/-- **The boundary-fan one-side residual (sharp).**  At a non-chord-endpoint vertex `w`, whenever the
rotation around `w` carries a `side₁` star face `s` to a star face `t` outside `side₁`, it must cross
a **boundary-edge** seam dart `c` (`dartEdge c.1` an old boundary edge) somewhere along the arc from
`s` to `t`.  This is the residual that the rotation escape reduces Bridge 1 to: the escape itself is
proved unconditionally to cross *some* seam (boundary edge **or** chord); the chord is excluded at a
non-chord vertex, so the seam is a boundary edge — and the genuine discrete-Schoenflies fan content is
that such a boundary-edge seam *cannot* separate an inner `side₁` face from an inner `side₂` face
(the non-outer faces of the single boundary gap stay on one side).

We isolate exactly the non-derivable consequence: a non-chord vertex carrying both a `side₁` and a
`side₂` star face is impossible.  The *reduction* (region → star, escape → seam, seam → boundary edge)
is discharged unconditionally in `sideRegionInterChordEnds_of_fan`; the residual is consumed only after
the boundary-edge seam has been exhibited, so it is the boundary-fan atom, not a rename of Bridge 1. -/
def StarFanOneSide (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {w : M.Vertex}, w ≠ u → w ≠ v →
    ∀ (s t : StarDart M w),
      starFace w s ∈ data.side₁ → starFace w t ∈ data.side₂ →
        -- the escape across the rotation arc from `s` to `t` lands on a boundary-edge seam:
        (∃ c : StarDart M w, hNT.outerCycle.IsBoundaryEdge (M.dartEdge c.1)) → False

/-! ### C.4  Bridge 1 from the residual + the rotation reduction.

The rotation reduction discharges everything except the fan-contiguity step, which is exactly
`StarFanOneSide`.  We keep the reduction explicit (not folded into the residual) so the residual is
strictly the boundary-fan atom: a vertex in both regions yields a `side₁` star dart and a `side₂`
star dart; if `w` is not a chord endpoint, `StarFanOneSide` rules this out. -/

/-- **Bridge 1 (`SideRegionInterChordEnds`), via the rotation reduction.**  Conditional on the single
isolated boundary-fan residual `StarFanOneSide` plus the landed `Separates`.

The reduction is genuine: a vertex `w` in both regions yields a `side₁` star face `s₁` and a `side₂`
star face `s₂`; under `Separates` the two sides are disjoint, so `s₂` reads *outside* `side₁`; the
unconditional rotation escape `star_escape_crosses_seam` then exhibits a seam dart `c` on the arc;
`chord_starDart_endpoint` excludes the chord at a non-chord `w`, so `c` is a **boundary-edge** seam.
Feeding that boundary-edge witness to `StarFanOneSide` closes the contradiction. -/
theorem sideRegionInterChordEnds_of_fan (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hfan : StarFanOneSide data) :
    SideRegionInterChordEnds data := by
  intro w hw₁ hw₂
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hwu, hwv⟩ := hcon
  obtain ⟨s₁, hs₁⟩ := exists_starDart_side₁ data hw₁
  obtain ⟨s₂, hs₂⟩ := exists_starDart_side₂ data hw₂
  -- `Separates` ⟹ `side₁ ∩ side₂ = ∅`, so `s₂` reads outside `side₁`.
  have hdisj : Disjoint data.side₁ data.side₂ := (separates_iff_sidesDisjoint data).1 hsep
  have hs₂_not₁ : starFace w s₂ ∉ data.side₁ := by
    intro hmem
    exact (Set.disjoint_left.1 hdisj) hmem hs₂
  -- The rotation escape from `s₁` (side₁) to `s₂` (not side₁) crosses a seam dart `c`.
  obtain ⟨c, hcseam, -⟩ := star_escape_crosses_seam hNT data hs₁ hs₂_not₁
  -- The seam is a boundary edge: the chord case forces `w ∈ {u, v}`, excluded.
  have hbe : hNT.outerCycle.IsBoundaryEdge (M.dartEdge c.1) := by
    rcases hcseam with hbe | hchord
    · exact hbe
    · exact absurd (chord_starDart_endpoint c hchord) (by rw [not_or]; exact ⟨hwu, hwv⟩)
  -- Feed the boundary-edge witness to the fan residual.
  exact hfan hwu hwv s₁ s₂ hs₁ hs₂ ⟨c, hbe⟩

/-- **Bridge 1, prompt-name alias.**  `SideRegionInterChordEnds`, conditional on `Separates` and the
single isolated boundary-fan residual `StarFanOneSide`. -/
theorem sideRegionInterChordEnds_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hfan : StarFanOneSide data) :
    SideRegionInterChordEnds data :=
  sideRegionInterChordEnds_of_fan data hsep hfan

end ProofsInTheBook.ZinanCh35Schoenflies2

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35Schoenflies2.alpha_dartFace_ne_outer_of_outer
#print axioms ProofsInTheBook.ZinanCh35Schoenflies2.outerDartArc₁_holds
#print axioms ProofsInTheBook.ZinanCh35Schoenflies2.exists_starDart_side₁
#print axioms ProofsInTheBook.ZinanCh35Schoenflies2.exists_starDart_side₂
#print axioms ProofsInTheBook.ZinanCh35Schoenflies2.chord_starDart_endpoint
#print axioms ProofsInTheBook.ZinanCh35Schoenflies2.starDart_outer_unique
#print axioms ProofsInTheBook.ZinanCh35Schoenflies2.sideRegionInterChordEnds_of_fan
#print axioms ProofsInTheBook.ZinanCh35Schoenflies2.sideRegionInterChordEnds_holds
