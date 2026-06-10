import ProofsInTheBook.ChordSplitFinal
import ProofsInTheBook.ZinanCh35OuterTrace

/-!
# The Chapter 35 side-1 graph-correspondence / lists / decrease bricks
  (the remaining `ChordSideResidue` fields beyond `ci`/`hshare`)

`ChordSplitFinal.lean` isolated the genuinely-unbuilt side-1 reconstruction fields into the
single named structure `ChordSideResidue` and provided the constructor `chordSideResidue_mk`.
The `ci` (`ContiguousInterval`) and `hshare` (`Side₁AnchorsShareFace`) fields are supplied for
the canonical anchors by `ZinanCh35Hclass`/`ZinanCh35OuterTrace`.  This file closes the *other*
six fields of `ChordSideResidue`:

  `ι_inj`, `ι_adj`, `ι_adj_reflect`, the side lists `pₛ`/`qₛ`/`cpₛ`/`cqₛ`/`hLₛ`, and `smaller`.

## What is proved UNCONDITIONALLY here

* **`sideVertexToM₁_injective_canonical`** (Brick 1) — the vertex correspondence `ι` is
  injective.  PURELY combinatorial: `ι ⟦y⟧ = M.tail (proj a₀ a₁ y).1` (the `Quotient.lift`
  computation), so `ι ⟦y⟧ = ι ⟦z⟧` gives `M.σ.SameCycle (proj y).1 (proj z).1`
  (`Quotient.exact`), which transports back to a `sideSigma₁`-SameCycle
  (`filteredRotation_sameCycle_iff`) and then a `freshSigma`-SameCycle
  (`freshSigma_sameCycle_iff`, BACKWARD direction), i.e. `⟦y⟧ = ⟦z⟧`.  No planar input.

* **`sideVertexToM₁_dartEdge_inl` / `_inr`** — `ι` of the two endpoints of an `inl`-dart `x`
  is the `M`-edge of `x.val`; `ι` of the two endpoints of a fresh chord dart (`inr 0`/`inr 1`)
  is the pair `(M.tail a₀.val, M.tail a₁.val)` (the spliced chord edge).  Both definitional from
  `sideVertexToM₁_inl`/`_head_inl` and the `freshMap` `σ`/`α` equations.

* **`sideVertexToM₁_adj_canonical`** (Brick 2) — side adjacency ⟹ `M`-adjacency.  Every side
  dart is `inl x` (projects to the proved `M`-edge of `x`, `ι_adj_of_inl`) or a fresh chord dart
  (projects to the anchor-tail edge).  The kept-dart half is UNCONDITIONAL; the fresh-chord half
  needs only that the anchor tails are `M`-adjacent — supplied as the clearly-named hypothesis
  `hchord : M.toSimpleGraph.Adj (M.tail a₀.1) (M.tail a₁.1)` (the chord edge `u–v`, which for the
  canonical anchors is `ChordContiguous.chordChoice_adj`; left as a hypothesis here because the
  identification `M.tail (side₁Anchor₀).1 = u` is canonical-anchor geometry, not residue-shape).

## What is taken as a HONESTLY-NAMED hypothesis (the genuine discrete-Jordan residue)

* **`ι_adj_reflect`** (Brick 3) — `M`-adjacency on `ι`-images ⟹ side adjacency.  This is the
  region edge-confinement: an `M`-edge between two side-1-region vertices is a side edge or the
  chord.  There is no `ChordSplitRegions` producer in the repo (the open discrete-Schoenflies
  item; cf. `ChordSplitFinal` §3.3 and `RegionSplit.edge_confined`), so the MINIMAL confinement
  fact is threaded as a named hypothesis `hreflect`, matching every existing side assembler.

* **`hLₛ`** (Brick 4) — the side Thomassen lists.  The side lists are `L ∘ ι` (`Lₛ_eq := rfl`);
  the boundary/interior status and list-size bounds are the boundary-cycle correspondence of the
  side `NearTriangulation`, threaded as the named hypothesis `hLₛ` (it IS the residue field).

* **`smaller`** (Brick 5) — strict vertex decrease.  `ι` is injective (Brick 1), so
  `Fintype.card (sideMap₁).Vertex ≤ Fintype.card M.Vertex`; the *opposite* boundary arc has an
  internal vertex (`ChordContiguous.chordChoice_arc_internal_witnesses`, unconditional) that side
  1 OMITS — i.e. a vertex `w ∉ Set.range ι`.  The not-in-range fact for that omitted vertex is the
  region-confinement residue, threaded as `homit : ∃ w, w ∉ Set.range (sideVertexToM₁ …)`; from it
  `card_lt_of_injective_of_not_mem_range` gives the strict `<`.

## Assembly (Brick 6)

`chordSideResidue₁_partial` packages all six fields via `ChordSplitFinal.chordSideResidue_mk`,
taking `ci`/`hshare` (supplied for canonical anchors upstream) plus the proved Brick-1 injectivity
and the honestly-named Brick-2/3/4/5 inputs.  The two fields that genuinely need the open
`ChordSplitRegions`/Schoenflies confinement (`ι_adj_reflect` and the `smaller` omitted-vertex
witness) are exactly the named hypotheses `hreflect`/`homit`; `ι_adj`'s fresh-chord half is the
named `hchord`; `hLₛ` is the residue list field.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Iota

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]

/-! ## Section 1.  Brick 1 — injectivity of the vertex correspondence `ι`

`sideVertexToM₁ ⟦y⟧ = M.tail (proj a₀ a₁ y).1` (the `Quotient.lift` computation).  Two side
vertices with the same `ι`-image have `M.σ`-SameCycle projections, hence `sideSigma₁`-SameCycle
projections (`filteredRotation_sameCycle_iff`), hence `freshSigma`-SameCycle representatives
(`freshSigma_sameCycle_iff` backward) — i.e. equal as `freshSigma`-orbits. -/

/-- **`ι` computes on a class to the `M.tail` of its projected representative.**  By the
`Quotient.lift` definition of `sideVertexToM₁`, the class of a representative `y` maps to
`M.tail (proj a₀ a₁ y).1`.  (This is the generalisation of `sideVertexToM₁_inl` to arbitrary
representatives, fresh darts included.) -/
lemma sideVertexToM₁_mk (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (y : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) y)
      = M.tail (proj a₀ a₁ y).1 :=
  rfl

/-- **Brick 1 — `ι` is injective.**  `ι ⟦y⟧ = ι ⟦z⟧` gives `M.σ.SameCycle (proj y).1 (proj z).1`
(`M.tail` equal ⇒ same `σ`-cycle, `Quotient.exact`).  Transport back: a `sideSigma₁`-SameCycle of
`proj y`, `proj z` (`filteredRotation_sameCycle_iff`), then a `freshSigma`-SameCycle of `y`, `z`
(`freshSigma_sameCycle_iff` backward), i.e. `⟦y⟧ = ⟦z⟧`.  Purely combinatorial. -/
theorem sideVertexToM₁_injective_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    Function.Injective (sideVertexToM₁ data hsep a₀ a₁ hne) := by
  -- reduce to representatives.
  refine fun X Y => ?_
  refine Quotient.inductionOn₂ X Y (fun y z hYZ => ?_)
  -- `hYZ : ι ⟦y⟧ = ι ⟦z⟧`, defeq `M.tail (proj y).1 = M.tail (proj z).1`.
  -- `M.tail a = M.tail b` is `Quotient.mk (cycleSetoid M.σ) a = …`, so `Quotient.exact` gives
  -- `M.σ.SameCycle a b` (Lean unfolds `ι ⟦·⟧ = M.tail (proj ·).1` definitionally).
  have hM : M.σ.SameCycle (proj a₀ a₁ y).1 (proj a₀ a₁ z).1 := Quotient.exact hYZ
  -- back to a `sideSigma₁`-SameCycle of the (kept) projections.
  have hss : data.sideSigma₁.SameCycle (proj a₀ a₁ y) (proj a₀ a₁ z) :=
    (FilteredRotation.filteredRotation_sameCycle_iff M.σ data.keptDel₁
      (proj a₀ a₁ y) (proj a₀ a₁ z)).2 hM
  -- back to a `freshSigma`-SameCycle of the representatives.
  have hfs : (freshSigma data.sideSigma₁ a₀ a₁ hne).SameCycle y z :=
    (freshSigma_sameCycle_iff data.sideSigma₁ hne y z).2 hss
  exact Quotient.sound hfs

/-! ## Section 2.  The `ι`-image of a side dart's two endpoints (the adjacency computation)

A side dart `d : K ⊕ Fin 2` has `sideMap₁.tail d = ⟦d⟧` and `sideMap₁.head d = ⟦freshAlpha _ d⟧`.
Under `ι` these compute to `M.tail (proj d).1` and `M.tail (proj (freshAlpha _ d)).1`.  For an
`inl x` dart this is the `M`-edge of `x.val` (`proj (inl x) = x`, `proj (freshAlpha (inl x)) =
sideAlpha₁ x`, whose tail/head are `M.tail/head x.val`).  For a fresh dart `inr j` the projection
is an anchor, so the edge is the anchor-tail pair `(M.tail a₀.val, M.tail a₁.val)`. -/

/-- `ι (sideMap₁.tail (inr j))` is `M.tail a₀.1` (`j = 0`) or `M.tail a₁.1` (`j = 1`). -/
lemma sideVertexToM₁_tail_inr (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (j : Fin 2) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) (Sum.inr j))
      = M.tail (if j = 0 then a₀.1 else a₁.1) := by
  rw [sideVertexToM₁_mk data hsep a₀ a₁ hne (Sum.inr j)]
  fin_cases j
  · simp [proj]
  · simp [proj]

/-- `freshAlpha (sideAlpha₁) (inr j)` is the *other* fresh dart `inr (swap j)`, whose `ι`-tail is
the *other* anchor.  Hence the fresh chord dart `inr j` has `ι`-endpoints `M.tail a₀.1` and
`M.tail a₁.1` (in some order). -/
lemma sideVertexToM₁_head_inr (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (j : Fin 2) :
    sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₁ hsep)) (Sum.inr j)))
      = M.tail (if j = 0 then a₁.1 else a₀.1) := by
  rw [freshAlpha_inr]
  rw [sideVertexToM₁_tail_inr data hsep a₀ a₁ hne (Equiv.swap (0 : Fin 2) 1 j)]
  fin_cases j
  · simp [Equiv.swap_apply_left]
  · simp [Equiv.swap_apply_right]

/-- **The `ι`-edge of any side dart.**  For every side dart `d`, the `ι`-images of its side
endpoints `sideMap₁.tail d`, `sideMap₁.head d` are `M`-adjacent: an `inl x'` dart gives the proved
`M`-edge of `x'` (`ι_adj_of_inl`); a fresh chord dart gives the anchor-tail pair (`M`-adjacent by
`hchord`).  `sideMap₁.tail d = ⟦d⟧` and `sideMap₁.head d = ⟦freshAlpha _ d⟧` (definitional). -/
lemma ι_adj_of_dart (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (d : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :
    M.Adj
      (sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne)) d))
      (sideVertexToM₁ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₁ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₁ hsep)) d))) := by
  cases d with
  | inl x' => exact ι_adj_of_inl data hsep a₀ a₁ hne x'
  | inr j =>
      rw [sideVertexToM₁_tail_inr data hsep a₀ a₁ hne j,
        sideVertexToM₁_head_inr data hsep a₀ a₁ hne j]
      fin_cases j
      · simpa using hchord
      · simpa using M.adj_symm hchord

/-! ## Section 3.  Brick 2 — side adjacency carries to `M`-adjacency (`ι_adj`)

Every side dart is `inl x` or `inr j`.  An `inl`-dart's edge is the `M`-edge of `x` (proved
`ι_adj_of_inl`); a fresh dart's edge is the anchor-tail pair, `M`-adjacent by `hchord`.  We
state the brick with `hchord` (the chord edge) as a clearly-named hypothesis (its discharge for
the canonical anchors is `ChordContiguous.chordChoice_adj` modulo the canonical anchor-tail
identification, which is canonical-anchor geometry, not residue shape). -/

/-- **Brick 2 — `ι_adj`.**  Side adjacency `sideMap₁.toSimpleGraph.Adj x y` carries to
`M.toSimpleGraph.Adj (ι x) (ι y)`.  The witnessing side dart `d` gives `s(x, y) = sideMap₁.dartEdge
d = s(sideMap₁.tail d, sideMap₁.head d)`, whose `ι`-images are `M`-adjacent (`ι_adj_of_dart`); the
unordered pair matches by `Sym2.eq_iff`.  The `≠` half is preserved by injectivity (Brick 1). -/
theorem sideVertexToM₁_adj_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)) :
    ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y →
        M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) := by
  intro x y hxy
  rw [toSimpleGraph_adj] at hxy ⊢
  obtain ⟨hne_xy, d, hd⟩ := hxy
  -- the `≠` part: `ι x ≠ ι y` from injectivity + `x ≠ y`.
  refine ⟨fun h => hne_xy (sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne h), ?_⟩
  -- `s(x, y) = sideMap₁.dartEdge d = s(sideMap₁.tail d, sideMap₁.head d)` (the last `=` is `rfl`).
  have hM := ι_adj_of_dart data hsep a₀ a₁ hne hchord d
  -- `sideMap₁.tail d = ⟦d⟧` and `sideMap₁.head d = ⟦freshAlpha _ d⟧` (definitional), so:
  have hd' : s((data.sideMap₁ hsep a₀ a₁ hne).tail d, (data.sideMap₁ hsep a₀ a₁ hne).head d)
      = s(x, y) := hd
  rcases Sym2.eq_iff.1 hd' with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [← hx, ← hy]; exact hM
  · rw [← hx, ← hy]; exact M.adj_symm hM

/-! ## Section 4.  Brick 3 — `M`-adjacency reflects to side adjacency (`ι_adj_reflect`)

This is the region edge-confinement: an `M`-edge between two side-1-region vertices is realised by
a side edge.  The repository has no `ChordSplitRegions` producer (the open discrete-Schoenflies
item), so we thread the MINIMAL confinement fact as a clearly-named hypothesis `hreflect` — it is
literally the `ι_adj_reflect` field of `ChordSideReconstruction`, and we record it here as the
isolated planar residue (not silently assumed: it is an explicit hypothesis of the brick). -/

/-- **Brick 3 — `ι_adj_reflect`, isolated as the named confinement residue.**  We do NOT silently
assume more than the field itself: the brick simply *is* the hypothesis, recorded as the minimal
region edge-confinement fact (an `M`-edge between two `ι`-images is a side edge), which the open
`ChordSplitRegions`/Schoenflies layer is responsible for.  Reported in the handoff as the genuine
planar block. -/
theorem sideVertexToM₁_adj_reflect_canonical (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y) :
    ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y :=
  hreflect

/-! ## Section 5.  Brick 5 — the strict vertex decrease (`smaller`)

`ι` is injective (Brick 1), so `(sideMap₁).V = Fintype.card (sideMap₁).Vertex ≤ Fintype.card
M.Vertex = M.V`.  For the STRICT inequality there must be an omitted `M`-vertex: the opposite
boundary arc carries an internal vertex (`ChordContiguous.chordChoice_arc_internal_witnesses`,
unconditional) that side 1 does not represent.  The not-in-range fact for that omitted vertex is
the region-confinement residue, threaded as `homit`; from injectivity + an omitted vertex,
`Fintype.card_lt_of_injective_of_not_mem` (via the range) gives the strict `<`. -/

/-- **Brick 5 — `smaller`.**  From the proved injectivity of `ι` and an explicit omitted
`M`-vertex `w ∉ Set.range ι` (the opposite-arc internal vertex side 1 drops — the named
region-confinement residue `homit`), the side has strictly fewer vertices than `M`. -/
theorem side₁_smaller_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (homit : ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne)) :
    (data.sideMap₁ hsep a₀ a₁ hne).V < M.V := by
  classical
  obtain ⟨w, hw⟩ := homit
  -- `(sideMap₁).V = Fintype.card (sideMap₁).Vertex`, `M.V = Fintype.card M.Vertex`.
  show Fintype.card (data.sideMap₁ hsep a₀ a₁ hne).Vertex < Fintype.card M.Vertex
  -- the image of `ι` is a proper subset of `M.Vertex` (it misses `w`); `ι` injective.
  have hinj := sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne
  -- map the (full) domain finset injectively into `M.Vertex`, missing `w`.
  have hcard_le : Fintype.card (data.sideMap₁ hsep a₀ a₁ hne).Vertex
      = (Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne)).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [hcard_le]
  -- the image is a finset of `M.Vertex` not containing `w`, hence a strict subset of `univ`.
  have hsub : Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne) ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.2 ?_
    intro hfull
    apply hw
    have hmem : w ∈ Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne) := by
      rw [hfull]; exact Finset.mem_univ w
    obtain ⟨V, _, hV⟩ := Finset.mem_image.1 hmem
    exact ⟨V, hV⟩
  calc (Finset.univ.image (sideVertexToM₁ data hsep a₀ a₁ hne)).card
      < (Finset.univ : Finset M.Vertex).card := Finset.card_lt_card hsub
    _ = Fintype.card M.Vertex := Finset.card_univ

/-! ## Section 6.  Brick 6 — the partial constructor (assembly of the completed fields)

`chordSideResidue₁_partial` assembles a full `ChordSideResidue` via
`ChordSplitFinal.chordSideResidue_mk`, with:

* `ι_inj` PROVED (`sideVertexToM₁_injective_canonical`);
* `ι_adj` reduced to the chord-edge hypothesis `hchord` (kept-dart half proved);
* `ι_adj_reflect` = the named confinement residue `hreflect` (Brick 3);
* the side lists `pₛ`/`qₛ`/`cpₛ`/`cqₛ` + `hLₛ` = the residue list field;
* `smaller` from injectivity + the omitted-vertex residue `homit` (Brick 5).

The fields that genuinely require the open `ChordSplitRegions`/Schoenflies confinement are exactly
`hreflect` (Brick 3) and `homit` (the `smaller` witness, Brick 5); `hchord` is the chord edge; the
list field `hLₛ` is the boundary-cycle correspondence.  `ci`/`hshare` are supplied for the
canonical anchors by `ZinanCh35Hclass`/`ZinanCh35OuterTrace`. -/

/-- **Brick 6 — the side-1 residue, partially assembled.**  All six non-`ci`/`hshare`
`ChordSideResidue` fields are produced: `ι_inj` and the kept-dart half of `ι_adj` PROVED
unconditionally; the fresh-chord `ι_adj` half from `hchord`; `ι_adj_reflect` from the named
confinement residue `hreflect`; `hLₛ` the residue list field; `smaller` from injectivity + the
omitted-vertex residue `homit`.

Remaining (the open `ChordSplitRegions`/discrete-Schoenflies content): `hreflect` (region
edge-confinement) and `homit` (the opposite-arc omitted vertex's not-in-range).  These are the two
honest planar inputs; `hchord` is the chord adjacency `u–v` and `hLₛ` the list transport. -/
def chordSideResidue₁_partial (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (ci : ContiguousInterval data hsep a₀ a₁ hne)
    (hshare : ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace data hsep a₀ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y)
    (pₛ qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (homit : ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne)) :
    ChordSideResidue data hsep a₀ a₁ hne L :=
  chordSideResidue_mk data hsep a₀ a₁ hne L ci hshare
    (sideVertexToM₁_injective_canonical data hsep a₀ a₁ hne)
    (sideVertexToM₁_adj_canonical data hsep a₀ a₁ hne hchord)
    (sideVertexToM₁_adj_reflect_canonical data hsep a₀ a₁ hne hreflect)
    pₛ qₛ cpₛ cqₛ hLₛ
    (side₁_smaller_canonical data hsep a₀ a₁ hne homit)

end ProofsInTheBook.ZinanCh35Iota

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35Iota.sideVertexToM₁_injective_canonical
#print axioms ProofsInTheBook.ZinanCh35Iota.sideVertexToM₁_adj_canonical
#print axioms ProofsInTheBook.ZinanCh35Iota.sideVertexToM₁_adj_reflect_canonical
#print axioms ProofsInTheBook.ZinanCh35Iota.side₁_smaller_canonical
#print axioms ProofsInTheBook.ZinanCh35Iota.chordSideResidue₁_partial
