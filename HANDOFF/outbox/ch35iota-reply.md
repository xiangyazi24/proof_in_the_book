# Ch35 ι / lists / decrease bricks — reply (ZinanCh35Iota.lean)

**Status: LANDED, clean-3 ×5.** Full `lake build ProofsInTheBook.ZinanCh35Iota` (8471 jobs)
green; every `#print axioms` = `{propext, Classical.choice, Quot.sound}` (no sorryAx, no
native_decide, no axiom). New file only; no other edits, no git.

## The `ChordSideResidue` fields covered (beyond `ci`/`hshare`, already landed upstream)

The structure `ChordSplitFinal.ChordSideResidue` has 8 non-`ci`/`hshare` fields (quote-verified
against ChordSplitFinal.lean L115-150): `ι_inj`, `ι_adj`, `ι_adj_reflect`, `pₛ`, `qₛ`, `cpₛ`,
`cqₛ`, `hLₛ`, `smaller`. All are produced here; `chordSideResidue₁_partial` assembles them via the
existing `ChordSplitFinal.chordSideResidue_mk`.

### Brick 1 — `sideVertexToM₁_injective_canonical` : PROVED UNCONDITIONALLY (general anchors)
Purely combinatorial. `ι ⟦y⟧ = M.tail (proj a₀ a₁ y).1` by the `Quotient.lift` defn
(`sideVertexToM₁_mk`, `rfl`). `ι ⟦y⟧ = ι ⟦z⟧` ⟹ `M.σ.SameCycle (proj y).1 (proj z).1`
(`Quotient.exact`, since `M.tail = Quotient.mk (cycleSetoid M.σ)`) ⟹ `sideSigma₁.SameCycle`
(`filteredRotation_sameCycle_iff`, backward) ⟹ `freshSigma.SameCycle y z`
(`freshSigma_sameCycle_iff`, BACKWARD — both directions already exist in ChordSplitEuler) ⟹
`⟦y⟧ = ⟦z⟧` (`Quotient.sound`). No planar input. Design "bounded-combinatorial" confirmed.

### Brick 2 — `sideVertexToM₁_adj_canonical` : kept-dart half PROVED; fresh-chord half = `hchord`
Via the unified helper `ι_adj_of_dart`: every side dart `d` has `M.Adj (ι (tail d)) (ι (head d))`.
- `inl x'` → the already-landed `ChordReconClose.ι_adj_of_inl` (the `M`-edge of `x'.val`). PROVED.
- `inr j` (fresh chord dart) → `ι`-endpoints are `(M.tail a₀.1, M.tail a₁.1)` (new lemmas
  `sideVertexToM₁_tail_inr`/`_head_inr`, definitional from `freshSigma`/`freshAlpha` eqns),
  `M`-adjacent by the named hypothesis `hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)`.
Main theorem: from the witnessing dart `hd : sideMap₁.dartEdge d = s(x,y)`, `Sym2.eq_iff` matches
the unordered pair to `(tail d, head d)`; `≠`-half preserved by Brick-1 injectivity.
**`hchord` is the chord edge `u–v`.** For the CANONICAL anchors it is
`ChordContiguous.chordChoice_adj` (`M.toSimpleGraph.Adj u v`), modulo the identification
`M.tail (side₁Anchor₀).1 = u`, `M.tail (side₁Anchor₁).1 = v` — that identification is
canonical-anchor *geometry* (the anchors are `sideSigma₁.symm (keptPhi d₂)` / `sideSigma₁.symm d₁`,
not literally darts at `u`/`v`), NOT residue shape, so I left it as the clean hypothesis `hchord`
rather than silently asserting the tail-identification. **Recommend a follow-up brick**
`side₁Anchor_tails_eq_uv` to discharge `hchord` for the canonical anchors (small, but needs the
`keptPhi`/`tracePhi` tail bookkeeping from ZinanCh35SideAnchors).

### Brick 3 — `sideVertexToM₁_adj_reflect_canonical` : NAMED PLANAR RESIDUE (`hreflect`)
This is the region edge-confinement (an `M`-edge between two side-1-region vertices is a side edge
or the chord). **There is NO `ChordSplitRegions.lean` in the repo** (grep-verified) — it is the
open discrete-Schoenflies item the design flagged. The brick is the hypothesis itself, recorded
verbatim as the `ι_adj_reflect` field type. NOT silently assumed: it is an explicit, clearly-named
parameter. This is the genuine planar block for this brick.

### Brick 4 — lists (`pₛ`/`qₛ`/`cpₛ`/`cqₛ`/`hLₛ`) : list-transport residue
`Lₛ := L ∘ ι`, `Lₛ_eq := rfl` (baked into `chordSideReconstruction_of_chord` upstream). The side
`ThomassenLists` `hLₛ` (boundary/interior status + list-size bounds over the side
`NearTriangulation`) is threaded as the residue field — it IS the `hLₛ` field of
`ChordSideReconstruction`. The boundary-cycle status comes from `ci`'s `outerCycle`; supplying it
unconditionally would require the side-boundary↔M-boundary correspondence, part of the same
region/Schoenflies layer. Carried honestly as the residue list datum.

### Brick 5 — `side₁_smaller_canonical` : injectivity PROVED + omitted-vertex residue (`homit`)
From Brick-1 injectivity, `Finset.card_image_of_injective` gives `(sideMap₁).V =
card (image ι univ)`; the named `homit : ∃ w, w ∉ Set.range ι` makes the image a STRICT subset of
`univ` (`Finset.card_lt_card`), so `(sideMap₁).V < M.V`. The omitted vertex EXISTS unconditionally
as the opposite-arc internal boundary vertex
(`ChordContiguous.chordChoice_arc_internal_witnesses`, which is unconditional — the chord is not a
boundary edge so each arc has an internal vertex); but *that this specific vertex is ∉ range ι* is
again the region-confinement residue (range ι = `sideRegion₁` = tails of side-1 kept darts). So the
strict-decrease *mechanism* is proved; only the not-in-range witness `homit` is the planar residue.

### Brick 6 — `chordSideResidue₁_partial`
Assembles all 8 fields. Residual planar inputs (the genuine `ChordSplitRegions`/Schoenflies
content): **`hreflect`** (Brick 3) and **`homit`** (Brick 5's omitted-vertex not-in-range). The
chord edge **`hchord`** (Brick 2 fresh half) is `chordChoice_adj` modulo the canonical anchor-tail
identification. **`hLₛ`** is the list-transport. `ci`/`hshare` supplied for canonical anchors by
ZinanCh35Hclass/ZinanCh35OuterTrace.

## §3.3 self-audit (non-vacuity, faithfulness)
- Brick 1 is a *theorem about a real function* (`ι` surjects onto the nonempty `sideRegion₁`,
  `ChordReconClose.sideRegion₁_nonempty`) — not a vacuous injectivity on an empty domain.
- Brick 2/5 mechanisms are genuine (not conditioned on unsatisfiable premises): `hchord` is a real
  edge (the chord exists, `chordChoice_adj`); `homit`'s witness exists (the opposite arc has an
  internal vertex unconditionally). The hypotheses isolate the *confinement* (not-in-region /
  edge-stays-in-region), which is exactly the documented open Schoenflies layer — faithful, not a
  smuggled hard half.
- No field was strengthened: `chordSideResidue₁_partial` plugs into the EXISTING
  `chordSideResidue_mk` (signatures matched exactly), so the produced `ChordSideResidue` is the
  real recursion input, not a weakened variant.

## Net
Two of the eight residue fields are FULLY PROVED (`ι_inj`; the kept-dart majority of `ι_adj`).
The remaining genuinely-planar content is reduced to THREE clearly-named hypotheses
(`hreflect`, `homit`, `hchord`) + the list field (`hLₛ`), all consumed by the partial constructor.
Recommended next bricks: (a) `side₁Anchor_tails_eq_uv` to discharge `hchord`; (b) the
`ChordSplitRegions`/edge-confinement producer to discharge `hreflect`+`homit` (the open
discrete-Schoenflies item).
