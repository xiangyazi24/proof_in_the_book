# Ch35 final close — report

**File:** `ProofsInTheBook/ZinanCh35FinalClose.lean` (new, only file created/edited).
**Status:** compiles, 0 errors, clean-3. Every `#print axioms` →
`[propext, Classical.choice, Quot.sound]` only. No `sorry` / `admit` / `axiom` / `native_decide`.

This closes the Ch35 side-1 reconstruction residue `ChordSideResidue` **modulo the minimal named
planar-input bundle** `Side₁SchoenfliesConfinementInput` (verdict §4) plus the upstream
non-confinement inputs — the architecturally honest endpoint per the incidence verdict.

## The 6 bricks, as landed

| Brick | Name | Status |
|---|---|---|
| 1 | `Side₁SchoenfliesConfinementInput` (2-field bundle: `oppArcStarSeed`, `edge_core`) | landed, verbatim from verdict §4 |
| 2 | `homit_of_confinementInput` (`∃ w, w ∉ sideRegion₁`) | **proved** (via `data.arc₂_internal` + `List.exists_mem_of_ne_nil` + `oppArcStarSeed`) |
| 3 | `side_adj_of_kept_edge` | **proved** unconditionally (endpoint id via `sideVertexToM₁_injective_canonical`; side dart `Sum.inl ⟨e, he⟩`; edge match by `rfl`) |
| 4 | `side_adj_of_chord_edge` | **proved** (fresh chord dart `Sum.inr 0`; canonical anchor-tail eqns threaded) |
| 5 | `hreflect_of_confinementInput` (master) | **proved** (dart from `Adj`, `sideVertexToM₁_mem`, `edge_core`, `Sym2.eq_iff` orientation cases, dispatch B3/B4) |
| 6 | `chordSideResidue₁_final` (master) | **landed** — plugs B2+B5 into `chordSideResidue₁_partial` |

Plus `confinementInput_of_schoenflies` (non-vacuity guard, §below).

## The minimal bundle (the genuine discrete-Schoenflies content)

```
structure Side₁SchoenfliesConfinementInput (data) (hsep) : Prop where
  oppArcStarSeed : ∀ {w}, w ∈ data.arc.path₂.internalVertices → w ∉ sideRegion₁ data
  edge_core      : ∀ {e}, M.tail e ∈ sideRegion₁ data → M.head e ∈ sideRegion₁ data →
                     ((e ∉ data.keptDel₁ ∧ M.α e ∉ data.keptDel₁) ∨ M.dartEdge e = s(u, v))
```

This is the two-field minimum the verdict isolated. `oppArcStarSeed` is the concrete `homit`
content; `edge_core` is the region edge-confinement core in the `keptDel₁`-disjunction shape the
`hreflect` producer consumes directly (the `α`-closure folded into the conclusion).

## The chapter's COMPLETE remaining planar-input surface

`chordSideResidue₁_final` takes, as honest inputs:

1. **`ci : ContiguousInterval data hsep a₀ a₁ hne`** — supplied for the canonical anchors upstream
   by `ZinanCh35Hclass`/`ZinanCh35OuterTrace`. (Not confinement; the contiguity datum.)
2. **`hshare : Side₁AnchorsShareFace data hsep a₀ a₁`** — ditto, supplied for canonical anchors.
3. **`hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)`** — the chord edge `u–v`; the fresh-chord half of
   `ι_adj` (canonical: `ChordContiguous.chordChoice_adj` modulo anchor-tail id).
4. **`ha₀ : M.tail a₀.1 = u`, `ha₁ : M.tail a₁.1 = v`** — the **canonical anchor-tail geometry**.
   This is the chord-case driver of `hreflect`: it is genuinely *not* residue shape (the
   `ZinanCh35Iota` header explicitly flags `M.tail (side₁Anchor₀).1 = u` as "canonical-anchor
   geometry, not residue-shape"), so it is threaded exactly as `hchord` is. For the canonical
   anchors it is a true definitional identification, dischargeable in the anchor layer.
5. **`pₛ qₛ : sideMap₁.Vertex`, `cpₛ cqₛ : α`, `hLₛ : ThomassenLists …`** — the side Thomassen
   lists transport (the residue list field, `Lₛ = L ∘ ι`).
6. **`H : Side₁SchoenfliesConfinementInput data hsep`** — the genuine discrete-Schoenflies
   confinement (the two-field bundle above). This is the ONE genuinely-open planar item; it is the
   true fact about planar embeddings provable in the future `ZinanCh35BoundaryIncidence` layer
   (verdict §7).

Everything else is **proved**: `ι_inj` (`sideVertexToM₁_injective_canonical`), the kept half of
`ι_adj` (`sideVertexToM₁_adj_canonical`), the `homit`/`hreflect` **producers** (Bricks 2/5 here),
and the strict vertex decrease `smaller` (`side₁_smaller_canonical`).

## Non-vacuity / satisfiability (verdict §3.3)

`confinementInput_of_schoenflies` proves
`ZinanCh35Schoenflies.Side₁SchoenfliesConfinement data → Side₁SchoenfliesConfinementInput data hsep`
axiom-cleanly: `oppArcStarSeed = opposite_arc_omitted` verbatim, and `edge_core` is `edge_confined`
restricted to the two region-membership hypotheses. So the minimal bundle is a genuine
**consequence of an already-landed, documented-satisfiable inhabited structure** — it is NOT
propositionally `False`. The two fields are independently inhabited (the opposite arc carries an
internal vertex by `data.arc₂_internal`; the region is inhabited by `sideRegion₁_nonempty`) and
concern disjoint parts of `M` (opposite-arc star vs. region edge-realisation), so there is no
hidden contradiction.

## Note on the parallel route

`ZinanCh35Schoenflies.chordSideResidue₁_of_schoenflies` already closes the chain through the
`Side₁StarConfinement` star-rotation residual (whose `edge_core` asks for `dartFace e ∈ side₁`).
`ZinanCh35FinalClose` is the **leaner, verdict-§4 endpoint**: the same `ChordSideResidue` closed
through `chordSideResidue₁_partial` directly, on the strictly minimal two-field bundle, with the
`homit`/`hreflect` producers proved from that bundle here. Both are clean-3.
