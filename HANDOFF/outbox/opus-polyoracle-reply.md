# opus-polyoracle reply — CutGeometryOracle via the COMMON-RAY reduction

**Status: COMPLETE (the central correction landed, clean-3, 0 sorry).**
**File:** `ProofsInTheBook/PolygonOracle.lean` (659 lines, NEW, the only file I own).
**Build dep:** `ProofsInTheBook.PolygonLast` (whole Ch36 stack). Verified on `uisai1`.

## The correction

The previous endgame claimed the crossing-count identity "does not close because the
three crossing numbers use different rays." **It does close** — once the rays are made
*common*. This file proves the count identity outright and feeds it through the existing
`split_region_symmDiff_of_countSum` machinery, discharging the previously-*assumed*
`CountSummationDatum`.

## What is PROVED (unconditional, clean-3: {propext, Classical.choice, Quot.sound})

1. **`rawEdgeCrosses_symm`** — `RawEdgeCrosses r x a b ↔ RawEdgeCrosses r x b a`. The
   orientation symmetry of the raw half-open crossing (Span symmetric; the ray parameter
   is *equal* under swap because the two `rawTau` numerators differ by
   `det2 (a-b)(b-a) = 0`). This is the engine that lets the diagonal edge — read `j→i` in
   the left subpolygon and `i→j` in the right — count as the *same* geometric crossing.
   (Worked around the `private rawSide/rawTau` of `PolygonCutOracle` via a definitional
   `show` on the public `RawEdgeCrosses` body.)

2. **The edge-index correspondence** (`left_arc_edge_endpoints`, `left_diag_edge_endpoints`,
   `cyclicNext_arcPt`, `arcPt_j_eq`): each left/right sub-edge maps to a parent edge (the
   cyclic arc, `k.val < cyclicSteps i j` ↦ parent edge `(i+k)%n`) or the diagonal (the
   last index ↦ `{j,i}`). Pure modular arithmetic on `Fin n`.

3. **`rawCount_split_identity`** (unconditional, only `i ≠ j`) — the heart:
   ```
   rawCount_L(r,x) + rawCount_R(r,x) = rawCount_P(r,x) + 2 · [diagonal raw-crossed]
   ```
   The two arc-sums add to the parent via the rotation bijection `d ↦ arcPt i d` on
   `Fin n` (`rawCount_parent_eq_arcs`, using `cyclicSteps i j + cyclicSteps j i = n`); each
   side contributes the diagonal once.

4. **`crossingNumber'_split_identity_common`** — the count identity at the `CrossingNumber'`
   level, when `ρ.r = σL.r = σR.r` (a common ray `r*`):
   ```
   count_P(r*) + 2·diagCount(r*) = count_L(r*) + count_R(r*).
   ```
   This is *exactly* the `CountSummationDatum.count_sum` shape — the identity the previous
   analysis declared unclosable. Bridged via `crossingNumber'_eq_rawCount` (+ left/right
   versions), which use `edgeCrossesRay'_eq_raw` to drop ray-validity dependence.

5. **`countSummationDatum_of_commonRay`** — builds the `CountSummationDatum` from a
   `CommonRay` condition (previously the datum was an *assumed* input; now *derived*).

6. **`split_region_symmDiff_commonRay`** — the symmetric-difference split off all
   boundaries, fully discharged (count identity ⟹ XOR via the existing
   `split_region_symmDiff_of_countSum`).

7. **`region_union_off_boundary`** — union from symmDiff + the named disjointness residual
   `OffDiagDisjoint` (both-odd ⟹ `count_P` even ⟹ `x ∉ region_P`, so union over-counts
   exactly at points inside *both* subpolygons; that can't happen off the diagonal iff the
   half-plane separation holds). Pure logic on top of the proved XOR.

8. **`commonRay_reduction_summary`** — the headline contribution conjunct: (i) count
   identity, (ii) symmDiff split, (iii) union-from-disjointness — all under `CommonRay`,
   none assumed.

9. **`artGallery_strict_headline`** — re-export of `PolygonLast.artGallery_strict_attach`
   (the Ch36 `⌊n/3⌋` art-gallery conclusion) so this module names the final headline.

## Honest scope (what stays residual — NOT faked)

- **`CommonRay`** (named `def : Prop`): the condition that the subpolygon rays reuse the
  parent direction vector. Satisfiable via `validDir_avoiding` over the *union* of the
  three polygons' edge slopes (ℝ is never exhausted by finitely many bad slopes). The
  design's flagged obstruction — `ρ.r` possibly parallel to a diagonal — is sidestepped by
  choosing `r*` fresh for the union and *transferring* each region onto it via
  `region_transfer_common_ray` (Part-1 segment ray-independence). It is **not** a vacuous
  premise (it is a real selectable equation, not `False`); it is the genuine genericity
  residual.

- **`OffDiagDisjoint`** (named `def : Prop`): the half-plane disjointness — a point off the
  diagonal cannot lie strictly inside *both* subpolygons. This is **irreducibly Jordan**
  and is the precise residual of `split_region_union` *beyond* the parity content. The
  count identity alone provably cannot give union (it gives symmDiff); union needs this
  disjointness, exactly as `PolygonCutOracle` flagged.

- **`BaseTriangleFacts`** (n=3 region = closed hull) and the full set-equality
  `split_region_union`/`split_region_intersection` over *boundary* points remain the
  irreducible planar (Jordan) core. The count/parity half is now mechanically closed; the
  remaining surface is the half-plane disjointness + boundary bookkeeping + the n=3 leaf
  crossing-number computation. These were honestly isolated by the prior agents and I did
  not fake them.

- **`DiagonalAttachInput`** peel-ordering (from `PolygonLast`) is unchanged — its index
  freshness is already discharged by `leftRight_image_inter`.

## Faithfulness self-audit (§3.3)

- All headline theorems `#print axioms` clean-3 (no `sorryAx`, no
  `ofReduceBool`/`trustCompiler`).
- `rawCount_split_identity` / `crossingNumber'_split_identity_common` are genuine
  implications with satisfiable, non-contradictory hypotheses (not vacuous conditionals).
- `CommonRay`/`OffDiagDisjoint` are *named conditions consumed as inputs* (like the
  existing `UnconditionalRayIndepInput`, `DiagonalAttachInput`), not `def : Prop`
  substitutes for unproven target theorems. The substantive results are real `theorem`s
  with full proofs.
- The new content is non-trivial new mathematics: the edge-index correspondence + raw
  count identity was *assumed* (the `CountSummationDatum`) by every prior file; it is now
  derived.

## Verification

```
rsync -az ProofsInTheBook/PolygonOracle.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=/data/home/xhuan5/.elan/bin:$PATH && lake env lean ProofsInTheBook/PolygonOracle.lean'   # exit 0, no output
ssh uisai1 'lake build ProofsInTheBook.PolygonOracle'   # Build completed successfully (8434 jobs)
#print axioms artGallery_strict_headline   # [propext, Classical.choice, Quot.sound]
#print axioms commonRay_reduction_summary  # [propext, Classical.choice, Quot.sound]
```

No `sorry` / `axiom` / `admit` / `native_decide` in the file. No commits made; stayed on
`main`; touched only the new `PolygonOracle.lean`; no codex/OpenAI tooling; never ran
`lake build`/`lake env lean` on the Mac.
