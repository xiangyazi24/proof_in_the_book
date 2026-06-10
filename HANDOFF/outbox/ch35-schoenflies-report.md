# Ch35 Schoenflies star-rotation: bricks 4–7 report

**File:** `ProofsInTheBook/ZinanCh35Schoenflies.lean` (NEW, 0 errors, 0 warnings, clean-3 ×7).
**Build:** `lake build ProofsInTheBook.ZinanCh35Schoenflies` — 8500 jobs, success. Every audited
result depends only on `[propext, Classical.choice, Quot.sound]` (no `sorryAx`/`native`/`axiom`).

## Inventory findings (the decisive part)

The brief asked to INVENTORY the boundary-dart characterization FIRST, because it decides whether
`homit` is short or needs a residual. Verdict: **it needs a residual.** Details:

1. **`sideRegion₁` is fully concrete.** `sideRegion₁ data = {w | ∃ d ∉ keptDel₁, M.tail d = w}`
   (`ChordReconClose.lean:97`), and `d ∉ keptDel₁ ↔ d ∈ keptSet₁` (`mem_keptDel₁_iff`), with
   `keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}` (`PlanarMapChordSplit.lean:412`),
   `sideDarts₁ = {d | dartFace d ∈ side₁}` (`PlanarMapChordSplitData.lean:185`),
   `outerArc₁ = {b | dartFace b = outerFace ∧ dartFace (α b) ∈ side₁}`. So
   `w ∉ sideRegion₁` ⟺ **every** dart at `w` is the chord dart, or has its face outside `side₁` and
   is not a side-1 boundary dart. This is a **vertex-star confinement** statement. I proved this
   unfolding fully (`mem_sideRegion₁_iff`, `notMem_sideRegion₁_iff`).

2. **No landed anchoring exists.** I searched `ChordContiguous`, `ZinanCh35OuterTrace`,
   `ZinanCh35Iota`, `ZinanCh35Gates`, `PlanarMapChordSplit(Data)`, `ChordReconClose` for any lemma
   placing a `path₂`-internal vertex's star faces outside `side₁`, or characterizing which boundary
   darts bound `side₁` faces (the "side₁ boundary darts lie on arc₁" fact the brief hypothesized).
   **It does not exist.** What is landed is only the *face*-dual separation
   `separates_closed → data.Separates = (face₂ ∉ side₁)` (`ZinanCh35Gates.lean:286`), which says
   nothing about an internal arc-2 vertex's whole star — exactly the altitude mismatch already
   documented in `ZinanCh35Confinement.lean`'s header.

3. **The star machinery (bricks 1–3) is consistent, not contradictory, at a `path₂`-internal
   vertex.** Such a vertex `w` lies on the *old outer boundary*, so its star genuinely contains
   seam (boundary) edges; the escape lemma `star_escape_crosses_seam` then permits a side-1↔non
   bank change at `w`. The missing ingredient is the *anchoring* (which boundary bank is the side-1
   one) — precisely the discrete-Schoenflies content the campaign has always flagged as open. So
   the star bricks scaffold the statement but cannot close it from the landed inputs.

4. **`hreflect` is consumed verbatim.** `ZinanCh35Iota.sideVertexToM₁_adj_reflect_canonical` is the
   identity passthrough of `hreflect` — there is **no** landed reduction of the region
   edge-confinement either.

## What closed (proved unconditionally, around the residual)

* **Brick 4 — region/star bridges:** `mem_sideRegion₁_iff` (full concrete unfolding against
  `keptSet₁`), `notMem_sideRegion₁_iff` (the vertex-star-confinement form `homit` needs),
  `mem_sideRegion₁_of_star_side₁`, `mem_sideRegion₁_of_star_outerArc₁`, `dart_edge`.
* **Brick 5 — master confinement:** `vertexStar_confined_of_starConfinement` produces the design's
  `Side₁SchoenfliesConfinement` (fields `edge_confined` + `opposite_arc_omitted`) from the single
  residual. The `edge_confined` derivation does the genuine reduction: chord case → right disjunct;
  non-chord case uses the residual's `edge_core` to get `dartFace e ∈ side₁`, hence
  `e ∈ sideDarts₁ ⊆ keptSet₁`, and the landed `Separates`-conditional `α`-closure
  `mem_keptSet₁_alpha_iff` to discharge `α e ∉ keptDel₁`. `opposite_arc_omitted` is exactly
  `notMem_sideRegion₁_iff` ∘ the residual's `oppArc_star_core`.
* **Bricks 6–7 — producers + final plug-in:** `homit_region_of_schoenflies` is **fully proven**
  (extracts a `path₂`-internal vertex via `List.exists_mem_of_ne_nil data.arc₂_internal`, applies
  `opposite_arc_omitted`); `homit_of_schoenflies` transports it through the landed
  `homit_iff_exists_notMem_sideRegion₁`; `side₁Confinement_of_starConfinement` builds the landed
  `Side₁Confinement`; `chordSideResidue₁_of_schoenflies` feeds it into the landed
  `chordSideResidue₁_of_confinement`, producing the full `ChordSideResidue`.

## The single sharp residual (honest, named, non-vacuous)

`structure Side₁StarConfinement (data : hNT.ChordSplitData u v) : Prop` — the discrete-Schoenflies
vertex-star anchoring, two fields:

* `edge_core` : `dartEdge e ≠ s(u,v) → tail e ∈ sideRegion₁ → head e ∈ sideRegion₁ →
  dartFace e ∈ side₁` (geometric heart of `edge_confined`, after the chord/`α`-closure peel-off).
* `oppArc_star_core` : `w ∈ path₂.internalVertices → ∀ d, tail d = w →
  (d = dart ∨ (dartFace d ∉ side₁ ∧ ¬(dartFace d = outerFace ∧ dartFace (α d) ∈ side₁)))`
  (vertex-star-confinement form of `opposite_arc_omitted`).

Both fields quantify over genuinely-inhabited data (the opposite arc has an internal vertex by
`data.arc₂_internal`; the region is inhabited by `sideRegion₁_nonempty`; ambient edges exist), so
the residual is **satisfiable and non-vacuous** — it is exactly true in the planar Schoenflies
model and is the minimal honest blocking content. The two fields share one cause (boundary-bank
anchoring), so they are bundled into one residual rather than split artificially.

## Attack sketch for the residual (for the next wave)

Closing `Side₁StarConfinement` is the genuine discrete-Schoenflies keystone. The route the star
bricks set up: prove the **boundary-bank anchoring** `side₁_boundary_darts_on_arc₁` — a boundary
star dart `d` (an old outer-boundary edge) with `dartFace (α d) ∈ side₁` has its underlying edge on
`path₁`, not `path₂`. With that single fact: at a `path₂`-internal `w`, the two seam cuts in its
star are *both* `path₂` boundary edges, the outer face sits on one bank, and the anchoring forces
the other bank off `side₁` — so no star face at `w` is in `side₁`, giving `oppArc_star_core`; and
`edge_core` follows because a non-chord edge between two region vertices cannot have crossed the
chord/boundary seam. The anchoring itself is planar-Jordan content (it is where the chord∪arc cycle
`C = chord ∪ path₁` and the `jordan_simple_cycle2_unconditional` separation must be combined with
the *vertex*-star — currently only available at face level), dischargeable with the cut-cap /
bank-interval toolkit the bricks 1–3 escape lemma already exposes.
