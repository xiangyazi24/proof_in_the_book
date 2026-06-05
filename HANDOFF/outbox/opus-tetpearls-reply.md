# TetPearls.lean — reply

New file `ProofsInTheBook/TetPearls.lean` (831 lines), `import Mathlib`. Chapter-9 simplices-only
geometric substrate + the Pearls partition (CH09_GEOMETRY_DESIGN.md sections 1–3).

Verified with `lake env lean ProofsInTheBook/TetPearls.lean` on uisai1: compiles clean, the only
warning is `declaration uses 'sorry'` on the single isolated gap `volume_tet`. `#print axioms` on
all four partition lemmas + `Tet.relativeInterior_eq_interior` reports exactly
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

Does NOT touch any other file (Chapter09.lean, SectorSum.lean, PearlLemma.lean, ConeLemma.lean
unchanged). Not yet wired into `ProofsInTheBook.lean` — left for the orchestrator.

## API (namespace `ProofsInTheBook.TetPearls`)

Substrate:
- `Pt3 := EuclideanSpace ℝ (Fin 3)`
- `Tet` (`v : Fin 4 → Pt3`, `affIndep`), `Tet.carrier := convexHull ℝ (range v)`,
  `Tet.interior := interior carrier`, `Tet.relInterior := interior` with
  `Tet.relativeInterior_eq_interior` (rfl). Helpers: `carrier_convex/compact/closed`,
  `vertex_mem_carrier`, `v_injective`.
- `TetSolid` (`pieces : Finset Tet`, `interior_disjoint`), `TetSolid.carrier`, `carrier_closed/compact`.
- `TetEquidecomp P Q` (`e : P.pieces ≃ Q.pieces`, `iso : P.pieces → (Pt3 ≃ᵢ Pt3)`,
  `maps_piece`). Uses `≃ᵢ` (full Euclidean isometries) so reflections are allowed.
- `Segment3` (`a b : Pt3`, `hne`), `carrier := segment`, `relInterior := openSegment`,
  `coord x := ⟪x-a,b-a⟫/⟪b-a,b-a⟫`, `point t := a + t•(b-a)`. Key lemmas:
  `coord_point`, `point_coord_of_mem`, `coord_mem_Icc`, `point_mem_carrier`, continuity, injectivity,
  `coordSet` (the coord-space description of `e.carrier ∩ r.carrier`) with
  `coordSet_convex/compact/closed/ordConnected`, `coord_image_inter`.
- `Tet.edges` / `PieceEdges S : Finset Segment3` — the six edges of every piece (index pairs `i<j`,
  endpoints distinct by affine independence).
- `segmentIntersectionPoints e r : Finset Pt3` — the two extreme points of `e.carrier ∩ r.carrier`
  along `e` (min/max coordinate), `∅` if disjoint. See design choice below.
- `BreakpointsOnEdge R e := {e.a, e.b} ∪ ⋃ r∈R, segmentIntersectionPoints e r`; `breakCoords` =
  their coords (always contains `0`,`1`, all in `[0,1]`).
- `Pearl` (`sourceEdge`, `lo`, `hi`), `Pearl.carrier`/`relInterior`, `IsPearlOf R p` (consecutive
  breakpoints), `Pearls R : Finset Pearl`, `mem_Pearls`.

Four partition lemmas (all `0 sorry`, clean-3 axioms):
- `pearls_finite`
- `raw_edge_covered_by_pearls : e ∈ R → e.carrier = ⋃ p∈Pearls R, ⋃ (_:p.sourceEdge=e), p.carrier`
- `pearl_interiors_disjoint_on_same_edge` (distinct pearls, same source edge → disjoint relInteriors)
- `incidence_constant_on_pearl : IsPearlOf R p → r ∈ R →
     p.relInterior ⊆ r.carrier ∨ Disjoint p.relInterior r.carrier`  (the heart)

## Design choices

1. **relInterior = topological interior, by definition.** Routing through Mathlib's
   `intrinsicInterior` would force proving `affineSpan ℝ (range v) = ⊤` and transporting along an
   affine isometry — a real detour, and every downstream lemma only needs topological interior.
   `Tet.relativeInterior_eq_interior` records the identification (the brief explicitly permits this).

2. **`segmentIntersectionPoints` = extreme points of the intersection along `e`.** Rather than the
   raw (possibly infinite) intersection set, it returns `point(tmin)` and `point(tmax)` where
   `tmin/tmax` minimise/maximise `coord` over the compact convex set `e.carrier ∩ r.carrier`
   (extracted via `IsCompact.exists_isMinOn/exists_isMaxOn`). This unifies the transverse case
   (`tmin=tmax`, a singleton) and the collinear-overlap case (the two ends of the overlap), and is
   precisely what makes incidence-constancy provable: the coords whose point lies in `r.carrier`
   form a closed ordConnected interval `[tmin,tmax]` whose endpoints are breakpoints, so any
   breakpoint-free open pearl interval is wholly inside or wholly outside. Noncomputable
   (`Classical.choice`), which is fine for this layer.

3. **Pearls indexed by coordinates.** `IsPearlOf` says `lo<hi` are consecutive breakpoint coords
   (both in `breakCoords`, none strictly between). `Pearls R` filters candidates over
   `breakCoords ×ˢ breakCoords` per edge. `DecidableEq` issues with `Tet`/`Pearl` (Prop / real
   fields) handled by `open scoped Classical`.

4. `set_option synthInstance.maxHeartbeats 400000`, `maxHeartbeats 1000000` (EuclideanSpace
   typeclass search + the `isCompact_convexHull` instances are slow).

## Isolated gap (the ONE permitted)

- `volume_tet : volume T.carrier = ENNReal.ofReal (|T.edgeMatrix.det| / 6)` — `sorry`.
  `Tet.edgeMatrix i j := (v i.succ - v 0) j`. Mathlib has parallelepiped volume
  (`volume_parallelepiped`) and the `|det|` change-of-variables (`addHaar_image_linearMap`) but
  **no** simplex-volume lemma; deriving `simplex = parallelepiped / 3!` is a separate iterated-
  integral development. Everything else in the file is `sorry`-free. Downstream only needs the
  *consequence* (regular tetrahedron vs. equal-volume cube), statable against this lemma.
