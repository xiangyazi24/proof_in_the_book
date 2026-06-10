# Ch35 confinement supplier — report

File: `ProofsInTheBook/ZinanCh35Confinement.lean` (NEW, only file touched).
Build: clean on uisai2 (`lake env lean`), 0 errors; all 5 `#print axioms` = `[propext,
Classical.choice, Quot.sound]` (clean-3). No `sorry`/`admit`/`axiom`/`native_decide`.

## Prior-art findings (bricks already landed — verified against source, not re-done)

- **Brick 1 `side₁OuterTraceData_canonical`** — ALREADY LANDED in
  `ProofsInTheBook/ZinanCh35OuterTrace.lean` (§3, lines 212–271), exactly in the design's shape:
  `outerFace := S.dartFace (Sum.inr 1)`, `hφ` from `S.phi_ne_self_of_isSimpleGraph`,
  `outerCycle := S.boundaryCycleOfFace … rfl arcSplit`, `chord1_is_outer := rfl`,
  `face₁_not_outer := side₁_face₁_not_outer_canonical`, with `hsimple/arcSplit/outer_simple/
  outer_len/inner_reps` as inputs. NOT re-implemented.
- **Brick 2 `contiguousInterval_canonical_of_outerTrace`** — the corollary
  `contiguousInterval_of_outerTraceInputs` is ALREADY LANDED in `ZinanCh35OuterTrace.lean`
  (§4, lines 280–322); `contiguousInterval_canonical` itself is in `ZinanCh35Hclass.lean`
  (Brick 8). NOT re-implemented.

So the supplier wiring was complete on arrival; my new content is the confinement brick only.

## What this file PROVES (landed, axiom-clean)

1. `Side₁Confinement` (structure) — bundles the two genuinely-open discrete-Schoenflies fields,
   field types stated VERBATIM to the `ZinanCh35Iota` consumption sites:
   - `hreflect : ∀ ⦃x y⦄, M.toSimpleGraph.Adj (sideVertexToM₁ … x) (sideVertexToM₁ … y) →
       (sideMap₁ …).toSimpleGraph.Adj x y`  (target: `sideVertexToM₁_adj_reflect_canonical`)
   - `homit : ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ …)`  (target: `side₁_smaller_canonical`)

2. `homit_iff_exists_notMem_sideRegion₁` — **genuine reduction**: `homit` ⟺
   `∃ w, w ∉ sideRegion₁ data`, via the landed `ChordReconClose.sideVertexToM₁_range`
   (`Set.range ι = sideRegion₁`). Replaces the opaque quotient-range residue with the concrete
   geometric one (`sideRegion₁ = {w | ∃ d ∉ keptDel₁, M.tail d = w}` = tails of kept side-1 darts).

3. `side₁Confinement_of_inputs` — bundling constructor from explicit `hreflect`/`homit`.

4. `side₁Confinement_of_notMem_sideRegion₁` — bundles from `hreflect` + the SHARP residue
   `∃ w, w ∉ sideRegion₁ data`, discharging `homit` through (2).

5. `chordSideResidue₁_of_confinement` — feeds a `Side₁Confinement` (+ the non-confinement
   `ci`/`hshare`/`hchord`/`hLₛ`) into `ZinanCh35Iota.chordSideResidue₁_partial`, producing the
   full `ChordSideResidue`. This is the bundle's downstream payoff.

6. `side₁Confinement_of_jordan` — the design's requested supplier, in the only honest form: it
   THREADS the closed Jordan separation (`hNT.separates_closed data C hsub i₀ hleft hright`,
   exactly the `ZinanCh35Gates` API, consumed in the body) and takes the two sharp residues
   (`hreflect`, `homit_region : ∃ w, w ∉ sideRegion₁ data`) as explicit inputs, producing
   `Side₁Confinement`.

## Delta vs design (§3) — the honest block

The design proposed DERIVING `hreflect`/`homit` from `separates_closed` /
`jordan_simple_cycle2_unconditional`. **That derivation is not available from the landed
material, and I did not write it as a vacuous theorem.** Verified altitude mismatch:

- `separates_closed` / `SphereChordSeparation` / `SidesDisjoint` / `Separates` are **face**-level
  dual-non-reachability: `Separates data := data.face₂ ∉ data.side₁`
  (`PlanarMapChordSplit.lean:266`); `SphereChordSeparation := ¬ ReflTransGen (ChordSplitAdj)
  face₁ face₂` (`PlanarMapSeparation.lean:211`). `ChordSplitAdj` is dual face-adjacency.

- `hreflect`/`homit` are **vertex/edge**-star confinement on `sideRegion₁` (the tails of kept
  side-1 darts, `keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`, `PlanarMapChordSplit.lean:412`).
  Proving an *internal* arc-2 vertex `w` has `w ∉ sideRegion₁` requires that NONE of `w`'s
  incident darts has its face in `side₁` — vertex-star confinement, strictly stronger than
  `face₂ ∉ side₁` (a chord endpoint's star meets both sides; the face-separation predicate says
  nothing about an internal arc-2 vertex's star). `hreflect` needs the edge analogue.

- There is no landed lemma bridging face-dual-separation to vertex-star/edge confinement. The
  whole chain documents this as the open item with NO producer: `ChordSplitFinal.lean` §3.3
  ("the side region … rest on the chord separation … no unconditional producer"),
  `ZinanCh35Iota.lean` header ("no `ChordSplitRegions` producer in the repo … the open
  discrete-Schoenflies item"), `PlanarMapChordSplit` module docstring.

I also searched for any vertex-star/incidence confinement API (`grep` over
`BoundaryVertex|star|incident|vertexDarts|tail.*side₁|confin` in the side-split files) — none
exists. So the residues are genuinely unlanded planar content, not a gap in my wiring.

## Residues (exact open goals) — both non-vacuous, both concrete

These are the two inputs of `side₁Confinement_of_jordan` / the `Side₁Confinement` fields that the
open discrete-Schoenflies layer must supply:

- **R1 (edge confinement, `hreflect`)**:
  ```
  ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
    M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
        (sideVertexToM₁ data hsep a₀ a₁ hne y) →
      (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y
  ```
  Content: an ambient `M`-edge between two side-1-region vertices is realised by a side dart
  (kept side-1 dart, or the fresh chord) — i.e. it does not "cross the separating cycle". Needs
  edge-level Jordan confinement.

- **R2 (vertex omission, sharpened `homit`)**:
  ```
  ∃ w : M.Vertex, w ∉ sideRegion₁ data
  ```
  where `sideRegion₁ data = {w : M.Vertex | ∃ d : D, d ∉ data.keptDel₁ ∧ M.tail d = w}`.
  Content: the opposite arc's internal vertex (`data.arc₂_internal_witness`, a boundary vertex
  ≠ u,v, UNCONDITIONAL) is not the tail of any kept side-1 dart. The witness exists; the
  not-in-`sideRegion₁` half is the vertex-star confinement residue.

  Note: `homit_iff_exists_notMem_sideRegion₁` makes R2 the *exact* equivalent of the opaque
  `∃ w, w ∉ Set.range (sideVertexToM₁ …)`; the arc-2 witness is the intended `w`, so R2 is
  one-step from `data.arc₂_internal_witness` once a vertex-star confinement lemma lands.

## Suggested next step (for whoever closes the Jordan layer)

A single lemma `tail_notMem_sideRegion₁_of_arc₂_internal` (or a general
`vertexStar_confined_of_separates`: for a boundary vertex `w` strictly inside arc 2, every dart
with `M.tail = w` has `M.dartFace ∈ side₂ ∪ {outerFace}`) discharges BOTH R2 (directly) and is
the natural lever for R1 (edge endpoints land in confined stars). That lemma is the genuine
discrete-Schoenflies content and is the right granularity to attack next; it consumes the
threaded `separates_closed` plus the planar embedding, which the abstract `CombMap` layer lacks.
