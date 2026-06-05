# File 10 reply: `ProofsInTheBook/ThomassenLists.lean`

## Status

**Complete and verified clean** on uisai1.

* `lake env lean ProofsInTheBook/ThomassenLists.lean` → 0 errors (only benign lint
  warnings: unused section variable `[DecidableEq α]` on a few lemmas, one
  `push_neg` deprecation, one unused `simp` arg, one unused `R`).
* `lake build ProofsInTheBook.ThomassenLists` → **Build completed successfully (8433 jobs)**.
* 0 `sorry` / `axiom` / `admit` / `native_decide` (the only textual "sorry" is the
  word `sorry`/`axiom`/`admit` inside a docstring sentence).
* `#print axioms` on all 9 headline declarations
  (`ChordSplitRegions.glue`, `ChordSplitRegions.chord_endpoints_colors_ne`,
  `deletedVertexToM_adj`, `deletedVertexToM_adj_reflect`,
  `deletedVertexToM'_bijective`, `deleteBoundaryVertex_extend_coloring`,
  `v0_neighbor_mem_fanPath`, `extend_avoid_of_fan`,
  `deleteBoundaryVertex_listColorable`) reports exactly
  `[propext, Classical.choice, Quot.sound]`.

Imports `PlanarMapSeparation` (transitively `PlanarMapChordSplit` and the whole
NearTriangulation stack), `PlanarMapFanSurgery`, and `ListColoring`. Owns nothing
else. 860 lines, namespace `ProofsInTheBook.ThomassenLists.CombMap`.

## What is implemented

### Section 1 — the Thomassen list invariant (task item 1)

`structure ThomassenLists hNT p q L cp cq` over a general `DecidableEq` color type
`α` (the book's `Fin 5` is an instance): `p,q` boundary-adjacent (a precolored
boundary *edge* `s(p,q)`), `L p = {cp}`, `L q = {cq}`, `cp ≠ cq`, every other
boundary vertex `3 ≤ (L v).card`, every interior (non-boundary) vertex
`5 ≤ (L v).card`. Plus consequences `p_ne_q`, `cp_mem`, `cq_mem`, `list_nonempty`.

### Section 2 — chord-split transport (task item 2)

`opus-f6-reply.md` states explicitly that the side maps `sideMap₁/₂` live on the
foreign dart type `keptSide ⊕ Fin 2`, are built only conditionally on `Separates`,
and **have no `NearTriangulation` instance and no side-vertex-to-`M`-vertex
correspondence** (that correspondence is part of the same unbuilt face/Euler
classification). So the faithful, provable form of the chord-split list step is
stated at the `M`-vertex level via `structure ChordSplitRegions`: the chord
partitions `Vertex M` into two regions `s₁,s₂` overlapping exactly in the chord
endpoints `{u,v}`, every `M`-edge confined to one region, precolored edge `pq` on
side 1, chord `uv` an edge of `M`. Proved:

* `chord_endpoints_colors_ne` (task 2b core): `c₁ u ≠ c₁ v` because `uv` is an
  edge of side 1 — the genuinely new forcing fact.
* `forcedLists` + `forced_listValid` (task 2b): the side-2 lists with `u,v` forced
  to `{c₁ u},{c₁ v}`, and that a side-2 coloring agreeing on the endpoints picks
  from them.
* `glue` (task 2c): a side-1 coloring + a compatible side-2 coloring (agreeing on
  the chord endpoints) combine to `IsListColoring M.toSimpleGraph L c`, via
  `ListColoring.isListColoring_glue`.

**Honest scope note**: the transport is stated on `M.toSimpleGraph` with the two
side-vertex-sets, *not* on the foreign `sideMap₁/₂` objects, because those carry
no near-triangulation / vertex map at the current build state. This is the
operationally meaningful content of the chord split (a coloring of each side
glues to a coloring of `M`); when f6's separation/face-classification layer later
exposes `NearTriangulation (sideMap)` plus the kept-dart vertex map, this glue is
the consumer.

### Section 3 — boundary-deletion transport, the review's Case 2 bookkeeping (task item 3)

Here the side-vertex map **is** canonically available. Defined and proved:

* `deletedVertexToM` — the kept-dart map `⟦e⟧ ↦ ⟦e.1⟧`, with
  `deletedVertexToM_injective`, `deletedVertexToM_adj` (graph hom), and
  `deletedVertexToM_adj_reflect` (an `M`-edge avoiding `v0` lifts back to a
  deleted-map edge — via `dart_notMem_deleteVertexSet_of_endpoints_ne`).
* `deletedVertexToM_ne_v0` (image avoids `v0`) + `deletedVertexToM'_bijective`:
  the map is a **bijection onto `{Q // Q ≠ ⟦d0⟧}`** (injective between equinumerous
  finite types, cardinality from `R.vertexQuotient`). This gives a canonical
  section `sectionToDeleted` — so I never need the abstract reconstruction equiv
  to agree with the natural map.
* `deleteFanLists` (the review's `C'`): remove the two reserved colors `γ,δ`
  **only at the fan interior vertices** `z₁,…,z_t` (`fan.interior`); everything else
  keeps `L`. `deleteFanLists_card_ge_three` (interior `≥5` → `≥3` after removing
  two), `deleteFanLists_notMem`, `deleteFanLists_subset`.
* `v0_neighbor_mem_fanPath`: every `M`-neighbour of `v0` lies on the exposed fan
  path `x,z₁,…,z_t,w` (from `NeighborRotationOrder.vertexDarts_eq` + `heads_eq`,
  re-orienting the realizing dart to tail `v0`). Proved fully — no isolation needed.
* `deleteBoundaryVertex_extend_coloring`: a deleted-map coloring `c` from lists
  `L' ⊆ L∘toM` extends to `IsListColoring M.toSimpleGraph L (extendColoring R c a)`
  whenever the `v0`-color `a ∈ L v0` avoids every surviving neighbour. Properness
  off `v0` is reflected through `deletedVertexToM_adj_reflect`; at `v0` it is the
  avoidance.
* `extend_avoid_of_fan`: **the avoidance discharge** — choose `a ∈ {γ,δ}` with
  `a ≠` color of `w`, and prove the full neighbour avoidance: fan interior
  vertices avoid `γ,δ` (`color_ne_reserved_of_fan` from `deleteFanLists`), the
  endpoint `x` (= precolored `p`, `cp ∉ {γ,δ}`) avoids them (hypothesis
  `hx_avoid`), and `w` is avoided by the choice of `a`.
* `deleteBoundaryVertex_listColorable`: assembles the above into a single
  `ListColorable M.toSimpleGraph L` endpoint from the fan, the reconstruction `R`,
  `γ,δ ∈ L v0` distinct, the deleted-map coloring, and the two endpoint conditions.

## Conditional hypotheses (the known upstream walls, carried as explicit parameters)

* `NearTriangulation.FanSurgeryReconstruction hNT d0` — the f7/fan-surgery dart-level
  reconstruction (used only for the vertex-quotient cardinality giving the section).
* `BoundaryVertexFan hNT v0` — the fan certificate (used for the neighbour
  enumeration and the fan-interior list shrink).
* `ChordSplitRegions` — the `M`-level chord partition (the chord-split analogue of
  `Separates`-conditioned side data).

None is a hidden assumption: each is a satisfiable object the upstream surgeries
produce (the tetrahedron `t=1` witnesses the deletion case; any genuine chord
gives the partition), so the conditional endpoints are **not vacuous**. Everything
not touching those parameters is proved.

## Verification commands run

```
rsync -az .../ThomassenLists.lean uisai1:.../ProofsInTheBook/
ssh uisai1 'lake env lean ProofsInTheBook/ThomassenLists.lean'        # 0 errors
ssh uisai1 'lake build ProofsInTheBook.ThomassenLists'                # 8433 jobs OK
ssh uisai1 'lake env lean audit_f10.lean'  # #print axioms → core 3 only, all 9 headlines
```
