# File 11 reply: `ProofsInTheBook/ThomassenInduction.lean`

## Status

**Complete and verified clean** on uisai1.  630 lines, 0 `sorry`/`axiom`/`admit`/
`native_decide`.  Namespace `ProofsInTheBook.ThomassenInduction`.  Imports
`ThomassenInduction` ⊇ `ThomassenLists` (the transport layer) + `PlanarMapFanExistence`
(the incidence-data / fan endpoints).

Verification:

```
rsync -az .../ThomassenInduction.lean uisai1:.../ProofsInTheBook/
ssh uisai1 'lake env lean ProofsInTheBook/ThomassenInduction.lean'   # 0 errors
ssh uisai1 'lake build ProofsInTheBook.ThomassenInduction'          # 8440 jobs OK
ssh uisai1 'lake env lean /tmp/audit_f11.lean'                      # #print axioms
```

`#print axioms` on all 9 headline declarations
(`thomassen_nearTriangulation_listColorable`, `thomassen_aux`, `base_case`,
`chord_case`, `chordless_case`, `nearTriangulation_five_list_colorable`,
`nearTriangulation_five_colorable`, `three_le_V`, `exists_boundary_edge`) reports
exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`ofReduceBool`/`trustCompiler`, no custom axioms.

Only benign warnings (5 × `push_neg` deprecation; a few unused-variable warnings from
the oracle's uniform `decide` signature).

## What is assembled

### The Jordan oracle (`JordanOracle α`) — the single permitted hypothesis bundle

`JordanOracle.decide` is stated uniformly over **all** dart types `D` and **all**
near-triangulations carrying `ThomassenLists`, returning `ChordOracle ⊕ ChordlessOracle`.
Uniformity is what lets the recursion pass the oracle to the strictly smaller deleted
map.  Two case data:

* `ChordOracle` — the `M`-vertex-level chord split (`ThomassenLists.ChordSplitRegions`,
  with chord endpoints `u,v`, `chord_adj : Adj u v`, `edge_confined`, `cover`,
  `overlap ⊆ {u,v}`) **plus** the two side region-colorings (`c₁` proper+list-valid on
  `s₁`, `c₂` on `s₂`, agreeing on `u,v`).
* `ChordlessOracle` — `BoundaryChordless`, the deletion site `v0`, the
  `FanIncidenceData` (which *constructs* the fan), the `FanSurgeryReconstruction recon`
  (the dart-level boundary-deletion Jordan data), `γ,δ ∈ L v0` distinct, `x = p`,
  `cp ≠ γ,δ`, `x,w ≠ v0`, and the existential `deleted_lists` (some precolored edge on
  the deleted map satisfies `ThomassenLists` with the `deleteFanLists` lists).

### Base case `M.V = 3` (`base_case`) — FULLY PROVED, no oracle

From `Fintype.card M.Vertex = 3` and `p ≠ q`, name the third vertex `r`; every vertex
is `p`, `q`, or `r`.  `r` has list `≥ 3` (boundary `≥ 3` / interior `≥ 5`), so
`L r \ {cp,cq}` is nonempty; color `p↦cp, q↦cq, r↦a`.  Properness holds for any edge
set on `{p,q,r}` since `cp,cq,a` are pairwise distinct.

### Chord case (`chord_case`) — PROVED via `ChordSplitRegions.glue`

The two side region-colorings from `ChordOracle` glue (proved upstream) into a list
coloring of `M`.

### Chordless case (`chordless_case`) — PROVED extension

The deleted map's list coloring (from `codLists = deleteFanLists`) extends across `v0`
by `deleteBoundaryVertex_listColorable`.  The precolored-endpoint avoidance `hx_avoid`
is **discharged** here (`chordless_hx_avoid`): `p = x` survives, is not a fan-interior
vertex (`fanX_notMem_interior`, from the chordless path-nodup), so its `deleteFanLists`
list is `L p = {cp}`; hence the deleted coloring at `p`'s image is `cp ≠ γ,δ`.

### The induction (`thomassen_aux` → `thomassen_nearTriangulation_listColorable`)

`thomassen_aux` is `Nat.strong_induction_on` over a vertex bound `n`, `∀`-quantified
over all `D, M`.  `three_le_V` (proved: outer cycle length `≥ 3` + nodup → `≥ 3`
distinct vertices) splits `M.V = 3` (base) from `3 < M.V` (oracle dichotomy).  Chord →
`chord_case`.  Chordless → recurse on the **strictly smaller** `M.deleteVertex d0`
(`deleted_smaller` from `recon.smaller`) to color it from `codLists`, then
`chordless_case`.  The deletion case is a genuine recursion (same dart type `D`,
`V-1`).

### Corollaries

* `exists_boundary_edge` — PROVED: the outer-cycle root dart gives an adjacent
  precolorable boundary edge `s(tail root, head root)`.
* `nearTriangulation_five_list_colorable` — PROVED (mod the per-`L'` oracle): uniform
  lists `≥ 5`; pick an adjacent boundary edge `p,q`, distinct precolors `cp ∈ L p`,
  `cq ∈ L q`, force singletons `L' ⊆ L`, apply the main theorem, lift via `mono_lists`.
* `nearTriangulation_five_colorable` — PROVED (mod oracle): constant list `Finset.univ`
  over a `≥ 5`-element color type, specializing the uniform theorem.

## The ONE isolated joint (named, honest)

**The chord-side recursion is delegated to the oracle's `ChordOracle`, not run.**

`opus-f10-reply.md` records that the chord-split *side maps* (`sideMap₁/₂`,
`PlanarMapChordSplit`) live on a **foreign dart type** `({d // d ∉ keptDel} ⊕ Fin 2)`
and carry **no `NearTriangulation` instance and no side-vertex-to-`M`-vertex
correspondence** (confirmed: the side maps establish only `α`/`σ`; the vertex map is
part of the unbuilt face/Euler classification).  Therefore the induction **cannot**
recurse on the chord sides the way it recurses on `M.deleteVertex d0` (which is a real
near-triangulation over the same `D` with `V-1`).

The missing topological piece — *a coloring of each side as a region coloring of `M`* —
is the single isolated joint, carried as the `c₁,c₂,proper₁₂,valid₁₂,agree_*` fields of
`ChordOracle`.  This is **not vacuous**: a genuine `ChordSplitRegions` exists for any
real boundary chord, and the side colorings are exactly Thomassen's chord step (color
side 1 by induction, force `u,v`, color side 2 by induction).  The glue
(`ChordSplitRegions.glue`) — the proved part — closes the case.  Verdict for the chord
branch: **CONDITIONAL-honest** on the chord-side vertex correspondence that upstream does
not yet expose.

The deletion branch's analogous residue — the deleted map's `ThomassenLists`
relabeling — is carried as the `ChordlessOracle.deleted_lists` field for the same
reason (the new-boundary vertex labelling is the deletion's Jordan-curve bookkeeping,
not synthesized by the combinatorial-map layer); the deletion *recursion itself* is
genuine.

Everything not touching the oracle (base case, glue, extension, `hx_avoid` discharge,
`three_le_V`, `exists_boundary_edge`, the forced-list bookkeeping of the corollaries,
and the well-founded strong-induction plumbing with the case dichotomy) is proved.

## Faithfulness verdict

* `base_case` — **FAITHFUL** (unconditional).
* `thomassen_nearTriangulation_listColorable` / `thomassen_aux` — **CONDITIONAL-honest**
  on `JordanOracle` (the chord-side correspondence + chord separation + boundary-deletion
  Jordan data), the explicitly-stated single permitted hypothesis bundle.
* corollaries — **CONDITIONAL-honest** on the oracle (per forced lists).
* The oracle's case data are satisfiable (tetrahedron `t=1` witnesses the deletion;
  any genuine chord gives the partition), so the conditional endpoints are **not
  vacuous** — no VACUOUS/IMPOSTOR pattern.
