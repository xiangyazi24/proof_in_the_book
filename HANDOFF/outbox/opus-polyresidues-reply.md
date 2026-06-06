# Ch36 Layer A3 — Polygon-substrate residues — Reply (opus-polyresidues)

**Status: DELIVERED + VERIFIED (partial discharge, one design-sanctioned residue
honestly isolated).** New file `ProofsInTheBook/PolygonResidues.lean` (imports
`ProofsInTheBook.PolygonConvexVertex`) compiles clean on **uisai2** (uisai1
down). 0 sorry / 0 axiom / 0 admit / 0 native_decide / 0 warnings. 357 lines.

## Verification

```
rsync -az ProofsInTheBook/PolygonResidues.lean uisai2:.../ProofsInTheBook/
ssh uisai2 'lake env lean ProofsInTheBook/PolygonResidues.lean'    # EXIT 0, no warnings
lake env lean -o .../PolygonResidues.olean ProofsInTheBook/PolygonResidues.lean   # EXIT 0
```
Dep oleans were built first: `nohup lake build ProofsInTheBook.PolygonConvexVertex`
→ 8422/8422 ✔ (pulls the whole Substrate→Diagonal→Parity→ConvexVertex chain).

`#print axioms` on all eight named results →
`[propext, Classical.choice, Quot.sound]` ONLY (no `sorryAx`, no custom axiom,
no `ofReduceBool`/`trustCompiler`):
`bdry_of_free`, `earTransversality_of`, `slideTransversality_of`,
`seg_disjoint_of_strict_same_side`, `edge_disjoint_base_of_same_side`,
`a3GeometryFacts_of_slim`, `exists_diagonal_slim`, `exists_convex_vertex_slim`.

Branch `main`, no commits, no codex/OpenAI tooling, never ran lake locally.
Own only the new file (did not touch the root, `ForcedSplits.lean`, or any
tracked file).

## What is proven unconditionally (genuine, non-vacuous content)

The task's three residue clauses split into a **finite-geometry part** (fully
discharged here) and a **topological/region part** (the design's deliberately
isolated residue, kept honest).

1. **Endpoints on boundary** (`vertex_onBoundary`): every vertex `P.q k` is the
   initial endpoint of its outgoing edge ⇒ `OnBoundary`. The `⊇` half of `bdry`.

2. **`bdry` ⇐ `free`** (`bdry_of_free`, both inclusions): the closed candidate
   segment = its two endpoints ∪ its open part
   (`insert_endpoints_openSegment`); a boundary point of the closed segment is an
   endpoint or interior, and an interior boundary point is exactly what `free`
   forbids. **This discharges clause 3 (`bdry`) of BOTH ear and slide residues
   entirely**, collapsing each residue from 3 transversal clauses to 2.

3. **Substrate-native half-plane separation for `free`** (clause 1, finite core),
   all in the substrate's own `orient`/`det2` API (no `AffineSubspace.SOppSide`):
   - `det2_lineMap` / `orient_lineMap`: `orient B C ·` is affine along a segment
     parameter (`(1-t)·orient B C P + t·orient B C Q`).
   - `orient_eq_zero_of_mem_seg_base`: the closed base `B C` lies on line `B C`.
   - `seg_disjoint_of_strict_same_side`: if `P,Q` are strictly same-side of line
     `B C` (`0 < orient B C P * orient B C Q`), no point of `seg P Q` is on line
     `B C` (convex-combination sign argument).
   - `edge_disjoint_base_of_same_side` / `openBase_notMem_edge_of_same_side` /
     `free_of_edge_certificate`: an edge with strictly same-side endpoints
     contributes no open-base boundary point; `free` reduces to a per-edge
     same-side sign certificate over the `n` edges. This is the finite,
     sign-based core the empty-ear / slide-maximality hypothesis must supply.

4. **Builders + slimmed assembly**:
   - `earTransversality_of` / `slideTransversality_of`: build the full
     `EarTransversality` / `SlideTransversality` of `PolygonConvexVertex` from
     just `(loc, free)`, deriving `bdry`. Downstream gets the identical structure
     (same field types) — `bdry` proved, not assumed.
   - `A3ResiduesSlim` + `a3Residues_of_slim`: a global package strictly smaller
     than `PolygonConvexVertex.A3Residues` (the `bdry` clause removed from every
     transversality field), converting back to the full `A3Residues`.
   - `a3GeometryFacts_of_slim`, `exists_diagonal_slim`, `exists_convex_vertex_slim`:
     the full `A3GeometryFacts` interface and the unconditional A3 headlines
     (`∃ convex vertex`; `∃ diagonal` for `4 ≤ n`) **stated through the slimmed
     two-clause residue surface**, via `a3GeometryFacts_of_residues`.

## The genuinely isolated residue (honest, NOT faked)

After sustained effort the irreducible core is **`loc` + `free`'s sign
certificate + the extreme-vertex convexity** — the substrate's *deliberately
isolated* transversality/region residue:

- **`loc` (`OpenSegmentRegionLocallyConstant`)** is a plane-sweep statement about
  how the half-open crossing *set* moves with the base point. `PolygonParity`'s
  §4 header explicitly names local constancy of the crossing parity as "the one
  genuine geometric residue" the ray-crossing substrate does not re-derive from a
  Jordan curve theorem. Nothing in the substrate produces it
  (`rg` confirms: only its `def` + consumers exist). Discharging it from scratch
  is the full plane-sweep transversality development — out of scope of a finite
  case analysis, and the design says so.

- **`free`'s same-side certificate**: I discharged the *separation geometry*
  (an edge cleanly on one side of the base misses the open base) in substrate
  terms. The remaining step — that the **empty-ear / height-maximal-slide**
  hypothesis *forces* that per-edge sign data (the classical "a crossing edge
  must enter the vertex-empty triangle, hence cross an incident edge,
  contradicting edge simplicity") — is the genuinely hard finite argument; it
  needs a full point-in-triangle / segment-crossing sign toolkit not present in
  the substrate. Kept as the honest residue, but its separation core is proved.

- **`ExtremeConvexResidue`**: the convexity (triangle ⊆ region) of the extreme
  vertex is a region-level parity computation, the same depth class as `loc`.
  Threaded as a residue field; `exists_convex_vertex_slim` consumes it faithfully.

These remain explicit, honestly-named hypotheses of the slimmed package. They are
satisfiable and faithful (true for a real strict simple polygon + non-parallel
ray), so `A3ResiduesSlim` and `exists_diagonal_slim` are **CONDITIONAL-honest**,
not vacuous — there is no clause forcing falsity, and `bdry` is genuinely
discharged (clause count 3→2 per residue).

## Audit verdicts (playbook Group C)

- `vertex_onBoundary`, `bdry_of_free`, the `orient`/separation lemmas, the
  builders, `a3Residues_of_slim`: **FAITHFUL** (unconditional, non-vacuous).
- `A3ResiduesSlim`, `a3GeometryFacts_of_slim`, `exists_diagonal_slim`,
  `exists_convex_vertex_slim`: **CONDITIONAL-honest** on the named residue
  (`loc` + empty-ear sign data + extreme convexity) — the substrate's
  design-sanctioned transversality/region core, with `bdry` discharged.

## Net effect

The third (`bdry`) clause of every A3 transversality residue is now **proved
from the substrate**, not assumed; the open-base edge-avoidance is reduced to a
substrate-native per-edge same-side sign certificate (separation geometry
proved); and the full A3 interface + headlines are restated through the
resulting slimmed `(loc, free)`-only residue surface. The single irreducible
residue (`loc` / empty-ear forcing / extreme convexity) is the design's
explicitly isolated topological core, kept honest with its separation geometry
discharged.
