# ChordSplitEuler.lean — the chord-split genus-0 orbit counts (Ch35)

## Status: V and E orbit counts of `freshMap` PROVED; genus-0 residue SHARPENED to
## one named face count. Verdict: CONDITIONAL-honest, residue precisely relocated.
## five_colorable is NOT made unconditional — see "Honest scope correction" below.

New leaf file `ProofsInTheBook/ChordSplitEuler.lean` (479 lines). Imports only
`ProofsInTheBook.ChordSplitNT`. Verified EXCLUSIVELY on uisai1; NEVER ran
lake/lean on the Mac. Branch `main` throughout; no commit; no branch switch; no
codex/OpenAI tooling. Leaf — nothing imports it; the import graph is untouched
(one-file-one-writer). Dep oleans (`ChordSplitNT` chain) built clean first
(8441 jobs, Build completed).

### Verification
- `lake env lean ProofsInTheBook/ChordSplitEuler.lean` → **RC=0, zero errors, zero warnings**.
- `lake build ProofsInTheBook.ChordSplitEuler` → **Build completed (8442 jobs)**.
- `grep -nE '\bsorry\b|\badmit\b|\bnative_decide\b|^axiom '` → none (only docstrings).
- `#print axioms` on all 7 headline results → **[propext, Classical.choice, Quot.sound]**
  (clean-3, no `sorryAx`, no `ofReduceBool`/`trustCompiler`):
  `freshMap_two_mul_E`, `freshMap_V`, `freshMap_eulerChar_eq_two_iff_faceCount`,
  `sideMap₁_eulerChar_eq_two_iff_faceCount`, `sideMap₂_eulerChar_eq_two_iff_faceCount`,
  `sphereWitness_eulerChar`, `freshFaceCount_satisfiable`.

## What was genuinely done (the new orbit-count infrastructure)

The orchestrator's diagnosis ("there is NO existing eulerChar-of-freshMap
infrastructure — you must BUILD the freshMap orbit-count lemmas") is exactly
right. This file builds it, and the result is that **two of the three orbit
counts are now proved purely**, and the genus-0 residue is sharpened to one
named face count.

- **Section B — `freshMap_two_mul_E` (E count, PROVED).** The edge count rises by
  exactly one over the kept side: `2·E(freshMap β ρ a₀ a₁) = |K| + 2`. Pure
  consequence of `freshAlpha` being a fixed-point-free involution (`2E = |D|`,
  `CombMap.two_mul_E_eq_card`) plus `|K ⊕ Fin 2| = |K| + 2`. The chord's single
  shared edge.

- **Section A — `freshMap_V` (V count, PROVED).** The vertex count equals the
  kept rotation's: `V(freshMap β ρ …) = Fintype.card (Quotient (cycleSetoid ρ))
  = numCycles ρ`. The two fresh darts are spliced *into* existing σ-orbits (one
  after each anchor), so no σ-orbit is created or destroyed. Proved via an
  explicit bijection of σ-orbit quotients `freshSigma_vertexQuotientEquiv` along
  the anchor projection `proj : K ⊕ Fin 2 → K`, whose well-definedness is the new
  lemma `freshSigma_sameCycle_iff` (two darts share a fresh σ-orbit iff their
  projections share a ρ-orbit). This is genuine new combinatorics — the orbit
  trace of the spliced rotation — about 130 lines.

- **Section C — `freshMap_eulerChar_eq_two_iff_faceCount` (the clean reduction).**
  With V and E pinned, `eulerChar(freshMap) = 2` is **equivalent** to one face
  count `FreshFaceCount : 2·F = |K| + 6 − 2·numCycles ρ` (= `F = E − V + 2`). In
  chord-split terms this is exactly the per-side `F₁ + F₂ = F + 1`.

- **Section D — instantiation at the genuine chord-split side maps.**
  `sideMap₁_two_mul_E`, `sideMap₂_two_mul_E`, `sideMap₁_V`, `sideMap₂_V` (the V/E
  counts at `sideMapᵢ = freshMap (sideAlphaᵢ) (sideSigmaᵢ) …`), and
  `sideMap₁/₂_eulerChar_eq_two_iff_faceCount`: `sideMapᵢ.eulerChar = 2` ⇔ the one
  face count of that side. This is the precise residue of the `hN` (IsSphereMap)
  field after V and E are retired.

- **Section E — non-vacuity (`freshFaceCount_satisfiable`).** A concrete genus-0
  fresh map `sphereWitness` (`K = Fin 2`, `β = swap 0 1`, `ρ = 1`, anchors `0,1` —
  the chord doubled into a sphere "theta"), with `V = 2`, `E = 2`, `F = 2` (all by
  `decide`, no `native_decide`), hence `eulerChar = 2` and `FreshFaceCount` holds.
  Certifies the isolated face count is a satisfiable arithmetic condition, NOT a
  disguised `False` (the §3.3 satisfiability obligation). It is also non-trivial:
  the equation depends on the actual face count, which depends on genus.

## The one honest residue (precisely isolated, with the concrete reason)

`FreshFaceCount` (the σα face-orbit count of the spliced face permutation) is the
single remaining Jordan/Euler input. It is **NOT** a free orbit-count fact:

- `eulerChar(freshMap β ρ a₀ a₁) = 2` is **false for generic** `β, ρ, a₀, a₁` —
  a higher-genus fresh map has `eulerChar < 2`. F is precisely the orbit count
  that V and E alone cannot determine (that is what Euler characteristic
  *measures*). Verified numerically: the count varies with the anchors.
- Decisively, the side construction (`PlanarMapChordSplit` §8) takes the splice
  anchors `a₀, a₁` as **arbitrary distinct parameters** ("the side map is well
  defined for any distinct anchors; the *correct* anchors are what make the outer
  boundary the arc-plus-fresh-chord, which is part of the
  separation/classification layer"). With arbitrary anchors the genus is not
  pinned, so `FreshFaceCount` for `sideMapᵢ` cannot follow from `Separates` alone
  — it additionally needs the correct anchors, which are themselves unbuilt
  classification data.
- This matches the repository's own discipline for the analogous boundary
  surgery: `CutCapSurgery.vertex_count` and `.face_count` are **structure fields**
  (the combinatorial-Jordan core), and only `edge_count` is proved purely
  (`PlanarMapCutCap.lean:488,506`). My Section A goes one step *further* than
  CutCap (it proves V, not just E, for the freshMap splice), but the face count is
  the same irreducible core CutCap also isolates.
- Consistent with the three upstream docstrings (`PlanarMapChordSplit` "honest
  gap" L61-73, `PlanarMapChordSplitData` "honest status" L22-39,
  `PlanarMapSeparation` "honest gap": "not derivable … without … the side
  sub-maps' Euler characteristic (which is circular with the separation itself)").

## Honest scope correction (must read)

The task framing asked to "discharge the `hN`/`ι_surj` FIELDS, producing a full
`ChordSideReconstruction`, and make `nearTriangulation_listColorable_chordRecursive`
UNCONDITIONAL → unconditional `five_colorable`." **This file does NOT achieve
that, and I assess it is not achievable at this layer without the unbuilt
classification:**

1. `hN : NearTriangulation N` requires the FULL `IsSphereMap` (Connected ∧
   eulerChar=2) **plus** an outer boundary cycle, inner-triangle property, and
   boundary simplicity (`NearTriangulation` has 6 fields, not just euler). Even
   the eulerChar=2 part reduces to the unprovable-here `FreshFaceCount`.
2. `ι_surj` is the side-vertex↦M graph-iso surjectivity onto the region — the
   side-vertex classification, the same unbuilt Jordan content.
3. The correct splice anchors are themselves classification data.

So `five_colorable` remains CONDITIONAL on `JordanInput`/`JordanOracle`, exactly
as before this file. What this file genuinely advances: it **retires the V and E
orbit counts** (previously unbuilt, now proved theorems) and **relocates the
genus-0 residue from "compute eulerChar from scratch" to "one named, satisfiable
face count `FreshFaceCount`"** — strictly finer than the prior state, with the V/E
two-thirds done and the exact remaining count named, satisfiable, and explained.

## Faithfulness verdict (§3.3)

- **CONDITIONAL-honest.** V count: FAITHFUL/unconditional. E count:
  FAITHFUL/unconditional. Genus-0 (eulerChar=2): CONDITIONAL on `FreshFaceCount`
  (the named face count), which is satisfiable (Section E) but not derivable here
  for the reasons above.
- **NOT vacuous / NOT a re-wrapper:** `freshMap_V` and `freshMap_two_mul_E` are
  genuine new theorems (the orbit-bijection `freshSigma_vertexQuotientEquiv` is
  real combinatorics, not a restatement). `FreshFaceCount` is certified
  satisfiable by a concrete `decide`-computed sphere witness — it is not a hidden
  `False` used to make the iff vacuous.
- **Does NOT make five-colorability unconditional** (see scope correction).

## To finish Ch35 unconditionally (the precise remaining front)
Prove `FreshFaceCount` for `sideMapᵢ` from `Separates` + the *correct* boundary-arc
anchors, by tracing the σα-orbits of `freshMap` against M's faces and using the
`Separates` disjointness/covering to count `F₁ + F₂ = F + 1`; then assemble the
remaining `NearTriangulation` fields (outer cycle, inner triangles) and the
`ι_surj` graph-iso. Everything *upstream* of those (the V and E counts, the
genus-0 reduction to a single face count, the recursion/glue/transport in
`ChordSplitNT`) is now proved.
