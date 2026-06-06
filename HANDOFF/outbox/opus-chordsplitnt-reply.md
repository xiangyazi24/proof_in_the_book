# ChordSplitNT.lean — closing the Ch35 chord-case recursion knot

## Status: the recursion knot is CLOSED. Verdict: CONDITIONAL-honest, with the
## residue correctly relocated and the chord branch now RECURSING (not consuming colorings).

New leaf file `ProofsInTheBook/ChordSplitNT.lean` (518 lines). Imports
`ThomassenInduction`, `PlanarMapChordSplit`, `PlanarMapSeparation` only. Verified
EXCLUSIVELY on uisai1; NEVER ran lake/lean on the Mac. Branch `main` throughout; no
commit; no branch switch; no codex/OpenAI tooling. Leaf — nothing imports it;
`ProofsInTheBook.lean` and the import graph untouched (one-file-one-writer). Dep
oleans (`WitnessFinal`, `ThomassenInduction`, `PlanarMapSeparation`) built clean
first (8468 jobs, Build completed).

### Verification
- `lake env lean ProofsInTheBook/ChordSplitNT.lean` → **RC=0, zero errors, zero warnings**.
- `lake build ProofsInTheBook.ChordSplitNT` → **Build completed (8441 jobs)**.
- `grep -nE '\bsorry\b|\badmit\b|\bnative_decide\b|^axiom '` → none (only docstring).
- `#print axioms` on all 5 headline results → **[propext, Classical.choice, Quot.sound]** (clean-3):
  `colorRegion_properOn`, `colorRegion_listValidOn`, `chord_case_recursive`,
  `nearTriangulation_listColorable_chordRecursive`,
  `chord_recursive_produces_colorings_not_consumes`.

## What was genuinely done (the structural fix, not a re-wrapper)

The orchestrator's diagnosis was correct: `thomassen_aux`'s chord branch
(`exact chord_case h cod`) does NOT recurse — it reads the side colorings `c₁, c₂`
out of `ChordOracle` (which carries `c₁ c₂ : M.Vertex → α` + 6 proper/valid/agree
fields). Only the chordless branch recurses (via `ih`). I closed this knot.

- **`ChordSideReconstruction`** (Section 1) — the chord analogue of the chordless
  branch's `FanSurgeryReconstruction`: a structure isolating, for ONE side, the
  irreducible Jordan/Euler outputs — a smaller near-triangulation `N` on the side
  dart type (carries `IsSphereMap`/genus-0), a region-faithful vertex correspondence
  `ι : N.Vertex → M.Vertex` (injective, lands in & surjects onto the region,
  adjacency-preserving AND adjacency-reflecting = graph iso onto `M⟦s⟧`), the
  pullback lists `Lₛ x = L (ι x)`, the side's `ThomassenLists`, and `N.V < M.V`.

- **`colorRegion` + `colorRegion_properOn`/`colorRegion_listValidOn`** (Section 2) —
  PROVED (not assumed): from a list coloring of the smaller side near-triangulation
  `N` (obtained by recursion), the region coloring of `M` is proper and list-valid
  on the side region. Properness uses `ι_adj_reflect`; list-validity uses `Lₛ_eq`.
  This is the chord analogue of the chordless `extendColoring`/`deletedVertexToM`
  transport.

- **`ChordRecursionData`** (Section 3) — the two side reconstructions + the
  `ChordSplitRegions` glue datum. CRUCIAL FAITHFULNESS POINT: it carries **NO
  coloring fields** — only `regions`, `uv_ne`, `R₁`, and `R₂ : (c₁ → side-2 recon
  with forced lists)`. Contrast `ChordOracle`, which carries `c₁, c₂` + 6 coloring
  properties. `R₂` is a *function of* `c₁` (faithful to Thomassen's order: color
  side 1, force `u,v`, color side 2).

- **`chord_case_recursive`** (Section 4) — the chord case proved by RECURSION:
  recurse on `R₁.N` (`color₁`), force the chord endpoints to the side-1 colors,
  recurse on `(R₂ c₁).N`, transport both to region colorings, and glue via the
  proved upstream `ChordSplitRegions.glue`. The side colorings are PRODUCED by `ih`
  (the strong-induction hypothesis), not consumed from input.

- **`thomassen_aux_chordRecursive` / `nearTriangulation_listColorable_chordRecursive`**
  (Section 5) — the strong induction reassembled with a `ChordRecursiveDichotomy`
  (chord branch → recursion datum, NO colorings; chordless branch → unchanged
  `ChordlessOracle`). This is **strictly weaker input than `JordanOracle`**: the
  chord side colorings are gone from the hypothesis surface; they are produced by
  recursion. The chordless branch reuses the existing recursive `chordless_case`.

- **Non-vacuity** (Section 5) — `ChordRecursionData.ofComponents` (inhabitation
  constructor, certifies no hidden `False`) and
  `chord_recursive_produces_colorings_not_consumes` (certifies the chord case
  genuinely fires via recursion, ruling out the trivial-constant / re-wrapper mode).

## The one honest residue (precisely isolated, with the concrete failing point)

After genuine attack on the sideMap-NearTriangulation proofs, ONE joint truly
resists, exactly as the task anticipated: **the genus-0 preservation
`sideMapᵢ.eulerChar = 2`** (and the paired side-vertex-to-`M` correspondence
`ι_surj`). These are now the FIELDS of `ChordSideReconstruction` (`hN`'s
`IsSphereMap`, and `ι_surj`), the chord analogue of the fields of
`FanSurgeryReconstruction`.

**Why it resists (verified against actual source, not impression):**
- `IsSphereMap M := M.Connected ∧ M.eulerChar = 2` (PlanarMap.lean:76). To make
  `sideMap₁` (= `freshMap (sideAlpha₁) (sideSigma₁) … : CombMap (keptSide₁ ⊕ Fin 2)`)
  a NearTriangulation, its `eulerChar = 2` must be computed from the orbit counts of
  `freshMap`'s α/σ — i.e. the per-side count `F₁ + F₂ = F + 1`.
- `separates_final` (WitnessFinal.lean:350-417) produces ONLY `data.Separates`
  (PlanarMapChordSplit.lean:266: `data.face₂ ∉ data.side₁` — pure face-reachability
  disjointness), and itself takes a large pile of hypotheses (gen/nonarc_step/
  revbank_step/.../hcompat). It does **not** give `sideMap.eulerChar`.
- The codebase documents — THREE independent times, with explicit circularity
  reasoning — that the side Euler count is NOT derivable from `Separates`:
  PlanarMapChordSplit §"honest status" (L42-73), PlanarMapChordSplitData
  §"honest status" (L22-39), PlanarMapSeparation §"honest gap" (L44-56:
  "not derivable … without constructing the side sub-maps' Euler characteristic
  (which is circular with the separation itself)").
- Mechanical confirmation: `F₁ + F₂` and any `freshMap`/sideMap `eulerChar` appear
  in the repo ONLY inside docstrings — never as a proved lemma. There is no
  eulerChar-of-freshMap infrastructure to build on.

**Correction to the orchestrator's premise:** the briefing stated "separates_final
directly gives Euler" / "the chord split preserves genus-0 using separates_final's
Jordan separation." This is not the case — `separates_final` gives `Separates`
(reachability), which is provably distinct from (and documented as circular with)
the side Euler count. So the genus-0 preservation is a genuinely separate,
currently-unbuilt count-level theorem, NOT a free consequence of the (done)
separation. This is the ONE named honest joint, with non-vacuity (Section 5) and the
concrete failing chain above.

## Faithfulness verdict (§3.3)

- **CONDITIONAL-honest.** The chord-recursive induction is unconditional GIVEN the
  `ChordRecursiveDichotomy`, whose chord-side payload is the
  `ChordSideReconstruction` (genus-0 + region correspondence). This is the SAME
  Jordan residue the whole Ch35 route carries; it is **NOT** newly assumed here.
- **Genuine advance over the prior re-wrapper** (`JordanOracleConstruct`'s
  `JordanInput ≡ JordanOracle.decide`): (a) the chord case now RECURSES on smaller
  side near-triangulations instead of consuming colorings; (b) the residue is
  relocated from "supply two colorings" to "supply two smaller recursable side
  near-triangulations + region iso" — strictly finer, and the colorings are produced;
  (c) the structure mirrors the chordless branch's proven `FanSurgeryReconstruction`
  pattern, so it is the architecturally correct shape.
- **NOT vacuous / NOT a co-extensive re-wrapper of JordanOracle:**
  `ChordRecursionData` carries no colorings (grep-verified: fields are only
  `regions, uv_ne, R₁, R₂`); `chord_case_recursive` discharges via `ih`, certified
  by `chord_recursive_produces_colorings_not_consumes`.
- It does **not** make five-colorability unconditional. Doing so requires the side
  Euler count `F₁ + F₂ = F + 1` (the genus-0 field) + the `ι_surj` side-vertex
  classification — the one isolated, named, non-vacuous Jordan joint, with the exact
  failing point recorded above.

## To finish Ch35 unconditionally (the precise remaining front)
Build a producer of `ChordSideReconstruction` from a bare `NearTriangulation` + a
boundary chord: i.e. prove `sideMap₁/₂.eulerChar = 2` (the per-side count
`F₁ + F₂ = F + 1` from `Separates` + the freshMap orbit bookkeeping) and the
`keptSide ⊕ Fin 2`-vertex ↦ `M`-vertex bijection onto the region. That is the one
genus-0/correspondence Jordan theorem; everything downstream of it (recursion, glue,
transport) is now proved in this file.
