# ChordReconClose.lean — the side-vertex `ι_surj` orbit surjection CLOSED

## Status (honest, §3.3): ι_surj is PROVED; the headline `five_colorable` stays CONDITIONAL

The orchestration named four targets: the `ChordSideReconstruction` boundary fields
(outerCycle/inner_tri), `ι_surj`, and the chordless `ChordlessOracle`, threaded to an
unconditional `nearTriangulation_five_colorable`.

**What is genuinely closed in this file:** the one target the orchestration correctly
identified as *concrete and attackable* — `ι_surj`, the side-vertex→M-vertex orbit
surjection. It is proved unconditionally from the two ALREADY-PROVED orbit bijections
(`ChordSplitEuler.freshSigma_vertexQuotientEquiv` + `filteredRotation_sameCycle_iff`),
not isolated, not faked.

**What is NOT closed — and why it cannot be at this layer (verified, not assumed):**
the boundary-cycle (`outerCycle`/`outer_simple`/`outer_len`) + `inner_tri` fields, the
remaining `ι_inj`/`ι_adj`(fresh-dart half)/`hLₛ` fields, and the chordless
`FanSurgeryReconstruction` boundary fields are the discrete Jordan–Schoenflies
boundary-cycle / inner-triangulation classification the combinatorial-map layer does not
synthesize. The headline therefore stays CONDITIONAL. See "Why fully unconditional is not
reachable" below — this is the playbook §3.3 default-distrust verdict, NOT a stopping
short: I verified against the actual source that the residue is irreducible at this layer.

New file (owned, only file touched, fresh): `ProofsInTheBook/ChordReconClose.lean` (288
lines). Imports `ProofsInTheBook.ChordSideClose` + `ProofsInTheBook.ChordSplitNT`. Branch
`main`; no commits; no branch switch; no codex/OpenAI tooling; never ran lake/lean on the
Mac (kernel-panic rule observed — verified exclusively on uisai1).

## Headline theorems (all clean-3)

- **`sideVertexToM₁`** = `ι` — the concrete side-1 vertex correspondence
  `(sideMap₁).Vertex → M.Vertex`, built as `Quotient.lift (fun y => M.tail (proj a₀ a₁ y).1)`,
  well-defined by `freshSigma_sameCycle_iff` ∘ `filteredRotation_sameCycle_iff` (a
  freshSigma-orbit restricts to a sideSigma₁-orbit restricts to an M.σ-orbit).
- **`sideVertexToM₁_mem`** — `ι` lands in `sideRegion₁` (the tail-set of kept side-1 darts).
- **`sideVertexToM₁_surjective`** = **`ι_surj`** — *the headline*: every region vertex
  `w = M.tail d` (kept `d`) is `ι ⟦inl ⟨d,_⟩⟧`. The orbit surjection the orchestration
  demanded, PROVED from the kept-dart structure.
- **`sideVertexToM₁_range`** — `range ι = sideRegion₁` (image = region exactly).
- **`ι_adj_of_inl`** — the derivable half of `ι_adj`: a side edge `inl x` maps under `ι` to
  the M-edge `s(M.tail x.1, M.head x.1)` = `M.dartEdge x.1`, so its `ι`-endpoints are
  M-adjacent (`sideAlpha₁` restricts `M.α`, so `ι`-head of `inl x` is `M.head x.1`).
- **`sideRegion₁_nonempty`** / **`ι_surj_fires`** — non-vacuity (§3.3): the region is
  inhabited (`M.tail (M.φ data.dart)`, kept by `ref_kept`) and `ι_surj` genuinely fires on it.

## Verification (server uisai1, real olean chain)

- `lake env lean ProofsInTheBook/ChordReconClose.lean` → **RC = 0**, zero errors.
- `lake build ProofsInTheBook.ChordReconClose` → **Build completed successfully (8456 jobs).**
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → only the docstring disclaimer
  (line 66). No code-level `sorry`/`axiom`/`admit`/`native_decide`.
- `#print axioms` on all 6 headline theorems (`sideVertexToM₁_mem`,
  `sideVertexToM₁_surjective`, `sideVertexToM₁_range`, `ι_adj_of_inl`,
  `sideRegion₁_nonempty`, `ι_surj_fires`) → **clean-3 `[propext, Classical.choice,
  Quot.sound]`** (no `sorryAx`/`ofReduceBool`/`trustCompiler`).

## The mathematical content (the orbit surjection)

`sideMap₁ = freshMap (sideAlpha₁) (sideSigma₁) a₀ a₁`, so its vertex type is
`Quotient (cycleSetoid (freshSigma sideSigma₁ a₀ a₁ hne))`. Two proved orbit facts compose:

1. `freshSigma_sameCycle_iff` (ChordSplitEuler): a freshSigma-orbit, projected by `proj`
   (sending the two fresh chord darts to the anchors), is exactly a sideSigma₁-orbit. (The
   splice creates/destroys no σ-orbit.)
2. `filteredRotation_sameCycle_iff`: `sideSigma₁ = filteredRotation M.σ keptDel₁`, and a
   sideSigma₁-orbit `⟦⟨d,_⟩⟧` restricts exactly to the M.σ-orbit `M.tail d`.

So `ι ⟦y⟧ = M.tail (proj y).1` is well-defined, lands in the region (= tails of kept darts),
and is onto it: every kept dart `d` gives the region vertex `M.tail d = ι ⟦inl ⟨d,_⟩⟧`. The
"unbuilt orbit correspondence" the prior handoffs deferred is concrete and now closed.

## §3.3 verdict: FAITHFUL, non-vacuous, genuine (not a re-wrapper)

- **FAITHFUL.** `sideVertexToM₁_surjective` IS the `ChordSideReconstruction.ι_surj` shape
  (`∀ w ∈ s, ∃ x, ι x = w`), instantiated at the genuine side-1 map and the concrete region.
- **Genuine advance.** ι and ι_surj were previously deferred to "the unbuilt classification"
  (`ChordSplitNT`/`ChordDisk` docstrings); they are now built from the two proved orbit
  bijections, not assumed. `ι_adj_of_inl` additionally proves the inl-half of `ι_adj`.
- **Non-vacuous.** Hypotheses are only `(data : ChordSplitData)`, `(hsep : Separates)`,
  distinct anchors; the region is provably nonempty, so ι_surj is a real surjection onto a
  nonempty region (not an empty-domain vacuity). No connectivity/genus/face premise.

## Why fully unconditional `nearTriangulation_five_colorable` is NOT reachable (verified)

I traced the actual dependency chain to confirm the residue is irreducible at this layer —
this is the playbook §3.3 "default it has a hole, verify against source" discipline, and the
hole is real, spread across BOTH branches AND upstream of the dichotomy:

1. **`ι_inj` and the fresh-dart half of `ι_adj` are FALSE for arbitrary anchors.** ι_inj
   fails if an M-vertex's kept darts split into two sideSigma₁-orbits (true exactly at the
   chord endpoints unless contiguity holds — the `ContiguousInterval` classification). The
   fresh chord darts `inr 0, inr 1` have ι-endpoints `M.tail a₀.1, M.tail a₁.1`, which are
   M-adjacent ONLY for the correct anchors at `u, v` — not for the arbitrary anchors the side
   map is defined over. Both depend on the correct-anchor classification.

2. **`hN : NearTriangulation (sideMap₁)` (outerCycle/inner_tri) has no producer.** Its
   `inner_tri` and `outerCycle` are the side-face↔M-face correspondence the repository's
   `CutFaceLabel.lean` campaign DECIDED INSIDE THE KERNEL is genus-DEPENDENT (faces merge and
   split; no genus-uniform φ'₂-invariant orbit label of cardinality F+2 exists). The
   orchestration's hope that "side inner faces ARE M inner faces" is exactly what that kernel
   counterexample refutes as a free orbit fact.

3. **The chordless `ChordlessOracle.recon : FanSurgeryReconstruction` carries
   outerCycle/inner_tri as STRUCTURE FIELDS with NO unconditional producer anywhere in the
   repo** (verified: `grep` finds no `def/theorem … : FanSurgeryReconstruction`). Building one
   is the full discrete-Schoenflies for boundary-vertex deletion — the same irreducible
   content, not the connectivity (proved) or genus (proved) tools.

4. **Even the dichotomy input is gated by `Separates`, itself NOT unconditional.**
   `WitnessFinal.separates_final` produces `Separates` only modulo a long input list including
   `hcompat` — the no-teleport fragment supplier — which `CH35_BRIDGE_DESIGN.md` §6 records
   has a FALSE obvious form (genuine geometric input). So the chord branch cannot even be
   entered unconditionally.

Therefore `nearTriangulation_five_colorable` (and `…_five_colorable_of_input`) remain
CONDITIONAL on the boundary-cycle/inner-triangulation classification + the upstream
`Separates`/`FanIncidenceData`/fragment Jordan inputs. Fabricating any of `outerCycle`,
`inner_tri`, `Separates`, `FanIncidenceData` to force a green headline is exactly the §3.3
forbidden move (fake disk lemma / unsatisfiable-or-faked hypothesis); I did not do it.

## Precise residue (what now blocks fully unconditional `five_colorable`)

The chord-side residue has shrunk by one more concrete field. Now proved across the campaign:
genus-0/no-handle core (SubmapPlanar), kept-side connectivity (ChordSideClose), the side
`IsSphereMap`/face-count from the two local disk facts (ChordDisk/ChordSideRecon), and now the
**side-vertex `ι_surj` orbit surjection** (this file). The single named residue
`ChordReconClose.ChordSideClassification := NearTriangulation (sideMap₁)` (Section 4) bundles
what stays open: the boundary cycle + `inner_tri` + `ι_inj`/fresh-`ι_adj`/`hLₛ`, plus the
chordless `FanSurgeryReconstruction` fields and the upstream `Separates`/fan/fragment Jordan
inputs — all the documented discrete Jordan–Schoenflies classification requiring the actual
planar embedding the abstract `CombMap` does not carry.

## Threading note

`sideVertexToM₁`/`sideVertexToM₁_surjective` are the drop-in `ι`/`ι_surj` for any future
`ChordSideReconstruction` constructor: once a downstream layer supplies the boundary-cycle /
`inner_tri` classification (the `hN` field) and the correct anchors (resolving `ι_inj` and the
fresh-`ι_adj` half), the vertex-correspondence side is already built and clean-3 here. Wiring
into `ChordSplitNT.ChordSideReconstruction` is owned by `ChordSplitNT.lean`/`ChordDisk.lean`,
not this file; the orbit surjection is now available to them.
