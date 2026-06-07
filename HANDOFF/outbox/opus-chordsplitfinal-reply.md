# Ch35 chord-split: the side near-triangulations UNIFIED into the generic `ChordSideReconstruction` framing that `chord_case_recursive` consumes — NOT the free-anchor `sideMap₁` detour. New file `ProofsInTheBook/ChordSplitFinal.lean`, RC=0, build OK (8458 jobs), all 8 headlines clean-3.

## Status (honest, §3.3): framing UNIFIED + every proven piece baked in; headline stays CONDITIONAL on ONE isolated discrete-Jordan residue. NOT unconditional — and that is faithful to the source, not premature.

The orchestration asked to build the two side near-triangulations in the SAME framing
`ThomassenInduction`/`ChordSplitNT.chord_case_recursive` consumes (the generic
`ChordSideReconstruction` with vertex correspondence `ι`), built from `M` directly with correct
structure baked in, NOT through the `sideMap₁`-with-free-anchors detour — then thread to an
UNCONDITIONAL `nearTriangulation_five_colorable` + the Five Colour Theorem.

**What is genuinely closed (the framing unification — the maximal faithful advance):**

1. **`chordSideReconstruction_of_chord`** — THE PRODUCER, PROVED. Builds a full
   `ChordSplitNT.ChordSideReconstruction hNT (sideRegion₁ data) L` — the exact generic shape
   `chord_case_recursive` consumes — for one side of the chord, **directly**, with the proven
   pieces baked in:
   - `N := sideMap₁`, `hN := ChordSideNT.chordSideNearTriangulation_of_share` (the side
     `NearTriangulation`: `sphere` = the **proved** disk core `side₁_sphere_unconditional`
     = genus-slack `eulerChar=2` (SubmapPlanar) + kept-side connectivity (ChordSideClose) +
     genus-0 face count (ChordFaceCount); `inner_tri` = the proved splice-untouched +
     chord-triangle face-size machinery (ChordInnerTri/ChordFaceFinal), carried by
     `ContiguousInterval`);
   - `ι := sideVertexToM₁`, with **`ι_mem`** (`ChordReconClose.sideVertexToM₁_mem`) and
     **`ι_surj`** (`ChordReconClose.sideVertexToM₁_surjective`) **proved and plugged in
     directly**; `Lₛ_eq := rfl` (pullback lists by construction).
   - The genuinely-unbuilt fields (`ι_inj`, full `ι_adj`/`ι_adj_reflect`, the side Thomassen
     lists `pₛ qₛ cpₛ cqₛ hLₛ`, `smaller`) are isolated into ONE named structure
     `ChordSideResidue`.
   This is the framing UNIFICATION: the side is now genuinely a `ChordSideReconstruction`
   (the recursion's input type), built from `M`, NOT a free-anchor `sideMap₁` object kept
   apart from the recursion path. The ~17-round anchor tangle (`ChordAnchorInst.ChordCapData.
   bigon_close`, `keptPhi d₂ = d₁`) is **not** on this path: the assembler consumes the proven
   `ContiguousInterval`/`Side₁AnchorsShareFace` directly, never re-deriving the bigon wrap.

2. **`chordRecursionData_of_branchResidue` / `chordBranch_colorable`** — the two side
   reconstructions + the `ChordSplitRegions` glue assemble a `ChordRecursionData`, and
   `chord_case_recursive` fires on it (side colorings PRODUCED by recursion, not consumed).

3. **`nearTriangulation_listColorable_unified` / `nearTriangulation_five_colorable_unified`** —
   the headline in the unified framing: given the chord-recursive dichotomy `O`, every
   near-triangulation is (five-)list-colorable, with the chord branch recursing on the
   generic-shape side reconstructions. The `L' ⊆ L` precolor-forcing is reproved end-to-end.

4. **No-rewrapper + non-vacuity certificates** — `chordSideReconstruction_ι_eq` /
   `_hN_eq` certify the produced `ι`/`hN` ARE the proved orbit correspondence / side NT (not
   read from the residue); `chordSideResidue_mk` is the explicit constructor;
   `chordSideReconstruction_region_nonempty` certifies the target region `sideRegion₁` is
   nonempty (real surjection, not empty-domain vacuity).

New file (owned, fresh): `ProofsInTheBook/ChordSplitFinal.lean` (~370 lines). Imports
`ChordSideNT` + `ChordSplitNT`. **`ChordSplitNT.lean` NOT edited** (no wiring change was
needed — the generic `ChordSideReconstruction` already exposes exactly the fields the
assembler fills). Branch `main`; no commits; no branch switch; no codex/OpenAI tooling; never
ran lake/lean on the Mac (kernel-panic rule observed — verified exclusively on uisai1).

## Verification (server uisai1, real olean chain)

- `lake env lean ProofsInTheBook/ChordSplitFinal.lean` → **RC = 0**, zero errors.
- `lake build ProofsInTheBook.ChordSplitFinal` → **Build completed successfully (8458 jobs).**
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → only in docstring prose (one line:
  "...not papered over with `sorry`/`axiom`"); none in code.
- `#print axioms` on **all 8** headline results → **clean-3 `[propext, Classical.choice,
  Quot.sound]`** (no `sorryAx`/`ofReduceBool`/`trustCompiler`/`native`):
  `chordSideReconstruction_of_chord`, `chordSideReconstruction_ι_eq`,
  `chordSideReconstruction_hN_eq`, `chordSideReconstruction_region_nonempty`,
  `chordRecursionData_of_branchResidue`, `chordBranch_colorable`,
  `nearTriangulation_listColorable_unified`, `nearTriangulation_five_colorable_unified`.
- `ThomassenInduction.nearTriangulation_five_colorable` (the existing headline) UNCHANGED — no
  upstream file edited, no regression.

## §3.3 verdict: FAITHFUL framing unification; the headline is CONDITIONAL-honest, NOT unconditional. Why unconditional is NOT reachable (verified against the SOURCE, not premature)

The orchestration's premise — "the math (a chord splits an NT into two NTs) is standard; all
genus/connectivity/face/orbit pieces are proven; this is architecture consolidation" — does
NOT survive contact with the source. Tracing the actual dependency chain:

- **The chord-side near-triangulation is not assemblable from `M` alone.** The side region,
  its boundary cycle, the side/`M` face correspondence, and `ContiguousInterval` ALL rest on
  the chord **separation** `data.Separates`. `PlanarMapSeparation.lean` proves (lines 16-55,
  205-244) that `data.Separates ⟺ hNT.SphereChordSeparation` — **the combinatorial Jordan
  curve theorem for the chord** — and documents it verbatim as "the one isolated input … the
  combinatorial Jordan curve theorem … circular with the side Euler characteristic," with **no
  unconditional producer**. `WitnessFinal.separates_final` derives `Separates` only from a
  large bundle of explicit discrete-Jordan witnesses (`Ls`, `gen`, `nonarc_step`,
  `revbank_step`, `offcycle_step`, `capP/M_step`, and crucially `hcompat` — the no-teleport
  dual-path step that `opus-chordsident-reply.md` §6 records is false in its obvious form).
- **The genus/connectivity/face/orbit pieces ARE proven — but ALL conditional on `Separates`.**
  `eulerChar=2`, kept connectivity, `ι_surj`, the splice-untouched + chord-triangle inner-face
  sizes are all `(data.Separates) → …`. They do not remove `Separates` from the residue; they
  presuppose it.
- **The `CombMap` layer cannot synthesize it** (kernel-confirmed, `CutFaceLabel.lean`): the
  side-face↔`M`-face correspondence is genus-DEPENDENT; no genus-uniform orbit label of the
  right cardinality exists. So `ContiguousInterval` and the `Side₁AnchorsShareFace`/anchor
  data are genuine planar-embedding content, not bookkeeping.
- **Both branches carry the same residue with no producer.** `grep` finds no
  `def/theorem … : ChordRecursiveDichotomy`, no `… : SphereChordSeparation`/`: Separates`
  producer, and no `… : FanSurgeryReconstruction`/`: ChordlessOracle` producer. The chordless
  branch's boundary fields are the identical boundary-deletion discrete-Schoenflies content.

Fabricating `Separates`, `ContiguousInterval`, a boundary cycle, or a `ChordRecursiveDichotomy`
to force a green unconditional headline is exactly the §3.3 forbidden move (fake disk/face
correspondence / vacuous-or-fabricated structure); I did NOT do it. NO `sorry`/`axiom`/`admit`/
`native_decide`; no re-wrapper.

## Precise residue (the ONE named non-vacuous Prop blocking unconditional `five_colorable`)

The headline `nearTriangulation_five_colorable_unified` is CONDITIONAL on exactly:

> **`ChordRecursiveDichotomy α`** — the uniform supplier, for every near-triangulation with the
> Thomassen lists, of EITHER a chord recursion datum `ChordRecursionData` OR a chordless oracle
> `ChordlessOracle`.

Concretely (state math vs formalization-architecture):

- **State math (the genuine gap):** the discrete **Jordan–Schoenflies separation** of a chord
  in a genus-0 near-triangulation — i.e. `hNT.SphereChordSeparation data.chord` (`⟺ Separates`),
  the combinatorial Jordan curve theorem. This is a real theorem of discrete planar topology,
  not wiring. From it, the per-side `ContiguousInterval` (boundary cycle + inner-triangulation)
  and the `ChordSideResidue` vertex/list/decrease fields follow with the proven machinery; the
  chordless branch needs the analogous boundary-deletion Jordan data.
- **Non-vacuity (NOT a hidden `False`):** `ChordRecursiveDichotomy` IS inhabitable —
  `ChordSplitNT.ChordRecursionData.ofComponents` is the explicit chord-branch constructor and
  `chord_recursive_produces_colorings_not_consumes` certifies it fires; `ChordlessOracle` is the
  same datum the existing `JordanOracle` path consumes. The dichotomy is the genuine geometric
  case-split, satisfiable in principle — it is simply not derivable inside the abstract
  `CombMap` layer (the §3.3 satisfiability check passes; only the *unconditional producer* is
  absent, which is the Jordan theorem).
- **Formalization-architecture (what is NOW done):** the entire downstream of the dichotomy is
  closed and unified — the side is built in the generic `ChordSideReconstruction` shape with
  every proven genus/connectivity/face/orbit piece baked in (`chordSideReconstruction_of_chord`),
  the recursion datum is assembled (`chordRecursionData_of_branchResidue`), and the chord case
  recurses+glues (`chordBranch_colorable`), threaded to the headline. The residue is reduced to
  the single isolated `ChordRecursiveDichotomy`, with the chord half's content explicitly named
  as `ChordBranchResidue`/`ChordSideResidue` (regions glue + per-side `ContiguousInterval` +
  `Side₁AnchorsShareFace` + the vertex/list/decrease fields).

Failing chain, concretely: to inhabit `ChordRecursiveDichotomy` you must, for an arbitrary NT,
produce `Separates` (= `SphereChordSeparation`); the only path to it is `separates_final`, whose
input `hcompat` (the dual-reachability-avoiding-cycle no-teleport step) has no unconditional
proof and is false in its obvious form (per `CH35_BRIDGE_DESIGN.md` §6 /
`opus-chordsident-reply.md` §6). This is the same single wall every prior round isolated; this
round removes the *framing* obstruction (the side is now in the recursion's own shape, no
free-anchor detour) and pins the residue to one named, satisfiable Prop.

## Threading note

`chordSideReconstruction_of_chord` is the drop-in side producer for `ChordRecursionData.R₁`/`R₂`.
Once a downstream layer supplies, for the correct chord-cap anchors at `u, v`: (i) the chord
separation `Separates`, (ii) the per-side `ContiguousInterval` + `Side₁AnchorsShareFace`, and
(iii) the `ChordSideResidue` vertex/list/decrease fields — plus the `ChordSplitRegions` glue and
the chordless `ChordlessOracle` for the other branch — `ChordBranchResidue` assembles, a
`ChordRecursiveDichotomy` is built, and `nearTriangulation_five_colorable_unified` becomes
unconditional. All of (ii)'s genus/connectivity/face content is already proved; (i) is the
Jordan theorem (the residue), and (iii)'s `ι_inj`/`ι_adj`/lists/`smaller` are the same
Jordan/Schoenflies boundary content.
