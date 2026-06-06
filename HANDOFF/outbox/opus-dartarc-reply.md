# DartArc.lean — the dart-level boundary arc + concrete chord∪arc primal cycle (Ch35)

## Status: COMPLETE. 0 sorry / 0 axiom / 0 admit / 0 native_decide. Axioms clean-3.

File: `ProofsInTheBook/DartArc.lean` (663 lines). Imports only
`ProofsInTheBook.SeamIncidence`. Verified EXCLUSIVELY on uisai1 (`lake env lean`),
**EXIT 0, zero errors, zero warnings**. NEVER ran lake/lean on the Mac. Branch
`main` throughout; **no commits**; no branch switch; no codex/OpenAI tooling. Leaf
file — nothing imports it; import graph + `Audit.lean` untouched (one-file-one-writer).
Dep oleans (`lake build ProofsInTheBook.SeamIncidence`, 8454 jobs) built clean first.

## What this closes — the ONE structural residue from `opus-seaminc-reply.md`

`SeamIncidence.lean` closed the seam *mathematics* and isolated the **single**
genuine remaining residue as *structural infrastructure*:

> The concrete `SimplePrimalCycle` whose `dart : Fin len → D` is `chord ∪ arc`
> cannot be extracted: `BoundaryPath` (the output of `two_arcs`) records only the
> arc's *vertex and edge* lists — **no dart list**.

This file removes that residue **without touching `BoundaryPath`/`BoundaryArcSplit`**
(files I do not own). The key realization: `BoundaryCycle` already carries its own
`darts : List D` field (the normalized cyclic enumeration of the outer face orbit)
with `consecutive_phi` / `consecutive_vertex` and, under `VertexNodup`, a globally
tail-injective enumeration. A dart-level arc is just a **contiguous slice of this
list**, read off by index arithmetic. `BoundaryPath` is bypassed entirely.

## What was built (all verified, all clean-3 axioms)

### 1. The dart-level boundary arc — `DartArc` + `boundaryDartArc`
- `DartArc M C u v` — the dart-level analogue of `BoundaryPath`, carrying the
  **dart list** the latter omits: `arcDart : Fin len → D`, all on `C.darts`
  (`boundary`), chaining head→tail internally (`chain`), endpoints `u`/`v`
  (`tail_first`/`head_last`), tail-simple (`tail_nodup`), `v` not revisited
  (`head_last_ne_tail`).
- **`boundaryDartArc`** — the slicing constructor: from a `BoundaryCycle` with
  `VertexNodup`, a start position `p` and length `k` (`1 ≤ k`, `p+k < length`,
  no wrap), produces a real `DartArc` whose darts are `C.darts[p..p+k-1]`. *Every*
  `DartArc` field is **proven** from the existing boundary fields:
  - `chain` / `head_last` from `consecutive_vertex` (`tail (darts[next i]) =
    head (darts[i])`);
  - `boundary` from `List.getElem_mem`;
  - `tail_nodup` / `head_last_ne_tail` from `VertexNodup` (`darts.map tail` Nodup
    ⟹ tails injective ⟹ the `k+1` no-wrap positions give distinct vertices).
  This is exactly the dart-level analogue of one of `two_arcs`' two arcs (start
  position + length = positions of the chord endpoints in the boundary vertex
  list). **It materializes the dart list the seam reply said "the boundary
  machinery does not yet expose" — directly from existing fields, no new
  infrastructure, no assumption.**

### 2. The concrete chord∪arc `SimplePrimalCycle` — `ofDartArc`
- `chordArcDart A c = Fin.cons c A.arcDart` (length `A.len+1`; index 0 = chord,
  index `i+1` = `arcDart i`), with `chordArcDart_zero`/`chordArcDart_succ`.
- **`ofDartArc A c (2 ≤ A.len) (tail c = v) (head c = u)`** — the concrete
  `SimplePrimalCycle`. All **three** structure fields PROVEN (not assumed):
  - `consecutive` (head `dart i` = tail `dart (nextIdx i)`, cyclically): arc-internal
    from `A.chain`; the two **junctions** are `head c = u = tail (arc 0)` and
    `head (arc last) = v = tail c` — the chord's two endpoints meeting the arc's two
    endpoints, orientation `v → u` on the chord;
  - `tail_inj` (tails pairwise distinct): arc tails from `A.tail_nodup`; the chord
    tail `v` differs from every arc tail by `A.head_last_ne_tail`;
  - `len_ge` (`3 ≤ len`): `len = A.len + 1 ≥ 3` from `A.len ≥ 2` (the arc is
    internally nonempty — the dart-level analogue of
    `two_arcs_internally_nonempty_of_chord`).

### 3. The `ArcChordSeam` structural fields, instantiated — `arcChordSeamOfDartArc`
- `chordArcIsArc` — the arc-index predicate: `i'.succ` with `i'.val+1 < A.len`
  (both `dart i` and its cyclic successor are arc darts). This **excludes** the
  chord index `0` and the last-arc junction index — exactly the seam analysis's
  "2 chord darts + 2 junctions = non-arc steps".
- **`chordArc_arc_darts_mem`** — for an arc index, both `dart i` and
  `dart (nextIdx i)` lie on `C.darts` (by `A.boundary`). PROVEN, no assumption.
- **`arcChordSeamOfDartArc`** — assembles the full `ArcChordSeam` for
  `ofDartArc A c …`: the **structural** half (`B := C`, `IsArc := chordArcIsArc`,
  `arc_darts_mem` by `chordArc_arc_darts_mem`) is *built* from the dart-level arc;
  the F-side data (`Ls`/`factor`/`gen` + the non-arc/reverse/off-cycle/cap step
  obligations) is taken as arguments — the genuine, isolated residue.

### 4. The chord separation, end-to-end — `separates2_of_dartArc`
- **`NearTriangulation.separates2_of_dartArc`** — produces `data.Separates`
  (the Ch35 F-side chord-wall target) from: a `DartArc` on `hNT.outerCycle`, the
  chord dart `c` oriented `v→u`, the F-side seam data, the bridge witnesses
  `CutBridgeWitness2`, and the index/face wiring. Threads
  `arcChordSeamOfDartArc` into the proven `SeamIncidence.separates2_of_seam`. The
  concrete chord∪arc cycle is now **built**, not a hypothesis.

## Faithfulness / non-vacuity audit (playbook §3.3)

- **`DartArc` is NOT a vacuous interface.** `boundaryDartArc` *constructs* it from
  `C.darts` + `consecutive_vertex` + `VertexNodup` (all pre-existing fields). The
  non-vacuity `example` exhibits a concrete inhabitant (`len = k`, `arcDart 0 =
  C.darts[p]`). Every `DartArc` obligation is *satisfiable* — indeed *built* — not
  assumed. This is the decisive point the seam layer could not reach (it had to take
  the dart data as `ArcChordCycleData`; here it is produced).
- **`ofDartArc`'s three `SimplePrimalCycle` fields are PROVEN**, not smuggled into
  hypotheses. The non-vacuity examples confirm the dart family is genuinely
  `chord ∪ arc` (`dart 0 = c`, `dart (i+1) = arcDart i`), not a trivial constant.
- **No assumption-smuggling beyond the prior layer.** `arcChordSeamOfDartArc` takes
  only the genuinely external F-side seam data as arguments (the same `step_component`
  shapes `ArcChordSeam` already isolated as residue); it does NOT take `arc_darts_mem`
  or `IsArc` — those are *built*. `separates2_of_dartArc`'s remaining hypotheses
  (`CutBridgeWitness2`, the non-arc seam steps, `i₀/hleft/hright`, `hsub`) are exactly
  the design's irreducible interior-dual residue, correctly NOT claimed proven.
- **Same conclusion.** `separates2_of_dartArc` proves the identical `data.Separates`
  as `separates2_of_seam`/`separates2_of_core` — strictly more structure built, no
  weaker conclusion. Verdict **CONDITIONAL-honest**, residue = (external) bridge
  witnesses + non-arc seam steps + the elementary position-wiring (below).

## Axiom audit (all 5 headline decls)
`boundaryDartArc`, `ofDartArc`, `chordArc_arc_darts_mem`, `arcChordSeamOfDartArc`,
`separates2_of_dartArc` → all `[propext, Classical.choice, Quot.sound]`. No
`sorryAx`, no `ofReduceBool`/native.

## The ONE remaining wiring point (named, honest — elementary, NOT structural)

`boundaryDartArc` is parameterized by a start position `p` (of `u`) and length `k`
(with `v` at position `p+k`, no wrap). To instantiate it for a *specific* chord
`u,v` one must (i) locate `u`'s position `p := C.vertices.idxOf u` and `v`'s
position, (ii) pick the slice direction so the arc does not wrap (one of the two
arcs always satisfies `p+k < length` after a suitable rotation of `root`), and
(iii) discharge `2 ≤ A.len` from `two_arcs_internally_nonempty_of_chord` at the
dart level. This is **elementary list-position bookkeeping** (`idxOf` on a
`Nodup` vertex list + a rotation choice), *not* the structural gap the seam reply
named — the dart list now provably exists with all coherence inherited. I scoped
this file to the structural construction (the gap) + the slice constructor + the
non-vacuity witness; the per-chord position selection is left as the connecting
wiring, isolated and honest. It needs no new infrastructure.

## Ch35 frontier, stated precisely (post this layer)

The dart-level boundary arc is now **built**, not assumed. The F-side chord wall
`data.Separates` has a fourth route, the lightest in F-side *structural* input:

  Route A: `NumCyclesCutPhi2`            → `separates2_of_core`
  Route B: `BankStepCert.step_component` → `separates2_of_stepCert`
  Route C: `ArcChordSeam` (arc free)     → `separates2_of_seam`
  Route D (this file): dart-level arc *built* → `separates2_of_dartArc`

The remaining chapter-wide frontier (shared by all routes), with item (1) of the
seam reply now CLOSED:

1. ~~The arc-dart reconstruction~~ — **CLOSED** by `boundaryDartArc` +
   `ofDartArc` + `arcChordSeamOfDartArc`. The concrete chord∪arc
   `SimplePrimalCycle` and the `ArcChordSeam` structural fields are now built from
   the boundary cycle's own dart list. Residual: the elementary per-chord position
   selection (above).
2. **The non-arc seam steps** `nonarc_step` (chord dart + 2 junctions) +
   reverse/off-cycle/cap obligations — chord-LOCAL, finite, pinned to the chord
   caps' generator edges by `faceCorr2_capP_cases`/`capM_cases`. (Taken as the
   F-side `gen`-step arguments of `arcChordSeamOfDartArc`.)
3. **The bridge-witness data** `CutBridgeWitness2 i` (Part-A `SidesReach2` +
   no-teleport `FragmentCompatible2`) — the design's irreducible interior-dual
   input, per `PlanarMapBridgeWitness.lean`. **The genuine remaining mathematics.**
4. The chord-cycle wiring `hsub`/`i₀`/`hleft`/`hright` from `ChordSplitData`, plus
   the deletion-side data and the f13–16 side-map assembly.

Items (2),(4) are wiring/finite-chord-local; **the sole genuine mathematical
residue is now (3)**, the bridge witness — the dart-level boundary arc (formerly
item 1, the structural gap) is closed.

## Notes for wiring
- Leaf file. To activate: add `import ProofsInTheBook.DartArc` to
  `ProofsInTheBook.lean` and the 5 `#print axioms` lines to `Audit.lean` (import
  the module there too). I own only DartArc.lean.

## Verification command
    rsync -az .../DartArc.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
    ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
                && lake env lean ProofsInTheBook/DartArc.lean'
    → EXIT 0, zero errors/warnings; 5 axiom prints all {propext, Classical.choice, Quot.sound}.
