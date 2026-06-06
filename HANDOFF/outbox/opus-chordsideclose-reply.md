# ChordSideClose.lean — kept-side connectivity CLOSED → `Side₁IsDisk` UNCONDITIONAL

## Status: the one remaining topological fact of the Ch35 chord case is PROVED

`SubmapPlanar.lean` had reduced the chord-side disk fact to a single input:
`(sideKeptMap₁ data hsep).Connected` (the genus-0/no-handle core was already proved there,
`side₁IsDisk_of_connected` discharging the Euler half from connectivity alone). This file
**proves that connectivity unconditionally** from the chord-split structure, and assembles
the unconditional side-1 disk fact.

New file (owned, only file touched, fresh — the prior partial was overwritten):
`ProofsInTheBook/ChordSideClose.lean` (454 lines). Imports `ProofsInTheBook.SubmapPlanar`.
Branch `main`; no commits; no branch switch; no codex/OpenAI tooling; never ran lake/lean on
the Mac (kernel-panic rule observed — verified exclusively on uisai1).

## Headline theorems (all clean-3)

- **`keptSideRawConnected`** — every two kept side-1 darts are connected through the *raw*
  relation `rawStep₁ = dartStepRel M.σ (rawAlpha …)`. The genuine dart-graph reachability
  fact "the side is the closure of one Jordan region", **proved** (not isolated).
- **`sideKeptMap₁_connected`** — `(sideKeptMap₁ data hsep).Connected`, UNCONDITIONAL (from
  the chord-split data + `Separates` alone). This is exactly the hypothesis
  `SubmapPlanar.side₁IsDisk_of_connected` consumed.
- **`side₁IsDisk_unconditional`** — `ChordDisk.Side₁IsDisk data hsep` from `(data, hsep)`
  alone: the Euler/genus half is SubmapPlanar's proved core, the connectivity half is the
  raw reachability proved here, and the kept-dart witness is `M.φ data.dart` (`ref_kept`).
  **The `hconn` hypothesis of `side₁IsDisk_of_connected` is removed.**

## Verification (server uisai1, real olean chain)

- `lake env lean ProofsInTheBook/ChordSideClose.lean` → **RC = 0**, zero errors.
- `lake build ProofsInTheBook.ChordSideClose` → **Build completed successfully (8455 jobs).**
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → only the docstring disclaimer
  (lines 47–48). No `sorry`/`axiom`/`admit`/`native_decide`.
- `#print axioms` on `keptSideRawConnected`, `sideKeptMap₁_connected`,
  `side₁IsDisk_unconditional` → **clean-3 `[propext, Classical.choice, Quot.sound]`**
  (no `sorryAx`/`ofReduceBool`/`trustCompiler`).

## The mathematical content (the connectivity certificate)

`side₁` is the `ChordSplitAdj`-reachability closure of `face₁`. The kept side-1 dart set is
`keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {chordDart}`. We prove every kept dart raw-connects to
the reference `M.φ data.dart`:

1. **Raw face walk** (`rawFace_walk`, `rawFace_sameCycle_of_face_kept`): for a kept dart one
   `(M.σ * rawAlpha)`-step is one `M.φ`-step, so a `φ`-walk that stays kept is a single raw
   cycle. Within any side-1 face **≠ `face₁`** all darts are kept (`inner_notMem_keptDel₁`),
   so same-face kept darts raw-connect (`rawE_within_face_ne_face₁`). Within the chord
   triangle `face₁`, the only deleted dart is the chord dart; the two survivors
   `M.φ dart`, `M.φ² dart` connect by a single raw `φ`-step (`rawE_face₁_to_ref`, using the
   period-3 face-dart classification `face₁_dart_cases`).
2. **Cross-face step is a raw `α`-edge between kept darts** (`rawE_chordSplitAdj_step`): each
   `ChordSplitAdj` step `f → g` is witnessed by a **non-chord** edge, so its dart `d`
   (`dartFace d = f ∈ side₁`) and reverse `M.α d` (`dartFace = g ∈ side₁`) are both ≠ chord
   dart, hence both kept; `d ↔ M.α d` is one raw `α`-step.
3. **Induction on the reachability closure** (`rawE_inner_kept_to_ref`): threads (1)+(2) from
   `face₁` out to any side-1 face. Outer-arc kept darts reduce to the inner case via their
   raw `α`-edge to the (kept) inner reverse (`rawE_kept_to_ref`).
4. **Descent** (`keptSide₁_connected_of_rawConnected`): `SubmapPlanar.raw_eqvGen_descends`
   carries raw `EqvGen` to the kept subtype's `keptStepRel`, identified with the side map's
   `dartStep` (`sideSigma₁ = deleteSet M.σ keptDel₁`, `sideAlpha₁ = keptAlpha`).

## §3.3 verdict: FAITHFUL, non-vacuous, genuine strengthening — no residue in this file

- **FAITHFUL.** `sideKeptMap₁_connected` is exactly `(sideKeptMap₁).Connected`, the input
  `SubmapPlanar` left open; `side₁IsDisk_unconditional` is exactly `ChordDisk.Side₁IsDisk`.
- **Genuine advance (not re-wrapper).** `side₁IsDisk_of_connected` required an extra `hconn`
  argument; `side₁IsDisk_unconditional` removes it. The connectivity is proved by new
  dart-graph reachability, not assumed.
- **Non-vacuous.** Hypotheses are only `(data : ChordSplitData)` and `(hsep : Separates)`;
  `Separates` is the chapter's named, satisfiable Jordan residue (it holds on the genus-0
  sphere witness and is produced unconditionally for the genuine data by
  `WitnessFinal.separates_final` modulo its own Jordan inputs). No connectivity/genus premise
  remains, so no §3.3 vacuity.

## Precise residue (what still blocks fully unconditional `nearTriangulation_five_colorable`)

The kept-side connectivity is **closed**. What this file does NOT close, and could not from
within `ChordSideClose.lean` (sole owned file), are the remaining `ChordSideReconstruction`
fields and the chordless branch — repeatedly flagged across `ChordDisk`, `ChordSplitNT`,
`PlanarMapChordSplit`, `ThomassenLists` docstrings as the genuinely-unbuilt face/Euler /
discrete-Schoenflies classification, NOT synthesizable at the combinatorial-map layer:

1. **`ChordSideReconstruction.N` as a `NearTriangulation`** (item 2, boundary structure): I
   proved `Side₁IsDisk` (and hence, via `ChordDisk.chordDisk_produces_isSphereMap` + the
   `AnchorsShareBoundaryFace` local fact, `sideMap₁.IsSphereMap`), but turning the side map
   into a `NearTriangulation` requires its **outer boundary cycle** (the boundary arc `u..v`
   + duplicated chord edge) and the **inner_tri** field — the boundary-cycle construction the
   task lists, not derivable here.
2. **`ι_surj`** (item 2, side-vertex correspondence): the side-vertex-to-`M` correspondence
   surjective onto the region. The `ChordSplitNT`/`ThomassenLists` docstrings state this is
   "part of the same unbuilt face/Euler classification" — the irreducible discrete-Schoenflies
   content, the chord analogue of the chordless branch's `deletedVertexToM`.
3. **Chordless branch `ChordlessOracle`** (item 3): the fan-surgery / merged-arc Jordan data
   + `deleted_lists` relabeling, the same irreducible boundary-deletion Jordan content carried
   in `FanSurgeryReconstruction`.

So `five_colorable` remains CONDITIONAL on `ChordRecursiveDichotomy` / `JordanInput`, but the
residue has shifted again: **the kept-side connectivity — the single remaining topological
fact that SubmapPlanar's no-handle core left open — is no longer in it.** The blocking facts
are now strictly the boundary-cycle / region-correspondence (`ι_surj`) classification and the
chordless oracle, all of which are the documented unbuilt Jordan/Euler classification, not the
connectivity/handle content that is now proved.

## Threading note

`side₁IsDisk_unconditional : (data, hsep) → ChordDisk.Side₁IsDisk data hsep` is the drop-in
replacement for any downstream use of `SubmapPlanar.side₁IsDisk_of_connected` (it discharges
its `hconn` argument). Downstream wiring (into `chordDisk_produces_isSphereMap` and then the
`ChordSideReconstruction.hN`/`N` fields) is owned by `ChordSplitNT.lean` / `ChordDisk.lean`,
not by this file; the unconditional connectivity is now available to them.
