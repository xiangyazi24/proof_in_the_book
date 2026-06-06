# SeamIncidence.lean — the seam incidence at the chord application cycle (Ch35)

## Status: COMPLETE. 0 sorry / 0 axiom / 0 admit / 0 native_decide. Axioms clean.

File: `ProofsInTheBook/SeamIncidence.lean` (431 lines). Imports only
`ProofsInTheBook.SeamApplication`. Verified EXCLUSIVELY on uisai1
(`lake env lean`), EXIT 0, **zero errors, zero warnings**. NEVER ran lake/lean on the
Mac. Branch `main` throughout; no commits; no branch switch. No codex/OpenAI tooling.
Leaf file — nothing imports it; import graph + Audit.lean untouched (one-file-one-writer).
Dep oleans (`lake build ProofsInTheBook.SeamApplication`, 8453 jobs) built clean first.

## The mathematical key (what closes, and why the prior layer could not see it)

`SeamApplication.lean` carried the whole F-side residue on the **abstract**
`SimplePrimalCycle`'s `BankStepCert.step_component` and (correctly, for an abstract
cycle) declared the forward bank-end seam incidence "not derivable". The decisive
observation of THIS layer: the *application* cycle is `chord ∪ boundary-arc`, and the
arc darts live on the `NearTriangulation`'s **outer `BoundaryCycle`**, whose
`consecutive_phi` field says the cyclic dart successor is the `M.φ`-image. Hence:

> **Every step between two arc darts is `EqvGen.refl` on the single outer-face orbit
> — no generator edge, no embedding datum.**

This removes the *bulk* of `step_component` (all arc-arc steps) unconditionally. The
genuine residue collapses to the **non-arc** steps: the 2 chord darts (faces = the two
*distinct* inner triangles, `chord_incident_faces_distinct`) and the 2 arc↔chord
junctions, which the chord caps' generator edges bridge.

## What was built (all verified, all clean-3 axioms)

### 1. The face ↔ `phiLift`-orbit dictionary (the missing bridge)
- `phiLift_zpow_inl` : `(phiLift^n)(inl d) = inl ((φ^n) d)` (clean `Int.induction_on`).
- `phiLift_sameCycle_inl_iff` : `phiLift.SameCycle (inl d) (inl d') ↔ φ.SameCycle d d'`.
- `dartFace_eq_iff_sameCycle` : `dartFace d = dartFace d' ↔ φ.SameCycle d d'`
  (`M.Face` and `POrb M.φ` are the *same* `cycleSetoid M.φ` quotient).
- **`pOrbOf_phiLift_inl_eq_iff`** : `pOrbOf phiLift (inl d) = pOrbOf phiLift (inl d')
  ↔ M.dartFace d = M.dartFace d'`. This is the dictionary that converts every
  `step_component` orbit obligation into an elementary `dartFace` equality — recorded
  for the first time.

### 2. The arc-step closure (the key application fact)
- `pOrbOf_phiLift_inl_boundary` : any two darts of one `BoundaryCycle` share the
  `phiLift`-orbit (both have face = the boundary face).
- **`boundary_step_eqvGen`** : two boundary darts are `EqvGen`-connected under *any*
  generator relation, by outer-face reflexivity. **The arc half of `step_component`,
  free of all embedding data.**

### 3. The chord-dart faces (the genuine non-arc steps, located)
- `pOrbOf_phiLift_chord_distinct` : the two chord darts land in two *distinct*
  `phiLift`-orbits (the two inner triangles) — orbit-level form of
  `chord_incident_faces_distinct`.
- `pOrbOf_phiLift_chord_face` : chord-side face identity for junction bookkeeping.

### 4. `ArcChordSeam` — the seam datum reduced to the non-arc steps
A structure carrying: the always-available cycle-decomposition data
(`Ls/factor/...`), the bank `gen` edges, the outer `BoundaryCycle B`, an arc-index
predicate `IsArc` with `arc_darts_mem` (arc darts lie on `B`), and the residual
`step_component` obligations **only** for: non-arc forward steps (`nonarc_step`),
reverse bank-ends (`revbank_step`), off-cycle `inl` darts (`offcycle_step`), and caps
(`capP_step`/`capM_step`).
- `forward_step` : the forward bank-end step for **every** index — arc indices by
  boundary reflexivity (using ZERO seam fields), non-arc by `nonarc_step`.
- `step_component` : discharged for **every** `CutDart`, by the `cycleKind` trichotomy
  (`dart i` / `α(dart i)` / off-cycle) plus the cap split.
- `toBankStepCert` : produces a genuine `BankStepCert` from the seam — arc forward
  steps pre-discharged, strictly lighter than a bare `BankStepCert`.

### 5. The chord separation from a seam
- `sphereChordSeparation_of_seam` — `SphereChordSeparation h` form.
- **`separates2_of_seam`** — `data.Separates` end-to-end form.
Both thread `toBankStepCert` into the proven `separates2_of_stepCert` /
`sphereChordSeparation_of_stepCert`. **Identical conclusion**, seam input reduced to
non-arc steps only.

## Faithfulness / non-vacuity audit (playbook §3.3)

- **Same conclusion, strictly fewer obligations.** `separates2_of_seam` proves the
  identical `data.Separates` as `separates2_of_stepCert`/`separates2_of_core`. The
  arc-arc forward steps are *eliminated* (discharged with no field via
  `boundary_step_eqvGen`); only the chord/junction/cap/reverse/off-cycle steps remain.
  Verdict **CONDITIONAL-honest**, residue isolated to the non-arc steps + the boundary
  datum `B`. NOT a re-wrapper: the dictionary lemmas and the arc closure are genuine
  new computations.
- **NOT vacuous.** `ArcChordSeam`'s fields are satisfiable exactly when `BankStepCert`'s
  `step_component` is, minus the arc steps. The two non-vacuity `example`s exercise the
  dictionary (genuine iff, orbit→face recovered) and the arc reflexivity on any
  boundary cycle. `#print axioms` clean is NOT the basis of the faithfulness claim —
  the reduction is verified by reading the discharge.
- **No assumption smuggling beyond the prior layer.** `BankStepCert.step_component` was
  already the carried F-side certificate; `ArcChordSeam` *reduces* it. The genuinely new
  carried datum is the boundary cycle `B` + arc identification — the application
  structure the abstract cycle lacked, not the goal in disguise.

## Axiom audit (all 6 headline decls)
`pOrbOf_phiLift_inl_eq_iff`, `boundary_step_eqvGen`, `pOrbOf_phiLift_chord_distinct`,
`ArcChordSeam.step_component`, `ArcChordSeam.toBankStepCert`, `separates2_of_seam`
→ all `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `ofReduceBool`/native.

## The ONE genuinely irreducible point (named, honest — structural, not mathematical)

The concrete `SimplePrimalCycle` whose `dart : Fin len → D` is `chord ∪ arc` **cannot
be extracted in this repository**: `BoundaryPath` (the output of
`BoundaryCycle.two_arcs`) records only the arc's **vertex and edge** lists — it carries
**no dart list**. There is no arc-dart sublist function and no `SimplePrimalCycle`
constructor anywhere in the repo (verified by exhaustive grep). Reconstructing the arc
darts (inverting `M.dartEdge`/`M.tail` along the arc with correct orientation) is the
one piece of structure the boundary machinery does not yet expose. It would require new
fields in `BoundaryPath`/`BoundaryArcSplit` (files I do not own under
one-file-one-writer). **This is the genuine long-standing gap** — and it is *structural
infrastructure*, not the seam mathematics. Everything downstream of it is now closed:
given the arc-dart data, `ArcChordSeam` discharges every `step_component` obligation,
the arc steps for free.

## Ch35 frontier, stated precisely (post this layer)

The F-side chord wall `data.Separates` now has THREE routes to the identical conclusion,
in increasing lightness of the F-side input:

  Route A (exact count):   `NumCyclesCutPhi2`            → `separates2_of_core`
  Route B (per-step):      `BankStepCert.step_component` → `separates2_of_stepCert`
  Route C (this file):     `ArcChordSeam` (arc steps free) → `separates2_of_seam`

The remaining chapter-wide frontier (shared by all routes):

1. **The arc-dart reconstruction** (the structural gap above): a dart-level boundary
   arc — i.e. give `BoundaryPath`/`BoundaryArcSplit` a `darts : List D` field with
   `tail`/`dartEdge`/`consecutive` coherence — so the concrete chord∪arc
   `SimplePrimalCycle` and the `ArcChordSeam.B`/`IsArc`/`arc_darts_mem` data can be
   *built* rather than assumed. This is the sole genuine open item that this layer
   reduces the seam mathematics to; it is infrastructure, not new topology.
2. **The non-arc seam steps** `nonarc_step` (chord dart + 2 junctions) + the
   reverse/off-cycle/cap obligations — all chord-LOCAL, finite, and pinned to the
   chord caps' generator edges by `faceCorr2_capP_cases`/`capM_cases`. (Discharged
   given the chord caps' `gen` edges; the symbolic cap actions already force them.)
3. **The bridge-witness data** `CutBridgeWitness2 i` (Part-A `SidesReach2` +
   no-teleport `FragmentCompatible2`) — the design's irreducible interior-dual input,
   per `PlanarMapBridgeWitness.lean`.
4. The chord-cycle wiring `hsub`/`i₀`/`hleft`/`hright` from `ChordSplitData`.

Items (2)–(4) are wiring/finite-chord-local; **the sole genuine residue is (1)**, the
dart-level boundary arc — now isolated to a structural field, the seam *mathematics*
(arc incidence) closed by `consecutive_phi`.

## Notes for wiring
- Leaf file. To activate: add `import ProofsInTheBook.SeamIncidence` to
  `ProofsInTheBook.lean` and the 6 `#print axioms` lines to `Audit.lean` (import the
  module there too). I own only SeamIncidence.lean.

## Verification command
    rsync -az .../SeamIncidence.lean uisai1:~/repos/proof_in_the_book/ProofsInTheBook/
    ssh uisai1 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH \
                && lake env lean ProofsInTheBook/SeamIncidence.lean'
    → EXIT 0, zero errors/warnings; 6 axiom prints all {propext, Classical.choice, Quot.sound}.
