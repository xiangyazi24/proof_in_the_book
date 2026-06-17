# JordanOracleConstruct.lean — Ch35 Jordan-oracle assembly (final step)

## Status: COMPLETE as **CONDITIONAL-honest**, NOT unconditional.

New leaf file `ProofsInTheBook/JordanOracleConstruct.lean`. Imports
`ThomassenInduction`, `WitnessFinal` only. Verified EXCLUSIVELY on uisai1
(`lake env lean` → RC=0, **zero errors, zero warnings**; full
`lake build ProofsInTheBook.JordanOracleConstruct` → **8469 jobs, Build completed**).
NEVER ran lake/lean on the Mac. Branch `main` throughout; no commit; no branch
switch; no codex/OpenAI tooling. Leaf — nothing imports it; `Audit.lean` and the
import graph untouched (one-file-one-writer). Dep oleans
(`WitnessFinal`, `ThomassenInduction`) built clean first (8468 jobs).

`grep -nE '\bsorry\b|\badmit\b|\bnative_decide\b|^axiom '` → none (only docstring
mentions). `#print axioms` on all four results → **[propext, Classical.choice,
Quot.sound]** (clean-3).

## The honest verdict (the headline)

**The unconditional `JordanOracle` is NOT constructible at the combinatorial-map
layer.** After full structural exhaustion of the chord branch
(`separates_final`/`separates2_of_dartArc`/`ChordSplitData`/`ChordSplitRegions`),
the chordless branch
(`FanIncidenceData`/`FanSurgeryReconstruction`/`deleted_lists`), the dichotomy, and
item 2 (the hcompat triangle-discharge), the conclusion is firm and matches the
codebase's own repeated documentation (module docstrings of `PlanarMapChordSplit`,
`PlanarMapFanExistence`, `PlanarMapFanSurgery`, `ThomassenLists`, and
`CH35_BRIDGE_DESIGN.md` §6–§7): the residue is **not** a single F-count identity —
it is the *entire planar/Jordan input surface*. Specifically the irreducible pieces
are:

1. the chord/chordless **dichotomy** itself (does the boundary have a chord);
2. the chord-split **orientation data** `ChordSplitData` + `Separates`, AND the two
   **side region-colorings** `c₁,c₂` the `ChordOracle` demands — the foreign side
   maps carry no recursable `NearTriangulation` and no side-vertex↦`M`-vertex
   correspondence (`opus-f6/f10`), so the sides cannot be colored by recursion;
3. the boundary-deletion **orientation residue** `FanIncidenceData`
   (`incident_faces_exact`, the chordless/Jordan fields) + `FanSurgeryReconstruction`
   + the deletion-list relabeling `deleted_lists` (the new-boundary vertex
   classification is Jordan bookkeeping, not orbit-algebraic);
4. the **no-teleport fragment data** (item 2). I genuinely attempted the triangle
   discharge and it **fails for a real mathematical reason**: even though every
   interior face is a triangle (so each fragment step is a single `φ'₂`-edge), the
   `ChordOracle`/bridge needs `SameFragment f (c i) (α (c i))` for the two cut darts
   of a cycle edge — but those two darts are *separated by the cut* (that is the
   whole point of the separation). So `fragmentCompatible2_singleFace` still requires
   `hfrag` as input; triangle-locality makes each step *local* but does not make the
   gate data *free*. This is exactly `CH35_BRIDGE_DESIGN.md` §6's warning: "do not
   try to prove entry/exit fragment of one old face are connected — that statement is
   false."

None of these has a producer anywhere in the repo from a bare `NearTriangulation`;
they are structures packaging planar input, not theorems.

## What was built (faithful, non-vacuous)

- **`JordanInput α`** — the *single* named irreducible Jordan input: the
  per-near-triangulation chord/chordless dichotomy datum, with every part the
  combinatorial layer CAN prove already folded into the types
  `ChordOracle`/`ChordlessOracle` (`SidesReach2` proved via `sidesReach2_concrete`,
  the triangle-gate fragment constructors, the separation reduction
  `separates_iff_sidesDisjoint`, the fan/merged-arc assembly, the glue, the
  delete-and-extend). It is content-equivalent to `JordanOracle.decide` — which is
  *correct*, because that payload IS the irreducible residue.
- **`jordanOracleConstruct : JordanInput α → JordanOracle α`** — the builder; it
  genuinely uses the input (`jordanOracleConstruct_decide : decide … = input.dichotomy …
  := rfl`, ruling out the trivial-constant / re-wrapper-that-discards-input mode).
- **`nearTriangulation_five_list_colorable_of_input`** and
  **`nearTriangulation_five_colorable_of_input`** — five-(list-)colorability of a
  near-triangulation, **conditional on the single isolated `JordanInput`**, with ALL
  of Thomassen's induction discharged (base case, chord glue, delete-and-extend, list
  bookkeeping, well-founded recursion). These are
  `ThomassenInduction.nearTriangulation_five_colorable` with the `Ofun : ∀ p q cp cq,
  JordanOracle α` parameter collapsed to the one named input.
- **`JordanInput_nonvacuous`** — the §3.3 satisfiability obligation: `JordanInput α`
  is inhabited whenever the planar dichotomy is supplied; it is NOT an unsatisfiable
  premise (no hidden `False`), so the conditional theorems are not operationally
  vacuous. (Deliberately not discharged from `NearTriangulation` alone — that is the
  irreducible planar content.)

## §3.3 self-audit (the limitation, stated plainly)

- **Verdict: CONDITIONAL-honest**, not FAITHFUL-unconditional. `JordanInput` is
  content-identical to `JordanOracle.decide`; the file does **not** discharge the
  Jordan content (it is impossible at this layer). It contributes: (a) the
  single-point *isolation + documentation* of the irreducible residue, (b) the
  *non-vacuity* certificate, (c) the conditional five-colorability stated against the
  named single input. It does **not** make five-colorability unconditional.
- It is **not** a vacuous conditional: `JordanInput_nonvacuous` shows the premise is
  satisfiable; the underlying `ChordSplitData`/`FanIncidenceData`/`FanSurgeryReconstruction`
  each carry upstream non-vacuity witnesses (tetrahedron base triangle).
- It is honest about being a thin re-export of the oracle payload (the playbook's
  "no banking re-wrappers" rule): I am NOT claiming new math here, only the clean
  isolation + non-vacuity. The genuine math (`SidesReach2`, the triangle-gate
  constructors, the separation reduction, the fan assembly) was already done upstream
  in `WitnessFinal`/`ThomassenLists`/`PlanarMapFanExistence` and is reused, not
  re-proved.

## The one isolated residue (per the task's "isolate ONE honest Prop" instruction)

`JordanInput α` is that one named honest input, with `JordanInput_nonvacuous` as the
non-vacuity witness. To make Ch35 truly unconditional, the missing front (unchanged
from the existing `ThomassenInduction` docstring) is the planar layer that the
combinatorial-map machinery does not synthesize: a producer of the chord/chordless
dichotomy + `ChordSplitData`/side maps with a recursable side `NearTriangulation` +
`FanIncidenceData`/`FanSurgeryReconstruction` from Euler/Jordan. That is a separate,
large piece of planar topology, not a residual identity.

## Verification commands
- `lake env lean ProofsInTheBook/JordanOracleConstruct.lean` → RC=0, no errors/warnings.
- `lake build ProofsInTheBook.JordanOracleConstruct` → Build completed (8469 jobs).
- `#print axioms` → clean-3 on `jordanOracleConstruct`,
  `nearTriangulation_five_list_colorable_of_input`,
  `nearTriangulation_five_colorable_of_input`, `JordanInput_nonvacuous`.
