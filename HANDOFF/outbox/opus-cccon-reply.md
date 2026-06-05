# Reply: PlanarMapCutCapConn.lean — connectivity of the cut-cap map (Ch35 Jordan §4)

**Status:** file created, compiles clean, axioms core-three only. The
`connected_of_dual_path` field is discharged **conditional on ONE named,
satisfiable Jordan-separation fact** (`DualPathSeparation`). All surrounding
infrastructure is proved unconditionally. Branch `main`, F-file untouched.

## What is fully proved (unconditional, 0 sorry/axiom/native_decide)

File: `ProofsInTheBook/PlanarMapCutCapConn.lean` (333 lines), imports
`ProofsInTheBook.PlanarMapCutCapF`.

1. **Reachability calculus on `C.cutCapMap`** (`cutReach := ReflTransGen dartStep`):
   - `cutDartStep_symm`, `cutReach_symm/trans/rfl`
   - `cutReach_of_sigma` (σ'-step), `cutReach_of_alpha` (α'-step),
     `cutReach_of_phi_step`/`_pow`/`_sameCycle` (same φ'-face ⇒ reachable, via
     α'-then-σ').
2. **Uncut bridge** `cutReach_uncut_bridge`: `dartEdge d ∉ E(C) ⇒ d ∉ dartSet ⇒
   cutReach (inl d) (inl (α d))` (the uncut edge's α-pairing survives). This is the
   genuine dart-level kernel of design §4 Part B.
3. **Cap→bank reductions** `cutReach_capP/capM`: each cap is one α'-step from a bank
   `inl`-dart.
4. **Connectivity reduction** `cutCapMap_connected_of_reachesBank_of_bridge`: given
   (A) every cut-dart reaches a bank of `e_i` and (B) the two banks are mutually
   reachable, the cut map is connected. Fully proved.

## The single isolated fact (honest)

`DualPathSeparation C i : Prop` — a 2-field structure:
- `reachesBank : ReachesBank i` — **design §4 Part A** ("≤2 components": every
  cut-dart reaches one of the two banks `inl (dart i)`, `inl (α (dart i))`);
- `bridge : cutReach (inl (dart i)) (inl (α (dart i)))` — **design §4 Part B** (the
  dual path forces the two banks to be cut-reachable).

`connected_of_dual_path` is then closed by
`cutCapMap_connected_of_dualPathSeparation`.

**Why isolated, not proved.** Both halves are the irreducible combinatorial-Jordan
*separation* and, after careful analysis, are as deep as the face-count `F'=F+2`:
- The cut genuinely **severs** each cycle edge — the forward dart `inl (dart i)`
  pairs (α') with `c_i^+`, the reverse with `c_i^-`; the two banks of every cycle
  vertex become distinct σ'-orbits. Two darts in the same M-σ-orbit at a cycle vertex
  are *not* σ'-co-cyclic.
- Consequently **old face orbits are rerouted**: when an M-φ-step `d ↦ φ d` lands on
  a bank-start (a cycle dart), φ' diverts to a cap (`φ'(inl d) = c_i^+`), so
  `M.φ.SameCycle d₁ d₂ ⇏ cutReach (inl d₁) (inl d₂)`. The naive "same old face ⇒
  connected" is **false** across the cut (the handoff's CAREFUL note confirmed).
- Both Part A (identify the two sides) and Part B (the +/−-cap faces thread the two
  banks; one dual bridge merges them) require the global two-sided / cap-face
  structure, i.e. the same orbit machinery as `face_count`. Not closeable in this
  budget without that development.

**Satisfiability check (not vacuous):** `DualPathSeparation` mentions neither
`Connected` nor any unsatisfiable premise; each conjunct is a concrete `cutReach`
statement about the banks of one cycle edge, true for the genuine surgery (sphere +
dual path). This is CONDITIONAL-honest, not a VACUOUS/IMPOSTOR field.

## Assembly (conditional)

- `cutSigmaCounts_of_faceCount_of_dualPathSeparation` — assembles `CutSigmaCounts`
  from proved `vertex_count` (`hV`, V-file), the F-file face count (`hF`), and the
  per-edge `DualPathSeparation` core (`hsep`).
- `jordan_simple_cycle_conditional` — the Jordan lemma, conditional on `hF`, `hsep`,
  Euler `chi_le`.
- `NearTriangulation.separates_of_jordan_conditional` — **end-to-end chord
  separation** (`data.Separates`), conditional on only `hF` + `hsep`; the Euler
  inequality is discharged **unconditionally** here via
  `chi_le_two_of_connected` (PlanarMapEulerInequality.lean is proved, 0 sorry).

## Status of CutSigmaCounts / the chord wall

Cannot be assembled unconditionally yet. Two open facts remain:
- **`face_count` (F' = F + 2)** — `PlanarMapCutCapF.lean` only proves the *reduction*
  `cutCapMap_F_iff` (to `numCycles (phiLift * faceCorr) = M.F + 2`); the final
  numCycles count is **not** discharged there. So F' has **not** landed.
- **`DualPathSeparation`** — the §4 Jordan-separation core isolated here.

Once those two close, `cutSigmaCounts_of_faceCount_of_dualPathSeparation` +
`separates_of_jordan_conditional` give the unconditional Chapter-35 chord wall with
zero further wiring.

## Verification

- Remote (uisai1): `lake build ProofsInTheBook.PlanarMapCutCapConn` → 8437 jobs,
  build OK; `lake env lean PlanarMapCutCapConn.lean` → no errors.
- `grep -nE '\bsorry\b|\badmit\b|\bnative_decide\b|^axiom '` → none (only the
  doc-comment line).
- `#print axioms` on all 6 headline theorems → `[propext, Classical.choice,
  Quot.sound]` only (no sorryAx / ofReduceBool / trustCompiler).
- Local: never ran lake (kernel-panic rule); verified exclusively via rsync→uisai1.
- Branch `main`; `PlanarMapCutCapConn.lean` untracked; `PlanarMapCutCapF.lean`
  untouched. No commit.
