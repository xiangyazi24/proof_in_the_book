# Reply: PlanarMapDualPathSep.lean — DualPathSeparation Parts A+B (Ch35 Jordan §4)

**Status:** new file `ProofsInTheBook/PlanarMapDualPathSep.lean` (462 lines) created,
compiles clean, all headline theorems depend on `[propext, Classical.choice,
Quot.sound]` only. Branch `main`; `PlanarMapCutCapConn.lean` and the cccon/ccfcore files
untouched; no commit. Builds on the full cccon reachability calculus.

## What is PROVED unconditionally (new content, 0 sorry/axiom/native_decide)

1. **Forward step lifts** (the dart-level lifts of design §4, with the
   divert-through-cap subtlety handled):
   - `cutReach_sigma_clean` / `cutReach_sigma_divertPlus` / `cutReach_sigma_divertMinus`
     — a single `σ`-step either lifts to `inl (σ d)` or diverts into a cap that is
     `α'`-adjacent to a bank dart.
   - `cutReach_sigma_step_or_bank`, `cutReach_sigma_pow_or_bank`,
     `cutReach_sameCycle_or_bank` — lift a whole `σ.SameCycle` relation, with a
     bank-escape via side-coherence.
   - `cutReach_alpha_step_or_bank` — an `α`-step lifts across an uncut edge
     (`cutReach_uncut_bridge`) or lands on a cycle bank dart.
   - `cutReach_phi_step_or_bank`, `cutReach_phi_pow_or_bank`,
     `cutReach_sameFace_or_bank` — the same lift for `φ`-steps (face traversal).

2. **PART A — `ReachesBank i` PROVED** from `M.Connected` + side-coherence:
   - `reachesBankI_backward` + `inl_reachesBankI` — backward induction on an
     `M`-`dartStep` walk from `proj x` to `dart i` (mirroring the `FanConnectivity`
     skeleton), invariant "reaches a bank of `e_i`", preserved by every `σ`/`α` step.
   - `reachesBank_of_connected : M.Connected → SidesReach i → C.ReachesBank i`
     (caps reduced to bank darts via cccon's `cutReach_capP/capM`).

   This **strictly deepens** cccon's isolation: there the *whole* of `DualPathSeparation`
   (both `reachesBank` and `bridge`) was assumed; here `reachesBank` is **discharged**
   from `M.Connected` and the sub-fact `SidesReach` (a concrete `cutReach` statement
   about only the `2k` cycle bank darts).

3. **Assembly**: `CutJordanCore` (the deepened 2-field core: `sidesReach` + `bridge`),
   `dualPathSeparation_of_connected`, `cutCapMap_connected_of_connected_of_core`,
   `cutSigmaCounts_of_faceCount_of_core`, `jordan_simple_cycle_conditional_core`, and the
   end-to-end `NearTriangulation.separates_of_jordan_conditional_core` — the chord wall
   conditional only on the F-file face count `hF` and the per-edge `CutJordanCore`
   (`M.Connected` and the Euler inequality are discharged from `hNT.sphere`).

## PART B — honestly isolated as the residual `bridge` (not faked)

After rigorous case analysis I established that **Part B's bridge is genuinely
irreducible by reachability bookkeeping** — it is the topological separation itself:

- The same-face `φ`-lift can *divert*: a single `M`-face whose `φ`-orbit is broken by the
  caps into two `φ'`-pieces puts two of its darts on **opposite banks**, which are
  genuinely different cut-components. So "same old face ⇒ cut-connected" fails (exactly
  the cccon `CAREFUL` warning, now made precise).
- Because `cutReach` is **symmetric** and Part A makes "reaches a bank" **universal**,
  the predicate "face `g` has a dart reachable from the `+` (or `−`) bank" is vacuously
  true for every face — there is **no monovariant** the dual path can increase. The
  merge of the two banks cannot be read off any single face or step.

Hence the residual `bridge : cutReach (inl (dart i)) (inl (α (dart i)))` is kept as the
second conjunct of the isolated `CutJordanCore` — the same fact cccon isolated, now
sitting beside the *proved* Part A.

## The deepened isolated core (honest, satisfiable, not vacuous)

`CutJordanCore C i : Prop`:
- `sidesReach : SidesReach i` — side-coherence (each forward/reverse cycle bank reaches
  the forward/reverse bank of `e_i`); **drives the proved Part A**.
- `bridge : cutReach (inl (dart i)) (inl (α (dart i)))` — the residual dual bridge.

Neither conjunct mentions `Connected` or any unsatisfiable premise. Both were verified
**true and satisfiable** by direct enumeration of the cut-and-cap map (Python) on the
tetrahedron, octahedron, cube (spheres: `ReachesBank` holds, 2 components, banks split)
and the 3×3 torus (non-separating cycle: dual path exists, cut map is connected, bridge
holds). This is CONDITIONAL-honest, not VACUOUS/IMPOSTOR.

## Net effect on the chord wall

The Chapter-35 chord wall now stands conditional on exactly:
- `hF` (F-file face count `F' = F + 2`) — `ccfcore` lands it in parallel;
- per-edge `CutJordanCore` = `SidesReach` (a finite cycle-bank `cutReach` fact, **Part A
  now consumes it via a proof**) **+** the residual `bridge` (Part B).

Part A is no longer an assumption. The isolated content has shrunk from cccon's full
`DualPathSeparation` (a `∀ x : CutDart` reach statement + bridge) to `SidesReach` (a
`∀ j : Fin len` cycle-bank statement) + bridge.

## Verification

- Remote (uisai1): `lake build ProofsInTheBook.PlanarMapDualPathSep` → 8438 jobs, build
  OK; `lake env lean PlanarMapDualPathSep.lean` → no errors.
- `grep -nE '\bsorry\b|\badmit\b|\bnative_decide\b|^axiom '` → none (only the
  doc-comment line).
- `#print axioms` on all 8 headline lemmas/theorems → `[propext, Classical.choice,
  Quot.sound]` only.
- Local: never ran lake (kernel-panic rule); verified exclusively via rsync→uisai1.
- Branch `main`; `PlanarMapDualPathSep.lean` untracked; cccon/ccfcore untouched. No commit.
