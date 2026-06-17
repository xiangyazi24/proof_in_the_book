# Ch13 B1 final wrapper chain — `ZinanFFCT35` report

**File:** `ProofsInTheBook/ZinanFFCT35.lean` (365 lines). Only file created/edited (FFCT36.lean belongs
to the sibling worker — NOT imported, NOT touched). Compiles **0 errors, 0 warnings**.
`lake build ProofsInTheBook.ZinanFFCT35` → built (8494 jobs). `#print axioms` on all 4 headline results
→ `[propext, Classical.choice, Quot.sound]` (clean-3, no `sorryAx`/`ofReduceBool`/`native_decide`).

## The decisive finding (settled FIRST, honesty contract)

**`InteriorOpeningGlue` clauses (i) and (ii) are FALSE for the `+δ` monitored family.** This is proven
*unconditionally* in `SphericalOpeningGlue` and is not threading-fixable:

- `SignBugBlocksI` : `sOrient (A K)(jointPrev)(jointNext) < 0` ∧ `sOrient (A K)(A 0)(A last) ≤ 0` — the
  monitored family rotates in the **closing** direction, so clause (i) `endpt A ≤ endpt A'` with `δ*>0`
  fails in general.
- `SignBugBlocksII` + `EndpointPosMono` : the same negative axis support forces `¬ Stuck` to the
  trichotomy CAP `δ* = π`, not `Reach` (clause (ii) fails). `EndpointPosMono` is the named *false* `+δ`
  clause; it is assumed nowhere.

Fixing (i)/(ii) needs the corrected `−δ` (widening) monitored family — a **substrate change, not
threading**. Per the prompt's >100-line stop rule, this is the hard mathematical block. The repo already
posture-carries `InteriorOpeningGlue` as a named (un-discharged) residue, so the honest headline carries
it explicitly. It is **not** provably `False` anywhere in the repo (only the `+δ` family's specific
realization is documented obstructed), so the conditional headline is **CONDITIONAL-honest, not
IMPOSTOR**.

## What threaded cleanly

| Theorem | Threads | Verdict |
|---------|---------|---------|
| `stuckSupport_betweenness_mod_gram` | FFCT28 `supportStuck_dispatch_partial` | clause (iii) support→betweenness, mod `GramSignsAtInteriorBinding` |
| `stuckSupport_betweenness_axisEdge` | FFCT29 `interiorAxisEdge_stuck_betweenness` | sharpest support→betweenness: residual = one near-side sign `NearSideCoeffNonneg` |
| `equatorTangent_at_sup_of_spreadExcluded` | FFCT33 `equatorTangent_of_spreadExcluded` | hemi tilt from `EquatorSpreadExcluded` |
| `stuckOutcome_of_supportVanish` | `weakConvex_of_supportStuck_of_hemiPos` + `vanishing_support_of_supportStuck` | support-stuck → WeakConvex ∧ vanish |
| `stuckOutcome_weakConvex_of_residues` | FFCT30 `hemiStuck_forces_supportStuck_or_weakConvex` + above | **clause (iii) full**: `Stuck → WeakConvex Aδ ∧ ∃ vanishing support` |
| `interiorOpeningOutcomePlus_of_residues` | `interiorOpeningOutcome_holds` | `InteriorOpeningOutcome` from the glue bundle |
| `mainPlus_headline_mod_residues` | `spherical_arm_mono_of_spliceBodyDiagMono` | **chapter headline** `sDist(A0)(Alast) ≤ sDist(B0)(Blast)` mod all residues |

Clause (iii) of `InteriorOpeningGlue` is the part the B1 wave (FFCT28–34) was built for, and it is now
assembled end-to-end (`stuckOutcome_weakConvex_of_residues`) modulo named geometric residues only.

## Final residue surface of the Ch13 headline (`mainPlus_headline_mod_residues`)

Every hypothesis is a NAMED, SATISFIABLE `Prop` (non-vacuity guards in §5, all compiled):

1. **`SpliceBodyDiagMono`** (`SphericalSpliceTransport`) — sub-arm diagonal monotonicity. Pre-B1.
2. **`SpliceStructuralData`** (`SphericalArmAssembly`) — cut sub-arm geometry. Pre-B1.
3. **`InteriorOpeningGlue`** (`SphericalOpeningOutcome`) — the opening trichotomy boundary glue.
   - clauses (i)/(ii): **FALSE for `+δ`** (sign bug above); need the `−δ` family (substrate).
   - clause (iii): geometry threaded by `stuckOutcome_weakConvex_of_residues`, itself modulo 4–6 below.

The clause-(iii) sub-residues that `stuckOutcome_weakConvex_of_residues` exposes:

4. **`HemiMarginStrictPosAtSup`** (`SphericalOpeningGlue`) — strict hemi margins `>0` at a Stuck sup
   (`BoundaryConvexPersistAtSup`); needed for `weakConvex_of_supportStuck_of_hemiPos`.
5. **`OpenedEdgesDistinct`** (NEW, this file) — consecutive opened vertices distinct at `δ*`. Genuine
   geometric fact, not free from supports at a Stuck sup (one vanishes); named + threaded.
6. **`EquatorSpreadExcluded`** (`ZinanFFCT33`) — equator-vertex sum positivity (→ the hemi tilt).
   FFCT34 excludes antipodal pairs + consecutive triples; residual = `|Z|≥3` pairwise-nonantipodal
   wide spread (2D winding, the next wave).
7. **`HemiStuckVanishingSupport`** (NEW, this file) — at a hemi-stuck sup whose opened arm is already
   weakly convex, some non-incident support still vanishes (the trichotomy's support disjunct);
   extracting the specific binding from a margin contact is the documented hemi residual.
8. **`GramSignsAtInteriorBinding` / `NearSideCoeffNonneg`** (FFCT28/29/31/32) — the multi-rotation Gram
   signs at a general interior binding (the support→betweenness residue, separate path consumed by
   `stuckSupport_betweenness_*`; not on the `stuckOutcome` weak-convex path itself but on the cut-step
   side of clause (iii)'s consumer `FoldedFlatCutTransportPlus`).

## Shape-mismatch stops (documented, per the prompt)

- **Clauses (i)/(ii) of `InteriorOpeningGlue`** — STOP. The `+δ` family is sign-wrong (proven
  unconditionally). The repaired `−δ` family is a substrate rebuild (>>100 lines new math), out of
  scope for assembly. Carried as the named residue `InteriorOpeningGlue` in the headline.
- **`FoldedFlatCutTransportPlus`** is a NAMED PREDICATE in FFCT18 (the betweenness→endpoint transport +
  ear sDist comparison), NOT proven. The betweenness wrappers (1,2) produce exactly its `span≥0` input;
  the endpoint endgame it bundles (via `stuckAtK_diag_le_plus` + `cut_diag_le`) is internal to that
  named residue. I did not re-thread the cut-step endpoint endgame into the headline because the
  `SphericalArmAssembly` spine already routes STUCK through `cut_step` (its own `SpliceStructuralData` /
  `SpliceBodyDiagMono` residues), so the chapter headline's honest residue set is the three
  `SphericalArmAssembly` inputs + the glue, NOT a separate `FoldedFlatCutTransportPlus`. The B1
  betweenness bricks feed the *interior-opening* trichotomy's clause (iii), which is exactly the
  `InteriorOpeningGlue` path I threaded.

## Verification

- `lake env lean ProofsInTheBook/ZinanFFCT35.lean` → 0 errors, 0 warnings.
- `lake build ProofsInTheBook.ZinanFFCT35` → built (8494 jobs).
- `#print axioms` (rebuilt oleans) on `mainPlus_headline_mod_residues`,
  `stuckOutcome_weakConvex_of_residues`, `stuckSupport_betweenness_axisEdge`,
  `interiorOpeningOutcomePlus_of_residues` → all `[propext, Classical.choice, Quot.sound]`.
- No file other than `ZinanFFCT35.lean` created or modified. NOT committed.
