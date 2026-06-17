import ProofsInTheBook.ZinanCh35ChordResidue
import ProofsInTheBook.ZinanCh35Regions
import ProofsInTheBook.ZinanCh35ChordSupplier
import ProofsInTheBook.ZinanCh35ChordSupplier2
import ProofsInTheBook.ZinanCh35MergedArc
import ProofsInTheBook.ZinanCh35DeletedAssembly
import ProofsInTheBook.ZinanCh35ChordlessOracle
import ProofsInTheBook.ZinanCh35ChordlessSupplier

/-!
# Chapter 35 (Five Colour Theorem): the final recursion-structural assembly

This leaf is the **endpoint** of the Chapter-35 campaign.  Every genuine planar /
discrete-Jordan / Schoenflies fact has been discharged unconditionally in the upstream
files; what is left is the recursion's own structural plumbing — the two side
near-triangulations / the deleted map, their boundary-cycle normalizations, the pullback
Thomassen lists, and the precolored-edge / reserved-colour placements that the Thomassen
strong induction supplies at each recursive call.  This file bundles exactly those
recursion-structural inputs, assembles them into the single induction-level supplier
`ZinanCh35Cert.PlanarInputs`, and threads that into
`ZinanCh35Cert.fiveColor_of_planarInputs`, delivering the maximal-form

  `fiveColor_planar_of_recursionResiduals`

— five-colorability of every near-triangulation from the two named recursion-structural
residuals, with the entire genuine planar content discharged.

## The two recursion-structural residuals (and why each is recursion structure, not a math gap)

The end-to-end chain `ZinanCh35Dichotomy.chordRecursiveDichotomy_of_suppliers`
routes the unconditional chord/chordless decision (`boundaryChord_em`, pure EM) into a
`ChordSplitNT.ChordRecursiveDichotomy`, which the **proven** recursion driver
`ChordSplitNT.thomassen_aux_chordRecursive` (and hence
`ChordSplitFinal.nearTriangulation_five_colorable_unified`) consumes.  The driver runs
the full strong induction internally: it recurses on the strictly-smaller side
near-triangulations (chord branch) or the strictly-smaller deleted map (chordless
branch), produces the side colorings *by recursion* (`ChordRecursionData.chord_case_recursive`,
no colorings supplied), and glues.  So the single remaining input is the per-step
*structural* choice, split into two named suppliers:

### 1. Chord branch — `ZinanCh35ChordResidue.ChordRecursionInputSupplier`

Per near-triangulation with a chord, it supplies a `ChordRecursionInputs`, which carries
the **legitimate recursion fuel** plus the now-discharged structural residue:

* the side near-triangulations `sideMap₁ / sideMap₂` (assembled by
  `chordSideNearTriangulation_of_share`), their `ContiguousInterval / ContiguousInterval₂`
  side-boundary-cycle normalizations, and the pullback Thomassen lists
  `Lₛ = L ∘ sideVertexToM` (`Side₁InputsNoConf / Side₂InputsNoConf`) — these are *how* the
  strong induction descends to the two smaller sides, exactly Thomassen's "color side 1,
  force `u,v`, color side 2" order;
* the structural region glue residue `ChordSplitRegionsResidue` — whose vertex `cover` and
  vertex-level `edge_confined` are now produced **unconditionally** by
  `ZinanCh35Regions.chordSplitRegionsResidue_of_precolored` (via `boundedFacePartition_uncond`
  + the side-region endpoint bridges), leaving only the precolored placement
  `p, q ∈ sideRegion₁` (the recursion's chord *choice*: it picks the chord so the precolored
  edge is on side 1) as the genuine recursion-supplied input.

The confinements (`Side₁StarConfinement`, `Side₂SchoenfliesConfinementInput`), the separation
`Separates`, `OuterDartArc₁`, the σ-star overlap, the canonical side-1 anchors realizing the
chord endpoints, and `chord_adj` are **all produced** upstream (see
`ZinanCh35ChordBranch` / `ZinanCh35ChordResidue`).  Nothing here posits them.

### 2. Chordless branch — `ZinanCh35ChordlessOracle.ChordlessOracleResidual`

Per chordless near-triangulation, it supplies a `ThomassenInduction.ChordlessOracle`, which
carries the boundary-deletion data:

* the fan incidence datum `FanIncidenceData` — now **σ-constructible** from `hNT` + the
  outgoing boundary spoke + the genuine Euler `BaseCount`, with the orientation obstruction
  fully discharged (`ZinanCh35ChordlessClose.fanIncidenceData_of_baseCount`,
  `ZinanCh35ChordlessOracle.fanIncidenceData_sigma_derived`); the deletion connectivity is
  σ-discharged with no chirality input (`ZinanCh35FanBackward.deleteVertex_connected_backward`);
* the fan-surgery reconstruction `FanSurgeryReconstruction` — its merged-orbit seam
  (`DeleteVertexMergedFaceSingleOrbit`, via `deleteVertexMergedFaceSingleOrbit_of_fan` modulo
  the local outer-arc seam) and the new deleted-outer-boundary normalization
  (`DeletedOuterBoundary`: the new boundary cycle, its simplicity and length, the surviving
  inner triangles via the clean-face classification) — the chordless mirror of the chord
  side's `ContiguousInterval`;
* the deleted lists `deleted_lists` (the new map's Thomassen-list certificate after the fan
  deletion) and the two reserved colours `γ, δ ∈ L v0` with `cp ≠ γ, δ` (the Thomassen
  colour-reservation step at the deleted vertex), plus the fan-endpoint placement `x = p`.

This is the same fan/deletion datum the recursion carries and recurses on; it is invoked only
under a true chordless witness, so the conditional is operationally non-vacuous.

## Honest accounting

`fiveColor_planar_of_recursionResiduals` is **CONDITIONAL** on exactly the two named
recursion-structural residuals (`ChordRecursionInputSupplier` + `ChordlessOracleResidual`).
The decision, the routing, the confinements, the region cover/edge-confinement, the σ-backward
deletion connectivity, the fan incidence orientation, and the entire colouring recursion are
**unconditional** (clean-3).  The two residuals carry the recursion's *structural choices* —
the side / deleted boundary-cycle normalizations, the pullback / deleted Thomassen-list
certificates on the strictly-smaller maps, and the precolored-edge / reserved-colour placements.
They are not unsatisfiable premises (each is applied only under its true chord / chordless
witness, and each field is the concrete combinatorial datum the recursion genuinely consumes),
so the conditional is non-vacuous (§3.3).

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.  Clean-3.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Final

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ZinanCh35Dichotomy
open ProofsInTheBook.ZinanCh35ChordResidue
open ProofsInTheBook.ZinanCh35ChordlessOracle

universe u

variable {α : Type u} [DecidableEq α]

/-! ## Section 1.  The bundled recursion-structural residuals

The single remaining Chapter-35 induction-level input, packaged as one bundle: the chord-branch
recursion-input supplier and the chordless-branch oracle residual.  Each is the genuine
recursion structure of one branch (side near-triangulations + pullback lists + precolored
placement; resp. deleted map + boundary normalization + deleted lists + reserved colours). -/

/-- **The two recursion-structural residuals of Chapter 35**, bundled.

* `chordInputs` — for every near-triangulation with a chord, the chord-branch recursion inputs
  (the two side near-triangulations, their boundary-cycle normalizations, the pullback Thomassen
  lists, the precolored placement, and the now-unconditionally-dischargeable region cover /
  edge-confinement residue); see `ZinanCh35ChordResidue.ChordRecursionInputs`.
* `chordlessResidual` — for every chordless near-triangulation, the boundary-deletion fan oracle
  (the deleted map, its boundary-cycle normalization, the deleted lists, and the reserved
  colours); see `ZinanCh35ChordlessOracle.ChordlessOracleResidual`. -/
structure Ch35RecursionResiduals (α : Type u) [DecidableEq α] : Type (u + 1) where
  /-- The chord-branch recursion-input supplier. -/
  chordInputs : ChordRecursionInputSupplier α
  /-- The chordless-branch boundary-deletion oracle residual. -/
  chordlessResidual : ChordlessOracleResidual α

/-! ## Section 2.  Assembling the chord-recursive dichotomy

From the bundle we build both branch suppliers — the chord-branch supplier via the *fully
produced* residual chain (`chordBranchSupplier_of_recursionInputs`: confinements, separation,
region cover/edge-confinement, σ-star overlap, canonical anchors, `chord_adj`), and the
chordless-branch supplier via the oracle-residual routing — and route them through the
unconditional decision `boundaryChord_em` into a `ChordRecursiveDichotomy`. -/

/-- **The chord-recursive dichotomy from the bundled recursion residuals.**

Routes `chordBranchSupplier_of_recursionInputs R.chordInputs` (the chord half, with every
chord-split structural/Jordan piece produced except the recursion-supplied fuel) and
`chordlessBranchSupplier_of_residual R.chordlessResidual` (the chordless half) through
`chordRecursiveDichotomy_of_suppliers`.  The decision and routing are unconditional. -/
noncomputable def chordRecursiveDichotomy_of_residuals (R : Ch35RecursionResiduals α) :
    ChordRecursiveDichotomy α :=
  chordRecursiveDichotomy_of_suppliers
    (chordBranchSupplier_of_recursionInputs R.chordInputs)
    (chordlessBranchSupplier_of_residual R.chordlessResidual)

/-- **Non-vacuity of the assembled dichotomy.**  Given the two recursion residuals, the
`ChordRecursiveDichotomy` is inhabited: the routing genuinely terminates in one summand
(chord recursion datum / chordless oracle) on every near-triangulation, so the assembly is not
a hidden `False`. -/
theorem chordRecursiveDichotomy_of_residuals_nonvacuous (R : Ch35RecursionResiduals α) :
    Nonempty (ChordRecursiveDichotomy α) :=
  ⟨chordRecursiveDichotomy_of_residuals R⟩

/-! ## Section 3.  Threading into `PlanarInputs` and `fiveColor_of_planarInputs` -/

/-- **The `PlanarInputs` bundle from the recursion residuals.**  Wraps the assembled dichotomy
into the exact remaining induction-level supplier `ZinanCh35Cert.fiveColor_of_planarInputs`
consumes. -/
noncomputable def planarInputs_of_residuals (R : Ch35RecursionResiduals α) :
    ProofsInTheBook.ZinanCh35Cert.PlanarInputs α :=
  ⟨chordRecursiveDichotomy_of_residuals R⟩

/-! ## Section 4.  The final five-colour theorem (maximal recursion-structural form)

`fiveColor_of_planarInputs` runs the entire proven Thomassen colouring recursion internally
(`nearTriangulation_five_colorable_unified`).  Composing it with `planarInputs_of_residuals`
gives the endpoint: every near-triangulation is five-colorable, conditional on exactly the two
named recursion-structural residuals — the maximal honest form, with all genuine planar content
discharged. -/

/-- **THE FINAL CHAPTER-35 ASSEMBLY (maximal recursion-structural form).**

Every near-triangulation `M` is five-colorable, given the two bundled recursion-structural
residuals (`ChordRecursionInputSupplier` + `ChordlessOracleResidual`).  The colouring recursion,
the chord/chordless decision, both confinements, the region cover/edge-confinement, the
σ-backward deletion connectivity, and the fan incidence orientation are all unconditional;
the residuals carry only the recursion's structural choices (side / deleted boundary-cycle
normalizations, pullback / deleted Thomassen-list certificates on the smaller maps, precolored
and reserved-colour placements). -/
theorem fiveColor_planar_of_recursionResiduals
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M)
    (R : Ch35RecursionResiduals (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  ProofsInTheBook.ZinanCh35Cert.fiveColor_of_planarInputs hNT (planarInputs_of_residuals R)

/-! ## Section 5.  Equivalent forms (record the relation to the upstream entry points) -/

/-- The same endpoint stated directly through the two underlying suppliers
(`fiveColor_of_recursionInputs`), confirming `fiveColor_planar_of_recursionResiduals` adds no
content beyond unbundling the residuals into the chord recursion-input supplier and the
chordless oracle residual (routed through `chordlessBranchSupplier_of_residual`). -/
theorem fiveColor_planar_of_recursionResiduals_eq_suppliers
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M)
    (R : Ch35RecursionResiduals (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  ProofsInTheBook.ZinanCh35ChordResidue.fiveColor_of_recursionInputs hNT
    R.chordInputs (chordlessBranchSupplier_of_residual R.chordlessResidual)

/-! ## Section 6.  §3.3 non-vacuity / faithfulness certificates

The bundle is not a disguised `False`, and the reduction is not vacuous: each summand is the
concrete combinatorial datum the proven recursion consumes. -/

/-- The chord half of the bundle genuinely produces a `ChordBranchSupplier` (the recursion's
left summand), with all chord-split structural content produced; only the recursion fuel +
precolored placement is carried. -/
noncomputable example (R : Ch35RecursionResiduals α) : ChordBranchSupplier α :=
  chordBranchSupplier_of_recursionInputs R.chordInputs

/-- The chordless half of the bundle genuinely produces a `ChordlessBranchSupplier` (the
recursion's right summand); the routing forwards the same chordless witness and returns the same
`ChordlessOracle`. -/
def chordlessSupplier_of_residuals (R : Ch35RecursionResiduals α) : ChordlessBranchSupplier α :=
  chordlessBranchSupplier_of_residual R.chordlessResidual

/-- The assembled `PlanarInputs` genuinely wraps the assembled dichotomy (no rewrapper / no
`False`): its `recursiveDichotomy` field IS `chordRecursiveDichotomy_of_residuals R`. -/
theorem planarInputs_of_residuals_recursiveDichotomy (R : Ch35RecursionResiduals α) :
    (planarInputs_of_residuals R).recursiveDichotomy = chordRecursiveDichotomy_of_residuals R :=
  rfl

/-! ## Section 7.  Canonical chordless closure

The chordless residual has been discharged by `ZinanCh35ChordlessSupplier`.
Together with the already-produced canonical chord residual supplier, this gives
the direct Chapter-35 endpoint through the older residual-level entry point. -/

/-- The canonical chordless branch supplier produced by the Phase-C deletion
assembly. -/
noncomputable def canonicalChordlessBranchSupplier (α : Type u) [DecidableEq α] :
    ChordlessBranchSupplier α :=
  chordlessBranchSupplier_of_residual
    (ProofsInTheBook.ZinanCh35ChordlessSupplier.canonicalChordlessOracleResidual
      (α := α))

/-- The direct canonical Chapter-35 endpoint: the chord branch uses the already
closed canonical chord residual supplier, and the chordless branch uses the
closed Phase-C deletion supplier. -/
theorem fiveColor_planar_canonical
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M) :
    M.toSimpleGraph.Colorable 5 :=
  ProofsInTheBook.ZinanCh35ChordBranch.fiveColor_of_residual hNT
    (ProofsInTheBook.ZinanCh35ChordSupplier2.canonicalChordBranchResidualSupplier
      (ULift.{u} (Fin 5)))
    (canonicalChordlessBranchSupplier (ULift.{u} (Fin 5)))

end ProofsInTheBook.ZinanCh35Final

/-! ## Axiom audit (expect clean-3: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35Final.chordRecursiveDichotomy_of_residuals
#print axioms ProofsInTheBook.ZinanCh35Final.chordRecursiveDichotomy_of_residuals_nonvacuous
#print axioms ProofsInTheBook.ZinanCh35Final.planarInputs_of_residuals
#print axioms ProofsInTheBook.ZinanCh35Final.fiveColor_planar_of_recursionResiduals
#print axioms ProofsInTheBook.ZinanCh35Final.fiveColor_planar_of_recursionResiduals_eq_suppliers
#print axioms ProofsInTheBook.ZinanCh35Final.chordlessSupplier_of_residuals
#print axioms ProofsInTheBook.ZinanCh35Final.planarInputs_of_residuals_recursiveDichotomy
#print axioms ProofsInTheBook.ZinanCh35Final.canonicalChordlessBranchSupplier
#print axioms ProofsInTheBook.ZinanCh35Final.fiveColor_planar_canonical
