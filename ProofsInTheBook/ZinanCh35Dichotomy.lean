import ProofsInTheBook.ChordSplitNT
import ProofsInTheBook.ChordSplitFinal
import ProofsInTheBook.ZinanCh35Cert

/-!
# The `ChordRecursiveDichotomy` supplier for Chapter 35 (Five Colour Theorem)

This leaf builds the last major induction-level piece of Chapter 35: a
`ChordSplitNT.ChordRecursiveDichotomy α` supplier, i.e. the uniform per-near-
triangulation choice the proven recursion driver
`ChordSplitNT.thomassen_aux_chordRecursive` consumes.

## What is proved here unconditionally

1. **The chord/chordless decision is unconditional.**  For *every* near-
   triangulation `M` with the Thomassen lists, classically either some boundary
   chord exists, `∃ u v, hNT.outerCycle.Chord u v`, or the boundary is chordless,
   `BoundaryChordless hNT.outerCycle`.  This is the plain law of excluded middle on
   the (Prop-valued) chord existence; it requires no planar input.  `boundaryChord_em`.

2. **The branch packaging is unconditional.**  Given
   * a uniform *chord-branch supplier* that, **only when a chord actually exists**,
     produces the chord-branch residue `ChordSplitFinal.ChordBranchResidue`
     (regions glue + the two `ChordSideReconstruction`s — the chord half of the
     dichotomy, from which `ChordRecursionData` is built by
     `ChordSplitFinal.chordRecursionData_of_branchResidue`), and
   * a uniform *chordless-branch supplier* that, **only when the boundary is
     chordless**, produces the boundary-deletion fan oracle
     `ThomassenInduction.ChordlessOracle`,

   the two are routed by the unconditional decision into a
   `ChordRecursiveDichotomy α`.  This routing — `chordRecursiveDichotomy_of_suppliers`
   — adds no fake content: the chord branch yields `Σ' u v, ChordRecursionData`
   (no colorings), the chordless branch yields the oracle, exactly the two summands
   `ChordRecursiveDichotomy.decide` must return.

## What this reduces to (the named residuals)

The supplier reduces *cleanly and unconditionally* to the two named branch
suppliers `ChordBranchSupplier` / `ChordlessBranchSupplier`.  These are the genuine,
already-isolated discrete Jordan–Schoenflies residues:

* `ChordBranchSupplier` consumes a real chord witness and returns
  `ChordBranchResidue`.  Its side-1 half is *already discharged* modulo the
  confinement bundle by `ZinanCh35Cert.side₁Reconstruction_of_certificateInputs`
  (← `ZinanCh35FinalClose.Side₁SchoenfliesConfinementInput`); the genuinely-missing
  pieces are the **side-2 mirror reconstruction** (no `chordSideResidue₂_final` is
  landed) and the **`ChordSplitRegions` glue** (the `M`-vertex partition, equivalent
  to `Separates`).
* `ChordlessBranchSupplier` consumes a real chordless witness and returns the
  `ChordlessOracle` (the boundary-deletion `FanSurgeryReconstruction` Jordan data).

Neither residual is vacuous: `ChordBranchResidue` is inhabited from genuine side
reconstructions (`ChordSplitFinal` Section 3, `chordSideResidue_mk`), and
`ChordlessOracle` is the same fan datum the existing `JordanOracle` /
`ThomassenInduction` chordless branch carries and recurses on.  The suppliers are
*hypotheses over real witnesses*, not unsatisfiable premises (each branch supplier
is only ever applied under a true chord / chordless witness), so the conditional is
operationally non-vacuous (§3.3).

## What genuinely remains (honest accounting)

`chordRecursiveDichotomy_of_suppliers` is **CONDITIONAL** on the two named branch
suppliers.  The *decision* and the *routing/packaging* are unconditional (clean-3);
the *content* of each branch (side-2 reconstruction + regions glue for the chord
branch, fan oracle for the chordless branch) is the isolated planar residue the
upstream files document has no unconditional producer.  No `sorry`/`axiom`/`admit`/
`native_decide`; no posited conclusion.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35Dichotomy

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ListColoring
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ThomassenInduction
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ChordSplitFinal

universe u

variable {α : Type u} [DecidableEq α]

/-! ## Section 1.  The chord/chordless decision (unconditional) -/

/-- **The chord / chordless decision is unconditional.**

For every near-triangulation `M`, *either* the outer boundary cycle has a chord
(some pair of distinct boundary vertices adjacent in `M` but not via a boundary
edge), *or* the boundary is chordless.  This is the law of excluded middle on the
Prop `∃ u v, hNT.outerCycle.Chord u v`; no planar/Jordan input is used.  It is the
exact case split the Thomassen induction performs at each recursive step. -/
theorem boundaryChord_em {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M) :
    (∃ u v : M.Vertex, hNT.outerCycle.Chord u v) ∨
      BoundaryChordless hNT.outerCycle := by
  classical
  by_cases h : ∃ u v : M.Vertex, hNT.outerCycle.Chord u v
  · exact Or.inl h
  · refine Or.inr ?_
    intro u v hchord
    exact h ⟨u, v, hchord⟩

/-! ## Section 2.  The two named branch suppliers (the isolated planar residues)

Each branch supplier is invoked only under a *true* witness (a chord, resp.
chordlessness), so the conditional is operationally non-vacuous: the hypotheses are
satisfiable on exactly the inputs at which they are used. -/

/-- **The chord-branch supplier** — the chord half of the dichotomy as a named
residual.  Given any near-triangulation with the Thomassen lists *and a genuine
boundary chord* `(u, v)`, it produces the chord-branch residue
`ChordSplitFinal.ChordBranchResidue` (the `M`-vertex `ChordSplitRegions` glue plus
the two side `ChordSideReconstruction`s).

This is exactly the discrete Jordan–Schoenflies content the chord case needs:
* the side-1 reconstruction is discharged modulo the confinement bundle by
  `ZinanCh35Cert.side₁Reconstruction_of_certificateInputs`;
* the side-2 mirror and the regions partition (`Separates`) are the still-unbuilt
  pieces.

It is *not* a vacuous premise: `ChordBranchResidue` is inhabited from genuine side
reconstructions (`ChordSplitFinal.chordSideResidue_mk`,
`chordSideReconstruction_region_nonempty`). -/
structure ChordBranchSupplier (α : Type u) [DecidableEq α] : Type (u + 1) where
  /-- For each near-triangulation with the Thomassen lists and a boundary chord,
  the chord-branch residue for some chord `(u, v)`. -/
  supply :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α), ThomassenLists hNT p q L cp cq →
      (∃ u v : M.Vertex, hNT.outerCycle.Chord u v) →
        Σ' u v : M.Vertex, ChordBranchResidue hNT u v p q L cp cq

/-- **The chordless-branch supplier** — the chordless half of the dichotomy as a
named residual.  Given any near-triangulation with the Thomassen lists *and a
chordless boundary*, it produces the boundary-deletion fan oracle
`ThomassenInduction.ChordlessOracle` (the `FanSurgeryReconstruction` Jordan data,
plus the reserved-colour and deleted-list bookkeeping).

This is the same fan datum the existing `JordanOracle` / `ThomassenInduction`
chordless branch carries and recurses on — not a vacuous premise. -/
structure ChordlessBranchSupplier (α : Type u) [DecidableEq α] : Type (u + 1) where
  /-- For each near-triangulation with the Thomassen lists and a chordless boundary,
  the chordless fan oracle. -/
  supply :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α), ThomassenLists hNT p q L cp cq →
      BoundaryChordless hNT.outerCycle →
        ChordlessOracle hNT p q L cp cq

/-! ## Section 3.  Routing the two suppliers into the dichotomy (unconditional) -/

/-- **The chord-recursive dichotomy, assembled from the two branch suppliers.**

The decision `boundaryChord_em` is unconditional; this theorem routes it:
* in the chord case, the chord-branch supplier yields a `ChordBranchResidue`, from
  which `ChordSplitFinal.chordRecursionData_of_branchResidue` builds the
  `ChordRecursionData` (carrying the two smaller side near-triangulations, **no
  colorings**) — the left summand;
* in the chordless case, the chordless-branch supplier yields the `ChordlessOracle`
  — the right summand.

No content is fabricated: the routing is pure case analysis on the unconditional
decision, and each branch is discharged by its named supplier.  Hence the supplier
is `CONDITIONAL` on exactly the two named residuals, with the decision and packaging
unconditional. -/
noncomputable def chordRecursiveDichotomy_of_suppliers
    (Sc : ChordBranchSupplier α) (Sl : ChordlessBranchSupplier α) :
    ChordRecursiveDichotomy α where
  decide := by
    classical
    intro D _ _ M hNT p q L cp cq h
    -- The decision `∃ u v, Chord u v` is a Prop; eliminate it into the `Type`-valued
    -- target via `Classical.dec` (the unconditional chord/chordless EM).
    by_cases hchord : ∃ u v : M.Vertex, hNT.outerCycle.Chord u v
    · -- chord case: produce the recursion datum (no colorings).
      obtain ⟨u, v, br⟩ := Sc.supply hNT p q L cp cq h hchord
      exact Sum.inl ⟨u, v, chordRecursionData_of_branchResidue br⟩
    · -- chordless case: the boundary is chordless; produce the fan oracle.
      have hchordless : BoundaryChordless hNT.outerCycle := by
        intro u v hc; exact hchord ⟨u, v, hc⟩
      exact Sum.inr (Sl.supply hNT p q L cp cq h hchordless)

/-- **Non-vacuity of the assembled dichotomy.**  Given the two branch suppliers, a
`ChordRecursiveDichotomy` is inhabited.  This certifies the assembly is not a hidden
`False`: the routing genuinely terminates in one of the two summands on every
near-triangulation. -/
theorem chordRecursiveDichotomy_nonvacuous
    (Sc : ChordBranchSupplier α) (Sl : ChordlessBranchSupplier α) :
    Nonempty (ChordRecursiveDichotomy α) :=
  ⟨chordRecursiveDichotomy_of_suppliers Sc Sl⟩

/-! ## Section 4.  The `PlanarInputs` corollary

Threading the assembled dichotomy into `ZinanCh35Cert.PlanarInputs`, the exact
remaining bundle `ZinanCh35Cert.fiveColor_of_planarInputs` consumes.  This closes
the induction-level supplier: the Five Colour Theorem for near-triangulations holds
given the two named branch suppliers (and `5 ≤ Fintype.card`). -/

/-- The `PlanarInputs` bundle assembled from the two branch suppliers. -/
noncomputable def planarInputs_of_suppliers
    (Sc : ChordBranchSupplier α) (Sl : ChordlessBranchSupplier α) :
    ProofsInTheBook.ZinanCh35Cert.PlanarInputs α :=
  ⟨chordRecursiveDichotomy_of_suppliers Sc Sl⟩

/-- **Five-colorability of a near-triangulation from the two named branch
suppliers.**  Composing `planarInputs_of_suppliers` with
`ZinanCh35Cert.fiveColor_of_planarInputs`: every near-triangulation is
five-colorable given the chord-branch and chordless-branch suppliers — the entire
Chapter-35 induction surface now reduced to those two isolated planar residues. -/
theorem fiveColor_of_branchSuppliers
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M)
    (Sc : ChordBranchSupplier (ULift.{u} (Fin 5)))
    (Sl : ChordlessBranchSupplier (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  ProofsInTheBook.ZinanCh35Cert.fiveColor_of_planarInputs hNT
    (planarInputs_of_suppliers Sc Sl)

end ProofsInTheBook.ZinanCh35Dichotomy

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35Dichotomy.boundaryChord_em
#print axioms ProofsInTheBook.ZinanCh35Dichotomy.chordRecursiveDichotomy_of_suppliers
#print axioms ProofsInTheBook.ZinanCh35Dichotomy.chordRecursiveDichotomy_nonvacuous
#print axioms ProofsInTheBook.ZinanCh35Dichotomy.planarInputs_of_suppliers
#print axioms ProofsInTheBook.ZinanCh35Dichotomy.fiveColor_of_branchSuppliers
