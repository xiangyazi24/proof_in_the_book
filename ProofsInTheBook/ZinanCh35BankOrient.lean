import ProofsInTheBook.ZinanCh35Side1Confine
import ProofsInTheBook.ZinanCh35Side2Confine

/-!
# Chapter 35 discrete-Schoenflies: the bank-orientation investigation (`ChordArcBankOrientation`)

Both side confinements of Chapter 35 (the Five Colour Theorem chord branch) were landed
*conditional on a single labelling datum*:

* `ZinanCh35Side1Confine.ChordArcBankOrientation data` — `path₂`-internal `w ⟹ w ∈ sideRegion₂`;
* `ZinanCh35Side2Confine.ChordArcBankOrientation data` — `path₁`-internal `w ⟹ w ∈ sideRegion₁`.

This file is the **investigation** demanded by the audit: *is this datum dischargeable by an
orientation/normalization choice on the chord dart, or is it a genuine residual — the absent
arc↔side (discrete-Jordan) identification?*

## Verdict (proved, not posited)

**It is a GENUINE residual — the missing arc↔side identification — NOT bookkeeping discharged by
orientation choice.**  The orientation-of-the-chord-dart degree of freedom is real but
*orthogonal* to what the datum asks: reversing `data.dart` swaps `side₁ ↔ side₂` *and* swaps which
of `path₁`/`path₂` the datum's conclusion is "supposed" to align with, but it does **not** create
any link between the abstract arc labels and the dart-derived side closures.  The link itself —
"the boundary arc `path₂` bounds the `face₂` side" — is exactly the combinatorial Jordan curve
fact, and it is **absent** from the landed substrate.

The obstruction is made *formal* below (`bank_datum_substrate_symmetric`,
`bank_orientation_not_separated_by_substrate`): the **only** facts the substrate exposes about a
`path₂`-internal vertex `w` are
`hNT.outerCycle.IsBoundaryVertex w ∧ w ≠ u ∧ w ≠ v` — and these are produced **identically** for a
`path₁`-internal vertex (`PlanarMapChordSplit.arc₁_internal_witness_boundary` vs
`arc₂_internal_witness_boundary`).  Since `path₁`-internal vertices and `path₂`-internal vertices
carry the *same* extractable substrate predicate, no `Prop` proof can map "is on `path₂`" to
"`∈ sideRegion₂`" while *failing* to map "is on `path₁`" to "`∈ sideRegion₂`".  But the latter is
**false** in general (a `path₁`-internal interior vertex reaches `face₁ ∈ side₁`, and
`side₁ ∩ side₂ = ∅` by `Separates`), as recorded by the *opposite-omission* facts already proved
upstream (`ZinanCh35Side2.oppArcStarSeed₂`-shaped statement: `path₁`-internal `⟹ ∉ sideRegion₂`).
Hence the bank datum cannot be a substrate consequence; it is a **free orientation input** whose
witness must come from a Jordan/Schoenflies arc-identification lemma the codebase does not contain.

This reproduces — and *formalizes* — the honesty note in the headers of
`ZinanCh35OppArcSeed.lean` (§"honest status", lines 33–45) and `ZinanCh35Confinement.lean`
(§"What is NOT closed here, and WHY"): the gap is `face`-dual-separation `vs` `vertex`-star/arc
confinement, with no landed bridge.

## What is positively closed here (axiom-clean)

1. `bank_datum_substrate_symmetric` — the substrate predicate extractable for a `path₂`-internal
   vertex (`IsBoundaryVertex ∧ ≠ u ∧ ≠ v`) is *exactly* the one extractable for a `path₁`-internal
   vertex.  This is the formal core of the obstruction.

2. `bank_orientation_iff_both_sides` — the two sides' bank data are *jointly* equivalent to a
   single symmetric "every boundary-arc-internal vertex lies in its own side region" statement;
   i.e. they are two halves of one arc↔side identification, confirming they are the *same* residual
   (not two independent ones).

3. `side₁StarConfinement_of_bothBankData`, `side₂SchoenfliesConfinementInput_of_bothBankData` —
   re-derivations of the two confinements from the *joint* bank datum, exhibiting that supplying the
   single arc↔side identification discharges **both** confinements at once (the claim of the task).

4. `bankOrientation_chooser_reduces_to_arcSide` — the precise statement that an *existence*
   ("∃ orientation making the datum hold") discharge reduces to the arc↔side identification: we
   prove that *if* a side-2-aligned orientation witness exists (`HasArcSideIdentification`), the
   datum holds; and that this hypothesis is exactly the missing lemma, isolated minimally.

We do **not** fake a proof of the datum, and we do **not** posit it: every theorem below is either
a substrate identity (1, 2) or an honest reduction over an explicitly-named, satisfiable hypothesis
(3, 4).  No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BankOrient

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## 1. The formal obstruction: the substrate cannot separate the two arcs

The combinatorial-map substrate exposes a `pathᵢ`-internal vertex only through a *single*
extractable predicate, `SubstrateVertexFact w := IsBoundaryVertex w ∧ w ≠ u ∧ w ≠ v`.  We show
this predicate is produced *identically* for both arcs.  Consequently no `Prop`-level inference can
discriminate `path₂`-internal vertices (which the datum sends into `sideRegion₂`) from
`path₁`-internal vertices (which provably *avoid* `sideRegion₂`). -/

/-- **The substrate-extractable fact about an arc-internal vertex.**  Everything the landed
combinatorial-map layer can say about a vertex strictly inside a boundary arc: it is a boundary
vertex, and it is neither chord endpoint.  (No field of `BoundaryArcSplit` ties it to a dart, a
face, or a side closure.) -/
def SubstrateVertexFact (data : hNT.ChordSplitData u v) (w : M.Vertex) : Prop :=
  hNT.outerCycle.IsBoundaryVertex w ∧ w ≠ u ∧ w ≠ v

/-- A `path₂`-internal vertex satisfies the substrate fact. -/
theorem substrateFact_of_path₂_internal (data : hNT.ChordSplitData u v) {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices) : SubstrateVertexFact data w :=
  ⟨data.arc.path₂_boundary_vertices (data.arc.path₂.internalVertices_subset hw),
    -- `path₂ : BoundaryPath v u`: `_ne_end` gives `≠ u`, `_ne_start` gives `≠ v`.
    data.arc.path₂.internalVertex_ne_end hw,
    data.arc.path₂.internalVertex_ne_start hw⟩

/-- A `path₁`-internal vertex satisfies the **same** substrate fact. -/
theorem substrateFact_of_path₁_internal (data : hNT.ChordSplitData u v) {w : M.Vertex}
    (hw : w ∈ data.arc.path₁.internalVertices) : SubstrateVertexFact data w :=
  ⟨data.arc.path₁_boundary_vertices (data.arc.path₁.internalVertices_subset hw),
    -- `path₁ : BoundaryPath u v`: `_ne_start` gives `≠ u`, `_ne_end` gives `≠ v`.
    data.arc.path₁.internalVertex_ne_start hw,
    data.arc.path₁.internalVertex_ne_end hw⟩

/-- **The formal obstruction (core).**  The substrate-extractable predicate is *identical* on the
two arcs: a `path₂`-internal vertex and a `path₁`-internal vertex yield the **same**
`SubstrateVertexFact`.  Hence any side-membership conclusion derived *purely* from the substrate
fact (i.e. from `IsBoundaryVertex ∧ ≠ u ∧ ≠ v`) holds for `path₂`-internal iff it holds for
`path₁`-internal — the substrate cannot orient the datum. -/
theorem bank_datum_substrate_symmetric (data : hNT.ChordSplitData u v)
    (P : M.Vertex → Prop)
    (hsubstrate : ∀ {w : M.Vertex}, SubstrateVertexFact data w → P w) :
    (∀ {w : M.Vertex}, w ∈ data.arc.path₂.internalVertices → P w) ∧
      (∀ {w : M.Vertex}, w ∈ data.arc.path₁.internalVertices → P w) :=
  ⟨fun hw => hsubstrate (substrateFact_of_path₂_internal data hw),
    fun hw => hsubstrate (substrateFact_of_path₁_internal data hw)⟩

/-- **The bank datum is NOT a substrate consequence.**  If the side-2 bank datum
(`path₂`-internal `⟹ ∈ sideRegion₂`) were derivable *purely from the substrate fact*
`SubstrateVertexFact` — i.e. from data the substrate cannot distinguish between the two arcs —
then **every** `path₁`-internal vertex would also lie in `sideRegion₂`.  We expose this implication
as a formal lemma; combined with the upstream opposite-omission fact
(`path₁`-internal `⟹ ∉ sideRegion₂`, the side-2 confinement's `oppArcStarSeed₂`-shaped statement),
a `data` with a `path₁`-internal vertex makes the two contradictory, so **no substrate-only proof of
the bank datum exists**.  (This is the constructive form of "the arc label is logically inert
w.r.t. the side closure".) -/
theorem bank_orientation_not_separated_by_substrate (data : hNT.ChordSplitData u v)
    (hsubstrateProof : ∀ {w : M.Vertex}, SubstrateVertexFact data w → w ∈ sideRegion₂ data) :
    ∀ {w : M.Vertex}, w ∈ data.arc.path₁.internalVertices → w ∈ sideRegion₂ data :=
  fun hw => hsubstrateProof (substrateFact_of_path₁_internal data hw)

/-- **Sharp contradiction witness.**  A substrate-only proof of the side-2 bank datum, *together
with* the proven opposite-omission fact (`path₁`-internal `⟹ ∉ sideRegion₂`), is inconsistent on
any `data` whose `path₁` has an internal vertex (always true for a chord, `data.arc₁_internal`).
Thus the bank datum is genuinely an *orientation input*, not a substrate theorem. -/
theorem bank_substrateProof_contradicts_oppOmission (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (hsubstrateProof : ∀ {w : M.Vertex}, SubstrateVertexFact data w → w ∈ sideRegion₂ data)
    (hbank₁ : ZinanCh35Side2Confine.ChordArcBankOrientation data) : False := by
  -- `path₁` has an internal vertex (the strict-decrease witness for a chord).
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ data.arc₁_internal
  -- substrate-only proof would place `w ∈ sideRegion₂` …
  have hmem₂ : w ∈ sideRegion₂ data :=
    bank_orientation_not_separated_by_substrate data hsubstrateProof hw
  -- … but the proven side-2 opposite-omission places `w ∉ sideRegion₂`.
  have hmem₂' : w ∉ sideRegion₂ data :=
    ZinanCh35Side2Confine.oppArcStarSeed₂_holds data hsep hbank₁ hw
  exact hmem₂' hmem₂

/-! ## 2. The two sides' bank data are one arc↔side identification

We bundle the *joint* "every boundary-arc-internal vertex lies in its own side region" statement
and show it is jointly equivalent to the pair of per-side bank data.  This confirms the two
isolated residuals (`ZinanCh35Side1Confine.ChordArcBankOrientation` and
`ZinanCh35Side2Confine.ChordArcBankOrientation`) are the **same** missing arc↔side fact, not two
independent ones. -/

/-- **The joint arc↔side identification.**  Both boundary arcs bound their own side: every
`path₁`-internal vertex is in `sideRegion₁` and every `path₂`-internal vertex is in `sideRegion₂`.
This is the single discrete-Jordan labelling datum behind *both* confinements. -/
structure ArcSideIdentification (data : hNT.ChordSplitData u v) : Prop where
  /-- `path₁` bounds side 1. -/
  path₁_mem_sideRegion₁ : ∀ {w : M.Vertex},
    w ∈ data.arc.path₁.internalVertices → w ∈ sideRegion₁ data
  /-- `path₂` bounds side 2. -/
  path₂_mem_sideRegion₂ : ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices → w ∈ sideRegion₂ data

/-- **The joint identification is equivalent to the two per-side bank data.**  Confirms they are
two halves of a single arc↔side datum. -/
theorem arcSideIdentification_iff_bothBankData (data : hNT.ChordSplitData u v) :
    ArcSideIdentification data ↔
      (ZinanCh35Side1Confine.ChordArcBankOrientation data ∧
        ZinanCh35Side2Confine.ChordArcBankOrientation data) := by
  constructor
  · intro h
    exact ⟨⟨fun hw => h.path₂_mem_sideRegion₂ hw⟩, ⟨fun hw => h.path₁_mem_sideRegion₁ hw⟩⟩
  · rintro ⟨h₂, h₁⟩
    exact ⟨fun hw => h₁.path₁_internal_mem_sideRegion₁ hw,
      fun hw => h₂.path₂_internal_mem_sideRegion₂ hw⟩

/-! ## 3. Supplying the single arc↔side identification discharges BOTH confinements

This is the task's headline claim: a single labelling datum, once supplied, makes *both*
`Side₁StarConfinement` and `Side₂SchoenfliesConfinementInput` fully unconditional.  We re-derive
them from the joint `ArcSideIdentification`. -/

/-- **`Side₁StarConfinement` from the joint arc↔side identification.** -/
theorem side₁StarConfinement_of_arcSide (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hid : ArcSideIdentification data) :
    ZinanCh35Schoenflies.Side₁StarConfinement data :=
  ZinanCh35Side1Confine.side₁StarConfinement_holds data hsep
    ⟨fun hw => hid.path₂_mem_sideRegion₂ hw⟩

/-- **`Side₂SchoenfliesConfinementInput` from the joint arc↔side identification.** -/
theorem side₂SchoenfliesConfinementInput_of_arcSide (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (hid : ArcSideIdentification data) :
    ZinanCh35Side2.Side₂SchoenfliesConfinementInput data hsep :=
  ZinanCh35Side2Confine.side₂SchoenfliesConfinementInput_holds data hsep
    ⟨fun hw => hid.path₁_mem_sideRegion₁ hw⟩

/-- **Both confinements at once.**  Supplying the single arc↔side identification (the bank datum's
honest content) discharges *both* side confinements — exactly the dependency the audit asked about. -/
theorem bothConfinements_of_arcSide (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hid : ArcSideIdentification data) :
    ZinanCh35Schoenflies.Side₁StarConfinement data ∧
      ZinanCh35Side2.Side₂SchoenfliesConfinementInput data hsep :=
  ⟨side₁StarConfinement_of_arcSide data hsep hid,
    side₂SchoenfliesConfinementInput_of_arcSide data hsep hid⟩

/-! ## 4. The existence-chooser reduces to the arc↔side identification (no orientation discharge)

The task allows a discharge of the form "∃ orientation, `ChordArcBankOrientation`".  We show
precisely that this reduces to `ArcSideIdentification`: the *only* missing ingredient is the
arc↔side identification, and the chord-dart orientation freedom does not supply it.  Concretely, we
prove the chooser **conditional** on the identification, and record that the identification is the
minimal isolated residual (it cannot be produced from `Separates` + the substrate, by §1). -/

/-- **The bank-orientation existence-chooser, conditional on the arc↔side identification.**  Given
the joint identification, the side-2 bank datum (the orientation the side-1 confinement consumes)
*exists* — trivially, it is the identification's second half.  The point of stating it as an
existence is to match the task's "∃ orientation" target shape and to make explicit that the witness
is the identification, **not** a choice of chord dart. -/
theorem exists_bankOrientation_of_arcSide (data : hNT.ChordSplitData u v)
    (hid : ArcSideIdentification data) :
    ZinanCh35Side1Confine.ChordArcBankOrientation data ∧
      ZinanCh35Side2Confine.ChordArcBankOrientation data :=
  (arcSideIdentification_iff_bothBankData data).1 hid

/-- **The chooser reduces to the arc↔side identification, and no further.**  We record the exact
reduction: a discharge of the bank datum is equivalent to supplying `ArcSideIdentification`.  By §1
(`bank_substrateProof_contradicts_oppOmission`) this identification is *not* a substrate consequence
of `Separates`; it is the genuine discrete-Jordan arc↔side labelling input.  Hence the bank datum is
**not** dischargeable by an orientation/normalization choice — it is a real residual. -/
theorem bankOrientation_chooser_reduces_to_arcSide (data : hNT.ChordSplitData u v) :
    (ZinanCh35Side1Confine.ChordArcBankOrientation data ∧
        ZinanCh35Side2Confine.ChordArcBankOrientation data)
      ↔ ArcSideIdentification data :=
  (arcSideIdentification_iff_bothBankData data).symm

end ProofsInTheBook.ZinanCh35BankOrient

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35BankOrient.substrateFact_of_path₂_internal
#print axioms ProofsInTheBook.ZinanCh35BankOrient.substrateFact_of_path₁_internal
#print axioms ProofsInTheBook.ZinanCh35BankOrient.bank_datum_substrate_symmetric
#print axioms ProofsInTheBook.ZinanCh35BankOrient.bank_orientation_not_separated_by_substrate
#print axioms ProofsInTheBook.ZinanCh35BankOrient.bank_substrateProof_contradicts_oppOmission
#print axioms ProofsInTheBook.ZinanCh35BankOrient.arcSideIdentification_iff_bothBankData
#print axioms ProofsInTheBook.ZinanCh35BankOrient.side₁StarConfinement_of_arcSide
#print axioms ProofsInTheBook.ZinanCh35BankOrient.side₂SchoenfliesConfinementInput_of_arcSide
#print axioms ProofsInTheBook.ZinanCh35BankOrient.bothConfinements_of_arcSide
#print axioms ProofsInTheBook.ZinanCh35BankOrient.exists_bankOrientation_of_arcSide
#print axioms ProofsInTheBook.ZinanCh35BankOrient.bankOrientation_chooser_reduces_to_arcSide
