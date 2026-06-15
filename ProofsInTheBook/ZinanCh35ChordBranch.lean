import ProofsInTheBook.ZinanCh35Dichotomy
import ProofsInTheBook.ZinanCh35Side2
import ProofsInTheBook.ZinanCh35Aligned

/-!
# Chapter 35: wiring the `ChordBranchSupplier` from the now-unconditional confinements

`ZinanCh35Dichotomy.chordRecursiveDichotomy_of_suppliers` builds the
`ChordRecursiveDichotomy α` from a `ChordBranchSupplier α` and a `ChordlessBranchSupplier α`.
This leaf attacks the chord half: it threads the now-UNCONDITIONAL confinements
(`ZinanCh35Aligned.NearTriangulation.bothConfinements_normalized`) into a
`ChordSplitFinal.ChordBranchResidue`, hence a `ChordBranchSupplier`.

## What `bothConfinements_normalized` genuinely buys

For the *normalized* chord-split datum `normalizedChordSplitData h` (whose `arc.path₂` IS the
forward `v → u` boundary run), the arc↔side identification holds **by construction**, so — modulo
the chord-level separation `Separates` and the 2-valued chord-dart orientation —
`bothConfinements_normalized` discharges BOTH

* `ZinanCh35Schoenflies.Side₁StarConfinement (normalizedChordSplitData h)`, and
* `ZinanCh35Side2.Side₂SchoenfliesConfinementInput (normalizedChordSplitData h) hsep`

with no discrete-Jordan arc↔side input.  The side-2 confinement is *exactly* the `confinement`
field of `ZinanCh35Side2.Side₂CertificateInputs`; the side-1 `Side₁StarConfinement` reaches the
`confinement` field of `ZinanCh35Cert.Side₁CertificateInputs` (typed
`ZinanCh35FinalClose.Side₁SchoenfliesConfinementInput`) through the landed bridges
`ZinanCh35Schoenflies.vertexStar_confined_of_starConfinement` (modulo the boundary-incidence
residual `OuterDartArc₁`) and `ZinanCh35FinalClose.confinementInput_of_schoenflies`.

So the confinement fields of BOTH side certificate-input bundles are removed from the residue:
they are *produced* here, not posited.

## What genuinely remains (honest accounting — the isolated residue)

A `ChordBranchResidue` further needs, for a chord `(u, v)`: the `M`-vertex-level
`ChordSplitRegions` glue (with `s₁ = sideRegion₁`, `s₂ = sideRegion₂`), the chord separation
`Separates`, and — for each side — the boundary/inner-triangulation classification
(`ContiguousInterval`), the anchor-incidence fact (`AnchorsShareFace`), the side Thomassen-list
hypotheses `hLₛ`, the anchor darts realizing the chord endpoints, and the boundary-incidence
residual `OuterDartArc₁` (side 1).  None has an unconditional producer in this checkout.  We
isolate them *sharply* into one named bundle `ChordBranchResidualData`, whose `confinement` fields
are **absent**, and prove

`chordBranchSupplier_of_residual : (uniform residual supplier) → ChordBranchSupplier α`.

This is `CONDITIONAL` on the named residual, with the confinements, the orientation routing, and
the side-reconstruction assembly UNCONDITIONAL.  No `sorry`/`axiom`/`admit`/`native_decide`.

### Verdict

`ChordBranchSupplier` is **NOT** dischargeable outright today: the `ChordSplitRegions` glue +
`Separates` + per-side `ContiguousInterval/AnchorsShareFace/hLₛ/anchors/OuterDartArc₁` have no
producer.  `bothConfinements_normalized` removes ONLY the two confinement fields.  The deliverable
is the honest reduction `ChordBranchSupplier ⟸ ChordBranchResidualData supplier`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordBranch

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35Side2
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {u v : M.Vertex} {α : Type u} [DecidableEq α]

/-! ## Section 1.  The side certificate-inputs WITHOUT the confinement field

These mirror `ZinanCh35Cert.Side₁CertificateInputs` / `ZinanCh35Side2.Side₂CertificateInputs`
field-for-field, **dropping** the `confinement` field — which is produced from
`bothConfinements_normalized` in the supplier.  They are stated against the normalized datum. -/

/-- Side-1 certificate inputs minus the confinement (produced from `Side₁StarConfinement`). -/
structure Side₁InputsNoConf (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α) where
  ci : ContiguousInterval data hsep a₀ a₁ hne
  hshare : ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace data hsep a₀ a₁
  hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)
  ha₀ : M.tail a₀.1 = u
  ha₁ : M.tail a₁.1 = v
  pₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex
  qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex
  cpₛ : α
  cqₛ : α
  hLₛ : ThomassenLists
    (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
    pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ
  /-- The boundary-incidence residual feeding the outer-dart half of the `edge_confined`
  reduction `Side₁StarConfinement → Side₁SchoenfliesConfinement`. -/
  houter : ProofsInTheBook.ZinanCh35Schoenflies.OuterDartArc₁ data

/-- Side-2 certificate inputs minus the confinement (produced as
`Side₂SchoenfliesConfinementInput` directly). -/
structure Side₂InputsNoConf (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α) where
  hdisk : ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep
  hshare : ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep a₀ a₁
  ci : ContiguousInterval₂ data hsep a₀ a₁ hne
  hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)
  ha₀ : M.tail a₀.1 = u
  ha₁ : M.tail a₁.1 = v
  pₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex
  qₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex
  cpₛ : α
  cqₛ : α
  hLₛ : ThomassenLists
    (chordSideNearTriangulation₂_of_share data hsep a₀ a₁ hne hdisk hshare ci)
    pₛ qₛ (fun x => L (sideVertexToM₂ data hsep a₀ a₁ hne x)) cpₛ cqₛ

/-! ## Section 2.  Producing the confinement fields from `bothConfinements_normalized`

`bothConfinements_normalized` gives `Side₁StarConfinement` and `Side₂SchoenfliesConfinementInput`
(modulo `hsep`, `htu`, `hhv`).  The side-1 `confinement` field needed by
`ZinanCh35Cert.Side₁CertificateInputs` is `Side₁SchoenfliesConfinementInput`; we bridge it with
the landed `vertexStar_confined_of_starConfinement` (needs `OuterDartArc₁`) +
`confinementInput_of_schoenflies`. -/

/-- The side-1 `Side₁SchoenfliesConfinementInput` from the star confinement and `OuterDartArc₁`. -/
theorem side₁ConfInput_of_star (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (conf : ProofsInTheBook.ZinanCh35Schoenflies.Side₁StarConfinement data)
    (houter : ProofsInTheBook.ZinanCh35Schoenflies.OuterDartArc₁ data) :
    ProofsInTheBook.ZinanCh35FinalClose.Side₁SchoenfliesConfinementInput data hsep :=
  ProofsInTheBook.ZinanCh35FinalClose.confinementInput_of_schoenflies data hsep
    (ProofsInTheBook.ZinanCh35Schoenflies.vertexStar_confined_of_starConfinement data hsep conf houter)

/-! ## Section 3.  Assembling the two side reconstructions (confinements produced)

Given the no-conf inputs and the produced confinements, build the full
`ZinanCh35Cert.Side₁CertificateInputs` / `ZinanCh35Side2.Side₂CertificateInputs`, then thread the
landed Cert builders into the `ChordSideReconstruction` shape. -/

/-- The side-1 reconstruction `ChordSideReconstruction hNT (sideRegion₁ data) L`, with the
confinement field produced from `Side₁StarConfinement` + `OuterDartArc₁`. -/
noncomputable def side₁Reconstruction_of_noConf (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α) (I : Side₁InputsNoConf data hsep a₀ a₁ hne L)
    (conf : ProofsInTheBook.ZinanCh35Schoenflies.Side₁StarConfinement data) :
    ChordSplitNT.ChordSideReconstruction hNT (sideRegion₁ data) L :=
  ProofsInTheBook.ZinanCh35Cert.side₁Reconstruction_of_certificateInputs data hsep a₀ a₁ hne L
    { ci := I.ci, hshare := I.hshare, hchord := I.hchord, ha₀ := I.ha₀, ha₁ := I.ha₁,
      pₛ := I.pₛ, qₛ := I.qₛ, cpₛ := I.cpₛ, cqₛ := I.cqₛ, hLₛ := I.hLₛ,
      confinement := side₁ConfInput_of_star data hsep conf I.houter }

/-- The side-2 reconstruction `ChordSideReconstruction hNT (sideRegion₂ data) L`, with the
confinement field produced as `Side₂SchoenfliesConfinementInput`. -/
noncomputable def side₂Reconstruction_of_noConf (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α) (I : Side₂InputsNoConf data hsep a₀ a₁ hne L)
    (conf : ProofsInTheBook.ZinanCh35Side2.Side₂SchoenfliesConfinementInput data hsep) :
    ChordSplitNT.ChordSideReconstruction hNT (sideRegion₂ data) L :=
  ProofsInTheBook.ZinanCh35Side2.side₂Reconstruction_of_certificateInputs data hsep a₀ a₁ hne L
    { hdisk := I.hdisk, hshare := I.hshare, ci := I.ci, hchord := I.hchord, ha₀ := I.ha₀,
      ha₁ := I.ha₁, pₛ := I.pₛ, qₛ := I.qₛ, cpₛ := I.cpₛ, cqₛ := I.cqₛ, hLₛ := I.hLₛ,
      confinement := conf }

/-! ## Section 4.  The per-chord residue bundle (confinements removed) and the branch residue

`ChordBranchResidualData h p q L cp cq` carries, for a chord `h : outerCycle.Chord u v` in the
*standard* chord-dart orientation, exactly the genuinely-unproduced planar pieces — **with neither
side confinement among them**.  The side regions are pinned to
`sideRegion₁/₂ (normalizedChordSplitData h)` via the `ChordSplitRegions` glue. -/

/-- Abbreviation for the normalized split datum of a chord. -/
local notation3 "ND " h => ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData h

/-- The genuinely-unproduced planar residue of one chord branch (confinements excluded). -/
structure ChordBranchResidualData (h : hNT.outerCycle.Chord u v)
    (p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) where
  /-- The chord separation keystone (`face₂ ∉ side₁`).  No unconditional producer. -/
  hsep : (ND h).Separates
  /-- The chord-dart standard orientation (`tail dart = u`). -/
  htu : M.tail (ND h).dart = u
  /-- The chord-dart standard orientation (`head dart = v`). -/
  hhv : M.head (ND h).dart = v
  /-- The `M`-vertex-level chord split regions glue, pinned to the side regions. -/
  regions : ChordSplitRegions hNT u v p q L cp cq
  regions_s₁ : regions.s₁ = sideRegion₁ (ND h)
  regions_s₂ : regions.s₂ = sideRegion₂ (ND h)
  /-- The side-1 certificate inputs WITHOUT confinement, at any anchors realizing the endpoints. -/
  side₁ : ∀ (a₀ a₁ : {d : D // d ∉ (ND h).keptDel₁}) (hne : a₀ ≠ a₁),
    M.tail a₀.1 = u → M.tail a₁.1 = v → Side₁InputsNoConf (ND h) hsep a₀ a₁ hne L
  /-- The side-2 certificate inputs WITHOUT confinement, for each forced-list coloring. -/
  side₂ : ∀ (c₁ : M.Vertex → α) (a₀ a₁ : {d : D // d ∉ (ND h).keptDel₂}) (hne : a₀ ≠ a₁),
    M.tail a₀.1 = u → M.tail a₁.1 = v →
      Side₂InputsNoConf (ND h) hsep a₀ a₁ hne (regions.forcedLists c₁ L)
  /-- Anchor darts realizing the chord endpoints on side 1. -/
  anchors₁ : Σ' (a₀ a₁ : {d : D // d ∉ (ND h).keptDel₁}) (_ : a₀ ≠ a₁),
    M.tail a₀.1 = u ∧ M.tail a₁.1 = v
  /-- Anchor darts realizing the chord endpoints on side 2. -/
  anchors₂ : Σ' (a₀ a₁ : {d : D // d ∉ (ND h).keptDel₂}) (_ : a₀ ≠ a₁),
    M.tail a₀.1 = u ∧ M.tail a₁.1 = v
  uv_ne : u ≠ v

/-- **The chord-branch residue from the residual bundle (confinements produced).**  Assembles a
`ChordSplitFinal.ChordBranchResidue hNT u v p q L cp cq` for the standard-orientation chord: the
`regions` glue is taken from the bundle, and the two side reconstructions are built by
`side₁/₂Reconstruction_of_noConf` — consuming the confinements PRODUCED from
`bothConfinements_normalized`, not posited.  The side reconstructions land on
`sideRegion₁/₂ (ND h)` and are transported onto `regions.s₁/s₂` along the pinning equalities. -/
noncomputable def chordBranchResidue_of_residualData {h : hNT.outerCycle.Chord u v}
    {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}
    (R : ChordBranchResidualData h p q L cp cq) :
    ChordBranchResidue hNT u v p q L cp cq := by
  classical
  -- both confinements, produced (not posited) from the normalized arc↔side identification.
  obtain ⟨conf₁, conf₂⟩ :=
    ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.bothConfinements_normalized
      h R.hsep R.htu R.hhv
  -- side-1 anchors and reconstruction on `sideRegion₁ (ND h)`, transported to `regions.s₁`.
  obtain ⟨a₀, a₁, hne, ha₀, ha₁⟩ := R.anchors₁
  have rec₁₀ : ChordSplitNT.ChordSideReconstruction hNT (sideRegion₁ (ND h)) L :=
    side₁Reconstruction_of_noConf (ND h) R.hsep a₀ a₁ hne L (R.side₁ a₀ a₁ hne ha₀ ha₁) conf₁
  refine
    { regions := R.regions
      uv_ne := R.uv_ne
      R₁ := R.regions_s₁ ▸ rec₁₀
      R₂ := ?_ }
  -- side-2 reconstruction family on `sideRegion₂ (ND h)`, transported to `regions.s₂`,
  -- with the forced lists from `regions`.
  intro c₁
  obtain ⟨b₀, b₁, hbne, hb₀, hb₁⟩ := R.anchors₂
  have rec₂₀ : ChordSplitNT.ChordSideReconstruction hNT (sideRegion₂ (ND h))
      (R.regions.forcedLists c₁ L) :=
    side₂Reconstruction_of_noConf (ND h) R.hsep b₀ b₁ hbne (R.regions.forcedLists c₁ L)
      (R.side₂ c₁ b₀ b₁ hbne hb₀ hb₁) conf₂
  exact R.regions_s₂ ▸ rec₂₀

/-! ## Section 5.  The uniform residual supplier and the `ChordBranchSupplier`

The residual `ChordBranchResidualData` is the per-chord isolated discrete-Jordan content
(confinements excluded).  A *uniform* supplier of it — for every near-triangulation with the
Thomassen lists and a chord in the standard chord-dart orientation — routes through
`chordBranchResidue_of_residualData` into the named `ChordBranchSupplier`.  The orientation
freedom is resolved with `chordDart_orientation` + `chord_symm`: whichever way the opaque chord
dart points, one of the two endpoint orderings is standard, and the residual is applied there. -/

/-- **The uniform residual supplier** — for every near-triangulation with the Thomassen lists and
a chord witness, the per-chord residue bundle (confinements excluded), at whatever endpoint
ordering makes the chord-dart orientation standard.  The supplier returns the standard-oriented
endpoint pair `(u', v')`, the chord `h'` on them, the witnessing orientation equalities, and the
residual data — pushing the (genuine, 2-valued) orientation selection into the planar-residue
layer where the side regions live. -/
structure ChordBranchResidualSupplier (α : Type u) [DecidableEq α] : Type (u + 1) where
  supply :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α), ThomassenLists hNT p q L cp cq →
      (∃ u v : M.Vertex, hNT.outerCycle.Chord u v) →
        Σ' (u' v' : M.Vertex) (h' : hNT.outerCycle.Chord u' v'),
          ChordBranchResidualData h' p q L cp cq

/-- **The `ChordBranchSupplier`, assembled from the uniform residual supplier.**

Given the uniform residual supplier (the discrete-Jordan content with confinements excluded), the
chord-branch supplier is dischargeable: under a true chord witness, the residual supplier delivers
a standard-oriented chord with its residue bundle, which `chordBranchResidue_of_residualData`
routes into a `ChordBranchResidue` — PRODUCING both confinements from
`bothConfinements_normalized` (not positing them).  The result is the `Σ' u v, ChordBranchResidue`
the supplier owes.

`CONDITIONAL` on `ChordBranchResidualSupplier`; the confinement production and branch-residue
assembly are UNCONDITIONAL. -/
noncomputable def chordBranchSupplier_of_residual
    (S : ChordBranchResidualSupplier α) :
    ProofsInTheBook.ZinanCh35Dichotomy.ChordBranchSupplier α where
  supply := by
    intro D _ _ M hNT p q L cp cq hTL hchord
    obtain ⟨u', v', h', R⟩ := S.supply hNT p q L cp cq hTL hchord
    exact ⟨u', v', chordBranchResidue_of_residualData R⟩

/-! ## Section 6.  Threading into the chord-recursive dichotomy (the payoff)

With the chord-branch supplier discharged from the residual, the full
`ChordRecursiveDichotomy` is one chordless supplier away. -/

/-- **The chord-recursive dichotomy from the residual chord-branch supplier and a chordless
supplier.**  Composes `chordBranchSupplier_of_residual` with
`ZinanCh35Dichotomy.chordRecursiveDichotomy_of_suppliers`. -/
noncomputable def chordRecursiveDichotomy_of_residual
    (S : ChordBranchResidualSupplier α)
    (Sl : ProofsInTheBook.ZinanCh35Dichotomy.ChordlessBranchSupplier α) :
    ChordRecursiveDichotomy α :=
  ProofsInTheBook.ZinanCh35Dichotomy.chordRecursiveDichotomy_of_suppliers
    (chordBranchSupplier_of_residual S) Sl

/-- **Five-colorability of a near-triangulation from the residual chord-branch supplier and a
chordless supplier.**  The chord half of Chapter 35 is now reduced to the confinement-free
residual bundle. -/
theorem fiveColor_of_residual
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M)
    (S : ChordBranchResidualSupplier (ULift.{u} (Fin 5)))
    (Sl : ProofsInTheBook.ZinanCh35Dichotomy.ChordlessBranchSupplier (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  ProofsInTheBook.ZinanCh35Dichotomy.fiveColor_of_branchSuppliers hNT
    (chordBranchSupplier_of_residual S) Sl

/-! ## Section 7.  Non-vacuity audit (§3.3 satisfiability)

The residual bundle and the assembled `ChordBranchResidue` are NOT hidden `False`:

* the confinement fields are **produced** (`bothConfinements_normalized`,
  `side₁ConfInput_of_star`), never posited — so no unsatisfiable confinement premise is smuggled
  in;
* the `Side₁/₂InputsNoConf` structures mirror the landed `ZinanCh35Cert.Side₁CertificateInputs` /
  `ZinanCh35Side2.Side₂CertificateInputs` field-for-field (minus `confinement`), each field an
  independently-inhabited concrete planar datum (the same fields the side reconstructions
  genuinely consume);
* the produced `ChordBranchResidue` feeds `ChordSplitFinal.chordRecursionData_of_branchResidue`
  (carrying two strictly-smaller side near-triangulations — the recursion fuel
  `ChordSideResidue.smaller`), so the chord branch genuinely recurses, it is not degenerate. -/

-- The residual genuinely PRODUCES (does not posit) the side-2 confinement: the field type that
-- `Side₂CertificateInputs.confinement` requires is exactly the output of
-- `bothConfinements_normalized`'s second component.
example (h : hNT.outerCycle.Chord u v) (hsep : (ND h).Separates)
    (htu : M.tail (ND h).dart = u) (hhv : M.head (ND h).dart = v) :
    ProofsInTheBook.ZinanCh35Side2.Side₂SchoenfliesConfinementInput (ND h) hsep :=
  (ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.bothConfinements_normalized h hsep htu hhv).2

-- The residual data's `side₁`/`side₂` carry NO confinement field (audit: the confinement burden
-- is off the residual — it is the genuine reduction `bothConfinements_normalized` buys).
example (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (I : Side₁InputsNoConf data hsep a₀ a₁ hne L) :
    ContiguousInterval data hsep a₀ a₁ hne := I.ci

end ProofsInTheBook.ZinanCh35ChordBranch

/-! ## Axiom audit (expect clean-3: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35ChordBranch.side₁ConfInput_of_star
#print axioms ProofsInTheBook.ZinanCh35ChordBranch.side₁Reconstruction_of_noConf
#print axioms ProofsInTheBook.ZinanCh35ChordBranch.side₂Reconstruction_of_noConf
#print axioms ProofsInTheBook.ZinanCh35ChordBranch.chordBranchResidue_of_residualData
#print axioms ProofsInTheBook.ZinanCh35ChordBranch.chordBranchSupplier_of_residual
#print axioms ProofsInTheBook.ZinanCh35ChordBranch.chordRecursiveDichotomy_of_residual
#print axioms ProofsInTheBook.ZinanCh35ChordBranch.fiveColor_of_residual
