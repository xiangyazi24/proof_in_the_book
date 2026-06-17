import ProofsInTheBook.ZinanCh35Iota
import ProofsInTheBook.ZinanCh35Gates

/-!
# The Chapter 35 side-1 region-confinement supplier (`Side₁Confinement`)

`ZinanCh35Iota.lean` reduced the side-1 reconstruction residue `ChordSideResidue` to a small set
of named planar inputs, of which the two genuinely-open discrete-Schoenflies items are

* `hreflect` — region **edge**-confinement: an ambient `M`-edge between two side-1-region
  vertices is realised by a side edge
  (`ι_adj_reflect : M.Adj (ι x) (ι y) → sideMap₁.Adj x y`); and
* `homit` — the **vertex**-omission witness
  (`∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ …)`), the strict-decrease fuel.

This file bundles those two into the named `Side₁Confinement` structure (the design's
`RegionConfinement`-style object), and supplies the genuinely-landed reductions that sharpen
their statements as far as the *proved* infrastructure allows.  It then feeds the bundle into
`ZinanCh35Iota.chordSideResidue₁_partial`.

## What is PROVED here (landed, axiom-clean)

* **`homit_iff_exists_notMem_sideRegion₁`** — `homit` is **equivalent** to the sharp geometric
  statement `∃ w : M.Vertex, w ∉ sideRegion₁ data` (the opposite-arc internal vertex is not the
  tail of any kept side-1 dart).  This is `ChordReconClose.sideVertexToM₁_range`
  (`Set.range ι = sideRegion₁`) transported through `Set.mem_range` / the range rewrite.  So the
  opaque `homit` residue is replaced by the *concrete* region-membership residue.

* **`side₁Confinement_of_inputs`** — the bundling constructor: from explicit `hreflect`/`homit`
  it produces `Side₁Confinement`.  (This is the trivially-true packaging; the genuine content is
  in its *hypotheses*, which are the named planar residues — NOT a vacuous conditional, since
  both hypotheses are inhabited statements about the concrete `M`/`sideMap₁` data.)

* **`side₁Confinement_of_notMem_sideRegion₁`** — bundles from `hreflect` plus the *sharp*
  region-omission residue `∃ w, w ∉ sideRegion₁ data`, discharging the `homit` field via the
  proved equivalence.

* **`chordSideResidue₁_of_confinement`** — feeds a `Side₁Confinement` (plus the upstream
  `ci`/`hshare`/`hchord`/`hLₛ` that are *not* confinement content) into
  `ZinanCh35Iota.chordSideResidue₁_partial`, producing the full `ChordSideResidue`.

## What is NOT closed here, and WHY (the honest block)

The design (`ch35-outer-trace-supplier.md` §3) proposed deriving `hreflect`/`homit` from
`ZinanCh35Gates.separates_closed` / `jordan_simple_cycle2_unconditional`.  **That derivation is
not available from the landed material**, and I do not write it as a vacuous theorem.

The reason is a genuine altitude mismatch, verified against the source:

* `separates_closed` / `SphereChordSeparation` / `SidesDisjoint` / `Separates` are all
  **face**-level dual-non-reachability statements:
  `Separates data := data.face₂ ∉ data.side₁`, and
  `SphereChordSeparation := ¬ Relation.ReflTransGen (ChordSplitAdj) face₁ face₂`
  (`PlanarMapChordSplit.lean:266`, `PlanarMapSeparation.lean:211`).  They control which **faces**
  are reachable across the chord.

* `hreflect`/`homit` are **vertex/edge**-level confinement statements on
  `sideRegion₁ data = {w | ∃ d ∉ keptDel₁, M.tail d = w}` (`ChordReconClose.lean:97`), where
  `keptDel₁` is the complement of `keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`
  (`PlanarMapChordSplit.lean:412`).  Proving that an *internal* arc-2 vertex `w` satisfies
  `w ∉ sideRegion₁` requires that **none** of `w`'s incident darts has its face in `side₁` —
  i.e. the vertex-star of `w` is confined to side 2 ∪ outer.  This is the discrete-Schoenflies
  **vertex-star confinement**, strictly stronger than the face-dual separation `face₂ ∉ side₁`
  (a chord endpoint's star meets *both* sides; the separation predicate says nothing about an
  internal arc-2 vertex's star).  Likewise `hreflect` needs **edge** confinement.

  There is no landed lemma bridging face-dual-separation to vertex-star/edge confinement: the
  entire chain (`ChordSplitFinal.lean` §3.3, `ZinanCh35Iota.lean` header, `PlanarMapChordSplit`
  module docstring) documents this region confinement as the open item with **no unconditional
  producer**.  So the two residual hypotheses below are the honest, minimal, *satisfiable*
  blocking goals — reported exactly, not papered over.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Confinement

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ZinanCh35Iota
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]

/-! ## Section 1.  The `Side₁Confinement` bundle

The region-confinement datum: the two genuinely-open discrete-Schoenflies fields, bundled.  The
field types match the *exact* consumption sites in `ZinanCh35Iota`
(`sideVertexToM₁_adj_reflect_canonical` for `hreflect`, `side₁_smaller_canonical` for `homit`). -/

/-- **The side-1 region-confinement bundle.**  Carries the two genuinely-open discrete-Jordan
confinement facts for the canonical (or any) side-1 anchors: the adjacency **reflection**
`hreflect` (region edge-confinement) and the vertex **omission** witness `homit` (the
strict-decrease fuel).  Both fields are stated verbatim in the shape `ZinanCh35Iota` consumes. -/
structure Side₁Confinement (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) : Prop where
  /-- **Region edge-confinement.**  An ambient `M`-edge between two side-1-region vertices is
  realised by a side edge. -/
  hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
    M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
        (sideVertexToM₁ data hsep a₀ a₁ hne y) →
      (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y
  /-- **Vertex omission.**  Some `M`-vertex (the opposite-arc internal vertex) is not in the
  image of the side-1 vertex correspondence. -/
  homit : ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne)

/-! ## Section 2.  The `homit` reduction to the sharp region-omission residue

`homit` is opaque (it quantifies over the side-vertex quotient via `Set.range`).  The landed
`ChordReconClose.sideVertexToM₁_range` (`Set.range ι = sideRegion₁ data`) makes it **equivalent**
to the concrete geometric statement `∃ w, w ∉ sideRegion₁ data`.  This is the genuine reduction:
the strict-decrease fuel is exactly "the opposite arc has an internal vertex side 1 omits", with
`sideRegion₁ data = {w | ∃ d ∉ keptDel₁, M.tail d = w}` the tails of kept side-1 darts. -/

/-- **`homit` ⟺ a vertex outside the side-1 region.**  Via `sideVertexToM₁_range`
(`Set.range ι = sideRegion₁`), the abstract omitted-vertex witness is equivalent to the concrete
region-omission residue `∃ w : M.Vertex, w ∉ sideRegion₁ data`. -/
theorem homit_iff_exists_notMem_sideRegion₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    (∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne))
      ↔ (∃ w : M.Vertex, w ∉ sideRegion₁ data) := by
  rw [sideVertexToM₁_range data hsep a₀ a₁ hne]

/-! ## Section 3.  The bundling constructors -/

/-- **`Side₁Confinement` from explicit confinement inputs.**  The packaging constructor.  Its two
hypotheses are exactly the named planar residues; this is NOT a vacuous conditional — both are
inhabited statements about the concrete `M`/`sideMap₁` data (`hreflect` is satisfiable because
`sideMap₁`'s edges are a subgraph of `M` and the region is a genuine subregion; `homit` because
the opposite arc carries an internal vertex side 1 drops). -/
theorem side₁Confinement_of_inputs (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y)
    (homit : ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₁ data hsep a₀ a₁ hne)) :
    Side₁Confinement data hsep a₀ a₁ hne :=
  { hreflect := hreflect, homit := homit }

/-- **`Side₁Confinement` from `hreflect` plus the SHARP region-omission residue.**  The `homit`
field is discharged from `∃ w, w ∉ sideRegion₁ data` via the proved equivalence
`homit_iff_exists_notMem_sideRegion₁` — so the caller need only supply the concrete geometric
omission, not the opaque `Set.range` form. -/
theorem side₁Confinement_of_notMem_sideRegion₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y)
    (homit_region : ∃ w : M.Vertex, w ∉ sideRegion₁ data) :
    Side₁Confinement data hsep a₀ a₁ hne :=
  { hreflect := hreflect
    homit := (homit_iff_exists_notMem_sideRegion₁ data hsep a₀ a₁ hne).2 homit_region }

/-! ## Section 4.  Feeding the confinement bundle into the residue assembler

`ZinanCh35Iota.chordSideResidue₁_partial` consumes `hreflect`/`homit` as its two confinement
inputs (alongside the non-confinement `ci`/`hshare`/`hchord`/`hLₛ`).  We project them out of a
`Side₁Confinement` and assemble the full `ChordSideResidue`. -/

/-- **The side-1 residue from a confinement bundle.**  Reads `hreflect`/`homit` from the
`Side₁Confinement` and supplies the remaining non-confinement inputs (`ci`/`hshare`/`hchord`/the
side lists `hLₛ`) — exactly `ZinanCh35Iota.chordSideResidue₁_partial`, with the two genuine
discrete-Schoenflies fields packaged into the single confinement object. -/
def chordSideResidue₁_of_confinement (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (ci : ContiguousInterval data hsep a₀ a₁ hne)
    (hshare : ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace data hsep a₀ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (pₛ qₛ : (data.sideMap₁ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₁ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (conf : Side₁Confinement data hsep a₀ a₁ hne) :
    ChordSideResidue data hsep a₀ a₁ hne L :=
  chordSideResidue₁_partial data hsep a₀ a₁ hne L ci hshare hchord
    conf.hreflect pₛ qₛ cpₛ cqₛ hLₛ conf.homit

/-! ## Section 5.  The Jordan-conditioned supplier (the design's `side₁Confinement_of_jordan`)

The design asked for `side₁Confinement_of_jordan` deriving `Side₁Confinement` from
`jordan_simple_cycle2_unconditional` + `separates_closed`.  As documented in the module header,
that derivation is **not** available from the landed material: those are face-dual separation
facts, while `Side₁Confinement` is vertex/edge-star confinement.  We therefore record the
supplier in the only honest form — taking the two genuine confinement facts as the explicit,
sharp, satisfiable residual hypotheses (the `homit` one already reduced to the concrete
`sideRegion₁` form) — and we additionally THREAD the closed Jordan separation so the statement
sits at the design's intended call site even though the separation does not by itself discharge
the residues.

The two residual hypotheses below are the exact open discrete-Schoenflies goals:

* `hreflect` : the region edge-confinement; and
* `homit_region : ∃ w, w ∉ sideRegion₁ data` : the opposite-arc internal vertex omission.

Both are non-vacuous and concrete. -/

/-- **The Jordan-conditioned side-1 confinement supplier.**  Given the closed Jordan separation
(`hjordan` / `hclosed`, threaded as the design's call-site context) together with the two sharp
discrete-Schoenflies residues — region edge-confinement `hreflect` and the concrete opposite-arc
vertex omission `homit_region : ∃ w, w ∉ sideRegion₁ data` — produces `Side₁Confinement`.

The `homit` field is discharged from `homit_region` via the proved equivalence
`homit_iff_exists_notMem_sideRegion₁`.  The separation inputs are recorded (the design's call
site supplies them); they do not by themselves close the residues — see the module header for the
face-vs-vertex altitude mismatch that keeps `hreflect`/`homit_region` as honest inputs. -/
theorem side₁Confinement_of_jordan (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord)))
    (hreflect : ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₁ data hsep a₀ a₁ hne x)
          (sideVertexToM₁ data hsep a₀ a₁ hne y) →
        (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y)
    (homit_region : ∃ w : M.Vertex, w ∉ sideRegion₁ data) :
    Side₁Confinement data hsep a₀ a₁ hne :=
  -- The threaded separation (recorded; `separates_closed` is consumable here but does not by
  -- itself supply the vertex/edge confinement — see the header).
  let _hsep_closed : data.Separates :=
    hNT.separates_closed data C hsub i₀ hleft hright
  side₁Confinement_of_notMem_sideRegion₁ data hsep a₀ a₁ hne hreflect homit_region

end ProofsInTheBook.ZinanCh35Confinement

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35Confinement.homit_iff_exists_notMem_sideRegion₁
#print axioms ProofsInTheBook.ZinanCh35Confinement.side₁Confinement_of_inputs
#print axioms ProofsInTheBook.ZinanCh35Confinement.side₁Confinement_of_notMem_sideRegion₁
#print axioms ProofsInTheBook.ZinanCh35Confinement.chordSideResidue₁_of_confinement
#print axioms ProofsInTheBook.ZinanCh35Confinement.side₁Confinement_of_jordan
