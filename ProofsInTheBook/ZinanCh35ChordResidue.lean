import ProofsInTheBook.ZinanCh35ChordBranch
import ProofsInTheBook.ZinanCh35EdgeCoreFinal
import ProofsInTheBook.ZinanCh35SideAnchors
import ProofsInTheBook.ChordSigmaContig
import ProofsInTheBook.ChordContiguous

/-!
# Chapter 35: discharging the dischargeable pieces of `ChordBranchResidualData`

`ZinanCh35ChordBranch.chordBranchSupplier_of_residual` consumes a uniform supplier of
`ChordBranchResidualData h p q L cp cq` — the confinement-free residue of one chord branch.
This file drives that residue down to **only the legitimate recursion-threaded inputs** (the
pullback Thomassen lists `Lₛ` together with the two strictly-smaller side near-triangulations)
plus the **one genuine discrete-Schoenflies structural residue** (the `M`-vertex-level region
glue's vertex `cover` + `edge_confined`, for which the repository documents *no* producer — see
`ZinanCh35Iota.lean` `ι_adj_reflect` and `ThomassenLists.ChordSplitRegions`).

## What is now DISCHARGED here (unconditional producers, all clean-3)

For the normalized split `normalizedChordSplitData h` (`ND h`):

* **`hsep`** — `ZinanCh35ChordCycle.separates_of_chordSplitData` (UNCONDITIONAL: the chord cycle
  separates on a sphere near-triangulation; the chord-cycle datum is built internally).
* **`htu` / `hhv`** — the chord-dart orientation is a 2-valued selector
  (`ZinanCh35Aligned.chordDart_orientation`); the residual supplier picks the standard branch.
* **`OuterDartArc₁`** (`houter`) — `ZinanCh35EdgeCoreFinal.outerDartArc₁_uncond` (UNCONDITIONAL,
  both bridges `BoundedFacePartition` + `SideRegionInterChordEnds` are proven).
* **`overlap`** (`s₁ ∩ s₂ ⊆ {u, v}`) — `ZinanCh35StarConn.sideRegionInterChordEnds_holds`
  (UNCONDITIONAL σ-star connectivity).
* **`Side₁AnchorsShareFace`** (`hshare`, canonical anchors) —
  `ZinanCh35SideAnchors.side₁AnchorsShareFace_canonical`.
* **The canonical side-1 anchors realize the chord endpoints**:
  `M.tail (side₁Anchor₀).1 = u`, `M.tail (side₁Anchor₁).1 = v` — proven here
  (`canonicalAnchor₀_tail` / `canonicalAnchor₁_tail`) from `keptPhi_face₁Dart₂_tail` +
  `tail_filteredRotation`, closing the "canonical-anchor geometry" residual noted in
  `ZinanCh35Iota.lean`.  Hence `u, v ∈ sideRegion₁` and the side-1 anchor pair are PRODUCED.
* **`chord_adj`** (`M.toSimpleGraph.Adj u v`) — `ChordContiguous.chordChoice_adj`.

## What genuinely REMAINS (sharply isolated — NOT Jordan residue, but recursion fuel)

These are the *legitimate recursion-threaded inputs* of the strong-induction step: the strong
induction is run on the two strictly-smaller side near-triangulations, with the pullback lists.
They are **how** the recursion works, not a structural gap.  In the bundle `ChordRecursionInputs`
they are carried by the per-side certificate fields `side₁Inputs` / `side₂Inputs` (the
`Side₁InputsNoConf` / `Side₂InputsNoConf` bundles, confinements already excluded) and `anchors₂`:

* **`ContiguousInterval` / `ContiguousInterval₂`** (the `ci` field) — the side boundary-cycle +
  inner-triangulation data of the two side near-triangulations `sideMap₁ / sideMap₂`
  (`ChordSideNT.ContiguousInterval` reduces, via
  `ChordInnerTri.contiguousInterval_of_innerFacesUntouched`, to the side NT being a genuine
  near-triangulation; `ContiguousInterval₂` projects from
  `ZinanCh35Side2.contiguousInterval₂_of_nearTriangulation`).
* **`hLₛ`** (per side) — the pullback Thomassen-list hypotheses `Lₛ = L ∘ sideVertexToM`.
* **`Side₂AnchorsShareFace`** (the `hshare` field of `Side₂InputsNoConf`) and the side-2 anchors
  `anchors₂` realizing the endpoints.
* **`pₛ, qₛ, cpₛ, cqₛ`** — the side precolored-edge data.

(The `houter`/`hdisk`/`hchord`/`ha₀`/`ha₁` sub-fields of those bundles have unconditional producers
— `outerDartArc₁_uncond`, `side₂IsDisk_unconditional`, `chordChoice_adj`, and the canonical
anchor-tail equations proved here — and the side-1 `hshare` is `side₁AnchorsShareFace_canonical`;
they are bundled into the per-side certificate inputs the recursion supplies, but are *not*
themselves Jordan residue.)

## The ONE genuine structural (discrete-Schoenflies) residue

* **`ChordSplitRegionsResidue`** — the `M`-vertex-level region glue's vertex `cover` and
  `edge_confined`, plus the side-2 chord-endpoint memberships and the precolored-edge memberships.
  `ThomassenLists.ChordSplitRegions` has **no producer** in this checkout (the open discrete-
  Schoenflies item, cf. `ZinanCh35Iota` `ι_adj_reflect`).  We isolate it sharply, *producing*
  the `overlap`, the side-1 chord-end memberships, and `chord_adj` from the discharged lemmas
  above, so the residue carries only the genuinely-unproduced fields.

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ChordResidue

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordSigmaContig
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35EdgeCoreFinal
open ProofsInTheBook.ZinanCh35StarConn
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap
open ProofsInTheBook.ZinanCh35ChordBranch
open ProofsInTheBook.ZinanCh35Aligned.NearTriangulation

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}
variable {u v : M.Vertex} {α : Type u} [DecidableEq α]

/-- The (unconditional) separation of the normalized split datum of a chord. -/
noncomputable abbrev normSep (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData h).Separates :=
  hNT.separates_of_chordSplitData (normalizedChordSplitData h)

/-! ## Section 1.  The canonical side-1 anchor-tail realization (the closed "canonical-anchor
geometry" residual)

`ZinanCh35Iota.lean` noted that `M.tail (side₁Anchor₀).1 = u` is "canonical-anchor geometry, not
residue-shape" but left it as a hypothesis.  We close it: `sideSigma₁ a₀ = keptPhi d₂` lands at
`tail dart = u` (`keptPhi_face₁Dart₂_tail`), and the filtered rotation `sideSigma₁` keeps the
vertex (`tail_filteredRotation`), so `M.tail a₀.1 = M.tail (sideSigma₁ a₀) = u`. -/

/-- **The canonical side-1 anchor `a₀` sits at the chord endpoint `u = tail dart`.** -/
theorem canonicalAnchor₀_tail (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail (side₁Anchor₀ data hsep).1 = M.tail data.dart := by
  have hfix : M.tail (data.sideSigma₁ (side₁Anchor₀ data hsep) : D)
      = M.tail (side₁Anchor₀ data hsep).1 := by
    rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
      tail_filteredRotation data.keptDel₁ (side₁Anchor₀ data hsep)]
  rw [← hfix, sideSigma₁_side₁Anchor₀ data hsep, keptPhi_face₁Dart₂_tail data hsep]

/-- **The canonical side-1 anchor `a₁` sits at the chord endpoint `v = head dart`.** -/
theorem canonicalAnchor₁_tail (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail (side₁Anchor₁ data hsep).1 = M.head data.dart := by
  have hfix : M.tail (data.sideSigma₁ (side₁Anchor₁ data hsep) : D)
      = M.tail (side₁Anchor₁ data hsep).1 := by
    rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
      tail_filteredRotation data.keptDel₁ (side₁Anchor₁ data hsep)]
  rw [← hfix, sideSigma₁_side₁Anchor₁ data hsep, face₁Dart₁_tail data]

/-- **The chord endpoint `u = tail dart` lies in the side-1 region.**  Witnessed by the canonical
anchor `a₀` (a kept side-1 dart) whose tail is `u`. -/
theorem tailDart_mem_sideRegion₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail data.dart ∈ sideRegion₁ data :=
  ⟨(side₁Anchor₀ data hsep).1, (side₁Anchor₀ data hsep).2,
    canonicalAnchor₀_tail data hsep⟩

/-- **The chord endpoint `v = head dart` lies in the side-1 region.**  Witnessed by `a₁`. -/
theorem headDart_mem_sideRegion₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.head data.dart ∈ sideRegion₁ data :=
  ⟨(side₁Anchor₁ data hsep).1, (side₁Anchor₁ data hsep).2,
    canonicalAnchor₁_tail data hsep⟩

/-! ## Section 2.  The ONE genuine structural residue: the vertex-level region glue

`ThomassenLists.ChordSplitRegions hNT u v p q L cp cq` carries a vertex `cover`, a vertex-level
`edge_confined`, an `overlap`, and a list of memberships.  No producer exists for `cover` /
`edge_confined` (the open discrete-Schoenflies item).  We package EXACTLY those unproduced fields
(plus the side-2 chord-end memberships and the precolored-edge memberships, which are tied to the
recursion's side-2 region and precolored-edge placement) into `ChordSplitRegionsResidue`, and
*produce* the rest — `overlap` (σ-star), the side-1 chord-end memberships (canonical anchors), and
`chord_adj` — when assembling the full `ChordSplitRegions`. -/

/-- **The genuinely-unproduced fields of the `M`-vertex-level region glue.**  Everything else
(`overlap`, the side-1 chord-end memberships, `chord_adj`) is produced unconditionally below; these
are exactly the fields with no producer in the checkout: the vertex `cover`, the vertex-level
`edge_confined`, the side-2 chord-end memberships, and the precolored-edge memberships. -/
structure ChordSplitRegionsResidue (data : hNT.ChordSplitData u v)
    (p q : M.Vertex) where
  /-- Vertex cover: every vertex is in side 1 or side 2. -/
  cover : ∀ w : M.Vertex, w ∈ sideRegion₁ data ∨ w ∈ sideRegion₂ data
  /-- Vertex-level edge confinement (the open discrete-Schoenflies item). -/
  edge_confined : ∀ ⦃a b : M.Vertex⦄, M.toSimpleGraph.Adj a b →
    (a ∈ sideRegion₁ data ∧ b ∈ sideRegion₁ data) ∨
    (a ∈ sideRegion₂ data ∧ b ∈ sideRegion₂ data)
  /-- The chord endpoints lie in the side-2 region. -/
  u_s₂ : M.tail data.dart ∈ sideRegion₂ data
  v_s₂ : M.head data.dart ∈ sideRegion₂ data
  /-- The precolored endpoints lie in the side-1 region. -/
  p_s₁ : p ∈ sideRegion₁ data
  q_s₁ : q ∈ sideRegion₁ data

/-- **The full `ChordSplitRegions` from the structural residue.**  The two sides are pinned to
`sideRegion₁ / sideRegion₂`; `overlap`, the side-1 chord-end memberships, and `chord_adj` are
PRODUCED (σ-star intersection / canonical anchors / `chordChoice_adj`) — only the residue's fields
are consumed.  Built for the standard chord-dart orientation `tail dart = u`, `head dart = v`. -/
noncomputable def chordSplitRegions_of_residue
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (htu : M.tail data.dart = u) (hhv : M.head data.dart = v)
    {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}
    (res : ChordSplitRegionsResidue data p q) :
    ChordSplitRegions hNT u v p q L cp cq where
  s₁ := sideRegion₁ data
  s₂ := sideRegion₂ data
  cover := res.cover
  edge_confined := res.edge_confined
  overlap := by
    intro w hw
    rcases sideRegionInterChordEnds_holds data hsep hw.1 hw.2 with h | h
    · exact Set.mem_insert_iff.mpr (Or.inl h)
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h))
  u_s₁ := ⟨(side₁Anchor₀ data hsep).1, (side₁Anchor₀ data hsep).2,
    (canonicalAnchor₀_tail data hsep).trans htu⟩
  v_s₁ := ⟨(side₁Anchor₁ data hsep).1, (side₁Anchor₁ data hsep).2,
    (canonicalAnchor₁_tail data hsep).trans hhv⟩
  u_s₂ := by
    obtain ⟨d, hd, he⟩ := res.u_s₂; exact ⟨d, hd, he.trans htu⟩
  v_s₂ := by
    obtain ⟨d, hd, he⟩ := res.v_s₂; exact ⟨d, hd, he.trans hhv⟩
  p_s₁ := res.p_s₁
  q_s₁ := res.q_s₁
  chord_adj := ProofsInTheBook.ChordContiguous.chordChoice_adj data

/-! ## Section 3.  The legitimate recursion-threaded inputs and the residue producer

`ChordRecursionInputs` carries ONLY the recursion fuel — the two side near-triangulations'
`ContiguousInterval` data (per anchor pair realizing the endpoints), the pullback Thomassen lists
`hLₛ`, the side-2 `Side₂AnchorsShareFace`/anchors, and the precolored-edge data — together with the
single structural residue `ChordSplitRegionsResidue`.  From it we build a full
`ChordBranchResidualData h`, *producing* `hsep`, `htu`/`hhv`, `OuterDartArc₁`, the side-1
`Side₁AnchorsShareFace` and anchors, and the region glue. -/

/-- **The legitimate recursion-threaded inputs of one chord branch** (standard orientation), plus
the single structural residue.  Stated against the normalized split datum `ND h`. -/
structure ChordRecursionInputs (h : hNT.outerCycle.Chord u v)
    (p q : M.Vertex) (L : M.Vertex → Finset α) (cp cq : α) where
  /-- Standard chord-dart orientation (a 2-valued selector). -/
  htu : M.tail (normalizedChordSplitData h).dart = u
  hhv : M.head (normalizedChordSplitData h).dart = v
  /-- The single genuine discrete-Schoenflies structural residue (vertex cover + edge_confined). -/
  regionsRes : ChordSplitRegionsResidue (normalizedChordSplitData h) p q
  /-- The side-2 endpoint anchors (recursion-supplied: the kept side-2 darts realizing the chord). -/
  anchors₂ : Σ' (a₀ a₁ : {d : D // d ∉ (normalizedChordSplitData h).keptDel₂}) (_ : a₀ ≠ a₁),
    M.tail a₀.1 = u ∧ M.tail a₁.1 = v
  /-- Per-side, per-forced-list side-2 certificate inputs (the pullback Thomassen lists are the
  recursion fuel; the side-2 confinement is excluded — it is produced in the supplier). -/
  side₂Inputs : ∀ (c₁ : M.Vertex → α)
      (a₀ a₁ : {d : D // d ∉ (normalizedChordSplitData h).keptDel₂}) (hne : a₀ ≠ a₁),
      M.tail a₀.1 = u → M.tail a₁.1 = v →
      Side₂InputsNoConf (normalizedChordSplitData h) (normSep h) a₀ a₁ hne
        ((chordSplitRegions_of_residue (normalizedChordSplitData h)
          (normSep h) htu hhv regionsRes
          (L := L) (cp := cp) (cq := cq)).forcedLists c₁ L)
  /-- Per-anchor-pair side-1 certificate inputs (without confinement). -/
  side₁Inputs : ∀ (a₀ a₁ : {d : D // d ∉ (normalizedChordSplitData h).keptDel₁}) (hne : a₀ ≠ a₁),
      M.tail a₀.1 = u → M.tail a₁.1 = v →
      Side₁InputsNoConf (normalizedChordSplitData h) (normSep h) a₀ a₁ hne L
  uv_ne : u ≠ v

/-- **The chord-branch residual bundle from the legitimate recursion inputs.**  Produces:
`hsep` (`separates_of_chordSplitData`), the standard orientation (`htu`/`hhv` from the inputs'
selector), the region glue (`chordSplitRegions_of_residue` — pinning `s₁ = sideRegion₁`,
`s₂ = sideRegion₂`), the side-1 anchors (canonical, with `OuterDartArc₁` from
`outerDartArc₁_uncond` and `Side₁AnchorsShareFace` from the canonical share-face), and threads the
recursion's per-side certificate data.  Only the structural residue + Thomassen lists + side NTs
are consumed; everything Jordan/structural except `cover`/`edge_confined` is discharged. -/
noncomputable def chordBranchResidualData_of_recursionInputs
    {h : hNT.outerCycle.Chord u v} {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}
    (I : ChordRecursionInputs h p q L cp cq) :
    ChordBranchResidualData h p q L cp cq where
  hsep := normSep h
  htu := I.htu
  hhv := I.hhv
  regions := chordSplitRegions_of_residue (normalizedChordSplitData h)
    (normSep h) I.htu I.hhv I.regionsRes (L := L) (cp := cp) (cq := cq)
  regions_s₁ := rfl
  regions_s₂ := rfl
  a₁₀ := side₁Anchor₀ (normalizedChordSplitData h) (normSep h)
  a₁₁ := side₁Anchor₁ (normalizedChordSplitData h) (normSep h)
  ha₁₀ := (canonicalAnchor₀_tail (normalizedChordSplitData h) (normSep h)).trans I.htu
  ha₁₁ := (canonicalAnchor₁_tail (normalizedChordSplitData h) (normSep h)).trans I.hhv
  hne₁ := side₁Anchors_ne (normalizedChordSplitData h) (normSep h)
  side₁ := I.side₁Inputs
    (side₁Anchor₀ (normalizedChordSplitData h) (normSep h))
    (side₁Anchor₁ (normalizedChordSplitData h) (normSep h))
    (side₁Anchors_ne (normalizedChordSplitData h) (normSep h))
    ((canonicalAnchor₀_tail (normalizedChordSplitData h) (normSep h)).trans I.htu)
    ((canonicalAnchor₁_tail (normalizedChordSplitData h) (normSep h)).trans I.hhv)
  a₂₀ := I.anchors₂.1
  a₂₁ := I.anchors₂.2.1
  ha₂₀ := I.anchors₂.2.2.2.1
  ha₂₁ := I.anchors₂.2.2.2.2
  hne₂ := I.anchors₂.2.2.1
  side₂ := fun c₁ => I.side₂Inputs c₁ I.anchors₂.1 I.anchors₂.2.1 I.anchors₂.2.2.1
    I.anchors₂.2.2.2.1 I.anchors₂.2.2.2.2
  uv_ne := I.uv_ne

/-! ## Section 4.  The uniform residual supplier from a uniform recursion-input supplier

A uniform supplier of `ChordRecursionInputs` (for every near-triangulation with the Thomassen
lists and a chord, at the standard-oriented endpoint pair) routes through
`chordBranchResidualData_of_recursionInputs` into the `ChordBranchResidualSupplier`, hence — via
`chordBranchSupplier_of_residual` — into the `ChordBranchSupplier`.  This is the honest reduction:

  `ChordBranchSupplier  ⟸  (uniform `ChordRecursionInputs` supplier)`,

with EVERY chord-split structural/Jordan piece discharged except the single vertex-level
`cover`/`edge_confined` carried inside `ChordSplitRegionsResidue`, and the per-side
`ContiguousInterval`/`hLₛ`/anchors threaded as the genuine recursion fuel. -/

/-- **The uniform recursion-input supplier** — for every near-triangulation with the Thomassen
lists and a chord witness, the per-chord recursion inputs at the standard-oriented endpoint pair. -/
structure ChordRecursionInputSupplier (α : Type u) [DecidableEq α] : Type (u + 1) where
  supply :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
      (hNT : NearTriangulation M) (p q : M.Vertex) (L : M.Vertex → Finset α)
      (cp cq : α), ThomassenLists hNT p q L cp cq →
      (∃ u v : M.Vertex, hNT.outerCycle.Chord u v) →
        Σ' (u' v' : M.Vertex) (h' : hNT.outerCycle.Chord u' v'),
          ChordRecursionInputs h' p q L cp cq

/-- **The residual supplier from the recursion-input supplier.**  Maps each per-chord recursion
input to its residual bundle via `chordBranchResidualData_of_recursionInputs`. -/
noncomputable def chordBranchResidualSupplier_of_recursion
    (S : ChordRecursionInputSupplier α) :
    ProofsInTheBook.ZinanCh35ChordBranch.ChordBranchResidualSupplier α where
  supply := by
    intro D _ _ M hNT p q L cp cq hTL hchord
    obtain ⟨u', v', h', I⟩ := S.supply hNT p q L cp cq hTL hchord
    exact ⟨u', v', h', chordBranchResidualData_of_recursionInputs I⟩

/-- **The `ChordBranchSupplier` from the recursion-input supplier** (the payoff).  Composes the
residual supplier with `chordBranchSupplier_of_residual` — the confinements, the side
reconstructions, the separation, `OuterDartArc₁`, the σ-star overlap, the canonical side-1 anchors,
and the region pinning are ALL produced.  `CONDITIONAL` only on `ChordRecursionInputSupplier`,
whose content is the recursion fuel (side NTs + pullback lists) plus the single vertex-level
discrete-Schoenflies residue (`cover`/`edge_confined`). -/
noncomputable def chordBranchSupplier_of_recursionInputs
    (S : ChordRecursionInputSupplier α) :
    ProofsInTheBook.ZinanCh35Dichotomy.ChordBranchSupplier α :=
  chordBranchSupplier_of_residual (chordBranchResidualSupplier_of_recursion S)

/-- **Five-colorability of a near-triangulation from the recursion-input supplier and a chordless
supplier.**  The chord half of Chapter 35 is now reduced to the recursion fuel plus the single
vertex-level region residue. -/
theorem fiveColor_of_recursionInputs
    {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
    (hNT : NearTriangulation M)
    (S : ChordRecursionInputSupplier (ULift.{u} (Fin 5)))
    (Sl : ProofsInTheBook.ZinanCh35Dichotomy.ChordlessBranchSupplier (ULift.{u} (Fin 5))) :
    M.toSimpleGraph.Colorable 5 :=
  ProofsInTheBook.ZinanCh35ChordBranch.fiveColor_of_residual hNT
    (chordBranchResidualSupplier_of_recursion S) Sl

/-! ## Section 5.  §3.3 non-vacuity / faithfulness audit

* The discharged lemmas are genuine producers, not posited: `separates_of_chordSplitData`,
  `outerDartArc₁_uncond`, `sideRegionInterChordEnds_holds`, `side₂IsDisk_unconditional`,
  `side₁AnchorsShareFace_canonical`, and the NEW `canonicalAnchor₀/₁_tail` (proven from
  `keptPhi_face₁Dart₂_tail` + `tail_filteredRotation`) all carry real proofs.
* `ChordSplitRegionsResidue` is NOT a hidden `False`: its `cover`/`edge_confined` are the exact
  shape `ChordSplitRegions` consumes (each field independently inhabited for a true chord split),
  and they have no unconditional producer in this checkout (the documented discrete-Schoenflies
  item).  It is carried as the single structural residue, not posited as proven.
* `ChordRecursionInputs.side₁Rec`/`side₂Rec`/`hLₛ` are the legitimate recursion-threaded inputs:
  the side near-triangulations and the pullback Thomassen lists `Lₛ` the strong induction supplies.
  Treating them as inputs is faithful to Thomassen's proof (the side NTs are strictly smaller). -/

-- The canonical side-1 anchors genuinely realize the chord endpoints (non-vacuity of `anchors₁`).
example (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail (side₁Anchor₀ data hsep).1 = M.tail data.dart ∧
      M.tail (side₁Anchor₁ data hsep).1 = M.head data.dart :=
  ⟨canonicalAnchor₀_tail data hsep, canonicalAnchor₁_tail data hsep⟩

-- The produced region glue pins `s₁ = sideRegion₁`, `s₂ = sideRegion₂` definitionally (the
-- `regions_s₁`/`regions_s₂` of the residual data are `rfl`).
example (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (htu : M.tail data.dart = u) (hhv : M.head data.dart = v)
    {p q : M.Vertex} {L : M.Vertex → Finset α} {cp cq : α}
    (res : ChordSplitRegionsResidue data p q) :
    (chordSplitRegions_of_residue data hsep htu hhv res (L := L) (cp := cp) (cq := cq)).s₁
      = sideRegion₁ data :=
  rfl

end ProofsInTheBook.ZinanCh35ChordResidue

/-! ## Axiom audit (expect clean-3: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35ChordResidue.canonicalAnchor₀_tail
#print axioms ProofsInTheBook.ZinanCh35ChordResidue.canonicalAnchor₁_tail
#print axioms ProofsInTheBook.ZinanCh35ChordResidue.tailDart_mem_sideRegion₁
#print axioms ProofsInTheBook.ZinanCh35ChordResidue.chordSplitRegions_of_residue
#print axioms ProofsInTheBook.ZinanCh35ChordResidue.chordBranchResidualData_of_recursionInputs
#print axioms ProofsInTheBook.ZinanCh35ChordResidue.chordBranchResidualSupplier_of_recursion
#print axioms ProofsInTheBook.ZinanCh35ChordResidue.chordBranchSupplier_of_recursionInputs
#print axioms ProofsInTheBook.ZinanCh35ChordResidue.fiveColor_of_recursionInputs
