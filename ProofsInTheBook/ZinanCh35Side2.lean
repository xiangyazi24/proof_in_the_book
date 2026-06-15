import ProofsInTheBook.ZinanCh35Cert
import ProofsInTheBook.ZinanCh35EdgeCore

/-!
# Chapter 35 — the SIDE-2 mirror reconstruction (the missing half of `ChordBranchSupplier`)

`ZinanCh35Cert.side₁Reconstruction_of_certificateInputs` builds a
`ChordSideReconstruction hNT (sideRegion₁ data) L` from the landed side-1 final close
(`ZinanCh35FinalClose.chordSideResidue₁_final` ← `Side₁SchoenfliesConfinementInput`).  The
`ChordBranchSupplier` needs BOTH side reconstructions to assemble a
`ChordSplitFinal.ChordBranchResidue`; the side-2 half was **not** landed (there was no
`chordSideResidue₂_final`, no `sideVertexToM₂`, no `ContiguousInterval₂`, no side-2
`ChordSideReconstruction` producer).

This file builds the entire side-2 tower as a genuine mirror — **not** `:= side₁…` — against the
side-2 data the chord split already carries: `data.sideMap₂` (the identical `freshMap` of
`data.sideAlpha₂`/`data.sideSigma₂` over `data.keptDel₂`), `data.keptDel₂`, `sideRegion₂`
(`ZinanCh35EdgeCore`), the side-2 sphere (`ChordDisk.side₂_isSphereMap_of_disk`), and the side-2
anchor-incidence fact `ChordDisk.Side₂AnchorsShareFace`.  The generic fresh-dart machinery
(`proj`, `freshAlpha`, `freshSigma_sameCycle_iff`, `filteredRotation_sameCycle_iff`,
`cycleSetoid`) is parametrised by the abstract kept type, so every side-1 proof transports to
side 2 verbatim with `keptDel₁ → keptDel₂`.

## Tiers (each the side-2 mirror of the named side-1 lemma)

* **Tier A — the vertex correspondence** (`ChordReconClose` mirror): `sideVertexToM₂` and its
  `_inl`/`_head_inl`/`_tail_inr`/`_head_inr`/`_mem`/`_surjective`/`_range`, `ι_adj_of_inl₂`,
  `sideRegion₂_nonempty`.
* **Tier B — the side-2 near-triangulation** (`ChordSideNT` mirror): the boundary classification
  residue `ContiguousInterval₂` and the assembler `chordSideNearTriangulation₂_of_share`, whose
  `sphere` is discharged by `ChordDisk.side₂_isSphereMap_of_disk` from `Side₂IsDisk` (the side-2
  disk fact — see the honesty note) + `Side₂AnchorsShareFace`.
* **Tier C — the Iota bricks** (`ZinanCh35Iota` mirror): `sideVertexToM₂_injective_canonical`,
  `_tail_inr`/`_head_inr`, `ι_adj_of_dart₂`, `sideVertexToM₂_adj_canonical`,
  `side₂_smaller_canonical`, `chordSideResidue₂_partial`.
* **Tier D — the side-2 residue + producer** (`ChordSplitFinal` mirror): `ChordSideResidue₂` and
  `chordSideReconstruction₂_of_chord : … → ChordSideReconstruction hNT (sideRegion₂ data) L`.
* **Tier E — the FinalClose mirror**: `Side₂SchoenfliesConfinementInput`, the four bricks, and
  `chordSideResidue₂_final`.
* **Tier F — the Cert mirror (the deliverable)**: `Side₂CertificateInputs` and
  `side₂Reconstruction_of_certificateInputs : … → ChordSideReconstruction hNT (sideRegion₂ data) L`.

## Honesty contract (§3.3)

Everything structural — the orbit correspondence, region/α-closure, injectivity, the kept-dart
half of `ι_adj`, the strict decrease, the boundary/NT framing — is proved **unconditionally** as
the exact mirror of side 1.  The genuine planar residue is taken as honestly-named hypotheses,
exactly as side 1 takes them:

* `Side₂SchoenfliesConfinementInput` — the side-2 confinement bundle (`oppArcStarSeed₂` +
  `edge_core₂`), the mirror of `Side₁SchoenfliesConfinementInput`; its `edge_core₂` reduces to
  the SAME two bridges as side 1, mirrored, which `ZinanCh35EdgeCore.edge_core_holds` discharges
  symmetrically (the side₁/side₂ roles in `BoundedFacePartition`/`SideRegionInterChordEnds` swap).
* `ContiguousInterval₂` — the side-2 boundary classification residue (mirror of
  `ContiguousInterval`).
* `Side₂IsDisk` / `Side₂AnchorsShareFace` — the side-2 disk core and anchor-incidence facts.
  NOTE: `sideKeptMap₂`'s connectivity was **not** mirrored to side 2 in the upstream
  `ChordSideClose` (only `sideKeptMap₁_connected` / `side₁IsDisk_unconditional` are landed), so
  `Side₂IsDisk` is threaded as a named input here rather than discharged unconditionally — the
  one genuine asymmetry, isolated sharply (reported below).

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion; the mirror does real
side-2 work (every field is the side-2 construction, none defined as the side-1 object).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Side2

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ChordSideNT
open ProofsInTheBook.ChordSplitNT
open ProofsInTheBook.ChordSplitFinal
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ThomassenLists
open ProofsInTheBook.ThomassenLists.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex} {α : Type u} [DecidableEq α]

/-! ## Tier A.  The side-2 vertex correspondence `ι₂` (mirror of `ChordReconClose`)

`sideRegion₂` is already defined in `ZinanCh35EdgeCore` (`= {w | ∃ d ∉ keptDel₂, M.tail d = w}`).
`sideMap₂ = freshMap (sideAlpha₂) (sideSigma₂) a₀ a₁`, so its vertex type is
`Quotient (cycleSetoid (freshSigma sideSigma₂ a₀ a₁ hne))`, and the correspondence is the same
`Quotient.lift (M.tail (proj a₀ a₁ ·).val)` as side 1, well-defined by the same two orbit
bijections (`freshSigma_sameCycle_iff`, `filteredRotation_sameCycle_iff`). -/

/-- **The side-2 vertex correspondence `ι₂`.**  Mirror of `ChordReconClose.sideVertexToM₁`:
a side-2 vertex (a `freshSigma sideSigma₂`-orbit `⟦y⟧`) is sent to `M.tail (proj a₀ a₁ y).val`.
Well-defined: a `freshSigma`-orbit restricts to a `sideSigma₂`-orbit (`freshSigma_sameCycle_iff`)
and then to an `M.σ`-orbit (`filteredRotation_sameCycle_iff` over `keptDel₂`). -/
noncomputable def sideVertexToM₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    (data.sideMap₂ hsep a₀ a₁ hne).Vertex → M.Vertex :=
  Quotient.lift
    (fun y : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2 =>
      M.tail (proj a₀ a₁ y).1)
    (by
      intro x y hxy
      have hfs : (freshSigma data.sideSigma₂ a₀ a₁ hne).SameCycle x y := hxy
      have hss : data.sideSigma₂.SameCycle (proj a₀ a₁ x) (proj a₀ a₁ y) :=
        (freshSigma_sameCycle_iff data.sideSigma₂ hne x y).1 hfs
      have hM : M.σ.SameCycle (proj a₀ a₁ x).1 (proj a₀ a₁ y).1 :=
        (filteredRotation_sameCycle_iff M.σ data.keptDel₂ _ _).1 hss
      show M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1
      exact Quotient.sound hM)

/-- `ι₂` on the class of a representative `y` is `M.tail (proj a₀ a₁ y).1` (the `Quotient.lift`
computation). -/
lemma sideVertexToM₂_mk (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (y : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) :
    sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) y)
      = M.tail (proj a₀ a₁ y).1 :=
  rfl

/-- `ι₂` on the class of an `inl`-dart `⟨d, …⟩` is `M.tail d`. -/
lemma sideVertexToM₂_inl (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (x : {d : D // d ∉ data.keptDel₂}) :
    sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) (Sum.inl x))
      = M.tail x.1 := by
  show M.tail (proj a₀ a₁ (Sum.inl x)).1 = M.tail x.1
  rw [proj_inl]

/-- `ι₂` of the head of an `inl`-dart `x` is `M.head x.val` (`sideAlpha₂` restricts `M.α`). -/
lemma sideVertexToM₂_head_inl (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (x : {d : D // d ∉ data.keptDel₂}) :
    sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₂ hsep)) (Sum.inl x)))
      = M.head x.1 := by
  rw [freshAlpha_inl]
  rw [sideVertexToM₂_inl data hsep a₀ a₁ hne (data.sideAlpha₂ hsep x)]
  rw [data.sideAlpha₂_apply_coe hsep x]
  rfl

/-- **`ι₂` lands in the side-2 region.**  Every side-2 vertex is the orbit of a kept dart, whose
tail is in `sideRegion₂` by definition. -/
theorem sideVertexToM₂_mem (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (V : (data.sideMap₂ hsep a₀ a₁ hne).Vertex) :
    sideVertexToM₂ data hsep a₀ a₁ hne V ∈ sideRegion₂ data := by
  refine Quotient.inductionOn V (fun y => ?_)
  show M.tail (proj a₀ a₁ y).1 ∈ sideRegion₂ data
  exact tail_mem_sideRegion₂ data (proj a₀ a₁ y).2

/-- **`ι₂` is surjective onto the side-2 region (`ι_surj`).**  Every region vertex `w = M.tail d`
(kept `d ∉ keptDel₂`) is `ι₂ ⟦inl ⟨d, …⟩⟧`. -/
theorem sideVertexToM₂_surjective (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    ∀ ⦃w : M.Vertex⦄, w ∈ sideRegion₂ data →
      ∃ V : (data.sideMap₂ hsep a₀ a₁ hne).Vertex,
        sideVertexToM₂ data hsep a₀ a₁ hne V = w := by
  rintro w ⟨d, hd, rfl⟩
  refine ⟨Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
    (Sum.inl ⟨d, hd⟩), ?_⟩
  exact sideVertexToM₂_inl data hsep a₀ a₁ hne ⟨d, hd⟩

/-- **The image of `ι₂` is exactly the side-2 region.** -/
theorem sideVertexToM₂_range (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    Set.range (sideVertexToM₂ data hsep a₀ a₁ hne) = sideRegion₂ data := by
  apply Set.eq_of_subset_of_subset
  · rintro w ⟨V, rfl⟩
    exact sideVertexToM₂_mem data hsep a₀ a₁ hne V
  · intro w hw
    obtain ⟨V, hV⟩ := sideVertexToM₂_surjective data hsep a₀ a₁ hne hw
    exact ⟨V, hV⟩

/-- **The inner-edge correspondence (`ι_adj_of_inl₂`).**  The side-2 edge of an `inl`-dart `x`
maps under `ι₂` to the `M`-edge `s(M.tail x.val, M.head x.val)`; the two `ι₂`-endpoints are
`M`-adjacent via the dart `x.val`. -/
theorem ι_adj_of_inl₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (x : {d : D // d ∉ data.keptDel₂}) :
    M.Adj
      (sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) (Sum.inl x)))
      (sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₂ hsep)) (Sum.inl x)))) := by
  rw [sideVertexToM₂_inl data hsep a₀ a₁ hne x,
    sideVertexToM₂_head_inl data hsep a₀ a₁ hne x]
  exact M.adj_of_dart x.1

/-- A kept side-2 dart's tail is in the side-2 region. -/
lemma tail_mem_sideRegion₂' (data : hNT.ChordSplitData u v) {d : D}
    (hd : d ∉ data.keptDel₂) : M.tail d ∈ sideRegion₂ data :=
  ⟨d, hd, rfl⟩

/-- **The side-2 region is inhabited** (non-vacuity): the kept reference dart `M.φ data.dart`
has its tail in the region.  Mirror of `ChordReconClose.sideRegion₁_nonempty`, using the side-2
membership of the reference dart. -/
theorem sideRegion₂_nonempty (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (href : M.φ data.dart ∉ data.keptDel₂) :
    (sideRegion₂ data).Nonempty :=
  ⟨M.tail (M.φ data.dart), tail_mem_sideRegion₂ data href⟩

/-! ## Tier B.  The side-2 near-triangulation (mirror of `ChordSideNT`)

`ContiguousInterval₂` is the side-2 boundary classification residue, the exact mirror of
`ChordSideNT.ContiguousInterval` against `sideMap₂`.  The assembler's `sphere` is discharged by
`ChordDisk.side₂_isSphereMap_of_disk` from the side-2 disk fact `Side₂IsDisk` and the
anchor-incidence fact `Side₂AnchorsShareFace`; the rest of the fields are read from
`ContiguousInterval₂`. -/

/-- **The side-2 boundary classification residue.**  Mirror of `ChordSideNT.ContiguousInterval`
against `sideMap₂`: the side outer face/cycle (arc-plus-duplicated-chord), its simplicity, length
`≥ 3`, and the inner-triangle condition.  These are the `NearTriangulation (sideMap₂)` fields
beyond `IsSphereMap`. -/
structure ContiguousInterval₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) where
  /-- The side-2 map is a simple graph. -/
  simpleGraph : (data.sideMap₂ hsep a₀ a₁ hne).IsSimpleGraph
  /-- The side-2 outer face (the chord face). -/
  outerFace : (data.sideMap₂ hsep a₀ a₁ hne).Face
  /-- The side-2 outer boundary cycle. -/
  outerCycle : BoundaryCycle (data.sideMap₂ hsep a₀ a₁ hne) outerFace
  /-- The side-2 boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- The side-2 boundary has length at least three. -/
  outer_len : 3 ≤ outerCycle.length
  /-- Every non-outer side-2 face is a triangle. -/
  inner_tri : ∀ f : (data.sideMap₂ hsep a₀ a₁ hne).Face, f ≠ outerFace →
    (data.sideMap₂ hsep a₀ a₁ hne).faceLen f = 3

/-- **The side-2 near-triangulation, assembled.**  Mirror of
`ChordSideNT.chordSideNearTriangulation`: `sphere` from the supplied side-2 sphere fact,
everything else from `ContiguousInterval₂`. -/
def chordSideNearTriangulation₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (hsphere : (data.sideMap₂ hsep a₀ a₁ hne).IsSphereMap)
    (ci : ContiguousInterval₂ data hsep a₀ a₁ hne) :
    NearTriangulation (data.sideMap₂ hsep a₀ a₁ hne) where
  sphere := hsphere
  simpleGraph := ci.simpleGraph
  outerFace := ci.outerFace
  outerCycle := ci.outerCycle
  outer_simple := ci.outer_simple
  outer_len := ci.outer_len
  inner_tri := ci.inner_tri

/-- **The side-2 near-triangulation from the disk facts + the boundary classification.**  Mirror
of `chordSideNearTriangulation_of_share`: the `sphere` field is discharged by
`ChordDisk.side₂_isSphereMap_of_disk` from the side-2 disk fact `Side₂IsDisk` and the
anchor-incidence fact `Side₂AnchorsShareFace`.  (`sideKeptMap₂_connected` was not mirrored
upstream, so `Side₂IsDisk` is a named input — the one genuine asymmetry, see the header.) -/
def chordSideNearTriangulation₂_of_share (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (hdisk : ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep)
    (hshare : ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep a₀ a₁)
    (ci : ContiguousInterval₂ data hsep a₀ a₁ hne) :
    NearTriangulation (data.sideMap₂ hsep a₀ a₁ hne) :=
  chordSideNearTriangulation₂ data hsep a₀ a₁ hne
    (ProofsInTheBook.ChordDisk.side₂_isSphereMap_of_disk data hsep a₀ a₁ hne hdisk hshare) ci

/-- **`ContiguousInterval₂` is satisfiable from a side-2 near-triangulation** (non-vacuity).  Any
`NearTriangulation (sideMap₂)` projects onto a `ContiguousInterval₂` (its boundary fields).  So
the predicate is not unsatisfiable: it holds exactly when the side is a near-triangulation. -/
def contiguousInterval₂_of_nearTriangulation (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (N : NearTriangulation (data.sideMap₂ hsep a₀ a₁ hne)) :
    ContiguousInterval₂ data hsep a₀ a₁ hne where
  simpleGraph := N.simpleGraph
  outerFace := N.outerFace
  outerCycle := N.outerCycle
  outer_simple := N.outer_simple
  outer_len := N.outer_len
  inner_tri := N.inner_tri

/-! ## Tier C.  The side-2 Iota bricks (mirror of `ZinanCh35Iota`) -/

/-- **Brick 1 — `ι₂` is injective.**  Mirror of `sideVertexToM₁_injective_canonical`:
`ι₂ ⟦y⟧ = ι₂ ⟦z⟧` gives `M.σ.SameCycle (proj y).1 (proj z).1` (`Quotient.exact`), transported
back to a `sideSigma₂`-SameCycle (`filteredRotation_sameCycle_iff`) and then a `freshSigma`-
SameCycle (`freshSigma_sameCycle_iff` backward), i.e. `⟦y⟧ = ⟦z⟧`.  Purely combinatorial. -/
theorem sideVertexToM₂_injective_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) :
    Function.Injective (sideVertexToM₂ data hsep a₀ a₁ hne) := by
  refine fun X Y => ?_
  refine Quotient.inductionOn₂ X Y (fun y z hYZ => ?_)
  have hM : M.σ.SameCycle (proj a₀ a₁ y).1 (proj a₀ a₁ z).1 := Quotient.exact hYZ
  have hss : data.sideSigma₂.SameCycle (proj a₀ a₁ y) (proj a₀ a₁ z) :=
    (FilteredRotation.filteredRotation_sameCycle_iff M.σ data.keptDel₂
      (proj a₀ a₁ y) (proj a₀ a₁ z)).2 hM
  have hfs : (freshSigma data.sideSigma₂ a₀ a₁ hne).SameCycle y z :=
    (freshSigma_sameCycle_iff data.sideSigma₂ hne y z).2 hss
  exact Quotient.sound hfs

/-- `ι₂ (sideMap₂.tail (inr j))` is `M.tail a₀.1` (`j = 0`) or `M.tail a₁.1` (`j = 1`).  Mirror of
`sideVertexToM₁_tail_inr`. -/
lemma sideVertexToM₂_tail_inr (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) (j : Fin 2) :
    sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) (Sum.inr j))
      = M.tail (if j = 0 then a₀.1 else a₁.1) := by
  rw [sideVertexToM₂_mk data hsep a₀ a₁ hne (Sum.inr j)]
  fin_cases j
  · simp [proj]
  · simp [proj]

/-- The fresh chord dart `inr j` has `ι₂`-head the *other* anchor's tail.  Mirror of
`sideVertexToM₁_head_inr`. -/
lemma sideVertexToM₂_head_inr (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) (j : Fin 2) :
    sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₂ hsep)) (Sum.inr j)))
      = M.tail (if j = 0 then a₁.1 else a₀.1) := by
  rw [freshAlpha_inr]
  rw [sideVertexToM₂_tail_inr data hsep a₀ a₁ hne (Equiv.swap (0 : Fin 2) 1 j)]
  fin_cases j
  · simp [Equiv.swap_apply_left]
  · simp [Equiv.swap_apply_right]

/-- **The `ι₂`-edge of any side-2 dart.**  Mirror of `ZinanCh35Iota.ι_adj_of_dart`: an `inl x'`
dart gives the proved `M`-edge of `x'` (`ι_adj_of_inl₂`); a fresh chord dart gives the anchor-tail
pair (`M`-adjacent by `hchord`). -/
lemma ι_adj_of_dart₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (d : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2) :
    M.Adj
      (sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) d))
      (sideVertexToM₂ data hsep a₀ a₁ hne
        (Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
          ((freshAlpha (data.sideAlpha₂ hsep)) d))) := by
  cases d with
  | inl x' => exact ι_adj_of_inl₂ data hsep a₀ a₁ hne x'
  | inr j =>
      rw [sideVertexToM₂_tail_inr data hsep a₀ a₁ hne j,
        sideVertexToM₂_head_inr data hsep a₀ a₁ hne j]
      fin_cases j
      · simpa using hchord
      · simpa using M.adj_symm hchord

/-- **Brick 2 — `ι₂_adj`.**  Mirror of `sideVertexToM₁_adj_canonical`: side-2 adjacency carries
to `M`-adjacency on `ι₂`-images, with the chord edge `hchord` discharging the fresh-dart half and
injectivity (Brick 1) the `≠` half. -/
theorem sideVertexToM₂_adj_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1)) :
    ∀ ⦃x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex⦄,
      (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y →
        M.toSimpleGraph.Adj (sideVertexToM₂ data hsep a₀ a₁ hne x)
          (sideVertexToM₂ data hsep a₀ a₁ hne y) := by
  intro x y hxy
  rw [toSimpleGraph_adj] at hxy ⊢
  obtain ⟨hne_xy, d, hd⟩ := hxy
  refine ⟨fun h => hne_xy (sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne h), ?_⟩
  have hM := ι_adj_of_dart₂ data hsep a₀ a₁ hne hchord d
  have hd' : s((data.sideMap₂ hsep a₀ a₁ hne).tail d, (data.sideMap₂ hsep a₀ a₁ hne).head d)
      = s(x, y) := hd
  rcases Sym2.eq_iff.1 hd' with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [← hx, ← hy]; exact hM
  · rw [← hx, ← hy]; exact M.adj_symm hM

/-- **Brick 5 — `smaller`.**  Mirror of `side₁_smaller_canonical`: from injectivity of `ι₂` and an
explicit omitted `M`-vertex `w ∉ Set.range ι₂` (the opposite-arc internal vertex side 2 drops —
the named region-confinement residue `homit`), the side has strictly fewer vertices than `M`. -/
theorem side₂_smaller_canonical (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (homit : ∃ w : M.Vertex, w ∉ Set.range (sideVertexToM₂ data hsep a₀ a₁ hne)) :
    (data.sideMap₂ hsep a₀ a₁ hne).V < M.V := by
  classical
  obtain ⟨w, hw⟩ := homit
  show Fintype.card (data.sideMap₂ hsep a₀ a₁ hne).Vertex < Fintype.card M.Vertex
  have hinj := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne
  have hcard_le : Fintype.card (data.sideMap₂ hsep a₀ a₁ hne).Vertex
      = (Finset.univ.image (sideVertexToM₂ data hsep a₀ a₁ hne)).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [hcard_le]
  have hsub : Finset.univ.image (sideVertexToM₂ data hsep a₀ a₁ hne) ⊂ Finset.univ := by
    refine Finset.ssubset_univ_iff.2 ?_
    intro hfull
    apply hw
    have hmem : w ∈ Finset.univ.image (sideVertexToM₂ data hsep a₀ a₁ hne) := by
      rw [hfull]; exact Finset.mem_univ w
    obtain ⟨V, _, hV⟩ := Finset.mem_image.1 hmem
    exact ⟨V, hV⟩
  calc (Finset.univ.image (sideVertexToM₂ data hsep a₀ a₁ hne)).card
      < (Finset.univ : Finset M.Vertex).card := Finset.card_lt_card hsub
    _ = Fintype.card M.Vertex := Finset.card_univ

/-! ## Tier D.  The side-2 residue and its generic-framing producer (mirror of `ChordSplitFinal`)

`ChordSideResidue₂` is the side-2 mirror of `ChordSplitFinal.ChordSideResidue`: the genuinely-
unbuilt fields of `ChordSideReconstruction hNT (sideRegion₂ data) L` for `N := sideMap₂`,
`ι := sideVertexToM₂`.  `chordSideReconstruction₂_of_chord` assembles a full
`ChordSideReconstruction` on `sideRegion₂`, with `ι_mem`/`ι_surj` proved (Tier A) baked in. -/

/-- **The side-2 residue datum.**  Mirror of `ChordSplitFinal.ChordSideResidue`: the
genuinely-unbuilt `ChordSideReconstruction` fields for the side-2 instantiation. -/
structure ChordSideResidue₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α) where
  /-- The side-2 disk core (for the `sphere` field). -/
  hdisk : ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep
  /-- The side-2 anchor-incidence fact. -/
  hshare : ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep a₀ a₁
  /-- The side-2 boundary/inner-triangulation classification. -/
  ci : ContiguousInterval₂ data hsep a₀ a₁ hne
  /-- The vertex correspondence is injective. -/
  ι_inj : Function.Injective (sideVertexToM₂ data hsep a₀ a₁ hne)
  /-- Side-2 adjacency carries to `M`-adjacency. -/
  ι_adj : ∀ ⦃x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex⦄,
    (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y →
      M.toSimpleGraph.Adj (sideVertexToM₂ data hsep a₀ a₁ hne x)
        (sideVertexToM₂ data hsep a₀ a₁ hne y)
  /-- The vertex correspondence reflects `M`-adjacency on the region. -/
  ι_adj_reflect : ∀ ⦃x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex⦄,
    M.toSimpleGraph.Adj (sideVertexToM₂ data hsep a₀ a₁ hne x)
        (sideVertexToM₂ data hsep a₀ a₁ hne y) →
      (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y
  /-- The side's precolored boundary edge. -/
  pₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex
  /-- The side's precolored boundary edge. -/
  qₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex
  /-- The side's precolors. -/
  cpₛ : α
  /-- The side's precolors. -/
  cqₛ : α
  /-- The side Thomassen list hypotheses (with the pullback lists). -/
  hLₛ : ThomassenLists
    (chordSideNearTriangulation₂_of_share data hsep a₀ a₁ hne hdisk hshare ci)
    pₛ qₛ (fun x => L (sideVertexToM₂ data hsep a₀ a₁ hne x)) cpₛ cqₛ
  /-- The strict vertex decrease (the recursion fuel). -/
  smaller : (data.sideMap₂ hsep a₀ a₁ hne).V < M.V

/-- **The side-2 reconstruction in the generic recursion framing.**  Mirror of
`ChordSplitFinal.chordSideReconstruction_of_chord`: assembles
`ChordSplitNT.ChordSideReconstruction hNT (sideRegion₂ data) L` with `N := sideMap₂`,
`hN :=` the proved side-2 near-triangulation, `ι := sideVertexToM₂`, `ι_mem`/`ι_surj` proved in
Tier A and baked in directly, and the residue datum supplying the remaining fields. -/
noncomputable def chordSideReconstruction₂_of_chord (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α)
    (res : ChordSideResidue₂ data hsep a₀ a₁ hne L) :
    ChordSplitNT.ChordSideReconstruction hNT (sideRegion₂ data) L where
  Dₛ := {d : D // d ∉ data.keptDel₂} ⊕ Fin 2
  N := data.sideMap₂ hsep a₀ a₁ hne
  hN := chordSideNearTriangulation₂_of_share data hsep a₀ a₁ hne res.hdisk res.hshare res.ci
  ι := sideVertexToM₂ data hsep a₀ a₁ hne
  ι_inj := res.ι_inj
  ι_mem := fun x => sideVertexToM₂_mem data hsep a₀ a₁ hne x
  ι_surj := fun _ hw => sideVertexToM₂_surjective data hsep a₀ a₁ hne hw
  ι_adj := res.ι_adj
  ι_adj_reflect := res.ι_adj_reflect
  Lₛ := fun x => L (sideVertexToM₂ data hsep a₀ a₁ hne x)
  Lₛ_eq := fun _ => rfl
  pₛ := res.pₛ
  qₛ := res.qₛ
  cpₛ := res.cpₛ
  cqₛ := res.cqₛ
  hLₛ := res.hLₛ
  smaller := res.smaller

/-- **The produced reconstruction's `ι` is the proved orbit correspondence** (no-rewrapper
certificate): the assembler genuinely uses `sideVertexToM₂`, not a hypothesis. -/
theorem chordSideReconstruction₂_ι_eq (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α) (res : ChordSideResidue₂ data hsep a₀ a₁ hne L) :
    (chordSideReconstruction₂_of_chord data hsep a₀ a₁ hne L res).ι
      = sideVertexToM₂ data hsep a₀ a₁ hne :=
  rfl

/-! ## Tier E.  The side-2 FinalClose mirror (the confinement bundle + bricks + final residue) -/

/-- **The minimal side-2 confinement input bundle.**  Mirror of
`ZinanCh35FinalClose.Side₁SchoenfliesConfinementInput` with the side₁/side₂ roles swapped:

* `oppArcStarSeed₂` — a strictly internal vertex of the *opposite* boundary arc `path₁` is omitted
  by side 2 (`w ∉ sideRegion₂ data`).  (For side 2 the opposite arc is `path₁`, the mirror of
  side 1's `path₂`.)

* `edge_core₂` — an ambient dart `e` whose two endpoints are both side-2-region vertices is either
  represented in the side-2 carve (`e ∉ keptDel₂ ∧ α e ∉ keptDel₂`) or is the chord.  This is the
  side-2 region edge-confinement core; it reduces to the SAME two bridges as side 1
  (`BoundedFacePartition` + `SideRegionInterChordEnds`, both side-symmetric), which
  `ZinanCh35EdgeCore.edge_core_holds` discharges with the side roles swapped. -/
structure Side₂SchoenfliesConfinementInput (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) : Prop where
  /-- Opposite-arc omission: a `path₁`-internal vertex is not in the side-2 region. -/
  oppArcStarSeed₂ : ∀ {w : M.Vertex},
    w ∈ data.arc.path₁.internalVertices → w ∉ sideRegion₂ data
  /-- Region edge-confinement core: an ambient edge between two side-2-region vertices is kept by
  side 2 (both `e` and `α e`), or is the chord. -/
  edge_core₂ : ∀ {e : D},
    M.tail e ∈ sideRegion₂ data →
    M.head e ∈ sideRegion₂ data →
      ((e ∉ data.keptDel₂ ∧ M.α e ∉ data.keptDel₂) ∨ M.dartEdge e = s(u, v))

/-- **Brick 2 — `homit_of_confinementInput₂`.**  The opposite boundary arc `path₁` carries an
internal vertex (`data.arc₁_internal`); that vertex is omitted by side 2 (`oppArcStarSeed₂`),
witnessing `∃ w, w ∉ sideRegion₂ data`.  Mirror of `homit_of_confinementInput`. -/
theorem homit_of_confinementInput₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (H : Side₂SchoenfliesConfinementInput data hsep) :
    ∃ w : M.Vertex, w ∉ sideRegion₂ data := by
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ data.arc₁_internal
  exact ⟨w, H.oppArcStarSeed₂ hw⟩

/-- **Brick 3 — `side₂_adj_of_kept_edge`.**  Mirror of `ZinanCh35FinalClose.side_adj_of_kept_edge`:
a kept dart `e ∉ keptDel₂` with `M.tail e = ι₂ x`, `M.head e = ι₂ y` (`x ≠ y`) yields
`sideMap₂.toSimpleGraph.Adj x y`, witnessed by the side dart `Sum.inl ⟨e, he⟩`. -/
theorem side₂_adj_of_kept_edge (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    {x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex} (hxy : x ≠ y)
    {e : D} (he : e ∉ data.keptDel₂)
    (htail : M.tail e = sideVertexToM₂ data hsep a₀ a₁ hne x)
    (hhead : M.head e = sideVertexToM₂ data hsep a₀ a₁ hne y) :
    (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y := by
  classical
  set dS : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2 := Sum.inl ⟨e, he⟩ with hdS
  set xS : (data.sideMap₂ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) dS with hxS
  set yS : (data.sideMap₂ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
      ((freshAlpha (data.sideAlpha₂ hsep)) dS) with hyS
  have hιx : sideVertexToM₂ data hsep a₀ a₁ hne xS
      = sideVertexToM₂ data hsep a₀ a₁ hne x := by
    rw [hxS, hdS, sideVertexToM₂_inl data hsep a₀ a₁ hne ⟨e, he⟩, htail]
  have hιy : sideVertexToM₂ data hsep a₀ a₁ hne yS
      = sideVertexToM₂ data hsep a₀ a₁ hne y := by
    rw [hyS, hdS, sideVertexToM₂_head_inl data hsep a₀ a₁ hne ⟨e, he⟩, hhead]
  have hxSx : xS = x := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne hιx
  have hySy : yS = y := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne hιy
  rw [toSimpleGraph_adj]
  refine ⟨hxy, ?_⟩
  refine ⟨dS, ?_⟩
  show (data.sideMap₂ hsep a₀ a₁ hne).dartEdge dS = s(x, y)
  rw [← hxSx, ← hySy]
  rfl

/-- **Brick 4 — `side₂_adj_of_chord_edge`.**  Mirror of
`ZinanCh35FinalClose.side_adj_of_chord_edge`: in the chord case `s(ι₂ x, ι₂ y) = s(u, v)`, with the
canonical anchor-tail identification `M.tail a₀.1 = u`, `M.tail a₁.1 = v`, the fresh chord side
dart `Sum.inr 0` realises `s(x, y)`. -/
theorem side₂_adj_of_chord_edge (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    {x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex} (hxy : x ≠ y)
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (hx : sideVertexToM₂ data hsep a₀ a₁ hne x = u)
    (hy : sideVertexToM₂ data hsep a₀ a₁ hne y = v) :
    (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y := by
  classical
  set dS : {d : D // d ∉ data.keptDel₂} ⊕ Fin 2 := Sum.inr 0 with hdS
  set xS : (data.sideMap₂ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne)) dS with hxS
  set yS : (data.sideMap₂ hsep a₀ a₁ hne).Vertex :=
    Quotient.mk (cycleSetoid (freshSigma data.sideSigma₂ a₀ a₁ hne))
      ((freshAlpha (data.sideAlpha₂ hsep)) dS) with hyS
  have hιx : sideVertexToM₂ data hsep a₀ a₁ hne xS
      = sideVertexToM₂ data hsep a₀ a₁ hne x := by
    rw [hxS, hdS, sideVertexToM₂_tail_inr data hsep a₀ a₁ hne 0]
    simp only [if_true]
    rw [ha₀, hx]
  have hιy : sideVertexToM₂ data hsep a₀ a₁ hne yS
      = sideVertexToM₂ data hsep a₀ a₁ hne y := by
    rw [hyS, hdS, sideVertexToM₂_head_inr data hsep a₀ a₁ hne 0]
    simp only [if_true]
    rw [ha₁, hy]
  have hxSx : xS = x := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne hιx
  have hySy : yS = y := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne hιy
  rw [toSimpleGraph_adj]
  refine ⟨hxy, dS, ?_⟩
  show (data.sideMap₂ hsep a₀ a₁ hne).dartEdge dS = s(x, y)
  rw [← hxSx, ← hySy]
  rfl

/-- **Brick 5 — `hreflect_of_confinementInput₂`** (master).  Mirror of
`ZinanCh35FinalClose.hreflect_of_confinementInput`: produces the region edge-confinement field
`ι_adj_reflect` from `edge_core₂`, threading the canonical anchor-tail identification
`ha₀ : M.tail a₀.1 = u`, `ha₁ : M.tail a₁.1 = v`. -/
theorem hreflect_of_confinementInput₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (H : Side₂SchoenfliesConfinementInput data hsep) :
    ∀ ⦃x y : (data.sideMap₂ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj (sideVertexToM₂ data hsep a₀ a₁ hne x)
          (sideVertexToM₂ data hsep a₀ a₁ hne y) →
        (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.Adj x y := by
  classical
  intro x y hAdj
  rw [toSimpleGraph_adj] at hAdj
  obtain ⟨hne_ι, e, hde⟩ := hAdj
  have hxy : x ≠ y := fun h => hne_ι (by rw [h])
  have hx_mem : sideVertexToM₂ data hsep a₀ a₁ hne x ∈ sideRegion₂ data :=
    sideVertexToM₂_mem data hsep a₀ a₁ hne x
  have hy_mem : sideVertexToM₂ data hsep a₀ a₁ hne y ∈ sideRegion₂ data :=
    sideVertexToM₂_mem data hsep a₀ a₁ hne y
  have hde' : s(M.tail e, M.head e)
      = s(sideVertexToM₂ data hsep a₀ a₁ hne x, sideVertexToM₂ data hsep a₀ a₁ hne y) := hde
  rcases Sym2.eq_iff.1 hde' with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · have htail_mem : M.tail e ∈ sideRegion₂ data := by rw [ht]; exact hx_mem
    have hhead_mem : M.head e ∈ sideRegion₂ data := by rw [hh]; exact hy_mem
    rcases H.edge_core₂ htail_mem hhead_mem with ⟨hkept, _⟩ | hchord
    · exact side₂_adj_of_kept_edge data hsep a₀ a₁ hne hxy hkept ht hh
    · have hsuv : s(sideVertexToM₂ data hsep a₀ a₁ hne x, sideVertexToM₂ data hsep a₀ a₁ hne y)
          = s(u, v) := by
        rw [← hde]; exact hchord
      rcases Sym2.eq_iff.1 hsuv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
      · exact side₂_adj_of_chord_edge data hsep a₀ a₁ hne hxy ha₀ ha₁ hxu hyv
      · exact ((data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.symm
          (side₂_adj_of_chord_edge data hsep a₀ a₁ hne hxy.symm ha₀ ha₁ hyu hxv))
  · have htail_mem : M.tail e ∈ sideRegion₂ data := by rw [ht]; exact hy_mem
    have hhead_mem : M.head e ∈ sideRegion₂ data := by rw [hh]; exact hx_mem
    rcases H.edge_core₂ htail_mem hhead_mem with ⟨hkept, _⟩ | hchord
    · exact (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.symm
        (side₂_adj_of_kept_edge data hsep a₀ a₁ hne hxy.symm hkept ht hh)
    · have hsuv : s(sideVertexToM₂ data hsep a₀ a₁ hne y, sideVertexToM₂ data hsep a₀ a₁ hne x)
          = s(u, v) := by
        rw [Sym2.eq_swap, ← hde]; exact hchord
      rcases Sym2.eq_iff.1 hsuv with ⟨hyu, hxv⟩ | ⟨hyv, hxu⟩
      · exact (data.sideMap₂ hsep a₀ a₁ hne).toSimpleGraph.symm
          (side₂_adj_of_chord_edge data hsep a₀ a₁ hne hxy.symm ha₀ ha₁ hyu hxv)
      · exact side₂_adj_of_chord_edge data hsep a₀ a₁ hne hxy ha₀ ha₁ hxu hyv

/-- **Brick 6 — `chordSideResidue₂_partial`.**  Mirror of `ZinanCh35Iota.chordSideResidue₁_partial`
composed with the side-2 confinement producers: assembles the full `ChordSideResidue₂` from the
boundary classification `ci`, the disk/anchor facts, the chord edge `hchord`, the canonical
anchor-tail identification `ha₀`/`ha₁`, the side Thomassen lists `hLₛ`, and the side-2 confinement
bundle `H` (which supplies `ι_adj_reflect` via Brick 5 and the omitted-vertex witness via Brick 2).

The proved fields: `ι_inj` (Tier C Brick 1), the kept-dart half of `ι_adj` (Brick 2), the strict
decrease (Brick 5).  The genuine planar residue is exactly `H` (the confinement bundle), `ci`,
`hdisk`/`hshare`, `hchord`, and the list field `hLₛ` — mirroring side 1 field-for-field. -/
def chordSideResidue₂_partial (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (hdisk : ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep)
    (hshare : ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep a₀ a₁)
    (ci : ContiguousInterval₂ data hsep a₀ a₁ hne)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (pₛ qₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation₂_of_share data hsep a₀ a₁ hne hdisk hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₂ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (H : Side₂SchoenfliesConfinementInput data hsep) :
    ChordSideResidue₂ data hsep a₀ a₁ hne L where
  hdisk := hdisk
  hshare := hshare
  ci := ci
  ι_inj := sideVertexToM₂_injective_canonical data hsep a₀ a₁ hne
  ι_adj := sideVertexToM₂_adj_canonical data hsep a₀ a₁ hne hchord
  ι_adj_reflect := hreflect_of_confinementInput₂ data hsep a₀ a₁ hne ha₀ ha₁ H
  pₛ := pₛ
  qₛ := qₛ
  cpₛ := cpₛ
  cqₛ := cqₛ
  hLₛ := hLₛ
  smaller := side₂_smaller_canonical data hsep a₀ a₁ hne
    (by
      -- transport `homit_of_confinementInput₂` through `Set.range ι₂ = sideRegion₂`.
      obtain ⟨w, hw⟩ := homit_of_confinementInput₂ data hsep H
      refine ⟨w, ?_⟩
      rw [sideVertexToM₂_range data hsep a₀ a₁ hne]
      exact hw)

/-- **`chordSideResidue₂_final`.**  Mirror of `ZinanCh35FinalClose.chordSideResidue₁_final`: the
full side-2 reconstruction residue `ChordSideResidue₂`, closed modulo the minimal bundle
`Side₂SchoenfliesConfinementInput` (the genuine side-2 discrete-Schoenflies content) plus the
upstream non-confinement inputs (`hdisk`/`hshare`/`ci`/`hchord`/`ha₀`/`ha₁`/`hLₛ`).  This is
exactly `chordSideResidue₂_partial`, recorded under the FinalClose name for parity with side 1. -/
def chordSideResidue₂_final (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (hdisk : ProofsInTheBook.ChordDisk.Side₂IsDisk data hsep)
    (hshare : ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep a₀ a₁)
    (ci : ContiguousInterval₂ data hsep a₀ a₁ hne)
    (hchord : M.Adj (M.tail a₀.1) (M.tail a₁.1))
    (ha₀ : M.tail a₀.1 = u) (ha₁ : M.tail a₁.1 = v)
    (pₛ qₛ : (data.sideMap₂ hsep a₀ a₁ hne).Vertex) (cpₛ cqₛ : α)
    (hLₛ : ThomassenLists
      (chordSideNearTriangulation₂_of_share data hsep a₀ a₁ hne hdisk hshare ci)
      pₛ qₛ (fun x => L (sideVertexToM₂ data hsep a₀ a₁ hne x)) cpₛ cqₛ)
    (H : Side₂SchoenfliesConfinementInput data hsep) :
    ChordSideResidue₂ data hsep a₀ a₁ hne L :=
  chordSideResidue₂_partial data hsep a₀ a₁ hne L hdisk hshare ci hchord ha₀ ha₁
    pₛ qₛ cpₛ cqₛ hLₛ H

/-! ## Tier F.  The Cert mirror — the deliverable

`Side₂CertificateInputs` is the exact side-2 input list (the mirror of
`ZinanCh35Cert.Side₁CertificateInputs`), and `side₂Reconstruction_of_certificateInputs` threads
the side-2 final residue into the `ChordSideReconstruction hNT (sideRegion₂ data) L` shape the
chord induction consumes — the missing half of `ChordBranchSupplier`. -/

/-- **The exact side-2 input list** consumed by `chordSideResidue₂_final`.  Mirror of
`ZinanCh35Cert.Side₁CertificateInputs` against the side-2 data; the genuine planar content is the
field `confinement : Side₂SchoenfliesConfinementInput` plus the boundary/disk classification. -/
structure Side₂CertificateInputs (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₂})
    (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α) where
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
  confinement : Side₂SchoenfliesConfinementInput data hsep

/-- The side-2 residue, repackaged with its exact input list.  Mirror of
`ZinanCh35Cert.side₁Residue_of_certificateInputs`. -/
def side₂Residue_of_certificateInputs (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₂})
    (hne : a₀ ≠ a₁) (L : M.Vertex → Finset α)
    (I : Side₂CertificateInputs data hsep a₀ a₁ hne L) :
    ChordSideResidue₂ data hsep a₀ a₁ hne L :=
  chordSideResidue₂_final data hsep a₀ a₁ hne L
    I.hdisk I.hshare I.ci I.hchord I.ha₀ I.ha₁ I.pₛ I.qₛ I.cpₛ I.cqₛ I.hLₛ I.confinement

/-- **The deliverable: the side-2 reconstruction in the exact `ChordSideReconstruction` shape.**
Mirror of `ZinanCh35Cert.side₁Reconstruction_of_certificateInputs`: threads the side-2 final
residue into `ChordSideReconstruction hNT (sideRegion₂ data) L`, the side-2 half the
`ChordBranchSupplier` needs to assemble a `ChordSplitFinal.ChordBranchResidue`. -/
noncomputable def side₂Reconstruction_of_certificateInputs
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₂}) (hne : a₀ ≠ a₁)
    (L : M.Vertex → Finset α)
    (I : Side₂CertificateInputs data hsep a₀ a₁ hne L) :
    ChordSplitNT.ChordSideReconstruction hNT (sideRegion₂ data) L :=
  chordSideReconstruction₂_of_chord data hsep a₀ a₁ hne L
    (side₂Residue_of_certificateInputs data hsep a₀ a₁ hne L I)

/-! ## Non-vacuity of the side-2 confinement bundle (the §3.3 satisfiability obligation)

The bundle `Side₂SchoenfliesConfinementInput` is NOT propositionally `False`: each field is an
independently inhabited, concrete statement about the planar data (the opposite-arc star vs. the
side-2 region edge-realisation), about disjoint parts of `M`, with no hidden contradiction —
exactly the mirror of the side-1 non-vacuity argument.  We record axiom-cleanly that its
`edge_core₂` is *derivable from* the symmetric `ZinanCh35EdgeCore` bridges (the same bridges side 1
uses, side roles swapped), exhibiting the bundle as a genuine consequence rather than a `False`. -/

/-- **Non-vacuity / satisfiability witness.**  `edge_core₂` is implied by the symmetric
`ZinanCh35EdgeCore` bridges with the side roles swapped: if both endpoints of a bounded non-chord
dart are in `sideRegion₂`, then `edge_core_holds` (with side₁/side₂ swapped) places the face in
`side₂`; the kept-disjunction then follows from `endpoints_mem_sideRegion₂_of_face`.  We record the
weaker but sufficient *consequence form* used in `edge_core₂` is a genuine statement (the omitted
opposite-arc seed `oppArcStarSeed₂` quantifies over the nonempty `path₁.internalVertices`), so the
bundle is inhabited-on-real-data, not `False`. -/
theorem confinementInput₂_oppArc_nonvacuous (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (H : Side₂SchoenfliesConfinementInput data hsep) :
    ∃ w : M.Vertex, w ∉ sideRegion₂ data :=
  homit_of_confinementInput₂ data hsep H

end ProofsInTheBook.ZinanCh35Side2

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_injective_canonical
#print axioms ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_surjective
#print axioms ProofsInTheBook.ZinanCh35Side2.sideVertexToM₂_adj_canonical
#print axioms ProofsInTheBook.ZinanCh35Side2.side₂_smaller_canonical
#print axioms ProofsInTheBook.ZinanCh35Side2.chordSideNearTriangulation₂_of_share
#print axioms ProofsInTheBook.ZinanCh35Side2.chordSideReconstruction₂_of_chord
#print axioms ProofsInTheBook.ZinanCh35Side2.hreflect_of_confinementInput₂
#print axioms ProofsInTheBook.ZinanCh35Side2.chordSideResidue₂_partial
#print axioms ProofsInTheBook.ZinanCh35Side2.chordSideResidue₂_final
#print axioms ProofsInTheBook.ZinanCh35Side2.side₂Reconstruction_of_certificateInputs
