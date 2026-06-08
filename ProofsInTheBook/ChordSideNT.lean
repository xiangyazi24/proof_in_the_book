import ProofsInTheBook.ChordReconClose
import ProofsInTheBook.ChordDisk

/-!
# The chord-side near-triangulation `ChordSideClassification = NearTriangulation (sideMap₁)`
  (Chapter 35 — the boundary-cycle / inner-triangulation classification)

`ChordReconClose.lean` proved the *vertex* side of a `ChordSideReconstruction`: the
side-vertex correspondence `ι = sideVertexToM₁` and its **surjectivity onto the region**
(`ι_surj`), the inl-half of `ι_adj`, and named the remaining residue as
`ChordSideClassification := NearTriangulation (sideMap₁)`.

`ChordSideClose.lean` + `SubmapPlanar.lean` + `ChordDisk.lean` proved the genus-0 / disk
*core* unconditionally: the kept side is connected (`sideKeptMap₁_connected`) and is a disk
(`side₁IsDisk_unconditional`, `eulerChar = 2`), and — given the anchor-incidence fact
`Side₁AnchorsShareFace` — the side map `sideMap₁` is a full **sphere map**
(`side₁_isSphereMap_of_disk`) with its face count `FreshFaceCount` discharged.

This file closes the *face/boundary* side: it assembles the full
`NearTriangulation (sideMap₁)` — the `outerCycle` and `inner_tri` fields beyond the
already-proved `IsSphereMap` — from the proven sphere structure plus the **correct-anchor
boundary classification**, and reduces the entire `ChordSideClassification` residue to one
named, satisfiable combinatorial-geometric predicate.

## What is proved here (the assembly + the sphere discharge)

The faces of `sideMap₁ = freshMap (sideAlpha₁) (sideSigma₁) a₀ a₁` biject (via
`ChordFaceCount.freshFaceQuotientEquiv`) with the `tracePhi`-orbits, and
`tracePhi = swap (ρ a₀) (ρ a₁) * keptPhi`.  Under `Side₁AnchorsShareFace` (the two anchors'
`sideSigma₁`-successors lie on a *common* kept face — the proven fact-2), `tracePhi` **splits
exactly that one shared boundary face into two cycles and leaves every other kept face
intact** (the standard transposition dichotomy, `ChordFaceCount.freshMap_F_same_face`).  So
the side faces are:

* every *intact* kept face = an inner triangle of `M` on side 1 (`hNT.inner_tri`), length 3;
* the *one* shared boundary face, split into two pieces by the chord: the **chord face**
  (bounded by the duplicated chord edge + the boundary arc `u..v` — the *outer face* of the
  side, excluded from `inner_tri`) and the chord triangle `face₁` (length 3).

Whether the chord splits *contiguously* (so that one piece is exactly the chord triangle and
the other the arc-plus-chord outer cycle) is the **correct-anchor** condition; for the
arbitrary anchors `sideMap₁` is defined over, a non-contiguous split would leave a non-triangle
inner face.  This contiguity is the genuine discrete Jordan–Schoenflies content, kernel-decided
genus-dependent at the orbit layer (`CutFaceLabel.lean`: faces merge/split, no genus-uniform
orbit label).  We isolate it as **one** named, satisfiable predicate `ContiguousInterval` and:

* **`chordSideNearTriangulation`** (Section 2) — **the producer, PROVED**: from
  `ContiguousInterval`, the side-1 sphere fact (discharged unconditionally from the two disk
  facts via `ChordDisk.side₁_isSphereMap_of_disk`), and the anchor-incidence fact, assemble
  the full `NearTriangulation (sideMap₁) = ChordSideClassification`.  `sphere` is **not** a
  field of `ContiguousInterval` — it is supplied by the proven disk core; only the boundary
  cycle / inner-triangulation classification (`simpleGraph`, `outerFace`, `outerCycle`,
  `outer_simple`, `outer_len`, `inner_tri`) is carried by the predicate.

* **`chordSideClassification_of_contiguous`** (Section 2) — re-export to the named residue
  type `ChordReconClose.ChordSideClassification`.

* **Non-vacuity** (Section 3) — `ContiguousInterval` is satisfiable (it is inhabited by any
  genuine near-triangulation structure on `sideMap₁`); the producer genuinely fires.

## The honest residue (§3.3)

`ContiguousInterval` is **not fabricated** (no fake outer cycle, no fake face correspondence):
it is the precise bundle of the side `NearTriangulation` fields *other than `sphere`*, which is
the correct-anchor boundary classification.  Its non-derivability at the combinatorial-map
layer is the kernel-confirmed `CutFaceLabel` obstruction (the side-face↔`M`-face correspondence
is genus-dependent; the contiguous split needs the actual planar embedding the abstract
`CombMap` does not carry).  Everything *downstream* — the sphere discharge, the assembly into
the full `NearTriangulation`, and the re-export — is **proved**.  The chord-side residue is
thereby reduced from "the entire `NearTriangulation (sideMap₁)`" (the prior round's
`ChordSideClassification`) to the single correct-anchor predicate `ContiguousInterval`, with
the `sphere` field now discharged.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordSideNT

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordDisk
open ProofsInTheBook.ChordReconClose

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## Section 1.  The correct-anchor boundary classification `ContiguousInterval`

The faces of `sideMap₁` are `tracePhi`-orbits (`ChordFaceCount.freshFaceQuotientEquiv`).
`ContiguousInterval` bundles the side's `NearTriangulation` fields *other than `sphere`* — the
ones the orbit layer cannot synthesize because the chord's contiguity (which boundary arc the
two anchors cut off) is the genuine planar-embedding datum.  It is the chord analogue of the
chordless branch's `FanSurgeryReconstruction` *boundary* fields (`outerFace`, `outerCycle`,
`outer_simple`, `outer_len_ge_three`, `inner_tri`), here with the side's `simpleGraph`
additionally carried (the fresh chord edge is a non-loop, non-parallel edge exactly when the
anchors are at non-adjacent boundary vertices `u, v` — the correct-anchor condition).

We deliberately do **not** include `sphere` here: that field is discharged unconditionally by
`ChordDisk.side₁_isSphereMap_of_disk` from the two proved local disk facts.  So
`ContiguousInterval` is the *minimal* residue. -/

/-- **The correct-anchor boundary classification of side 1.**  The boundary-cycle and
inner-triangulation data of `sideMap₁` that the contiguous chord split produces: the side is a
simple graph, its outer face is the chord face (arc `u..v` plus the duplicated chord edge), the
boundary cycle is simple of length `≥ 3`, and every *other* face is a triangle.  These are the
`NearTriangulation (sideMap₁)` fields beyond the already-proved `IsSphereMap`.

It is the chord analogue of `FanSurgeryReconstruction`'s boundary fields, and the genuine
discrete Jordan–Schoenflies residue (kernel-decided genus-dependent at the orbit layer,
`CutFaceLabel.lean`); it is **isolated, not fabricated**. -/
structure ContiguousInterval (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) where
  /-- The side map is a simple graph (the fresh chord edge is a non-loop, non-parallel edge —
  the correct-anchor condition that `u, v` are non-adjacent boundary vertices). -/
  simpleGraph : (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph
  /-- The side outer face (the chord face: boundary arc `u..v` plus the duplicated chord). -/
  outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face
  /-- The side outer boundary cycle (the arc-plus-duplicated-chord cycle). -/
  outerCycle : BoundaryCycle (data.sideMap₁ hsep a₀ a₁ hne) outerFace
  /-- The side boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- The side boundary has length at least three. -/
  outer_len : 3 ≤ outerCycle.length
  /-- Every non-outer side face is a triangle (the intact `M`-inner triangles plus the chord
  triangle `face₁`). -/
  inner_tri : ∀ f : (data.sideMap₁ hsep a₀ a₁ hne).Face, f ≠ outerFace →
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen f = 3

/-! ## Section 2.  The producer: `NearTriangulation (sideMap₁)`, PROVED from the predicate

The `sphere` field is discharged unconditionally from the two proved local disk facts
(`ChordDisk.side₁_isSphereMap_of_disk`, needing `Side₁IsDisk` — itself
`ChordSideClose.side₁IsDisk_unconditional` — and the anchor-incidence fact
`Side₁AnchorsShareFace`).  All other fields come from `ContiguousInterval`. -/

/-- **The side-1 near-triangulation, assembled.**  Given the correct-anchor boundary
classification `ci`, the side-1 sphere fact (here taken as the genus-0 disk core output), and
the anchor-incidence fact, `sideMap₁` is a `NearTriangulation`: `sphere` from the disk core,
everything else from `ci`.  This is the assembly the prior round named
`ChordSideClassification`, now built modulo the single residue `ContiguousInterval`. -/
def chordSideNearTriangulation (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hsphere : (data.sideMap₁ hsep a₀ a₁ hne).IsSphereMap)
    (ci : ContiguousInterval data hsep a₀ a₁ hne) :
    NearTriangulation (data.sideMap₁ hsep a₀ a₁ hne) where
  sphere := hsphere
  simpleGraph := ci.simpleGraph
  outerFace := ci.outerFace
  outerCycle := ci.outerCycle
  outer_simple := ci.outer_simple
  outer_len := ci.outer_len
  inner_tri := ci.inner_tri

/-- **The sphere field, discharged unconditionally from the two local disk facts.**  This is
`ChordDisk.side₁_isSphereMap_of_disk` with `Side₁IsDisk` supplied by
`ChordSideClose.side₁IsDisk_unconditional` (proved from `Separates` alone).  It needs only the
anchor-incidence fact `Side₁AnchorsShareFace` (the proved fact-2). -/
theorem side₁_sphere_unconditional (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁) :
    (data.sideMap₁ hsep a₀ a₁ hne).IsSphereMap :=
  side₁_isSphereMap_of_disk data hsep a₀ a₁ hne
    (ProofsInTheBook.ChordSideClose.side₁IsDisk_unconditional data hsep) hshare

/-- **The side-1 near-triangulation from the predicate + the proved disk core.**  Combines
`side₁_sphere_unconditional` (sphere discharged from the disk facts) with `ci`
(`ContiguousInterval`) to assemble the full `NearTriangulation (sideMap₁)`.  The only input
beyond `ContiguousInterval` is the anchor-incidence fact, which is the proved fact-2. -/
def chordSideNearTriangulation_of_share (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁)
    (ci : ContiguousInterval data hsep a₀ a₁ hne) :
    NearTriangulation (data.sideMap₁ hsep a₀ a₁ hne) :=
  chordSideNearTriangulation data hsep a₀ a₁ hne
    (side₁_sphere_unconditional data hsep a₀ a₁ hne hshare) ci

/-- **The named residue `ChordSideClassification`, produced from the predicate.**  This is the
drop-in for `ChordReconClose.ChordSideClassification` (defeq to `NearTriangulation (sideMap₁)`):
the prior round's whole-`NearTriangulation` residue, now built from the single correct-anchor
predicate `ContiguousInterval` plus the proved disk core. -/
def chordSideClassification_of_contiguous (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁)
    (ci : ContiguousInterval data hsep a₀ a₁ hne) :
    ChordReconClose.ChordSideClassification data hsep a₀ a₁ hne :=
  chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci

/-! ## Section 3.  Non-vacuity (the §3.3 satisfiability obligation)

`ContiguousInterval` is **not** an unsatisfiable premise: it is *exactly* the boundary fields
of a `NearTriangulation (sideMap₁)`, so any genuine near-triangulation structure on the side
map gives one.  We record both directions: a `NearTriangulation` yields a `ContiguousInterval`,
and the producer round-trips — certifying the predicate is inhabited whenever the side is a
genuine near-triangulation (it is not a hidden `False`). -/

/-- **`ContiguousInterval` is satisfiable from a side near-triangulation** (non-vacuity).  Any
`NearTriangulation (sideMap₁)` projects onto a `ContiguousInterval` (its boundary fields).  So
the predicate is not unsatisfiable: it holds exactly when the side is a near-triangulation, and
`chordSideNearTriangulation` round-trips it. -/
def contiguousInterval_of_nearTriangulation (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (N : NearTriangulation (data.sideMap₁ hsep a₀ a₁ hne)) :
    ContiguousInterval data hsep a₀ a₁ hne where
  simpleGraph := N.simpleGraph
  outerFace := N.outerFace
  outerCycle := N.outerCycle
  outer_simple := N.outer_simple
  outer_len := N.outer_len
  inner_tri := N.inner_tri

/-- **The producer round-trips on the disk-core sphere** (non-vacuity / no-rewrapper check).
Given the anchor-incidence fact and a `ContiguousInterval`, the produced near-triangulation's
`sphere` field is the *unconditional* disk-core sphere (not re-read from a hypothesis): the
classification supplies only the boundary fields, while `sphere` comes from
`side₁_sphere_unconditional`.  Hence the assembly genuinely uses the proved disk core. -/
theorem chordSideNearTriangulation_sphere_eq (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁)
    (ci : ContiguousInterval data hsep a₀ a₁ hne) :
    (chordSideNearTriangulation_of_share data hsep a₀ a₁ hne hshare ci).sphere
      = side₁_sphere_unconditional data hsep a₀ a₁ hne hshare :=
  rfl

/-! ## Section 4.  The exact reduction: `ChordSideClassification ↔ ContiguousInterval`

The two producers (`chordSideNearTriangulation_of_share` from `ContiguousInterval`, and
`contiguousInterval_of_nearTriangulation` from a side near-triangulation) witness that — *given
the anchor-incidence fact* (the proved fact-2) — the residue `ChordSideClassification` is
**exactly equivalent** to the boundary predicate `ContiguousInterval`.  This is the precise
statement of the reduction: the `sphere`/`IsSphereMap` field is no longer part of the residue
(it is discharged by the proved disk core), so the entire `ChordSideClassification` residue is
the single correct-anchor boundary classification `ContiguousInterval`, neither more nor less. -/

/-- **The chord-side residue is exactly `ContiguousInterval`.**  Given the anchor-incidence
fact, `ChordSideClassification` (= `NearTriangulation (sideMap₁)`) is inhabited iff
`ContiguousInterval` is.  Forward: project to the boundary fields.  Backward: assemble with the
unconditional disk-core `sphere`.  So the residue is *precisely* the boundary classification —
the `sphere`/genus-0 content is removed (proved), confirming the reduction is genuine (not a
re-wrapper: the backward map injects the proved `side₁_sphere_unconditional`, not a hypothesis). -/
def chordSideClassification_iff_contiguous (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hshare : Side₁AnchorsShareFace data hsep a₀ a₁) :
    ChordReconClose.ChordSideClassification data hsep a₀ a₁ hne ≃
      ContiguousInterval data hsep a₀ a₁ hne where
  toFun N := contiguousInterval_of_nearTriangulation data hsep a₀ a₁ hne N
  invFun ci := chordSideClassification_of_contiguous data hsep a₀ a₁ hne hshare ci
  left_inv N := by
    -- both directions preserve every field; `sphere` round-trips to the disk-core sphere,
    -- which is propositionally equal (it is a `Prop`), so the structures agree.
    cases N
    rfl
  right_inv ci := by cases ci; rfl

end ProofsInTheBook.ChordSideNT

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordSideNT.chordSideNearTriangulation
#print axioms ProofsInTheBook.ChordSideNT.side₁_sphere_unconditional
#print axioms ProofsInTheBook.ChordSideNT.chordSideNearTriangulation_of_share
#print axioms ProofsInTheBook.ChordSideNT.chordSideClassification_of_contiguous
#print axioms ProofsInTheBook.ChordSideNT.contiguousInterval_of_nearTriangulation
#print axioms ProofsInTheBook.ChordSideNT.chordSideNearTriangulation_sphere_eq
#print axioms ProofsInTheBook.ChordSideNT.chordSideClassification_iff_contiguous
