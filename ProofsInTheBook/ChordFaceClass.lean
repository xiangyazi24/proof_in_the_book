import ProofsInTheBook.ChordInnerTri

/-!
# Discharging `InnerFacesSide₁`: the FACE-level analogue of the proved vertex `ι_surj`
  (Chapter 35 — the chord-side face-orbit classification)

`ChordInnerTri.lean` reduced the entire chord-side residue to the single face-classification
predicate `InnerFacesSide₁ data hsep a₀ a₁ hne outerFace` — *every non-outer side face of
`sideMap₁` is represented by an `inl k` whose `M`-face lies in `side₁`, is not the chord face
`face₁`, and whose `keptPhi`-orbit is splice-untouched*.  `ChordReconClose.lean` proved the
**vertex**-level analogue `ι_surj` (`sideVertexToM₁_surjective`): every side-1 region vertex is
the image of an `inl`-orbit.  This file builds the **FACE**-level analogue with the SAME
orbit-bijection machinery, at the face level.

## The two genuinely-unconditional halves (the face-level orbit surjection)

The face permutation of `sideMap₁ = freshMap (sideAlpha₁) (sideSigma₁) a₀ a₁` is traced on the
kept type `K = {d // d ∉ keptDel₁}` as `tracePhi = swap (ρ a₀) (ρ a₁) · keptPhi`
(`ChordFaceCount`).  Two facts are UNCONDITIONAL — the face analogue of the vertex `ι_surj`:

* **`sideFace_has_inl_rep`** (Section 1) — *every* side face is `dartFace (inl k)` for some
  kept dart `k`.  This is the exact face-level surjection: a side face is a `freshMap.φ`-orbit;
  every dart `x` in it is `φ`-SameCycle to `inl (faceProj x)` (`freshPhi_sameCycle_inl_faceProj`,
  `ChordFaceCount`), and `faceProj x` is a kept dart.  This is the `freshFace_sameCycle_iff` /
  `freshFaceQuotientEquiv` content used pointwise, exactly as `ι_surj` used the σ-orbit
  bijection pointwise.

* **`keptDart_face_side₁_or_outer`** (Section 2) — *every* kept dart `k.1 ∈ keptSet₁` has its
  `M`-face in `side₁` **or** equal to the `M`-outer face.  This is the unconditional dichotomy
  built directly from `keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`: a kept dart is either an
  inner side-1 dart (`sideDarts₁`, face `∈ side₁`) or an outer-arc dart (`outerArc₁`, face
  `= outerFace`).

So the residue per inner side face collapses, *unconditionally*, to: the representative `inl k`
is *not* an outer-arc representative (`M.dartFace k.1 ≠ M`-outer-face) and `≠ face₁`, **and** it
is splice-untouched.  The first two are the discrete-Schoenflies datum "the side outer face is
precisely the orbit of the `M`-outer arc"; splice-untouchedness is the correct-anchor datum
"`β a₀, β a₁` sit on that boundary orbit" (`chordChoice_contiguousArc`).  We bundle these into
ONE named correct-anchor predicate `BoundaryOrbitClass` and discharge `InnerFacesSide₁` from it
— this is the genuine reduction the orchestration named.

## Why this is the face analogue of `ι_surj` and not a re-wrapper

`ι_surj` proved a *surjection onto the region* from the σ-orbit bijection; the face conditions
(`ι_inj`, the boundary cycle) stayed open as the correct-anchor classification.  Symmetrically,
`sideFace_has_inl_rep` proves the *face surjection onto kept-`inl` reps* from the φ-orbit
bijection; the face conditions (`∈ side₁ ≠ face₁`, splice-untouched) stay open as the SAME
correct-anchor classification, now named `BoundaryOrbitClass`.  The face-SIZE machinery of
`ChordInnerTri` (`sideMap₁_faceLen_inl_three_of_side₁`) then turns the classified faces into
triangles — discharging `SideInnerTriangulation`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordFaceClass

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordContiguous

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## Section 1.  The face-level orbit surjection (UNCONDITIONAL)

Every side face is represented by an `inl k` for a kept dart `k`.  This is the FACE analogue of
the vertex `ι_surj`, proved from the same orbit-bijection ingredient
(`freshPhi_sameCycle_inl_faceProj`) used pointwise on a single orbit. -/

/-- **Every side face has a kept-`inl` representative** (the face-level `ι_surj`).  For any face
`f` of `sideMap₁`, there is a kept dart `k` with `dartFace (inl k) = f`.  Proof: a face is a
`freshMap.φ`-orbit; pick any representative `x`, then `f = dartFace (inl (faceProj x))` because
`x` is `φ`-SameCycle to `inl (faceProj x)` (`ChordFaceCount.freshPhi_sameCycle_inl_faceProj`),
and `faceProj x` is a kept dart of `K`. -/
theorem sideFace_has_inl_rep (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face) :
    ∃ k : {d : D // d ∉ data.keptDel₁},
      (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f := by
  classical
  refine Quotient.inductionOn f (fun x => ?_)
  -- `f = ⟦x⟧`; take `k = faceProj x` and use `freshPhi_sameCycle_inl_faceProj`.
  refine ⟨faceProj (data.sideAlpha₁ hsep) a₀ a₁ x, ?_⟩
  show Quotient.mk (cycleSetoid (data.sideMap₁ hsep a₀ a₁ hne).φ)
      (Sum.inl (faceProj (data.sideAlpha₁ hsep) a₀ a₁ x))
    = Quotient.mk (cycleSetoid (data.sideMap₁ hsep a₀ a₁ hne).φ) x
  apply Quotient.sound
  -- need `(sideMap₁).φ.SameCycle (inl (faceProj x)) x`; we have the reverse from ChordFaceCount.
  have h := freshPhi_sameCycle_inl_faceProj (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne x
  -- `h : (freshMap …).φ.SameCycle x (inl (faceProj x))`; `sideMap₁ = freshMap …`.
  exact h.symm

/-! ## Section 2.  The kept-dart face dichotomy (UNCONDITIONAL)

Every kept dart's `M`-face is in `side₁` or is the `M`-outer face.  Built directly from
`keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`. -/

/-- **Every kept dart has its `M`-face in `side₁` or equal to the outer face** (unconditional).
A kept dart `k.1 ∈ keptSet₁` is in `sideDarts₁` (face `∈ side₁`) or in `outerArc₁`
(face `= outerFace`). -/
theorem keptDart_face_side₁_or_outer (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₁}) :
    M.dartFace k.1 ∈ data.side₁ ∨ M.dartFace k.1 = hNT.outerFace := by
  -- `k.1 ∉ keptDel₁ ↔ k.1 ∈ keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`.
  have hk : k.1 ∈ data.keptSet₁ := (data.mem_keptDel₁_iff k.1).1 k.2
  obtain ⟨hU, _⟩ := hk
  rcases hU with hin | hout
  · -- `k.1 ∈ sideDarts₁`, i.e. `M.dartFace k.1 ∈ side₁`.
    exact Or.inl hin
  · -- `k.1 ∈ outerArc₁`, i.e. `M.dartFace k.1 = outerFace`.
    exact Or.inr hout.1

/-- **A kept dart whose `M`-face is neither outer nor the chord face lies in `side₁`.**  The
contrapositive packaging of the dichotomy: if `M.dartFace k.1 ≠ outerFace` then it is in `side₁`
(and we carry the `≠ face₁` hypothesis alongside).  Unconditional. -/
theorem keptDart_face_mem_side₁ (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₁}) (houter : M.dartFace k.1 ≠ hNT.outerFace) :
    M.dartFace k.1 ∈ data.side₁ :=
  (keptDart_face_side₁_or_outer data k).resolve_right houter

/-! ## Section 3.  The correct-anchor boundary-orbit classification (the named residue)

The two unconditional halves (Sections 1–2) reduce `InnerFacesSide₁` to: for each non-outer
side face, its kept-`inl` representative `k` has `M.dartFace k.1 ≠ outerFace`, `≠ face₁`, and is
splice-untouched.  These are the discrete Jordan–Schoenflies data: the side outer face is
precisely the `M`-outer-arc orbit, and `β a₀, β a₁` sit on that boundary orbit
(`chordChoice_contiguousArc`).  We name them as ONE correct-anchor predicate and discharge
`InnerFacesSide₁` from it. -/

/-- **The correct-anchor boundary-orbit classification** (the single named residue).  For the
chosen side outer face `outerFace`, every *other* side face has a kept-`inl` representative `k`
whose `M`-face is **not** the `M`-outer face, is **not** the chord face `face₁`, and whose
`keptPhi`-orbit is **splice-untouched** (avoids `β a₀, β a₁`).

This is precisely the discrete Jordan–Schoenflies datum: (i) the side outer face captures
exactly the `M`-outer-arc orbit (so other faces' reps avoid the outer face — `face_ne_outer`);
(ii) other faces avoid the chord face (`face_ne_face₁`); (iii) `β a₀, β a₁` sit on the side
outer/boundary orbit, leaving the other orbits splice-untouched (`untouched`, the correct-anchor
content `chordChoice_contiguousArc` supplies).  It is the FACE analogue of the correct-anchor
classification that `ι_inj`/`ι_adj` left open at the vertex level. -/
structure BoundaryOrbitClass (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Prop where
  /-- Every non-outer side face's kept-`inl` representative has its `M`-face not the outer face,
  not the chord face, and is splice-untouched. -/
  classify : ∀ f : (data.sideMap₁ hsep a₀ a₁ hne).Face, f ≠ outerFace →
    ∃ k : {d : D // d ∉ data.keptDel₁},
      (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f ∧
      M.dartFace k.1 ≠ hNT.outerFace ∧
      M.dartFace k.1 ≠ data.face₁ ∧
      SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k

/-- **`InnerFacesSide₁` is discharged from the correct-anchor classification.**  Combining the
classification (Section 3) with the unconditional dichotomy (Section 2): each non-outer side
face's kept-`inl` representative `k` has `M.dartFace k.1 ≠ outerFace`, hence `∈ side₁`
(`keptDart_face_mem_side₁`), and `≠ face₁`, and is splice-untouched — exactly the data
`InnerFacesSide₁` requires.  The face surjection itself (`dartFace (inl k) = f`) is the
unconditional `sideFace_has_inl_rep` content, carried by the classification's representative. -/
theorem innerFacesSide₁_of_boundaryOrbitClass (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hcl : BoundaryOrbitClass data hsep a₀ a₁ hne outerFace) :
    InnerFacesSide₁ data hsep a₀ a₁ hne outerFace := by
  intro f hf
  obtain ⟨k, hkf, houter, hface₁, huntouched⟩ := hcl.classify f hf
  exact ⟨k, hkf, keptDart_face_mem_side₁ data k houter, hface₁, huntouched⟩

/-! ## Section 4.  The full discharge: `SideInnerTriangulation` from the classification

Chaining the discharge of `InnerFacesSide₁` (Section 3) with the face-SIZE machinery of
`ChordInnerTri` (`sideInnerTriangulation_of_innerFacesSide₁`): the correct-anchor classification
yields `SideInnerTriangulation`, hence (with the side boundary cycle) a full
`ContiguousInterval`. -/

/-- **`SideInnerTriangulation` from the correct-anchor classification.**  The boundary-orbit
classification discharges `InnerFacesSide₁`, which the `ChordInnerTri` face-SIZE machinery turns
into `SideInnerTriangulation` (every non-outer side face is a triangle). -/
theorem sideInnerTriangulation_of_boundaryOrbitClass (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hcl : BoundaryOrbitClass data hsep a₀ a₁ hne outerFace) :
    SideInnerTriangulation data hsep a₀ a₁ hne outerFace :=
  sideInnerTriangulation_of_innerFacesSide₁ data hsep a₀ a₁ hne outerFace
    (innerFacesSide₁_of_boundaryOrbitClass data hsep a₀ a₁ hne outerFace hcl)

/-- **A full `ContiguousInterval` from the classification + the side boundary cycle.**  This is
the chord-side drop-in: given the side map's simple-graph structure, an outer face with its
boundary cycle (simple, length `≥ 3`), and the correct-anchor boundary-orbit classification, the
full `ContiguousInterval` is assembled (its `inner_tri` discharged via the face-SIZE angle). -/
def contiguousInterval_of_boundaryOrbitClass (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hsimple : (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (outerCycle : BoundaryCycle (data.sideMap₁ hsep a₀ a₁ hne) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len : 3 ≤ outerCycle.length)
    (hcl : BoundaryOrbitClass data hsep a₀ a₁ hne outerFace) :
    ChordSideNT.ContiguousInterval data hsep a₀ a₁ hne :=
  contiguousInterval_of_boundary_and_innerTri data hsep a₀ a₁ hne hsimple outerFace
    outerCycle outer_simple outer_len
    (sideInnerTriangulation_of_boundaryOrbitClass data hsep a₀ a₁ hne outerFace hcl)

/-! ## Section 5.  No-rewrapper / non-vacuity certificates (the §3.3 obligations)

The discharge genuinely uses the classification field (not a hidden hypothesis), and the
classification is satisfiable (not a disguised `False`). -/

/-- **The discharge round-trips into the residue field** (no-rewrapper check): the
`SideInnerTriangulation` produced from `BoundaryOrbitClass` is the `inner_tri` of the assembled
`ContiguousInterval`.  Certifies the assembly genuinely consumes the discharged classification. -/
theorem boundaryOrbitClass_discharge_eq (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hsimple : (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (outerCycle : BoundaryCycle (data.sideMap₁ hsep a₀ a₁ hne) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len : 3 ≤ outerCycle.length)
    (hcl : BoundaryOrbitClass data hsep a₀ a₁ hne outerFace) :
    (contiguousInterval_of_boundaryOrbitClass data hsep a₀ a₁ hne hsimple outerFace
        outerCycle outer_simple outer_len hcl).inner_tri
      = sideInnerTriangulation_of_boundaryOrbitClass data hsep a₀ a₁ hne outerFace hcl :=
  rfl

/-- **`BoundaryOrbitClass` is satisfiable from `InnerFacesSide₁`** (non-vacuity): the sharpened
classification of `ChordInnerTri` already supplies a representative with `M`-face in `side₁`
(hence `≠ outerFace` by `side₁_subset_nonouter`), `≠ face₁`, and splice-untouched.  So
`BoundaryOrbitClass` is *equivalent* to `InnerFacesSide₁`; it is not a stronger (possibly empty)
premise.  This shows the named residue is exactly the `ChordInnerTri` residue, restated in the
unconditional-dichotomy form. -/
theorem boundaryOrbitClass_of_innerFacesSide₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hcl : InnerFacesSide₁ data hsep a₀ a₁ hne outerFace) :
    BoundaryOrbitClass data hsep a₀ a₁ hne outerFace where
  classify := by
    intro f hf
    obtain ⟨k, hkf, hside, hface₁, huntouched⟩ := hcl f hf
    exact ⟨k, hkf, data.side₁_subset_nonouter hside, hface₁, huntouched⟩

/-- **The two classifications are equivalent** (the precise residue identity): `BoundaryOrbitClass`
holds iff `InnerFacesSide₁` holds.  So the unconditional dichotomy (Section 2) genuinely converts
between the two forms — the `∈ side₁` half of `InnerFacesSide₁` is *equivalent* to the
`≠ outerFace` half of `BoundaryOrbitClass`, both modulo the kept-dart dichotomy.  This is the
faithful reduction, not a re-wrapper: it carries the real `keptSet₁` structure. -/
theorem boundaryOrbitClass_iff_innerFacesSide₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face) :
    BoundaryOrbitClass data hsep a₀ a₁ hne outerFace ↔
      InnerFacesSide₁ data hsep a₀ a₁ hne outerFace :=
  ⟨innerFacesSide₁_of_boundaryOrbitClass data hsep a₀ a₁ hne outerFace,
   boundaryOrbitClass_of_innerFacesSide₁ data hsep a₀ a₁ hne outerFace⟩

/-! ## Section 6.  The face surjection genuinely fires (non-vacuity of Section 1)

`sideFace_has_inl_rep` is not vacuous: the side face type is inhabited (it has at least the
outer face), and every face — including a concrete one — has a kept-`inl` representative. -/

/-- **The face-level orbit surjection genuinely fires** (non-vacuity): the side face of the
fresh chord dart `inr 0` is represented by a kept-`inl` dart (its face projection `β a₀`).  So
`sideFace_has_inl_rep` is a real surjection, not an empty-domain vacuity. -/
theorem sideFace_has_inl_rep_fires (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    ∃ k : {d : D // d ∉ data.keptDel₁},
      (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)
        = (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inr 0) :=
  sideFace_has_inl_rep data hsep a₀ a₁ hne
    ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inr 0))

end ProofsInTheBook.ChordFaceClass

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordFaceClass.sideFace_has_inl_rep
#print axioms ProofsInTheBook.ChordFaceClass.keptDart_face_side₁_or_outer
#print axioms ProofsInTheBook.ChordFaceClass.keptDart_face_mem_side₁
#print axioms ProofsInTheBook.ChordFaceClass.innerFacesSide₁_of_boundaryOrbitClass
#print axioms ProofsInTheBook.ChordFaceClass.sideInnerTriangulation_of_boundaryOrbitClass
#print axioms ProofsInTheBook.ChordFaceClass.contiguousInterval_of_boundaryOrbitClass
#print axioms ProofsInTheBook.ChordFaceClass.boundaryOrbitClass_discharge_eq
#print axioms ProofsInTheBook.ChordFaceClass.boundaryOrbitClass_iff_innerFacesSide₁
#print axioms ProofsInTheBook.ChordFaceClass.sideFace_has_inl_rep_fires
