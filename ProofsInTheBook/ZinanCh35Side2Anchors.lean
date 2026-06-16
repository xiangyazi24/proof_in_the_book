import ProofsInTheBook.ChordAnchorInst
import ProofsInTheBook.ChordDisk

/-!
# Chapter 35 — side-2 chord anchors + `Side₂AnchorsShareFace` (the missing side-2 producer)

The side-1 mirror `side₁AnchorsShareFace_canonical` exists; the side-2 analogue had no producer.
This file ports it: the `face₂`-dart layer (built around the reverse chord dart `M.α data.dart`)
and the canonical side-2 anchors, yielding `side₂AnchorsShareFace_canonical`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35Side2Anchors

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u
variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ### Step 1: face₂ is a triangle (mirror of face₁_isFaceTriangle via the α-dart). -/
theorem face₂_isFaceTriangle (data : hNT.ChordSplitData u v) :
    M.IsFaceTriangle (M.α data.dart) (M.φ (M.α data.dart)) (M.φ (M.φ (M.α data.dart))) :=
  hNT.inner_face_isFaceTriangle (hNT.chordDart_alpha_not_outer data.chord)

/-! ### Step 2: the two non-chord darts of face₂ are kept & distinct. -/
theorem face₂_phi_dart_kept (data : hNT.ChordSplitData u v)
    (hd1 : M.φ (M.α data.dart) ≠ M.α data.dart) :
    M.φ (M.α data.dart) ∉ data.keptDel₂ := by
  classical
  rw [data.mem_keptDel₂_iff]
  refine ⟨Or.inl ?_, by simpa using hd1⟩
  show M.dartFace (M.φ (M.α data.dart)) ∈ data.side₂
  rw [M.dartFace_phi]; exact data.face₂_mem_side₂

theorem face₂_phi_phi_dart_kept (data : hNT.ChordSplitData u v)
    (hd2 : M.φ (M.φ (M.α data.dart)) ≠ M.α data.dart) :
    M.φ (M.φ (M.α data.dart)) ∉ data.keptDel₂ := by
  classical
  rw [data.mem_keptDel₂_iff]
  refine ⟨Or.inl ?_, by simpa using hd2⟩
  show M.dartFace (M.φ (M.φ (M.α data.dart))) ∈ data.side₂
  rw [M.dartFace_phi, M.dartFace_phi]; exact data.face₂_mem_side₂

theorem face₂_kept_darts_distinct (data : hNT.ChordSplitData u v) :
    M.φ (M.α data.dart) ≠ M.φ (M.φ (M.α data.dart)) := by
  intro h
  have heq : M.α data.dart = M.φ (M.α data.dart) := M.φ.injective h
  exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph (M.α data.dart)) heq.symm

theorem face₂_two_kept_darts (data : hNT.ChordSplitData u v) :
    (M.φ (M.α data.dart) ∉ data.keptDel₂) ∧
      (M.φ (M.φ (M.α data.dart)) ∉ data.keptDel₂) ∧
      M.φ (M.α data.dart) ≠ M.φ (M.φ (M.α data.dart)) ∧
      M.dartFace (M.φ (M.α data.dart)) = data.face₂ ∧
      M.dartFace (M.φ (M.φ (M.α data.dart))) = data.face₂ := by
  obtain ⟨_, h12, h20⟩ := face₂_isFaceTriangle data
  have hd1 : M.φ (M.α data.dart) ≠ M.α data.dart := by
    intro he
    exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph (M.α data.dart)) he
  have hd2 : M.φ (M.φ (M.α data.dart)) ≠ M.α data.dart := by
    intro he
    have hstep : M.φ (M.φ (M.φ (M.α data.dart))) = M.φ (M.α data.dart) := congrArg M.φ he
    have : M.α data.dart = M.φ (M.α data.dart) := h20.symm.trans hstep
    exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph (M.α data.dart)) this.symm
  refine ⟨face₂_phi_dart_kept data hd1, face₂_phi_phi_dart_kept data hd2,
    face₂_kept_darts_distinct data, ?_, ?_⟩
  · show M.dartFace (M.φ (M.α data.dart)) = M.dartFace (M.α data.dart); rw [M.dartFace_phi]
  · show M.dartFace (M.φ (M.φ (M.α data.dart))) = M.dartFace (M.α data.dart)
    rw [M.dartFace_phi, M.dartFace_phi]

/-! ### Step 3: the side-2 face₂ darts and canonical anchors. -/
noncomputable def face₂Dart₁ (data : hNT.ChordSplitData u v) :
    {d : D // d ∉ data.keptDel₂} :=
  ⟨M.φ (M.α data.dart), (face₂_two_kept_darts data).1⟩

noncomputable def face₂Dart₂ (data : hNT.ChordSplitData u v) :
    {d : D // d ∉ data.keptDel₂} :=
  ⟨M.φ (M.φ (M.α data.dart)), (face₂_two_kept_darts data).2.1⟩

noncomputable def side₂Anchor₀ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    {d : D // d ∉ data.keptDel₂} :=
  (data.sideSigma₂).symm
    (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂ (face₂Dart₂ data))

noncomputable def side₂Anchor₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    {d : D // d ∉ data.keptDel₂} :=
  (data.sideSigma₂).symm (face₂Dart₁ data)

@[simp] theorem sideSigma₂_side₂Anchor₀ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideSigma₂ (side₂Anchor₀ data hsep)
      = keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂ (face₂Dart₂ data) := by
  rw [side₂Anchor₀, Equiv.apply_symm_apply]

@[simp] theorem sideSigma₂_side₂Anchor₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    data.sideSigma₂ (side₂Anchor₁ data hsep) = face₂Dart₁ data := by
  rw [side₂Anchor₁, Equiv.apply_symm_apply]

/-! ### Step 4: keptPhi d₁ = d₂ on side 2 (the easy filtered step). -/
theorem keptPhi_face₂Dart₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂ (face₂Dart₁ data) = face₂Dart₂ data := by
  classical
  apply Subtype.ext
  show ((data.sideSigma₂ (data.sideAlpha₂ hsep (face₂Dart₁ data))) : D)
    = (face₂Dart₂ data : D)
  have hval : ((data.sideAlpha₂ hsep (face₂Dart₁ data)) : D) = M.α (M.φ (M.α data.dart)) := by
    rw [sideAlpha₂_apply_coe]; rfl
  have hstep : M.σ ((data.sideAlpha₂ hsep (face₂Dart₁ data)) : D)
      = M.φ (M.φ (M.α data.dart)) := by
    rw [hval]
    show M.σ (M.α (M.φ (M.α data.dart))) = (M.σ * M.α) (M.φ (M.α data.dart))
    rw [Equiv.Perm.mul_apply]
  have hkept : M.σ ((data.sideAlpha₂ hsep (face₂Dart₁ data)) : D) ∉ data.keptDel₂ := by
    rw [hstep]; exact (face₂_two_kept_darts data).2.1
  show ((FilteredRotation.filteredRotation M.σ data.keptDel₂
        (data.sideAlpha₂ hsep (face₂Dart₁ data))) : D) = (face₂Dart₂ data : D)
  rw [FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₂
    (data.sideAlpha₂ hsep (face₂Dart₁ data)) hkept, hstep]
  rfl

/-! ### Step 5: same-cycle of the two anchor images. -/
theorem keptPhi_sameCycle_d₁_keptPhi_d₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂).SameCycle
      (face₂Dart₁ data)
      (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂ (face₂Dart₂ data)) := by
  rw [Equiv.Perm.sameCycle_apply_right]
  rw [← keptPhi_face₂Dart₁ data hsep]
  exact (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _))

/-! ### Step 6: the producer. -/
theorem side₂AnchorsShareFace_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ChordDisk.Side₂AnchorsShareFace data hsep
      (side₂Anchor₀ data hsep) (side₂Anchor₁ data hsep) := by
  show (keptPhi (data.sideAlpha₂ hsep) data.sideSigma₂).SameCycle
    (data.sideSigma₂ (side₂Anchor₀ data hsep)) (data.sideSigma₂ (side₂Anchor₁ data hsep))
  rw [sideSigma₂_side₂Anchor₀, sideSigma₂_side₂Anchor₁]
  exact (keptPhi_sameCycle_d₁_keptPhi_d₂ data hsep).symm

end ProofsInTheBook.ZinanCh35Side2Anchors

#print axioms ProofsInTheBook.ZinanCh35Side2Anchors.side₂AnchorsShareFace_canonical
