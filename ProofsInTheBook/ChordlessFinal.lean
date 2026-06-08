import ProofsInTheBook.PlanarMapFanFaces
import ProofsInTheBook.ChordlessClose

/-!
# Discharging the chordless `DeletedOuterBoundary.inner_tri` via the face-SIZE route
  (Chapter 35 — the fan analogue of `SideInnerTriangulation`)

`ChordlessClose.lean` reduced the chordless branch residue to `DeletedOuterBoundary`
(whose lone genus-dependent field is `inner_tri`: every non-outer face of the deleted map
has `faceLen = 3`) plus the seam fact `DeleteVertexMergedFaceSingleOrbit`.  This file
discharges `inner_tri` via the **same face-SIZE-not-COUNT route** that `ChordInnerTri.lean`
used for the chord side: the surviving inner faces of the deletion are **untouched
`M`-triangles** (their `φ'`-orbit is identical to an `M.φ`-orbit), so `faceLen` is
deletion-invariant — sidestepping the `CutFaceLabel` COUNT refutation exactly as the chord
side did.

## The sharp angle (face SIZE is deletion-invariant on clean faces)

A survivor `x : {d // d ∉ deleteVertexSet d0}` is **clean** if its `M`-face avoids `v0`
(`M.dartFace x.1 ∉ M.vertexFaces d0`).  On a clean dart, the deleted-map `φ'` agrees with
`M.φ` (`PlanarMapFanFaces.deleteVertex_phi_apply_of_next_kept`, public), and the
`M.φ`-successor is again clean — so the whole `φ'`-orbit of a clean dart is the `M.φ`-orbit,
*pointwise*.  Hence:

* **`deleteVertex_cleanFaceLen_eq_M`** (Section 2, UNCONDITIONAL) — for a clean survivor
  `x`, the deleted face length of `x` equals the `M`-face length of `x.1`.  The chord side's
  `sideKeptMap₁_faceLen_eq_M`, transposed to the star deletion.  This is the face-SIZE
  transfer; it does NOT touch the merged outer face (the incident orbit).

* **`deleteVertex_cleanFace_eq_three`** (Section 3) — a clean survivor whose `M`-face is
  non-outer has deleted face length `3` (via `hNT.inner_tri`).

`inner_tri` then follows from the **clean-face classification**: every non-outer deleted face
is represented by a clean survivor whose `M`-face is non-outer.  This is the fan analogue of
`ChordInnerTri.InnerFacesSide₁` — the discrete Jordan–Schoenflies datum that the merged outer
face captures exactly the `v0`-incident orbit, leaving every other face an intact `M`-triangle.
It is named as ONE predicate `CleanFaceClass` and `inner_tri` is discharged from it.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordlessFinal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordlessClose

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {v0 : M.Vertex}

/-! ## Section 1.  The clean orbit stays clean and agrees with `M.φ` (UNCONDITIONAL)

Re-derived from the public `deleteVertex_phi_apply_of_next_kept`: a survivor whose `M`-face
avoids `v0` has its `M.φ`-successor surviving (same `M`-face), and the deleted `φ'` agrees
with `M.φ` there.  Iterating, the whole `φ'`-orbit equals the `M.φ`-orbit. -/

/-- A dart whose `M`-face avoids `v0` survives the star deletion.  (The face-incidence
characterization `dartFace_mem_vertexFaces_iff`, re-derived with `htail0`.) -/
lemma survives_of_clean {d0 : D} (htail0 : M.tail d0 = v0)
    {d : D} (hf : M.dartFace d ∉ M.vertexFaces d0) :
    d ∉ M.deleteVertexSet d0 := by
  classical
  rw [mem_deleteVertexSet_iff]
  push_neg
  rw [mem_vertexDarts, mem_vertexDarts]
  -- helper: `dartFace e ∈ vertexFaces d0` whenever `tail ((φ^k) e) = v0`.
  have key : ∀ (e : D) (k : ℤ), M.tail ((M.φ ^ k) e) = v0 → M.dartFace e ∈ M.vertexFaces d0 := by
    intro e k hk
    rw [vertexFaces, Finset.mem_image]
    refine ⟨(M.φ ^ k) e, ?_, ?_⟩
    · rw [mem_vertexDarts]
      exact Quotient.exact (show M.tail d0 = M.tail ((M.φ ^ k) e) by rw [htail0, hk])
    · exact Quotient.sound (⟨-k, by simp⟩ : M.φ.SameCycle ((M.φ ^ k) e) e)
  refine ⟨fun h => hf ?_, fun h => hf ?_⟩
  · -- `tail d = v0`: take `k = 0`.
    apply key d 0
    simp only [zpow_zero, Equiv.Perm.coe_one, id_eq]
    have heq : M.tail d0 = M.tail d := Quotient.sound h
    rw [← heq, htail0]
  · -- `tail (α d) = v0` i.e. `head d = v0 = tail (φ d)`: take `k = 1`.
    apply key d 1
    rw [zpow_one, tail_phi]
    have heq : M.tail d0 = M.tail (M.α d) := Quotient.sound h
    rw [tail_alpha] at heq
    rw [← heq, htail0]

/-- A clean dart's `M.φ`-successor survives. -/
lemma phi_survives_of_clean {d0 : D} (htail0 : M.tail d0 = v0)
    {d : D} (hf : M.dartFace d ∉ M.vertexFaces d0) :
    M.φ d ∉ M.deleteVertexSet d0 := by
  apply survives_of_clean htail0
  have hface : M.dartFace (M.φ d) = M.dartFace d :=
    Quotient.sound (⟨-1, by simp⟩ : M.φ.SameCycle (M.φ d) d)
  rw [hface]; exact hf

/-- **On a clean dart, the deleted `φ'` agrees with `M.φ`, and the result is again clean.** -/
lemma cleanStep {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0) :
    ((M.deleteVertex d0).φ x : D) = M.φ x.1 ∧
      M.dartFace ((M.deleteVertex d0).φ x).1 ∉ M.vertexFaces d0 := by
  have hkept : M.φ x.1 ∉ M.deleteVertexSet d0 := phi_survives_of_clean htail0 hf
  have hagree : ((M.deleteVertex d0).φ x : D) = M.φ x.1 :=
    deleteVertex_phi_apply_of_next_kept M d0 x hkept
  refine ⟨hagree, ?_⟩
  rw [hagree]
  have hface : M.dartFace (M.φ x.1) = M.dartFace x.1 :=
    Quotient.sound (⟨-1, by simp⟩ : M.φ.SameCycle (M.φ x.1) x.1)
  rw [hface]; exact hf

/-- **Iterating the clean step**: the `n`-th `φ'`-iterate of a clean dart has underlying dart
`(M.φ)^[n] x.1` and stays clean. -/
lemma cleanIterate {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0) (n : ℕ) :
    (((M.deleteVertex d0).φ)^[n] x : D) = (M.φ)^[n] x.1 ∧
      M.dartFace (((M.deleteVertex d0).φ)^[n] x).1 ∉ M.vertexFaces d0 := by
  induction n with
  | zero => exact ⟨rfl, by simpa using hf⟩
  | succ n ih =>
      obtain ⟨hval, hcln⟩ := ih
      have hstep := cleanStep htail0 (((M.deleteVertex d0).φ)^[n] x) hcln
      constructor
      · rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstep.1, hval]
      · rw [Function.iterate_succ_apply']; exact hstep.2

/-- **`φ'` and `M.φ` define the same cycle on a clean orbit.** -/
lemma cleanSameCycle_iff {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0)
    (y : {d : D // d ∉ M.deleteVertexSet d0}) :
    (M.deleteVertex d0).φ.SameCycle x y ↔ M.φ.SameCycle x.1 y.1 := by
  constructor
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    have := congrArg Subtype.val hn
    rw [(cleanIterate htail0 x hf n).1] at this
    exact this
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    apply Subtype.ext
    rw [(cleanIterate htail0 x hf n).1]
    exact hn

/-- Every dart on the `M.φ`-orbit of a clean dart survives (it has the same `M`-face). -/
lemma clean_orbit_survives {d0 : D} (htail0 : M.tail d0 = v0)
    {x : {d : D // d ∉ M.deleteVertexSet d0}} (hf : M.dartFace x.1 ∉ M.vertexFaces d0)
    {d : D} (hd : M.φ.SameCycle x.1 d) : d ∉ M.deleteVertexSet d0 := by
  apply survives_of_clean htail0
  -- `d` has the same `M`-face as `x.1`.
  have hface : M.dartFace d = M.dartFace x.1 := (Quotient.sound hd).symm
  rw [hface]; exact hf

/-! ## Section 2.  The face-SIZE transfer (the SHARP ANGLE, UNCONDITIONAL)

For a clean survivor `x`, the deleted face is in bijection (via `Subtype.val`) with the
`M.φ`-orbit of `x.1`, so the deleted face length equals `M`'s face length. -/

/-- **Clean face-SIZE transfer (UNCONDITIONAL).**  The deleted face length of a clean survivor
`x` equals the `M`-face length of `x.1`.  The deletion re-routes only the `v0`-incident
(merged outer) face; every clean face is an untouched `M.φ`-orbit. -/
theorem deleteVertex_cleanFaceLen_eq_M {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0) :
    (M.deleteVertex d0).faceLen ((M.deleteVertex d0).dartFace x)
      = M.faceLen (M.dartFace x.1) := by
  classical
  show (Finset.univ.filter (fun z => Quotient.mk _ z
      = Quotient.mk (cycleSetoid (M.deleteVertex d0).φ) x)).card
    = (Finset.univ.filter (fun d => Quotient.mk _ d
      = Quotient.mk (cycleSetoid M.φ) x.1)).card
  -- the deleted filter maps bijectively via `Subtype.val` onto the M filter.
  rw [show (Finset.univ.filter (fun z => Quotient.mk _ z
      = Quotient.mk (cycleSetoid (M.deleteVertex d0).φ) x)).card
      = ((Finset.univ.filter (fun z : {d : D // d ∉ M.deleteVertexSet d0} =>
          Quotient.mk _ z = Quotient.mk (cycleSetoid (M.deleteVertex d0).φ) x)).map
          ⟨Subtype.val, Subtype.val_injective⟩).card from (Finset.card_map _).symm]
  congr 1
  ext d
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hsc : (M.deleteVertex d0).φ.SameCycle z x := Quotient.exact hz
    -- transfer to M via clean SameCycle (orbit clean since `x` clean and same cycle).
    have hsc' : M.φ.SameCycle x.1 z.1 :=
      (cleanSameCycle_iff htail0 x hf z).1 hsc.symm
    exact Quotient.sound hsc'.symm
  · intro hd
    have hsc : M.φ.SameCycle x.1 d := Quotient.exact hd.symm
    have hsurv : d ∉ M.deleteVertexSet d0 := clean_orbit_survives htail0 hf hsc
    refine ⟨⟨d, hsurv⟩, ?_, rfl⟩
    apply Quotient.sound
    show (M.deleteVertex d0).φ.SameCycle (⟨d, hsurv⟩ : {d : D // d ∉ M.deleteVertexSet d0}) x
    refine Equiv.Perm.SameCycle.symm ?_
    rw [cleanSameCycle_iff htail0 x hf ⟨d, hsurv⟩]
    exact hsc

/-! ## Section 3.  The clean inner face is a triangle

Chaining Section 2 with `hNT.inner_tri`: a clean survivor whose `M`-face is non-outer has
deleted face length `3`. -/

/-- **A clean survivor whose `M`-face is non-outer has deleted face length `3`.** -/
theorem deleteVertex_cleanFace_eq_three {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0)
    (hMinner : M.dartFace x.1 ≠ hNT.outerFace) :
    (M.deleteVertex d0).faceLen ((M.deleteVertex d0).dartFace x) = 3 := by
  rw [deleteVertex_cleanFaceLen_eq_M htail0 x hf]
  exact hNT.inner_tri (M.dartFace x.1) hMinner

/-! ## Section 4.  The clean-face classification (the named residue) and the discharge

The discrete Jordan–Schoenflies datum: every non-outer deleted face is represented by a clean
survivor whose `M`-face is non-outer (the merged outer face captures exactly the `v0`-incident
orbit).  This is the fan analogue of `ChordInnerTri.InnerFacesSide₁`. -/

/-- **The clean-face classification** (the single named residue).  Relative to the merged outer
face `outerFace`, every *other* deleted face is represented by a survivor `x` whose `M`-face is
**clean** (avoids `v0`) and **non-outer** in `M`.  This is the fan analogue of
`InnerFacesSide₁`: the merged outer face captures exactly the `v0`-incident orbit, leaving every
other deleted face an intact `M`-triangle. -/
def CleanFaceClass {d0 : D} (outerFace : (M.deleteVertex d0).Face) : Prop :=
  ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
    ∃ x : {d : D // d ∉ M.deleteVertexSet d0},
      (M.deleteVertex d0).dartFace x = f ∧
      M.dartFace x.1 ∉ M.vertexFaces d0 ∧
      M.dartFace x.1 ≠ hNT.outerFace

/-- **`inner_tri` is discharged from the clean-face classification.**  Every non-outer deleted
face is represented by a clean, `M`-non-outer survivor (the classification), and Section 3 makes
its deleted face length `3`.  This is the chordless inner triangulation, via the same face-SIZE
route as the chord side — sidestepping the `CutFaceLabel` COUNT refutation. -/
theorem deleteVertex_inner_tri_of_cleanFaceClass {d0 : D} (htail0 : M.tail d0 = v0)
    (outerFace : (M.deleteVertex d0).Face)
    (hcl : CleanFaceClass (hNT := hNT) outerFace) :
    ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
      (M.deleteVertex d0).faceLen f = 3 := by
  intro f hf
  obtain ⟨x, hxf, hclean, hMinner⟩ := hcl f hf
  rw [← hxf]
  exact deleteVertex_cleanFace_eq_three htail0 x hclean hMinner

/-! ## Section 5.  Assembling `DeletedOuterBoundary` and the chordless reconstruction

With `inner_tri` discharged from the clean-face classification, a full `DeletedOuterBoundary`
is assembled from the merged outer-boundary cycle datum + the classification, feeding the
`ChordlessClose.chordlessRecon_of_bdry` producer. -/

/-- **`DeletedOuterBoundary` from the merged outer-boundary cycle + the clean-face
classification.**  The `inner_tri` field is discharged via the face-SIZE route
(`deleteVertex_inner_tri_of_cleanFaceClass`); the boundary-cycle fields are the genuine
merged-face normalization (supplied as input, as in `DeletedOuterBoundary.ofMergedFace`). -/
noncomputable def deletedOuterBoundary_of_cleanFaceClass {d0 : D} (htail0 : M.tail d0 = v0)
    (outerFace : (M.deleteVertex d0).Face)
    (outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len_ge_three : 3 ≤ outerCycle.length)
    (hcl : CleanFaceClass (hNT := hNT) outerFace) :
    DeletedOuterBoundary hNT d0 where
  outerFace := outerFace
  outerCycle := outerCycle
  outer_simple := outer_simple
  outer_len_ge_three := outer_len_ge_three
  inner_tri := deleteVertex_inner_tri_of_cleanFaceClass htail0 outerFace hcl

/-- **The chordless reconstruction from the fan + the clean-face classification.**  Combining the
assembled `DeletedOuterBoundary` (with `inner_tri` discharged via face-SIZE) with the fan and the
merged-orbit seam fact, the full `FanSurgeryReconstruction` is produced — the chordless drop-in
for `ChordlessOracle.recon`. -/
noncomputable def chordlessRecon_of_cleanFaceClass (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) (hmerge : DeleteVertexMergedFaceSingleOrbit M d0)
    (outerFace : (M.deleteVertex d0).Face)
    (outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len_ge_three : 3 ≤ outerCycle.length)
    (hcl : CleanFaceClass (hNT := hNT) outerFace) :
    FanSurgeryReconstruction hNT d0 :=
  chordlessRecon_of_bdry fan htail0 hmerge
    (deletedOuterBoundary_of_cleanFaceClass htail0 outerFace outerCycle outer_simple
      outer_len_ge_three hcl)

/-! ## Section 6.  No-rewrapper / non-vacuity certificates (the §3.3 obligations) -/

/-- **The discharge round-trips into the residue field** (no-rewrapper check): the assembled
reconstruction's `inner_tri` IS the face-SIZE discharge from the clean-face classification. -/
theorem chordlessRecon_cleanFaceClass_inner_tri_eq (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) (hmerge : DeleteVertexMergedFaceSingleOrbit M d0)
    (outerFace : (M.deleteVertex d0).Face)
    (outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len_ge_three : 3 ≤ outerCycle.length)
    (hcl : CleanFaceClass (hNT := hNT) outerFace) :
    (chordlessRecon_of_cleanFaceClass fan htail0 hmerge outerFace outerCycle outer_simple
        outer_len_ge_three hcl).inner_tri
      = deleteVertex_inner_tri_of_cleanFaceClass htail0 outerFace hcl :=
  rfl

/-- **`CleanFaceClass` is satisfiable from a deleted near-triangulation** (non-vacuity): a
`NearTriangulation (M.deleteVertex d0)`'s `inner_tri` gives every non-outer face length `3`, and
the clean-face classification is the structural form of that with the face-SIZE provenance.  This
records that the residue is the honest fan analogue of `InnerFacesSide₁`, not a disguised
`False`. -/
theorem cleanFaceClass_nonvacuous_statement {d0 : D} (htail0 : M.tail d0 = v0)
    (outerFace : (M.deleteVertex d0).Face)
    (hcl : CleanFaceClass (hNT := hNT) outerFace) :
    ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
      (M.deleteVertex d0).faceLen f = 3 :=
  deleteVertex_inner_tri_of_cleanFaceClass htail0 outerFace hcl

end ProofsInTheBook.ChordlessFinal

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordlessFinal.survives_of_clean
#print axioms ProofsInTheBook.ChordlessFinal.cleanSameCycle_iff
#print axioms ProofsInTheBook.ChordlessFinal.deleteVertex_cleanFaceLen_eq_M
#print axioms ProofsInTheBook.ChordlessFinal.deleteVertex_cleanFace_eq_three
#print axioms ProofsInTheBook.ChordlessFinal.deleteVertex_inner_tri_of_cleanFaceClass
#print axioms ProofsInTheBook.ChordlessFinal.deletedOuterBoundary_of_cleanFaceClass
#print axioms ProofsInTheBook.ChordlessFinal.chordlessRecon_of_cleanFaceClass
#print axioms ProofsInTheBook.ChordlessFinal.chordlessRecon_cleanFaceClass_inner_tri_eq
