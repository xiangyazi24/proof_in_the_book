import ProofsInTheBook.ZinanCh35Hclass
import ProofsInTheBook.PlanarMapDeletedBoundary

/-!
# The Chapter 35 side-1 outer-trace supplier (`Side₁OuterTraceData`)

`ZinanCh35Hclass.lean` assembled the master per-face classifier `side1_hclass_canonical` and the
final assembler `contiguousInterval_canonical`, both consuming the **input bundle**
`Side₁OuterTraceData data hsep`.  This file is the *supplier*: it constructs that bundle for the
canonical side-1 anchors, closing the `ContiguousInterval` chain modulo the genuinely-planar
Jordan/Schoenflies residues (which — per the repo's own design and the way `NearTriangulation`
itself *stores* its `outerCycle`/`outer_simple`/`outer_len` as primitive inputs — are NOT
derivable from the abstract `CombMap`).

## What is DERIVED here (not taken as input)

* `outerFace := S.dartFace (Sum.inr 1)` — the design's pin "the fresh chord dart `inr 1` closes
  the side outer boundary".  With this choice `chord1_is_outer` is `rfl`.
* `face₁_not_outer` : `S.dartFace (inl face₁Dart₁) ≠ S.dartFace (inr 1)`.  Via brick 3
  (`side₁_chord0_face_eq_face₁_canonical`: `S.dartFace (inr 0) = S.dartFace (inl face₁Dart₁)`)
  this is exactly `S.dartFace (inr 0) ≠ S.dartFace (inr 1)`, which by
  `ChordBoundaryOrbit.chordOrbits_eq_iff_tracePhi` is `¬ τ.SameCycle (β a₀) (β a₁)`.  We PROVE
  this splice-split fact unconditionally from the proved canonical share-face datum
  `side₁AnchorsShareFace_canonical` (the two chord predecessors lie on one kept face) and the
  general transposition-split lemma `notSameCycle_swap_mul_left_of_sameCycle`: multiplying a
  permutation on the left by the transposition of two of its same-cycle points splits that cycle
  so the two points no longer share a cycle.  (This is the element-level content of the proven
  `+1` branch `ChordFaceCount.freshMap_F_same_face`.)

## What is taken as INPUT (the genuine Jordan-curve / discrete-Schoenflies residues)

The boundary cycle of the *side* map (a `freshMap`) needs the same kind of planar input that
`NearTriangulation` and `PlanarMapDeletedBoundary.DeletedOuterBoundary.ofMergedFace` take as
data: the cyclic-list `arcSplit` Jordan-pairing, the vertex-simplicity, the length `≥ 3`, and the
inner-rep-avoidance residue `InnerRepsAvoidBoundary`.  The orbit-algebraic boundary-cycle fields
(`NormalizedCyclicDartList`, `consecutive_phi`, `consecutive_vertex`, `vertices_eq`, `edges_eq`)
are discharged from `CombMap.boundaryCycleOfFace` (the `φ`-iterate calculus of the side map).
The side-map simplicity `hsimple` is likewise an input here (as it is for every other
`ContiguousInterval` assembler in the repo).

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterTrace

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordFaceClass
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordSigmaContig
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35Hclass

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

/-! ## Section 1.  A general transposition-split lemma

If `p.SameCycle a b` and `a ≠ b`, then `Equiv.swap a b * p` (the transposition applied on the
**left**) no longer has `a, b` in one cycle.  This is the element-level form of the cycle-count
`+1` split. -/

section PermSplit

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- **Right-multiplication split.**  If `a ≠ b` and `a, b` are in the same `p`-cycle, then
`p * swap a b` does NOT have `a, b` in one cycle.  (The `same`-cycle branch of the dichotomy:
the swap splits the shared cycle.) -/
theorem notSameCycle_mul_swap_right_of_sameCycle (p : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hsc : p.SameCycle a b) :
    ¬ (p * Equiv.swap a b).SameCycle a b := by
  intro hqsc
  -- If both `p` and `p * swap` had `a, b` same-cycle, the cycle counts coincide,
  -- contradicting `numCycles_mul_swap_ne`.
  have hq_le_p : numCycles (p * Equiv.swap a b) ≤ numCycles p := by
    have h := PermTranspositionCycleCount.numCycles_le_mul_swap_of_sameCycle
      (p * Equiv.swap a b) hqsc
    simpa [mul_assoc] using h
  have hp_le_q : numCycles p ≤ numCycles (p * Equiv.swap a b) :=
    PermTranspositionCycleCount.numCycles_le_mul_swap_of_sameCycle p hsc
  exact PermTranspositionCycleCount.numCycles_mul_swap_ne p hab
    (le_antisymm hq_le_p hp_le_q)

/-- **Left-multiplication split.**  If `a ≠ b` and `a, b` are in the same `p`-cycle, then
`swap a b * p` does NOT have `a, b` in one cycle.  Reduced to the right-multiplication split by
conjugation with `swap a b` (which fixes the cycle structure and swaps `a ↔ b`). -/
theorem notSameCycle_swap_mul_left_of_sameCycle (p : Equiv.Perm D) {a b : D}
    (hab : a ≠ b) (hsc : p.SameCycle a b) :
    ¬ (Equiv.swap a b * p).SameCycle a b := by
  intro hsc'
  -- Conjugating `(swap a b * p).SameCycle a b` by `g := swap a b`:
  -- `(swap·(swap·p)·swap⁻¹).SameCycle (swap a)(swap b)`, and
  -- `swap·(swap·p)·swap⁻¹ = p·swap⁻¹ = p·swap`, `swap a = b`, `swap b = a`.
  apply notSameCycle_mul_swap_right_of_sameCycle p hab hsc
  have h2 := hsc'.conj (g := Equiv.swap a b)
  -- normalise the conjugate permutation and the two swapped endpoints.
  have hperm : Equiv.swap a b * (Equiv.swap a b * p) * (Equiv.swap a b)⁻¹
      = p * Equiv.swap a b := by
    rw [← mul_assoc, Equiv.swap_mul_self, one_mul, Equiv.swap_inv]
  rw [hperm, Equiv.swap_apply_left, Equiv.swap_apply_right] at h2
  exact h2.symm

end PermSplit

/-! ## Section 2.  The splice-split fact for the canonical anchors

`¬ τ.SameCycle (β a₀) (β a₁)`, the two chord-incident orbits are genuinely distinct. -/

section Canonical

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The canonical chord predecessors are NOT `tracePhi`-SameCycle.**  `τ = swap (ρ a₀) (ρ a₁)
* keptPhi`, with `keptPhi.SameCycle (ρ a₀) (ρ a₁)` (the proved `side₁AnchorsShareFace_canonical`)
and `ρ a₀ ≠ ρ a₁` (anchors distinct).  Hence the swap splits the shared kept face, so the two
chord predecessors `ρ a₀`, `ρ a₁` no longer share a `τ`-cycle; transporting one `τ`-step on each
side gives `¬ τ.SameCycle (β a₀) (β a₁)`. -/
theorem side₁_chordPred_notSameCycle_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ¬ (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
      ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep))
      ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) := by
  classical
  set β := data.sideAlpha₁ hsep with hβ
  set ρ := data.sideSigma₁ with hρ
  set a₀ := side₁Anchor₀ data hsep with ha₀
  set a₁ := side₁Anchor₁ data hsep with ha₁
  -- the share-face fact: `keptPhi.SameCycle (ρ a₀) (ρ a₁)`.
  have hshare : (keptPhi β ρ).SameCycle (ρ a₀) (ρ a₁) := by
    have h := side₁AnchorsShareFace_canonical data hsep
    -- unfolds to `keptPhi.SameCycle (sideSigma₁ a₀) (sideSigma₁ a₁)`.
    simpa [hβ, hρ, ha₀, ha₁, ProofsInTheBook.ChordDisk.Side₁AnchorsShareFace, keptPhi]
      using h
  -- `ρ a₀ ≠ ρ a₁`.
  have hne : ρ a₀ ≠ ρ a₁ := ρa₀_ne_ρa₁ ρ (side₁Anchors_ne data hsep)
  -- the split: `¬ τ.SameCycle (ρ a₀) (ρ a₁)`.
  have hsplit : ¬ (tracePhi β ρ a₀ a₁).SameCycle (ρ a₀) (ρ a₁) := by
    rw [show tracePhi β ρ a₀ a₁ = Equiv.swap (ρ a₀) (ρ a₁) * keptPhi β ρ from rfl]
    exact notSameCycle_swap_mul_left_of_sameCycle (keptPhi β ρ) hne hshare
  -- transport: `τ (β a₀) = ρ a₁` and `τ (β a₁) = ρ a₀`, so
  -- `τ.SameCycle (β a₀) (β a₁) ↔ τ.SameCycle (ρ a₁) (ρ a₀)`.
  intro hsc
  apply hsplit
  have hb0 : tracePhi β ρ a₀ a₁ (β a₀) = ρ a₁ :=
    tracePhi_b0 β ρ (data.sideAlpha₁_involutive hsep) a₀ a₁
  have hb1 : tracePhi β ρ a₀ a₁ (β a₁) = ρ a₀ :=
    tracePhi_b1 β ρ (data.sideAlpha₁_involutive hsep) a₀ a₁
  -- `τ.SameCycle (β a₀) (β a₁) → τ.SameCycle (τ (β a₀)) (τ (β a₁)) = τ.SameCycle (ρ a₁) (ρ a₀)`.
  have hstep : (tracePhi β ρ a₀ a₁).SameCycle
      (tracePhi β ρ a₀ a₁ (β a₀)) (tracePhi β ρ a₀ a₁ (β a₁)) :=
    hsc.apply_left.apply_right
  rw [hb0, hb1] at hstep
  exact hstep.symm

/-- **`face₁_not_outer` for `outerFace := S.dartFace (inr 1)`.**  `S.dartFace (inl face₁Dart₁)
= S.dartFace (inr 0)` (brick 3), and `S.dartFace (inr 0) ≠ S.dartFace (inr 1)` by
`chordOrbits_eq_iff_tracePhi` + the splice-split fact. -/
theorem side₁_face₁_not_outer_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data))
      ≠ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) := by
  intro hcontra
  -- `S.dartFace (inr 0) = S.dartFace (inl face₁Dart₁) = S.dartFace (inr 1)`.
  have h01 : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inr 0)
      = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) := by
    rw [side₁_chord0_face_eq_face₁_canonical data hsep, hcontra]
  -- `chordOrbits_eq_iff_tracePhi` : the chord-dart faces coincide iff the chord predecessors
  -- share a `tracePhi`-orbit.
  have hsame : (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep))
        ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) :=
    (chordOrbits_eq_iff_tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
      (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
      (side₁Anchors_ne data hsep)).1 h01
  exact side₁_chordPred_notSameCycle_canonical data hsep hsame

/-! ## Section 3.  The outer-trace supplier `side₁OuterTraceData_canonical`

We define `outerFace := S.dartFace (inr 1)` and build the boundary cycle with
`CombMap.boundaryCycleOfFace` rooted at `inr 1` (its `φ`-orbit is nontrivial since the side map
is a simple graph).  The genuinely-planar Jordan residues are taken as inputs. -/

/-- **The side-1 outer-trace bundle for the canonical anchors.**

The orbit-algebraic boundary-cycle fields are discharged; `chord1_is_outer` is `rfl`;
`face₁_not_outer` is PROVED (the splice-split fact).  The genuine Jordan/Schoenflies residues —
the `arcSplit` cyclic-list pairing, the boundary simplicity, the length `≥ 3`, and the
inner-rep-avoidance `InnerRepsAvoidBoundary` — are taken as inputs, exactly as
`NearTriangulation`/`DeletedOuterBoundary.ofMergedFace` take them. -/
noncomputable def side₁OuterTraceData_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hsimple : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).IsSimpleGraph)
    (arcSplit :
      ∀ ⦃p q : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).Vertex⦄, p ≠ q →
        p ∈ ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
          (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).tail →
        q ∈ ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
          (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).tail →
        BoundaryArcSplit (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep))
          (((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
            (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).tail)
          (((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
            (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).dartEdge) p q)
    (outer_simple :
      (((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
        (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).tail).Nodup)
    (outer_len :
      3 ≤ ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).length)
    (inner_reps :
      InnerRepsAvoidBoundary data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)
        ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1))) :
    Side₁OuterTraceData data hsep := by
  classical
  -- abbreviation for the side map.
  set S := data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep) with hS
  -- the side map's `φ` has no fixed dart (it is a simple graph).
  have hφ : S.φ (Sum.inr 1) ≠ (Sum.inr 1) :=
    S.phi_ne_self_of_isSimpleGraph hsimple (Sum.inr 1)
  refine
    { outerFace := S.dartFace (Sum.inr 1)
      outerCycle := S.boundaryCycleOfFace (S.dartFace (Sum.inr 1)) hφ rfl arcSplit
      outer_simple := ?_
      outer_len := ?_
      chord1_is_outer := rfl
      face₁_not_outer := side₁_face₁_not_outer_canonical data hsep
      inner_reps := inner_reps }
  · -- `VertexNodup`: the boundary-cycle vertex list = the mapped face-dart-list.
    show (S.boundaryCycleOfFace (S.dartFace (Sum.inr 1)) hφ rfl arcSplit).vertices.Nodup
    exact outer_simple
  · -- `length ≥ 3`: the boundary-cycle length = the face-dart-list length.
    show 3 ≤ (S.boundaryCycleOfFace (S.dartFace (Sum.inr 1)) hφ rfl arcSplit).length
    exact outer_len

/-! ## Section 4.  The final corollary: `ContiguousInterval` from the outer-trace inputs

Composing the supplier with `ZinanCh35Hclass.contiguousInterval_canonical`: given the side-map
simplicity and the genuine Jordan/Schoenflies residues, the canonical side-1 anchors carry the
full `ChordSideNT.ContiguousInterval`. -/

/-- **`ContiguousInterval` for canonical side-1 anchors from the outer-trace residues.** -/
noncomputable def contiguousInterval_of_outerTraceInputs
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hsimple : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).IsSimpleGraph)
    (arcSplit :
      ∀ ⦃p q : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).Vertex⦄, p ≠ q →
        p ∈ ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
          (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).tail →
        q ∈ ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
          (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).tail →
        BoundaryArcSplit (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep))
          (((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
            (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).tail)
          (((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
            (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).dartEdge) p q)
    (outer_simple :
      (((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
        (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).tail).Nodup)
    (outer_len :
      3 ≤ ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).length)
    (inner_reps :
      InnerRepsAvoidBoundary data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)
        ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1))) :
    ChordSideNT.ContiguousInterval data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) :=
  contiguousInterval_canonical data hsep
    (side₁OuterTraceData_canonical data hsep hsimple arcSplit outer_simple outer_len inner_reps)
    hsimple

end Canonical

end ProofsInTheBook.ZinanCh35OuterTrace

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35OuterTrace.notSameCycle_swap_mul_left_of_sameCycle
#print axioms ProofsInTheBook.ZinanCh35OuterTrace.side₁_chordPred_notSameCycle_canonical
#print axioms ProofsInTheBook.ZinanCh35OuterTrace.side₁_face₁_not_outer_canonical
#print axioms ProofsInTheBook.ZinanCh35OuterTrace.side₁OuterTraceData_canonical
#print axioms ProofsInTheBook.ZinanCh35OuterTrace.contiguousInterval_of_outerTraceInputs
