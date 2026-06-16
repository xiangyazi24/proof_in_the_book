import ProofsInTheBook.ZinanCh35SideOuterSimple
import ProofsInTheBook.ZinanCh35ChordResidue
import ProofsInTheBook.ZinanCh35ArcDartRun

/-!
# Chapter 35 — discharging `OuterTraceInjOn` via the orbit↔boundary-arc VERTEX correspondence

`ZinanCh35SideOuterSimple.lean` reduced the side-1 `outer_simple` keystone to the single residual
`OuterTraceInjOn` (the composite `x ↦ M.tail (proj a₀ a₁ x).1` is injective on the side-1 outer
`φ`-orbit `S.faceDartList (inr 1)`).  The dead dart-level route `OrbitProjOnOuterArc` is UNSOUND
(it falsely requires `a₁.1 ∈ outerCycle.darts`; the chord is not a boundary edge).

This file builds the CORRECT, vertex-level route, following the orbit↔arc correspondence:

* The orbit's elements are the chord root `inr 1` (carrying the chord endpoint `v`) and the
  `inl`-darts whose underlying darts are exactly the **`u → v` boundary dart-arc** `A`.
* The orbit↔arc classifier `CanonicalSide₁OuterArcTrace` packages that: every orbit element is
  `inr 1` or `inl ⟨A.arcDart i, _⟩`.
* `M.tail` is injective on the arc tails (`A.tail_nodup`), and — crucially — the chord endpoint
  `v` is **not** an arc tail (`A.head_last_ne_tail : ∀ i, v ≠ M.tail (A.arcDart i)`).  This is the
  §3.3-critical fact that rules out the collision the *reversed* `v → u` run would create.

Given the classifier, `OuterTraceInjOn` is short (this file's `canonical_OuterTraceInjOn_of_arcTrace`).
The classifier itself — the ordered orbit↔arc trace — is the one genuine remaining bridge (the
inl-part of the orbit IS the boundary arc); it is isolated honestly here, not faked.

No `sorry` / `axiom` / `admit` / `native_decide` in the reduction.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterTraceProof

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35ChordResidue
open ProofsInTheBook.ZinanCh35SideOuterSimple
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ZinanCh35OuterTrace

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  (hNT : NearTriangulation M) {u v : M.Vertex}

/-- **The ordered orbit↔arc classifier** (the one genuine remaining bridge).  For the canonical
side-1 anchors, every dart on the side-1 outer `φ`-orbit `S.faceDartList (inr 1)` is either the
chord root `inr 1` or an `inl`-dart whose underlying dart is one of the boundary dart-arc `A`'s
darts.  The `inl`-part of the orbit IS the `u → v` boundary arc. -/
def CanonicalSide₁OuterArcTrace
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle u v)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁) : Prop :=
  ∀ x, x ∈ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1) →
    x = Sum.inr 1 ∨ ∃ i : Fin A.len, x = Sum.inl ⟨A.arcDart i, hArcKept i⟩

/-- **`OuterTraceInjOn` for the canonical anchors, from the orbit↔arc classifier.**  The chord
root `inr 1` carries `v` (`canonicalAnchor₁_tail` + the chord orientation `M.head data.dart = v`);
each `inl`-dart carries an arc tail.  `v` is not an arc tail (`A.head_last_ne_tail`), so root vs
arc cannot collide; two arc darts with equal tail are equal (`A.tail_nodup`). -/
theorem canonical_OuterTraceInjOn_of_arcTrace
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle u v)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hhv : M.head data.dart = v)
    (htrace : CanonicalSide₁OuterArcTrace hNT data hsep A hArcKept) :
    OuterTraceInjOn hNT data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) := by
  -- The root's projected tail is `v`.
  have hroot : M.tail (proj (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (Sum.inr 1)).1 = v := by
    rw [proj_inr_one, canonicalAnchor₁_tail data hsep, hhv]
  intro x hx y hy htail
  rcases htrace x hx with hxr | ⟨i, hxi⟩ <;> rcases htrace y hy with hyr | ⟨j, hyj⟩
  · -- root, root
    rw [hxr, hyr]
  · -- root, arc j  →  v = M.tail (arc j), impossible
    exfalso
    rw [hxr] at htail
    rw [hyj] at htail
    simp only [proj_inl, hroot] at htail
    exact A.head_last_ne_tail j htail
  · -- arc i, root  →  M.tail (arc i) = v, impossible
    exfalso
    rw [hyr] at htail
    rw [hxi] at htail
    simp only [proj_inl, hroot] at htail
    exact A.head_last_ne_tail i htail.symm
  · -- arc i, arc j  →  tails equal ⟹ i = j
    rw [hxi, hyj]
    rw [hxi, hyj] at htail
    simp only [proj_inl] at htail
    have hij : i = j := A.tail_nodup htail
    rw [hij]

/-- **Orbit membership iff** (canonical anchors).  A dart is on the side-1 outer `φ`-orbit
`S.faceDartList (inr 1)` iff it is the chord root `inr 1` or an `inl`-dart `inl k` with `k` in the
`tracePhi`-orbit of `β a₁`.  The negative case `inr 0` is excluded by the splice-split fact
`side₁_chordPred_notSameCycle_canonical` (the two chord predecessors are NOT `tracePhi`-SameCycle). -/
theorem canonical_side₁_outer_orbit_mem_iff
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (x : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2) :
    x ∈ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)
      ↔ x = Sum.inr 1 ∨
        ∃ k : {d : D // d ∉ data.keptDel₁}, x = Sum.inl k ∧
          (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
              (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
            ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) k := by
  classical
  -- shorthands
  set a₀ := side₁Anchor₀ data hsep with ha₀
  set a₁ := side₁Anchor₁ data hsep with ha₁
  set hne := side₁Anchors_ne data hsep with hhne
  set β := data.sideAlpha₁ hsep with hβ
  set ρ := data.sideSigma₁ with hρ
  have hinv : β * β = 1 := data.sideAlpha₁_involutive hsep
  have hfix : ∀ k, β k ≠ k := data.sideAlpha₁_no_fixed hsep
  -- the side map IS the fresh map.
  have hSeq : data.sideMap₁ hsep a₀ a₁ hne = freshMap β ρ hinv hfix a₀ a₁ hne := rfl
  -- the splice-split: ¬ τ.SameCycle (β a₁) (β a₀).
  have hsplit : ¬ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) (β a₀) := by
    intro h
    exact side₁_chordPred_notSameCycle_canonical data hsep h.symm
  -- root in the support of φ.
  have hroot_support :
      (Sum.inr 1 : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2)
        ∈ (freshMap β ρ hinv hfix a₀ a₁ hne).φ.support := by
    rw [Equiv.Perm.mem_support, freshMap_phi_inr_one β ρ hinv hfix hne]
    exact Sum.inl_ne_inr
  rw [hSeq, CombMap.faceDartList]
  constructor
  · intro hx
    rw [Equiv.Perm.mem_toList_iff] at hx
    obtain ⟨hcyc, _⟩ := hx
    -- transport the φ-SameCycle (inr 1 → x) to a tracePhi-SameCycle of faceProjs.
    have hτ : (tracePhi β ρ a₀ a₁).SameCycle (β a₁) (faceProj β a₀ a₁ x) := by
      have h := (freshFace_sameCycle_iff β ρ hinv hfix hne (Sum.inr 1) x).1 hcyc
      simpa [faceProj_inr_one] using h
    cases x with
    | inl k =>
        right
        exact ⟨k, rfl, by simpa [faceProj_inl] using hτ⟩
    | inr j =>
        fin_cases j
        · -- inr 0, excluded by the splice-split fact
          exact absurd (by simpa [faceProj_inr_zero] using hτ) hsplit
        · left; rfl
  · intro hx
    rw [Equiv.Perm.mem_toList_iff]
    refine ⟨?_, hroot_support⟩
    rcases hx with hroot | ⟨k, hxk, hk⟩
    · rw [hroot]
    · rw [hxk]
      refine (freshFace_sameCycle_iff β ρ hinv hfix hne (Sum.inr 1) (Sum.inl k)).2 ?_
      simpa [faceProj_inl, faceProj_inr_one] using hk

/-- **The canonical `tracePhi` orbit through `β a₁` is exactly the kept copies of the `u → v`
boundary dart-arc `A`** (the genuine remaining bridge — proved separately).  Packaged as a `Prop`
so the classifier follows mechanically. -/
structure CanonicalTracePhiArc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle u v)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁) : Prop where
  mem_iff : ∀ k : {d : D // d ∉ data.keptDel₁},
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
      ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) k
    ↔ ∃ i : Fin A.len, k = ⟨A.arcDart i, hArcKept i⟩

/-- **The classifier from the `tracePhi`-orbit ↔ arc identification.**  Combines the membership iff
(`canonical_side₁_outer_orbit_mem_iff`) with `CanonicalTracePhiArc`: an orbit dart is `inr 1` or
`inl k`; in the latter case `k`'s `tracePhi`-membership pins it to an arc dart. -/
theorem canonical_arcTrace_of_tracePhiArc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle u v)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hTA : CanonicalTracePhiArc hNT data hsep A hArcKept) :
    CanonicalSide₁OuterArcTrace hNT data hsep A hArcKept := by
  intro x hx
  rcases (canonical_side₁_outer_orbit_mem_iff hNT data hsep x).1 hx with hroot | ⟨k, hxk, hτ⟩
  · exact Or.inl hroot
  · rcases (hTA.mem_iff k).1 hτ with ⟨i, hk⟩
    exact Or.inr ⟨i, by rw [hxk, hk]⟩

end ProofsInTheBook.ZinanCh35OuterTraceProof

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_OuterTraceInjOn_of_arcTrace
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_side₁_outer_orbit_mem_iff
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_arcTrace_of_tracePhiArc
