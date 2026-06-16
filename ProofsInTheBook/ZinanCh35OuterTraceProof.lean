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
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ZinanCh35SideAnchors
open ProofsInTheBook.ZinanCh35ChordResidue
open ProofsInTheBook.ZinanCh35SideOuterSimple

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

end ProofsInTheBook.ZinanCh35OuterTraceProof

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_OuterTraceInjOn_of_arcTrace
