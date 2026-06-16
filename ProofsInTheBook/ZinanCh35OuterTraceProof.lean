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

/-! ## Boundary-cycle helpers (general `BoundaryCycle`) -/

/-- **Chain ⟹ `φ`-successor.**  If two boundary darts `d,e` lie on the same boundary cycle and
their endpoint vertices chain (`M.head d = M.tail e`), then `e` is the `φ`-successor of `d`.  Upgrades
a `DartArc.chain` *vertex* equality to a face-walk *dart* equality, via `consecutive_phi` +
`tail_injective_on_darts`. -/
lemma phi_eq_of_boundary_chain
    {f : M.Face} (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {d e : D} (hd : d ∈ C.darts) (he : e ∈ C.darts)
    (hchain : M.head d = M.tail e) :
    M.φ d = e := by
  classical
  rw [List.mem_iff_getElem] at hd
  obtain ⟨n, hn, hdget⟩ := hd
  set p : Fin C.darts.length := ⟨n, hn⟩ with hp
  have hphi_get : C.darts.get (cyclicNext C.normalized.length_pos p) = M.φ d := by
    have := C.consecutive_phi p
    rw [show C.darts.get p = d by rw [List.get_eq_getElem]; exact hdget] at this
    exact this
  have hphi_mem : M.φ d ∈ C.darts := by
    rw [← hphi_get]; exact List.get_mem _ _
  have htail_phi : M.tail (M.φ d) = M.head d := by
    have hv := C.consecutive_vertex p
    rw [hphi_get, show C.darts.get p = d by rw [List.get_eq_getElem]; exact hdget] at hv
    exact hv
  exact C.tail_injective_on_darts hC hphi_mem he (by rw [htail_phi, hchain])

/-- **`M.head` is injective on boundary-cycle darts** (mirror of `tail_injective_on_darts`).  Via the
`φ`-successor: `head d = tail (φ d)` on the cycle, then `tail`-injectivity + `φ` injective. -/
lemma head_injective_on_darts
    {f : M.Face} (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {d e : D} (hd : d ∈ C.darts) (he : e ∈ C.darts)
    (hhead : M.head d = M.head e) :
    d = e := by
  classical
  rw [List.mem_iff_getElem] at hd he
  obtain ⟨nd, hnd, hdget⟩ := hd
  obtain ⟨ne, hne, heget⟩ := he
  set id : Fin C.darts.length := ⟨nd, hnd⟩ with hid
  set ie : Fin C.darts.length := ⟨ne, hne⟩ with hie
  have hgd : C.darts.get id = d := by rw [List.get_eq_getElem]; exact hdget
  have hge : C.darts.get ie = e := by rw [List.get_eq_getElem]; exact heget
  have hphid : C.darts.get (cyclicNext C.normalized.length_pos id) = M.φ d := by
    have := C.consecutive_phi id; rw [hgd] at this; exact this
  have hphie : C.darts.get (cyclicNext C.normalized.length_pos ie) = M.φ e := by
    have := C.consecutive_phi ie; rw [hge] at this; exact this
  have htphid : M.tail (M.φ d) = M.head d := by
    have hv := C.consecutive_vertex id; rw [hphid, hgd] at hv; exact hv
  have htphie : M.tail (M.φ e) = M.head e := by
    have hv := C.consecutive_vertex ie; rw [hphie, hge] at hv; exact hv
  have hpd_mem : M.φ d ∈ C.darts := by rw [← hphid]; exact List.get_mem _ _
  have hpe_mem : M.φ e ∈ C.darts := by rw [← hphie]; exact List.get_mem _ _
  have hφeq : M.φ d = M.φ e :=
    C.tail_injective_on_darts hC hpd_mem hpe_mem (by rw [htphid, htphie, hhead])
  exact M.φ.injective hφeq

variable (hNT : NearTriangulation M) {u v : M.Vertex}

/-- **The canonical `u → v` boundary dart-arc**, built from the chord via
`dartArcOfNonBoundaryEdge` on the outer cycle.  Its darts are on `hNT.outerCycle.darts`, its tails
are distinct (`tail_nodup`), and the terminal `v` is not an arc tail (`head_last_ne_tail`). -/
noncomputable def canonicalOuterArc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    DartArc M hNT.outerCycle u v :=
  (hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple
    data.chord.endpoints_ne data.chord.left_boundary data.chord.right_boundary
    data.chord.not_boundary_edge).1

/-- The canonical outer arc has length `≥ 2` (the chord is not a boundary edge). -/
theorem canonicalOuterArc_len_ge_two
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    2 ≤ (canonicalOuterArc hNT data hsep).len :=
  (hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple
    data.chord.endpoints_ne data.chord.left_boundary data.chord.right_boundary
    data.chord.not_boundary_edge).2

/-- Kept copy of an arc dart. -/
def arcK (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle u v)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁) (i : Fin A.len) :
    {d : D // d ∉ data.keptDel₁} :=
  ⟨A.arcDart i, hArcKept i⟩

/-- **The side-1 kept face permutation walks one step along the boundary arc.**
`keptPhi = sideSigma₁ ∘ sideAlpha₁` sends the `i`-th arc dart to the `(i+1)`-th.  Route: the arc's
head→tail `chain` upgrades to the outer-face `φ`-step (`phi_eq_of_boundary_chain`); `sideAlpha₁`
restricts to `M.α`; `M.φ = M.σ ∘ M.α`; the next arc dart is kept, so `filteredRotation` agrees with
`M.σ`. -/
lemma sideSigma₁_alpha_arcDart_eq_next
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle u v)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (i : Fin A.len) (hi : (i : ℕ) + 1 < A.len) :
    data.sideSigma₁ (data.sideAlpha₁ hsep (arcK hNT data A hArcKept i))
      = arcK hNT data A hArcKept ⟨i + 1, hi⟩ := by
  classical
  have hphi : M.φ (A.arcDart i) = A.arcDart ⟨i + 1, hi⟩ :=
    phi_eq_of_boundary_chain hNT.outerCycle hNT.outer_simple
      (A.boundary i) (A.boundary ⟨i + 1, hi⟩) (A.chain i hi)
  have hαcoe : ((data.sideAlpha₁ hsep (arcK hNT data A hArcKept i)) : D) = M.α (A.arcDart i) := by
    simpa [arcK] using data.sideAlpha₁_apply_coe hsep (arcK hNT data A hArcKept i)
  have hσnext : M.σ ((data.sideAlpha₁ hsep (arcK hNT data A hArcKept i)) : D)
      = A.arcDart ⟨i + 1, hi⟩ := by
    rw [hαcoe]; exact hphi
  have hσ_kept : M.σ ((data.sideAlpha₁ hsep (arcK hNT data A hArcKept i)) : D) ∉ data.keptDel₁ := by
    rw [hσnext]; exact hArcKept ⟨i + 1, hi⟩
  apply Subtype.ext
  rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
    FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₁ _ hσ_kept]
  exact hσnext

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
