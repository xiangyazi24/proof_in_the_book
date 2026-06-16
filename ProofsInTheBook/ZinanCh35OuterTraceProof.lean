import ProofsInTheBook.ZinanCh35SideOuterSimple
import ProofsInTheBook.ZinanCh35ChordResidue
import ProofsInTheBook.ZinanCh35ArcDartRun
import ProofsInTheBook.ZinanCh35EdgeCoreFinal
import ProofsInTheBook.ZinanCh35ArcSide

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
open ProofsInTheBook.ChordAnchor
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
variable {a b : M.Vertex}

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
    (A : DartArc M hNT.outerCycle a b)
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
    (A : DartArc M hNT.outerCycle a b)
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
    (A : DartArc M hNT.outerCycle a b)
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
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hb : M.head data.dart = b)
    (htrace : CanonicalSide₁OuterArcTrace hNT data hsep A hArcKept) :
    OuterTraceInjOn hNT data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) := by
  -- The root's projected tail is `b` (the arc terminal).
  have hroot : M.tail (proj (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (Sum.inr 1)).1 = b := by
    rw [proj_inr_one, canonicalAnchor₁_tail data hsep, hb]
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
    (A : DartArc M hNT.outerCycle a b)
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
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hTA : CanonicalTracePhiArc hNT data hsep A hArcKept) :
    CanonicalSide₁OuterArcTrace hNT data hsep A hArcKept := by
  intro x hx
  rcases (canonical_side₁_outer_orbit_mem_iff hNT data hsep x).1 hx with hroot | ⟨k, hxk, hτ⟩
  · exact Or.inl hroot
  · rcases (hTA.mem_iff k).1 hτ with ⟨i, hk⟩
    exact Or.inr ⟨i, by rw [hxk, hk]⟩

/-! ## Assembly of `CanonicalTracePhiArc` from the walk + endpoint facts -/

/-- `arcK` is injective (its underlying darts have distinct tails). -/
lemma arcK_injective (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    {i j : Fin A.len} (h : arcK hNT data A hArcKept i = arcK hNT data A hArcKept j) :
    i = j := by
  apply A.tail_nodup
  show M.tail (A.arcDart i) = M.tail (A.arcDart j)
  have hd : A.arcDart i = A.arcDart j := by
    have := congrArg Subtype.val h; simpa [arcK] using this
  rw [hd]

/-- **`tracePhi` walks one step along the arc** (interior step).  Uses `tracePhi_other` (the two
chord-predecessor exceptions `β a₀, β a₁` are avoided) + the kept-σ walk. -/
lemma tracePhi_arc_step
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hlast : data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
      = arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
    (hnot_beta_a₀ : ∀ i : Fin A.len,
      arcK hNT data A hArcKept i ≠ data.sideAlpha₁ hsep (side₁Anchor₀ data hsep))
    (i : Fin A.len) (hi : (i : ℕ) + 1 < A.len) :
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
        (arcK hNT data A hArcKept i)
      = arcK hNT data A hArcKept ⟨i + 1, hi⟩ := by
  classical
  have hβinv : data.sideAlpha₁ hsep * data.sideAlpha₁ hsep = 1 := data.sideAlpha₁_involutive hsep
  have hinv2 : ∀ x, data.sideAlpha₁ hsep (data.sideAlpha₁ hsep x) = x := by
    intro x; rw [← Equiv.Perm.mul_apply, hβinv, Equiv.Perm.one_apply]
  -- β (arcK i) ≠ ρ-anchor-predecessors a₀, a₁
  have hnot0 : data.sideAlpha₁ hsep (arcK hNT data A hArcKept i) ≠ side₁Anchor₀ data hsep := by
    intro h
    apply hnot_beta_a₀ i
    have h2 := congrArg (data.sideAlpha₁ hsep) h
    rw [hinv2] at h2
    exact h2
  have hnot1 : data.sideAlpha₁ hsep (arcK hNT data A hArcKept i) ≠ side₁Anchor₁ data hsep := by
    intro h
    have h2 := congrArg (data.sideAlpha₁ hsep) h
    rw [hinv2] at h2
    rw [hlast] at h2
    have hieq : i = (⟨A.len - 1, by have := A.len_pos; omega⟩ : Fin A.len) :=
      arcK_injective hNT data A hArcKept h2
    have hi2 : (i : ℕ) = A.len - 1 := by rw [hieq]
    omega
  rw [tracePhi_other (data.sideAlpha₁ hsep) data.sideSigma₁ (side₁Anchor₀ data hsep)
    (side₁Anchor₁ data hsep) hnot0 hnot1]
  exact sideSigma₁_alpha_arcDart_eq_next hNT data hsep A hArcKept i hi

/-- **`tracePhi` wraps from the last arc dart back to the first** (the splice step `β a₁ ↦ ρ a₀`). -/
lemma tracePhi_arc_wrap
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hfirst : data.sideSigma₁ (side₁Anchor₀ data hsep)
      = arcK hNT data A hArcKept ⟨0, A.len_pos⟩)
    (hlast : data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
      = arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩) :
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
        (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      = arcK hNT data A hArcKept ⟨0, A.len_pos⟩ := by
  rw [← hlast, tracePhi_b1 (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)]
  exact hfirst

/-- From the last arc dart, every `tracePhi`-iterate stays within the arc. -/
lemma tracePhi_iterate_last_mem_arc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hstep : ∀ i : Fin A.len, ∀ hi : (i : ℕ) + 1 < A.len,
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
          (arcK hNT data A hArcKept i) = arcK hNT data A hArcKept ⟨i + 1, hi⟩)
    (hwrap : (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
        (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      = arcK hNT data A hArcKept ⟨0, A.len_pos⟩)
    (n : ℕ) :
    ∃ i : Fin A.len,
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))^[n]
        (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
        = arcK hNT data A hArcKept i := by
  classical
  induction n with
  | zero => exact ⟨⟨A.len - 1, by have := A.len_pos; omega⟩, rfl⟩
  | succ n ih =>
      rcases ih with ⟨i, hi_eq⟩
      rw [Function.iterate_succ_apply', hi_eq]
      by_cases hlt : (i : ℕ) + 1 < A.len
      · exact ⟨⟨i + 1, hlt⟩, hstep i hlt⟩
      · have hi_last : i = (⟨A.len - 1, by have := A.len_pos; omega⟩ : Fin A.len) := by
          apply Fin.ext
          show (i : ℕ) = A.len - 1
          have h1 := i.isLt
          have h2 : ¬ ((i : ℕ) + 1 < A.len) := hlt
          omega
        rw [hi_last]; exact ⟨⟨0, A.len_pos⟩, hwrap⟩

/-- Every arc dart is `tracePhi`-SameCycle to the last arc dart (walk first→i, wrap last→first). -/
lemma tracePhi_sameCycle_last_arc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hstep : ∀ i : Fin A.len, ∀ hi : (i : ℕ) + 1 < A.len,
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
          (arcK hNT data A hArcKept i) = arcK hNT data A hArcKept ⟨i + 1, hi⟩)
    (hwrap : (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
        (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      = arcK hNT data A hArcKept ⟨0, A.len_pos⟩)
    (i : Fin A.len) :
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
      (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      (arcK hNT data A hArcKept i) := by
  classical
  set τ := tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
    (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) with hτdef
  -- first reachable from last in one step (wrap)
  have hlast_first : τ.SameCycle (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
      (arcK hNT data A hArcKept ⟨0, A.len_pos⟩) := ⟨1, by rw [zpow_one]; exact hwrap⟩
  -- from first, reach index n by walking n steps
  have hfrom_first : ∀ n : ℕ, ∀ hn : n < A.len,
      τ.SameCycle (arcK hNT data A hArcKept ⟨0, A.len_pos⟩) (arcK hNT data A hArcKept ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero => intro hn; exact Equiv.Perm.SameCycle.refl _ _
    | succ m ih =>
        intro hn
        have hm : m < A.len := by omega
        have hmstep : (m : ℕ) + 1 < A.len := by
          simpa using hn
        refine (ih hm).trans ?_
        refine ⟨1, ?_⟩
        rw [zpow_one]
        have := hstep ⟨m, hm⟩ (by simpa using hmstep)
        -- arcK ⟨m,hm⟩ → arcK ⟨m+1, _⟩ = arcK ⟨n, hn⟩
        simpa using this
  exact hlast_first.trans (hfrom_first i.1 i.2)

/-- **`CanonicalTracePhiArc` from the step/wrap/endpoint data.**  Given the interior step, the wrap,
the two endpoint alignments, and the `β a₀`-exclusion, the `tracePhi`-orbit of `β a₁` is exactly the
arc darts. -/
theorem canonicalTracePhiArc_of_steps
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hfirst : data.sideSigma₁ (side₁Anchor₀ data hsep)
      = arcK hNT data A hArcKept ⟨0, A.len_pos⟩)
    (hlast : data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
      = arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩)
    (hnot_beta_a₀ : ∀ i : Fin A.len,
      arcK hNT data A hArcKept i ≠ data.sideAlpha₁ hsep (side₁Anchor₀ data hsep)) :
    CanonicalTracePhiArc hNT data hsep A hArcKept := by
  classical
  have hstep : ∀ i : Fin A.len, ∀ hi : (i : ℕ) + 1 < A.len,
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))
          (arcK hNT data A hArcKept i) = arcK hNT data A hArcKept ⟨i + 1, hi⟩ :=
    fun i hi => tracePhi_arc_step hNT data hsep A hArcKept hlast hnot_beta_a₀ i hi
  have hwrap := tracePhi_arc_wrap hNT data hsep A hArcKept hfirst hlast
  refine ⟨fun k => ?_⟩
  constructor
  · intro hk
    obtain ⟨n, hn⟩ := hk.exists_nat_pow_eq
    have hn' : (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep))^[n]
        (arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩) = k := by
      rw [Equiv.Perm.coe_pow] at hn
      rw [← hlast]; exact hn
    obtain ⟨i, hi⟩ := tracePhi_iterate_last_mem_arc hNT data hsep A hArcKept hstep hwrap n
    exact ⟨i, hn'.symm.trans hi⟩
  · rintro ⟨i, rfl⟩
    have hsc := tracePhi_sameCycle_last_arc hNT data hsep A hArcKept hstep hwrap i
    rw [hlast]; exact hsc

/-! ## hArcKept reduction (via the unconditional `outerDartArc₁_uncond`) + `hnot_beta_a₀` -/

open ProofsInTheBook.ChordReconClose in
/-- **`hArcKept` per arc dart, from side-1 region membership of its endpoints.**  A boundary arc
dart whose endpoints lie in `sideRegion₁` has its `α`-reverse face in `side₁` (the unconditional
`outerDartArc₁_uncond` confinement), so it lies in `outerArc₁ ⊆ keptSet₁`; it is not the chord dart
(the chord is not a boundary edge).  Reduces `hArcKept` to the vertex-level side-1 identification. -/
lemma arcDart_notMem_keptDel₁_of_sideRegion
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b) (i : Fin A.len)
    (htail : M.tail (A.arcDart i) ∈ sideRegion₁ data)
    (hhead : M.head (A.arcDart i) ∈ sideRegion₁ data) :
    A.arcDart i ∉ data.keptDel₁ := by
  classical
  have hbmem : A.arcDart i ∈ hNT.outerCycle.darts := A.boundary i
  have hface : M.dartFace (A.arcDart i) = hNT.outerFace :=
    (hNT.outerCycle.mem_darts_iff (A.arcDart i)).mp hbmem
  have hedge : M.dartEdge (A.arcDart i) ≠ s(u, v) := by
    intro he
    apply data.chord.not_boundary_edge
    show s(u, v) ∈ hNT.outerCycle.edges
    rw [← he, hNT.outerCycle.edges_eq]
    exact List.mem_map_of_mem hbmem
  have hne : A.arcDart i ≠ data.dart := by
    intro he
    have hno := hNT.chordDart_not_outer data.chord
    rw [he] at hface
    exact hno hface
  have hconf : M.dartFace (M.α (A.arcDart i)) ∈ data.side₁ :=
    ProofsInTheBook.ZinanCh35EdgeCoreFinal.outerDartArc₁_uncond data hsep hedge hface htail hhead
  rw [data.mem_keptDel₁_iff]
  refine ⟨Or.inr ?_, ?_⟩
  · exact ⟨hface, hconf⟩
  · simpa using hne

/-- **`hnot_beta_a₀`** (self-contained): `β a₀ = sideAlpha₁ (side₁Anchor₀) = face₁Dart₂`, an inner
chord-triangle dart whose face is `face₁ ≠ outerFace`; so it is none of the boundary arc darts. -/
lemma hnot_beta_a₀_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (i : Fin A.len) :
    arcK hNT data A hArcKept i ≠ data.sideAlpha₁ hsep (side₁Anchor₀ data hsep) := by
  intro h
  have ha₀ : side₁Anchor₀ data hsep = data.sideAlpha₁ hsep (face₁Dart₂ data) := by
    apply data.sideSigma₁.injective
    rw [sideSigma₁_side₁Anchor₀ data hsep]
    rfl
  have hinv2 : ∀ x, data.sideAlpha₁ hsep (data.sideAlpha₁ hsep x) = x := by
    intro x
    rw [← Equiv.Perm.mul_apply, data.sideAlpha₁_involutive hsep, Equiv.Perm.one_apply]
  have hβa₀ : data.sideAlpha₁ hsep (side₁Anchor₀ data hsep) = face₁Dart₂ data := by
    rw [ha₀]; exact hinv2 _
  -- arcK i = β a₀ (from h), so the arc dart's face = the inner chord face₁, but it is outerFace.
  have houter : M.dartFace ((data.sideAlpha₁ hsep (side₁Anchor₀ data hsep)) : D) = hNT.outerFace := by
    rw [← congrArg Subtype.val h]
    exact (hNT.outerCycle.mem_darts_iff _).mp (A.boundary i)
  have hinner : M.dartFace ((data.sideAlpha₁ hsep (side₁Anchor₀ data hsep)) : D) = data.face₁ := by
    rw [hβa₀]
    show M.dartFace (M.φ (M.φ data.dart)) = M.dartFace data.dart
    rw [M.dartFace_phi, M.dartFace_phi]
  exact data.face₁_not_outer (hinner.symm.trans houter)

/-- **`hArcKept` for the side-1 arc `bwdArc`, UNCONDITIONAL.**  Each `bwdArc` dart's `α`-reverse
face is in `side₁` (`bwdArc_reverse_face_mem_side₁`), so it lies in `outerArc₁ ⊆ keptSet₁`; it is
not the chord dart (`bwdArc_dartEdge_ne_chord`).  No orientation / region hypothesis. -/
lemma bwdArc_arcDart_notMem_keptDel₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (i : Fin (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).len) :
    (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i ∉ data.keptDel₁ := by
  classical
  have hbmem : (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i ∈ hNT.outerCycle.darts :=
    (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).boundary i
  have hface : M.dartFace ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i)
      = hNT.outerFace :=
    (hNT.outerCycle.mem_darts_iff _).mp hbmem
  have hconf : M.dartFace (M.α ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i))
      ∈ data.side₁ :=
    ProofsInTheBook.ZinanCh35ArcSide.bwdArc_reverse_face_mem_side₁ data i
  have hne : (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart i ≠ data.dart := by
    intro he
    apply ProofsInTheBook.ZinanCh35ArcSide.bwdArc_dartEdge_ne_chord data i
    rw [he]; exact hNT.chordDart_edge data.chord
  rw [data.mem_keptDel₁_iff]
  exact ⟨Or.inr ⟨hface, hconf⟩, by simpa using hne⟩

/-! ## Sharpening the residue: boundary membership ⟸ face ∉ side₁

A canonical splice dart is KEPT by type (`(sideSigma₁ _).2 : ∉ keptDel₁`).  `keptSet₁ =
(sideDarts₁ ∪ outerArc₁) \ {dart}`, and `sideDarts₁ = {d | dartFace d ∈ side₁}`.  So if the dart's
face is NOT in `side₁`, it cannot be a `sideDarts₁` dart, hence it is an `outerArc₁` dart
(`dartFace = outerFace`), hence on the boundary.  This reduces each boundary-membership residue to a
single face-fact `dartFace ∉ side₁` (the kept-σ step off the chord-triangle leaves the side-1 faces). -/

/-- Boundary membership of a kept dart from `dartFace ∉ side₁`. -/
lemma kept_mem_outerCycle_of_face_not_side₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁})
    (hface : M.dartFace (k : D) ∉ data.side₁) :
    (k : D) ∈ hNT.outerCycle.darts := by
  classical
  have hkept : (k : D) ∈ data.keptSet₁ := (data.mem_keptDel₁_iff _).1 k.2
  have hmem : (k : D) ∈ data.sideDarts₁ ∪ data.outerArc₁ := hkept.1
  rcases hmem with hsd | hoa
  · -- ∈ sideDarts₁ = {d | dartFace d ∈ side₁} contradicts hface
    exact absurd hsd hface
  · -- ∈ outerArc₁ ⟹ dartFace = outerFace ⟹ boundary
    exact (hNT.outerCycle.mem_darts_iff _).2 hoa.1

/-! ## bwdArc endpoint identification (from boundary membership — the lone residue) -/

/-- **The lone remaining residue**: the canonical splice darts `ρ a₀`, `β a₁` are boundary darts
(equivalently, they are the first/last darts of the side-1 arc `bwdArc`).  This is the vertex-star →
boundary endpoint alignment — NOT derivable from the arc/orbit machinery (which is all proved). -/
structure CanonicalBwdArcEndpointAlignment
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) : Prop where
  ρa₀_boundary : ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) ∈ hNT.outerCycle.darts
  βa₁_boundary : ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) ∈ hNT.outerCycle.darts

/-- `ρ a₀ = bwdArc's first dart` (from `ρ a₀` boundary; both have tail `M.tail data.dart`). -/
lemma sideSigma₁_anchor₀_eq_bwdArc_first
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hρa₀ : ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    data.sideSigma₁ (side₁Anchor₀ data hsep)
      = ⟨(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx,
          bwdArc_arcDart_notMem_keptDel₁ hNT data hsep _⟩ := by
  apply Subtype.ext
  apply hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hρa₀
    ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).boundary _)
  have hL : M.tail ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) = M.tail data.dart := by
    rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
      ProofsInTheBook.ChordSigmaContig.tail_filteredRotation data.keptDel₁ (side₁Anchor₀ data hsep)]
    exact canonicalAnchor₀_tail data hsep
  have hR : M.tail ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
      (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx) = M.tail data.dart := by
    rw [(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).tail_firstIdx, M.head_alpha]
  rw [hL, hR]

/-- `β a₁ = bwdArc's last dart` (from `β a₁` boundary; both have head `M.head data.dart`). -/
lemma sideAlpha₁_anchor₁_eq_bwdArc_last
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hβa₁ : ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
      = ⟨(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx,
          bwdArc_arcDart_notMem_keptDel₁ hNT data hsep _⟩ := by
  apply Subtype.ext
  apply head_injective_on_darts hNT.outerCycle hNT.outer_simple hβa₁
    ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).boundary _)
  have hL : M.head ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) = M.head data.dart := by
    have hαcoe : ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D)
        = M.α (side₁Anchor₁ data hsep).1 := by
      simpa using data.sideAlpha₁_apply_coe hsep (side₁Anchor₁ data hsep)
    rw [hαcoe, M.head_alpha, canonicalAnchor₁_tail data hsep]
  have hR : M.head ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
      (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx) = M.head data.dart := by
    rw [(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).head_lastIdx, M.tail_alpha]
  rw [hL, hR]

/-! ## Endpoint alignment + the full tie-together -/

/-- **First endpoint:** `ρ a₀` (the σ-successor of the canonical anchor `a₀`) is the first arc dart.
Both have tail `u`; `tail_injective_on_darts` pins them equal. -/
lemma canonical_trace_start_eq_first_arc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (ha : M.tail data.dart = a)
    (hρa₀_boundary : ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    data.sideSigma₁ (side₁Anchor₀ data hsep) = arcK hNT data A hArcKept ⟨0, A.len_pos⟩ := by
  apply Subtype.ext
  apply hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hρa₀_boundary
    (A.boundary ⟨0, A.len_pos⟩)
  have hfix : M.tail ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D)
      = M.tail (side₁Anchor₀ data hsep).1 := by
    rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
      ProofsInTheBook.ChordSigmaContig.tail_filteredRotation data.keptDel₁
        (side₁Anchor₀ data hsep)]
  rw [hfix, canonicalAnchor₀_tail data hsep, ha]
  exact A.tail_first.symm

/-- **Last endpoint:** `β a₁` (the α-partner of the canonical anchor `a₁`) is the last arc dart.
Both have head `v`; `head_injective_on_darts` pins them equal. -/
lemma canonical_trace_root_eq_last_arc
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (A : DartArc M hNT.outerCycle a b)
    (hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁)
    (hb : M.head data.dart = b)
    (hβa₁_boundary :
      ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) ∈ hNT.outerCycle.darts) :
    data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
      = arcK hNT data A hArcKept ⟨A.len - 1, by have := A.len_pos; omega⟩ := by
  apply Subtype.ext
  apply head_injective_on_darts hNT.outerCycle hNT.outer_simple hβa₁_boundary
    (A.boundary ⟨A.len - 1, by have := A.len_pos; omega⟩)
  have hαcoe : ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D)
      = M.α (side₁Anchor₁ data hsep).1 := by
    simpa using data.sideAlpha₁_apply_coe hsep (side₁Anchor₁ data hsep)
  rw [hαcoe, M.head_alpha, canonicalAnchor₁_tail data hsep, hb]
  exact A.head_last.symm

/-- **The residue, sharpened to two face-facts.**  `CanonicalBwdArcEndpointAlignment` follows from
the canonical splice darts' faces not lying in `side₁` (the genuine cyclic-order content: the
kept-σ step off the chord triangle exits the side-1 faces onto the outer boundary). -/
theorem canonicalBwdArcEndpointAlignment_of_faces
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hρ : M.dartFace ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) ∉ data.side₁)
    (hβ : M.dartFace ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) ∉ data.side₁) :
    CanonicalBwdArcEndpointAlignment hNT data hsep :=
  ⟨kept_mem_outerCycle_of_face_not_side₁ hNT data hsep _ hρ,
   kept_mem_outerCycle_of_face_not_side₁ hNT data hsep _ hβ⟩

/-- **`OuterTraceInjOn` for the canonical anchors, reduced to the genuine external facts.**  Ties
the whole chain: endpoint alignment → `canonicalTracePhiArc_of_steps` → classifier → reduction. -/
theorem canonical_OuterTraceInjOn_of_alignment
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (H : CanonicalBwdArcEndpointAlignment hNT data hsep) :
    OuterTraceInjOn hNT data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) := by
  set A := ProofsInTheBook.ZinanCh35ArcSide.bwdArc data with hA
  -- A : DartArc M outerCycle (M.head (M.α data.dart)) (M.tail (M.α data.dart))
  have hArcKept : ∀ i : Fin A.len, A.arcDart i ∉ data.keptDel₁ :=
    fun i => bwdArc_arcDart_notMem_keptDel₁ hNT data hsep i
  -- endpoint relations (no orientation needed; bwdArc's endpoints are the chord dart's tail/head)
  have ha : M.tail data.dart = M.head (M.α data.dart) := (M.head_alpha data.dart).symm
  have hb : M.head data.dart = M.tail (M.α data.dart) := (M.tail_alpha data.dart).symm
  have hfirst := canonical_trace_start_eq_first_arc hNT data hsep A hArcKept ha H.ρa₀_boundary
  have hlast := canonical_trace_root_eq_last_arc hNT data hsep A hArcKept hb H.βa₁_boundary
  have hnot : ∀ i : Fin A.len,
      arcK hNT data A hArcKept i ≠ data.sideAlpha₁ hsep (side₁Anchor₀ data hsep) :=
    fun i => hnot_beta_a₀_canonical hNT data hsep A hArcKept i
  have hTA := canonicalTracePhiArc_of_steps hNT data hsep A hArcKept hfirst hlast hnot
  have htrace := canonical_arcTrace_of_tracePhiArc hNT data hsep A hArcKept hTA
  exact canonical_OuterTraceInjOn_of_arcTrace hNT data hsep A hArcKept hb htrace

/-- A side-1 dart different from the chord dart is a kept side-1 dart. -/
private lemma keptSet₁_of_side₁_ne_dart
    (data : hNT.ChordSplitData u v) {d : D}
    (hside : M.dartFace d ∈ data.side₁) (hne : d ≠ data.dart) :
    d ∈ data.keptSet₁ := by
  exact ⟨Or.inl hside, by simpa using hne⟩

/-- The inverse `σ`-power stays in the same vertex star. -/
private lemma tail_pow_sigma_inv (n : ℕ) (d : D) :
    M.tail ((M.σ⁻¹ ^ n) d) = M.tail d := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    calc
      M.tail (M.σ⁻¹ ((M.σ⁻¹ ^ n) d))
          = M.tail (M.σ (M.σ⁻¹ ((M.σ⁻¹ ^ n) d))) := (M.tail_sigma _).symm
      _ = M.tail ((M.σ⁻¹ ^ n) d) := by simp
      _ = M.tail d := ih

/-- The first inverse-`σ` step from `face₁Dart₁` is the deleted chord reverse. -/
private lemma face₁Dart₁_inv_firstOutside_ge_two
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    2 ≤ Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₁ (face₁Dart₁ data) := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  have hpos : 0 < Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₁
      (face₁Dart₁ data) :=
    Equiv.Perm.DeleteSet.firstOutside_pos M.σ⁻¹ data.keptDel₁ _
  have heq1 : Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₁
      (face₁Dart₁ data) = 1 := by omega
  have hnot := Equiv.Perm.DeleteSet.firstOutside_notMem M.σ⁻¹ data.keptDel₁
    (face₁Dart₁ data)
  rw [heq1, pow_one] at hnot
  have hstep : M.σ⁻¹ ((face₁Dart₁ data : {d : D // d ∉ data.keptDel₁}) : D)
      = M.α data.dart := by
    show M.σ⁻¹ (M.φ data.dart) = M.α data.dart
    apply M.σ.injective
    calc
      M.σ (M.σ⁻¹ (M.φ data.dart)) = M.φ data.dart :=
        Equiv.apply_symm_apply M.σ (M.φ data.dart)
      _ = M.σ (M.α data.dart) := by
        show M.φ data.dart = (M.σ * M.α) data.dart
        rfl
  have hdeleted : M.α data.dart ∈ data.keptDel₁ := by
    by_contra hαdel
    exact data.alphaDart_notMem_keptSet₁ hsep ((data.mem_keptDel₁_iff _).1 hαdel)
  exact hnot (by rwa [hstep])

/-- First endpoint face fact: the kept `σ`-successor of `a₀` is not a side-1 dart. -/
theorem face_ρa₀_not_side₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.dartFace ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) ∉ data.side₁ := by
  classical
  intro htarget
  set x : {d : D // d ∉ data.keptDel₁} :=
    data.sideAlpha₁ hsep (face₁Dart₂ data) with hx
  set n := Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₁ x with hn
  set p : D := (M.σ ^ (n - 1)) x.1 with hp
  have hn_ge : 2 ≤ n := by
    rw [hn]
    exact ProofsInTheBook.ChordBigonWrap.sideSigma₁_sideAlpha₁_firstOutside_ge_two data hsep
  have hp_deleted : p ∈ data.keptDel₁ := by
    by_contra hp_not
    have hmin := Equiv.Perm.DeleteSet.firstOutside_min M.σ data.keptDel₁ x
      (m := n - 1) (by rw [hn]; omega)
    exact hmin ⟨by omega, by simpa [p] using hp_not⟩
  have htarget_coe :
      ((data.sideSigma₁ (side₁Anchor₀ data hsep)) : D) = (M.σ ^ n) x.1 := by
    rw [sideSigma₁_side₁Anchor₀ data hsep]
    change ((data.sideSigma₁ (data.sideAlpha₁ hsep (face₁Dart₂ data))) : D)
        = (M.σ ^ n) x.1
    rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl]
    rw [FilteredRotation.filteredRotation_apply_coe]
  have htarget_side_pow : M.dartFace ((M.σ ^ n) x.1) ∈ data.side₁ := by
    rw [htarget_coe] at htarget
    exact htarget
  have hσp : M.σ p = (M.σ ^ n) x.1 := by
    rw [hp]
    have hs : n - 1 + 1 = n := by omega
    rw [← hs, pow_succ']
    rfl
  have hαp_side : M.dartFace (M.α p) ∈ data.side₁ := by
    rw [← ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha (M := M) p]
    rw [hσp]
    exact htarget_side_pow
  have hp_ne_dart : p ≠ data.dart := by
    intro hpd
    have hface₂_side : data.face₂ ∈ data.side₁ := by
      have : M.dartFace (M.α data.dart) ∈ data.side₁ := by
        rwa [hpd] at hαp_side
      simpa [ChordSplitData.face₂] using this
    exact hsep hface₂_side
  have hx_coe : (x : D) = M.α (M.φ (M.φ data.dart)) := by
    rw [hx, data.sideAlpha₁_apply_coe hsep]
    rfl
  have hp_tail : M.tail p = M.tail data.dart := by
    rw [hp, ProofsInTheBook.ChordSigmaContig.tail_pow_sigma, hx_coe,
      ProofsInTheBook.ChordSigmaContig.tail_alpha_phiSq_dart data]
  have hp_ne_alpha_dart : p ≠ M.α data.dart := by
    intro hpα
    have htail_eq : M.tail data.dart = M.head data.dart := by
      rw [← hp_tail, hpα, M.tail_alpha]
    exact ProofsInTheBook.ChordSigmaContig.u_ne_v data htail_eq
  have hp_kept : p ∈ data.keptSet₁ := by
    by_cases hp_outer : M.dartFace p = hNT.outerFace
    · exact ⟨Or.inr ⟨hp_outer, hαp_side⟩, by simpa using hp_ne_dart⟩
    · have hp_not_boundary : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge p) := by
        intro hbe
        rcases data.boundaryEdge_dart_outer hbe with hpout | hαout
        · exact hp_outer hpout
        · exact data.side₁_subset_nonouter hαp_side hαout
      have hp_not_chord : M.dartEdge p ≠ s(u, v) := by
        intro hch
        rcases data.chord_edge_darts hch with hpd | hpα
        · exact hp_ne_dart hpd
        · exact hp_ne_alpha_dart hpα
      have hp_side : M.dartFace p ∈ data.side₁ := by
        have hα_edge_not_boundary :
            ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge (M.α p)) := by
          intro hbe
          exact hp_not_boundary (by rwa [M.dartEdge_alpha] at hbe)
        have hα_edge_not_chord : M.dartEdge (M.α p) ≠ s(u, v) := by
          intro hch
          exact hp_not_chord (by rwa [M.dartEdge_alpha] at hch)
        have := data.alpha_mem_side₁_of_interior (e := M.α p) hαp_side
          hα_edge_not_boundary hα_edge_not_chord
        rwa [M.alpha_alpha] at this
      exact keptSet₁_of_side₁_ne_dart hNT data hp_side hp_ne_dart
  have hp_not_deleted : p ∉ data.keptDel₁ := (data.mem_keptDel₁_iff p).2 hp_kept
  exact hp_not_deleted hp_deleted

/-- Second endpoint face fact: the edge-reverse of `a₁` is not a side-1 dart. -/
theorem face_βa₁_not_side₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.dartFace ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D) ∉ data.side₁ := by
  classical
  intro hβside
  set x : {d : D // d ∉ data.keptDel₁} := face₁Dart₁ data with hx
  set n := Equiv.Perm.DeleteSet.firstOutside M.σ⁻¹ data.keptDel₁ x with hn
  set p : D := (M.σ⁻¹ ^ (n - 1)) x.1 with hp
  have hn_ge : 2 ≤ n := by
    rw [hn, hx]
    exact face₁Dart₁_inv_firstOutside_ge_two hNT data hsep
  have hp_deleted : p ∈ data.keptDel₁ := by
    by_contra hp_not
    have hmin := Equiv.Perm.DeleteSet.firstOutside_min M.σ⁻¹ data.keptDel₁ x
      (m := n - 1) (by rw [hn]; omega)
    exact hmin ⟨by omega, by simpa [p] using hp_not⟩
  have ha₁_coe : ((side₁Anchor₁ data hsep) : D) = (M.σ⁻¹ ^ n) x.1 := by
    rw [side₁Anchor₁]
    change ((Equiv.Perm.DeleteSet.deleteSetFun M.σ⁻¹ data.keptDel₁
        (face₁Dart₁ data)) : D) = (M.σ⁻¹ ^ n) x.1
    rw [Equiv.Perm.DeleteSet.deleteSetFun_coe]
  have hσa₁ : M.σ ((side₁Anchor₁ data hsep : {d : D // d ∉ data.keptDel₁}) : D) = p := by
    rw [ha₁_coe, hp]
    have hs : n - 1 + 1 = n := by omega
    have hpow : (M.σ⁻¹ ^ n) x.1 = M.σ⁻¹ ((M.σ⁻¹ ^ (n - 1)) x.1) := by
      rw [← hs, pow_succ']
      rfl
    rw [hpow]
    simp
  have hβcoe : ((data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)) : D)
      = M.α ((side₁Anchor₁ data hsep : {d : D // d ∉ data.keptDel₁}) : D) := by
    rw [data.sideAlpha₁_apply_coe hsep]
  have hp_side : M.dartFace p ∈ data.side₁ := by
    rw [← hσa₁]
    rw [ProofsInTheBook.ZinanCh35StarConn.dartFace_sigma_eq_alpha (M := M)]
    rwa [← hβcoe]
  have hp_tail : M.tail p = M.head data.dart := by
    rw [hp, tail_pow_sigma_inv, hx]
    exact ProofsInTheBook.ChordSigmaContig.face₁Dart₁_tail data
  have hp_ne_dart : p ≠ data.dart := by
    intro hpd
    have htail_eq : M.tail data.dart = M.head data.dart := by
      rw [← hp_tail, hpd]
    exact ProofsInTheBook.ChordSigmaContig.u_ne_v data htail_eq
  have hp_not_deleted : p ∉ data.keptDel₁ :=
    (data.mem_keptDel₁_iff p).2 (keptSet₁_of_side₁_ne_dart hNT data hp_side hp_ne_dart)
  exact hp_not_deleted hp_deleted

/-- Canonical endpoint alignment with the two cyclic-order face facts discharged. -/
theorem canonicalBwdArcEndpointAlignment_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    CanonicalBwdArcEndpointAlignment hNT data hsep :=
  canonicalBwdArcEndpointAlignment_of_faces hNT data hsep
    (face_ρa₀_not_side₁ hNT data hsep)
    (face_βa₁_not_side₁ hNT data hsep)

/-- Unconditional `OuterTraceInjOn` for the canonical anchors. -/
theorem canonical_OuterTraceInjOn_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    OuterTraceInjOn hNT data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) :=
  canonical_OuterTraceInjOn_of_alignment hNT data hsep
    (canonicalBwdArcEndpointAlignment_uncond hNT data hsep)

/-- **The side-1 `outer_simple` keystone, UNCONDITIONAL** (canonical anchors).  Feeds the closed
`OuterTraceInjOn` into `side₁_outer_simple_canonical`.  This is exactly the `outer_simple` field
`ZinanCh35Contiguous.contiguousInterval_holds` consumes — no longer a residue. -/
theorem side₁_outer_simple_canonical_uncond
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).faceDartList (Sum.inr 1)).map
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).tail).Nodup :=
  side₁_outer_simple_canonical hNT data hsep (canonical_OuterTraceInjOn_uncond hNT data hsep)

/-- **Canonical chord-incidence non-degeneracy.**  The two chord-incidence darts consumed by
the Layer-B `outer_len` itinerary are the first and last darts of `bwdArc`; the arc has length at
least two, so tail-injectivity keeps those endpoints distinct. -/
theorem side₁ChordIncidenceNonDegenerate_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ProofsInTheBook.ZinanCh35Contiguous.Side₁ChordIncidenceNonDegenerate data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) := by
  classical
  intro h
  have H := canonicalBwdArcEndpointAlignment_uncond hNT data hsep
  have hfirst :
      data.sideSigma₁ (side₁Anchor₀ data hsep)
        = ⟨(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
            (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx,
          bwdArc_arcDart_notMem_keptDel₁ hNT data hsep _⟩ :=
    sideSigma₁_anchor₀_eq_bwdArc_first hNT data hsep H.ρa₀_boundary
  have hlast :
      data.sideAlpha₁ hsep (side₁Anchor₁ data hsep)
        = ⟨(ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
            (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx,
          bwdArc_arcDart_notMem_keptDel₁ hNT data hsep _⟩ :=
    sideAlpha₁_anchor₁_eq_bwdArc_last hNT data hsep H.βa₁_boundary
  have htail_eq :
      M.tail ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx)
        = M.tail ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).arcDart
          (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx) := by
    have hval := congrArg Subtype.val h
    rw [hfirst, hlast] at hval
    exact congrArg M.tail hval
  have hidx :
      (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx
        = (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx :=
    (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).tail_nodup htail_eq
  have hidx_val :
      ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx : ℕ)
        = ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx : ℕ) :=
    congrArg Fin.val hidx
  have hlen_ge : 2 ≤ (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).len :=
    ProofsInTheBook.ZinanCh35ArcSide.bwdArc_len data
  have hlast_val :
      ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).lastIdx : ℕ)
        = (ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).len - 1 := rfl
  have hfirst_val :
      ((ProofsInTheBook.ZinanCh35ArcSide.bwdArc data).firstIdx : ℕ) = 0 := rfl
  omega

/-- Translate a side-map dart-edge equality to the corresponding unordered pair of projected
ambient endpoints.  This is the local bridge used for side-map simplicity. -/
private lemma sideMap₁_dartEdge_eq_to_M_proj_edge
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    {x y : {d : D // d ∉ data.keptDel₁} ⊕ Fin 2}
    (h : (data.sideMap₁ hsep a₀ a₁ hne).dartEdge x
        = (data.sideMap₁ hsep a₀ a₁ hne).dartEdge y) :
    s(M.tail (proj a₀ a₁ x).1,
        M.tail (proj a₀ a₁ (freshAlpha (data.sideAlpha₁ hsep) x)).1)
      =
    s(M.tail (proj a₀ a₁ y).1,
        M.tail (proj a₀ a₁ (freshAlpha (data.sideAlpha₁ hsep) y)).1) := by
  classical
  unfold CombMap.dartEdge at h
  rcases Sym2.eq_iff.1 h with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · have htM := (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne x y).1 ht
    have hhTail :
        (data.sideMap₁ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₁ hsep) x)
          = (data.sideMap₁ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₁ hsep) y) := by
      simpa [CombMap.head] using hh
    have hhM := (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne
      (freshAlpha (data.sideAlpha₁ hsep) x) (freshAlpha (data.sideAlpha₁ hsep) y)).1 hhTail
    exact Sym2.eq_iff.2 (Or.inl ⟨htM, hhM⟩)
  · have htTail :
        (data.sideMap₁ hsep a₀ a₁ hne).tail x
          = (data.sideMap₁ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₁ hsep) y) := by
      simpa [CombMap.head] using ht
    have htM := (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne x
      (freshAlpha (data.sideAlpha₁ hsep) y)).1 htTail
    have hhTail :
        (data.sideMap₁ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₁ hsep) x)
          = (data.sideMap₁ hsep a₀ a₁ hne).tail y := by
      simpa [CombMap.head] using hh
    have hhM := (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne
      (freshAlpha (data.sideAlpha₁ hsep) x) y).1 hhTail
    exact Sym2.eq_iff.2 (Or.inr ⟨htM, hhM⟩)

/-- The chord dart and its reverse are not side-1 kept darts. -/
private lemma no_kept_dart_on_chord_edge
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (x : {d : D // d ∉ data.keptDel₁})
    (hxedge : M.dartEdge x.1 = M.dartEdge data.dart) : False := by
  have hchord : M.dartEdge x.1 = s(u, v) := by
    exact hxedge.trans (hNT.chordDart_edge data.chord)
  rcases data.chord_edge_darts hchord with hx | hx
  · exact x.2 (hx ▸ ProofsInTheBook.ChordFaceFinal.dart_mem_keptDel₁ data)
  · have hαdel : M.α data.dart ∈ data.keptDel₁ := by
      by_contra hnot
      exact data.alphaDart_notMem_keptSet₁ hsep ((data.mem_keptDel₁_iff _).1 hnot)
    exact x.2 (hx ▸ hαdel)

/-- **Side-map simplicity for the canonical side-1 anchors.**  The kept-kept cases inherit
simplicity from `M`; the fresh-fresh cases are the new chord edge; the mixed cases would put a kept
dart on the original chord edge, impossible because both chord darts are deleted from side 1. -/
theorem sideMap₁_isSimpleGraph_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).IsSimpleGraph := by
  classical
  let a₀ : {d : D // d ∉ data.keptDel₁} := side₁Anchor₀ data hsep
  let a₁ : {d : D // d ∉ data.keptDel₁} := side₁Anchor₁ data hsep
  let hne : a₀ ≠ a₁ := side₁Anchors_ne data hsep
  change (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph
  have ha₀ : M.tail a₀.1 = M.tail data.dart := by
    dsimp [a₀]
    exact canonicalAnchor₀_tail data hsep
  have ha₁ : M.tail a₁.1 = M.head data.dart := by
    dsimp [a₁]
    exact canonicalAnchor₁_tail data hsep
  have hαdart_del : M.α data.dart ∈ data.keptDel₁ := by
    by_contra hnot
    exact data.alphaDart_notMem_keptSet₁ hsep ((data.mem_keptDel₁_iff _).1 hnot)
  refine ⟨?_, ?_⟩
  · intro x hloop
    have htail :
        (data.sideMap₁ hsep a₀ a₁ hne).tail x
          = (data.sideMap₁ hsep a₀ a₁ hne).tail (freshAlpha (data.sideAlpha₁ hsep) x) := by
      simpa [CombMap.head] using hloop
    have hMtail := (sideMap₁_tail_eq_iff_M_tail_proj data hsep a₀ a₁ hne x
      (freshAlpha (data.sideAlpha₁ hsep) x)).1 htail
    cases x with
    | inl k =>
        apply hNT.simpleGraph.no_loop k.1
        simpa [freshAlpha_inl, data.sideAlpha₁_apply_coe hsep, M.tail_alpha] using hMtail
    | inr j =>
        fin_cases j
        · have huv : M.tail data.dart = M.head data.dart := by
            simpa [freshAlpha_inr, proj, ha₀, ha₁] using hMtail
          exact ProofsInTheBook.ChordSigmaContig.u_ne_v data huv
        · have hvu : M.head data.dart = M.tail data.dart := by
            simpa [freshAlpha_inr, proj, ha₀, ha₁] using hMtail
          exact ProofsInTheBook.ChordSigmaContig.u_ne_v data hvu.symm
  · intro x y hxy
    have hMedge := sideMap₁_dartEdge_eq_to_M_proj_edge hNT data hsep a₀ a₁ hne hxy
    cases x with
    | inl kx =>
        cases y with
        | inl ky =>
            have hM : M.dartEdge kx.1 = M.dartEdge ky.1 := by
              simpa [CombMap.dartEdge, freshAlpha_inl, data.sideAlpha₁_apply_coe hsep,
                M.tail_alpha] using hMedge
            have hsc : M.α.SameCycle kx.1 ky.1 := hNT.simpleGraph.no_parallel hM
            rcases (M.alpha_sameCycle_iff kx.1 ky.1).mp hsc with hsame | halpha
            · have hky : ky = kx := Subtype.ext hsame
              rw [hky]
            · have hky : ky = data.sideAlpha₁ hsep kx := by
                apply Subtype.ext
                rw [data.sideAlpha₁_apply_coe hsep]
                exact halpha
              refine ⟨1, ?_⟩
              rw [zpow_one]
              change freshAlpha (data.sideAlpha₁ hsep) (Sum.inl kx) = Sum.inl ky
              rw [freshAlpha_inl, hky]
        | inr jy =>
            fin_cases jy
            · have hxedge : M.dartEdge kx.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₁_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁] using hMedge
              exact False.elim (no_kept_dart_on_chord_edge hNT data hsep kx hxedge)
            · have hxedge : M.dartEdge kx.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₁_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁,
                  Sym2.eq_swap] using hMedge
              exact False.elim (no_kept_dart_on_chord_edge hNT data hsep kx hxedge)
    | inr jx =>
        cases y with
        | inl ky =>
            fin_cases jx
            · have hyedge : M.dartEdge ky.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₁_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁,
                  Sym2.eq_swap] using hMedge.symm
              exact False.elim (no_kept_dart_on_chord_edge hNT data hsep ky hyedge)
            · have hyedge : M.dartEdge ky.1 = M.dartEdge data.dart := by
                unfold CombMap.dartEdge
                simpa [CombMap.dartEdge, freshAlpha_inl, freshAlpha_inr,
                  data.sideAlpha₁_apply_coe hsep, M.tail_alpha, proj, ha₀, ha₁,
                  Sym2.eq_swap] using hMedge.symm
              exact False.elim (no_kept_dart_on_chord_edge hNT data hsep ky hyedge)
        | inr jy =>
            fin_cases jx <;> fin_cases jy
            · exact Equiv.Perm.SameCycle.refl _ _
            · refine ⟨1, ?_⟩
              rw [zpow_one]
              change freshAlpha (data.sideAlpha₁ hsep) (Sum.inr 0) = Sum.inr 1
              rw [freshAlpha_inr]
              rfl
            · refine ⟨1, ?_⟩
              rw [zpow_one]
              change freshAlpha (data.sideAlpha₁ hsep) (Sum.inr 1) = Sum.inr 0
              rw [freshAlpha_inr]
              rfl
            · exact Equiv.Perm.SameCycle.refl _ _

/-- `g.SameCycle k₀ c` with `g` swapping `k₀ ↔ k₁` forces `c` to be one of the two
swapped points.  This is the membership half of `ChordAnchor.twoCycle_orbit_card`, exposed here
because the original helper is private. -/
lemma sameCycle_mem_of_twoCycle {K : Type u} [Fintype K] {g : Equiv.Perm K} {k₀ k₁ c : K}
    (h01 : g k₀ = k₁) (h10 : g k₁ = k₀) (h : g.SameCycle k₀ c) :
    c = k₀ ∨ c = k₁ := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  have hiter : ∀ m : ℕ, g^[m] k₀ = k₀ ∨ g^[m] k₀ = k₁ := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        rw [Function.iterate_succ_apply']
        rcases ih with hmk₀ | hmk₁
        · rw [hmk₀]; exact Or.inr h01
        · rw [hmk₁]; exact Or.inl h10
  rcases hiter n with hnk₀ | hnk₁
  · exact Or.inl (by rw [← hn, hnk₀])
  · exact Or.inr (by rw [← hn, hnk₁])

/-- The touched side face
`f₀ = S.dartFace (Sum.inl (face₁Dart₁ data))` has only kept-`inl` representatives whose
underlying `M`-face is `data.face₁`, for the canonical side-1 anchors. -/
theorem touched_face₁_reps_all_face₁_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁})
    (hk :
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl k)
        =
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data))) :
    M.dartFace k.1 = data.face₁ := by
  classical
  have hτ :
      (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        k (face₁Dart₁ data) :=
    (ProofsInTheBook.ChordBoundaryOrbit.sideFace_inl_eq_iff_tracePhi
      (data.sideAlpha₁ hsep) data.sideSigma₁
      (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
      (side₁Anchors_ne data hsep) k (face₁Dart₁ data)).1 hk
  have hmem :
      k = face₁Dart₁ data ∨ k = face₁Dart₂ data :=
    sameCycle_mem_of_twoCycle
      (side₁Anchors_trace12 data hsep) (side₁Anchors_trace21 data hsep) hτ.symm
  rcases hmem with hk1 | hk2
  · rw [hk1]
    exact (ProofsInTheBook.ChordFaceFinal.face₁_two_kept_darts data).2.2.2.1
  · rw [hk2]
    exact (ProofsInTheBook.ChordFaceFinal.face₁_two_kept_darts data).2.2.2.2

/-- **Definite verdict for §3.3:** canonical `InnerRepsAvoidBoundary` is false.  The witness is
the touched face `f₀ = S.dartFace (Sum.inl (face₁Dart₁ data))`, which is non-outer but whose
kept-`inl` representatives all map back to `data.face₁`. -/
theorem innerRepsAvoidBoundary_canonical_false
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    ¬ ProofsInTheBook.ChordBoundaryOrbit.InnerRepsAvoidBoundary data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)
      ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1)) := by
  classical
  intro hreps
  set S := data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
    (side₁Anchors_ne data hsep) with hS
  set f₀ : S.Face := S.dartFace (Sum.inl (face₁Dart₁ data)) with hf₀
  have hf₀_ne :
      f₀ ≠ S.dartFace (Sum.inr 1) := by
    subst f₀
    subst S
    exact side₁_face₁_not_outer_canonical data hsep
  obtain ⟨k, hkf, _, hkface₁⟩ := hreps f₀ hf₀_ne
  have hkf₀ :
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl k)
        =
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data)) := by
    subst f₀
    subst S
    exact hkf
  exact hkface₁ (touched_face₁_reps_all_face₁_canonical hNT data hsep k hkf₀)

end ProofsInTheBook.ZinanCh35OuterTraceProof

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_OuterTraceInjOn_of_arcTrace
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_side₁_outer_orbit_mem_iff
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_arcTrace_of_tracePhiArc
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.sideSigma₁_alpha_arcDart_eq_next
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.canonicalTracePhiArc_of_steps
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_OuterTraceInjOn_of_alignment
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.canonical_OuterTraceInjOn_uncond

#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.side₁_outer_simple_canonical_uncond
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.side₁ChordIncidenceNonDegenerate_canonical
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.sideMap₁_isSimpleGraph_canonical
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.touched_face₁_reps_all_face₁_canonical
#print axioms ProofsInTheBook.ZinanCh35OuterTraceProof.innerRepsAvoidBoundary_canonical_false
