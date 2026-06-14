import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapEuler
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction
import ProofsInTheBook.Ch13ActiveComponent
import ProofsInTheBook.Ch13FlipTransport
import ProofsInTheBook.PlanarMapNearTriangulation

/-!
# Ch13 component closure: discharging `hFaceDeg` (no-digon) and `hconn` (component extraction)

This file closes the last two residuals of the simple-sphere discrete Cauchy combinatorial lemma:

* **`hFaceDeg` (no-digon)** — a simple combinatorial map has all faces of degree `≥ 3`, *unless* the
  component is a single edge (a genuine digon, handled by the trivial branch).  Derived from
  `M.IsSimpleGraph` (`no_loop` rules out length-1 faces, `no_parallel` rules out digons) once the
  active component has `≥ 2` edges.

* **`hconn` (component extraction)** — the active subgraph may be disconnected; we delete everything
  outside `d₀`'s active component, obtaining a connected kept (active) map by construction.

Assembling these with `Ch13FlipTransport.marked_sphere_low_active_vertex_no_htrans` (transport already
discharged) yields the headline `cauchy_marked_sphere_low_active_vertex_simple`.
-/

namespace ProofsInTheBook.Ch13ComponentClose

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction
open ProofsInTheBook.Ch13ActiveComponent
open ProofsInTheBook.Ch13FlipTransport
open ProofsInTheBook.SubmapPlanar
open EdgeSign
open Equiv Equiv.Perm

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Part 1: a simple combinatorial map with no digon faces has `faceDeg ≥ 3` -/

/-- `faceDeg = faceLen` (same orbit-card definition). -/
theorem faceDeg_eq_faceLen (M : CombMap D) (Q : Quotient (cycleSetoid M.φ)) :
    faceDeg M Q = M.faceLen Q := rfl

/-- A face has degree `≥ 2` for any simple map (no length-1 face: `phi_ne_self`). -/
theorem two_le_faceDeg_of_simple (M : CombMap D) (hM : M.IsSimpleGraph)
    (Q : Quotient (cycleSetoid M.φ)) : 2 ≤ faceDeg M Q := by
  obtain ⟨d, rfl⟩ := Q.exists_rep
  have hφ : M.φ d ≠ d := phi_ne_self_of_isSimpleGraph M hM d
  rw [faceDeg_eq_faceLen]
  show 2 ≤ M.faceLen (M.dartFace d)
  rw [faceLen_dartFace_eq_card_support_cycleOf M hφ]
  exact (Equiv.Perm.isCycle_cycleOf M.φ hφ).two_le_card_support

/-- **No digon in a simple map: every face has degree `≥ 3`** unless its boundary darts `d, φd`
form a single `α`-edge (`φ d = α d`), the genuine single-edge digon. -/
theorem three_le_faceDeg_of_simple_of_not_singleEdge (M : CombMap D) (hM : M.IsSimpleGraph)
    (Q : Quotient (cycleSetoid M.φ))
    (hNoDigonEdge : ∀ d : D, Quotient.mk (cycleSetoid M.φ) d = Q → M.φ d ≠ M.α d) :
    3 ≤ faceDeg M Q := by
  obtain ⟨d, rfl⟩ := Q.exists_rep
  have hφ : M.φ d ≠ d := phi_ne_self_of_isSimpleGraph M hM d
  rw [faceDeg_eq_faceLen]
  show 3 ≤ M.faceLen (M.dartFace d)
  rw [faceLen_dartFace_eq_card_support_cycleOf M hφ]
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ (M.φ.cycleOf d).support.card :=
    (Equiv.Perm.isCycle_cycleOf M.φ hφ).two_le_card_support
  have hcard2 : (M.φ.cycleOf d).support.card = 2 := by omega
  have hpow := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply M.φ 2 d
  rw [hcard2] at hpow
  have hsq : M.φ (M.φ d) = d := by
    have : (M.φ ^ 2) d = d := by simpa using hpow.symm
    simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using this
  have he1 : M.dartEdge d = s(M.tail d, M.tail (M.φ d)) := M.dartEdge_eq_mk_tail_tail_phi d
  have he2 : M.dartEdge (M.φ d) = s(M.tail (M.φ d), M.tail d) := by
    rw [M.dartEdge_eq_mk_tail_tail_phi (M.φ d), hsq]
  have hedge : M.dartEdge d = M.dartEdge (M.φ d) := by rw [he1, he2, Sym2.eq_swap]
  have hsc : M.α.SameCycle d (M.φ d) := hM.no_parallel hedge
  rcases (M.alpha_sameCycle_iff d (M.φ d)).mp hsc with hcase | hcase
  · exact hφ hcase
  · exact hNoDigonEdge d rfl hcase

/-! ## Part 2: the kept (active sub-)map inherits `IsSimpleGraph` from `M`

`keptMap.σ = deleteSet M.σ Del`, `keptMap.α x = M.α x.1`.  Two kept darts are in the same kept
vertex (`deleteSet M.σ Del`-cycle) iff their underlying darts are in the same `M.σ`-cycle
(`sameCycle_deleteSet_iff`).  This transports `M.tail`/`M.head` equalities to/from the kept map, so
`no_loop`/`no_parallel` descend. -/

/-- Two kept darts have the same kept tail-vertex iff their underlying darts have the same
`M`-tail-vertex. -/
theorem keptMap_tail_eq_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).tail x = (keptMap M Del hsub).tail y ↔ M.tail x.1 = M.tail y.1 := by
  unfold CombMap.tail
  rw [Quotient.eq, Quotient.eq]
  show (keptMap M Del hsub).σ.SameCycle x y ↔ M.σ.SameCycle x.1 y.1
  exact Equiv.Perm.sameCycle_deleteSet_iff M.σ Del x y

/-- The kept head-vertex of `x` is the `M`-head-vertex of `x.1`, transported. -/
theorem keptMap_head_eq_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).head x = (keptMap M Del hsub).head y ↔ M.head x.1 = M.head y.1 := by
  unfold CombMap.head
  rw [Quotient.eq, Quotient.eq]
  show (keptMap M Del hsub).σ.SameCycle ((keptMap M Del hsub).α x) ((keptMap M Del hsub).α y)
      ↔ M.σ.SameCycle (M.α x.1) (M.α y.1)
  have hx : ((keptMap M Del hsub).α x : D) = M.α x.1 := by
    rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub x
  have hy : ((keptMap M Del hsub).α y : D) = M.α y.1 := by
    rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub y
  rw [← hx, ← hy]
  exact Equiv.Perm.sameCycle_deleteSet_iff M.σ Del _ _

/-- Cross form: kept-tail of `x` equals kept-head of `y` iff `M`-tail of `x.1` equals `M`-head of
`y.1`. -/
theorem keptMap_tail_eq_head_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).tail x = (keptMap M Del hsub).head y ↔ M.tail x.1 = M.head y.1 := by
  unfold CombMap.tail CombMap.head
  rw [Quotient.eq, Quotient.eq]
  show (keptMap M Del hsub).σ.SameCycle x ((keptMap M Del hsub).α y)
      ↔ M.σ.SameCycle x.1 (M.α y.1)
  have hy : ((keptMap M Del hsub).α y : D) = M.α y.1 := by
    rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub y
  rw [← hy]
  exact Equiv.Perm.sameCycle_deleteSet_iff M.σ Del _ _

/-- The kept `dartEdge` of `x` is `s(keptTail x, keptHead x)`; we compare via the `M`-endpoints. -/
theorem keptMap_dartEdge_eq_iff (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (x y : {d : D // d ∉ Del}) :
    (keptMap M Del hsub).dartEdge x = (keptMap M Del hsub).dartEdge y
      ↔ M.dartEdge x.1 = M.dartEdge y.1 := by
  unfold CombMap.dartEdge
  rw [Sym2.eq_iff, Sym2.eq_iff,
    keptMap_tail_eq_iff M Del hsub x y, keptMap_head_eq_iff M Del hsub x y,
    keptMap_tail_eq_head_iff M Del hsub x y,
    show ((keptMap M Del hsub).head x = (keptMap M Del hsub).tail y)
        ↔ (M.head x.1 = M.tail y.1) from by
      rw [eq_comm, keptMap_tail_eq_head_iff M Del hsub y x, eq_comm]]

/-- **The kept (active sub-)map inherits `IsSimpleGraph`.** -/
theorem keptMap_isSimpleGraph (M : CombMap D) (hM : M.IsSimpleGraph) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    (keptMap M Del hsub).IsSimpleGraph where
  no_loop x := by
    rw [Ne, keptMap_tail_eq_head_iff M Del hsub x x]
    exact hM.no_loop x.1
  no_parallel {x y} h := by
    -- kept dartEdge equal ⟹ M dartEdge equal ⟹ M.α.SameCycle x.1 y.1 ⟹ keptAlpha.SameCycle x y
    rw [keptMap_dartEdge_eq_iff M Del hsub x y] at h
    have hMsc : M.α.SameCycle x.1 y.1 := hM.no_parallel h
    -- y.1 ∈ {x.1, M.α x.1}; both kept; gives keptAlpha.SameCycle x y
    rcases (M.alpha_sameCycle_iff x.1 y.1).mp hMsc with hxy | hxy
    · -- y = x
      have hyx : y = x := Subtype.ext hxy
      exact hyx ▸ Equiv.Perm.SameCycle.rfl
    · -- y = M.α x.1 = keptAlpha x (coercion)
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have hcoe : ((keptMap M Del hsub).α x : D) = M.α x.1 := by
        rw [keptMap_alpha]; exact keptAlpha_apply_coe M Del hsub x
      rw [zpow_one, hcoe]
      exact hxy.symm

/-! ## Part 3: the active-component deletion `Del` and its connectivity

Fix an active "seed" dart `d₀` (`es d₀ ≠ zero`).  The **active step relation** links two darts that
share a vertex (`M.σ`-cycle) or an edge (`α`) **provided both are active**.  Deleting everything not
`EqvGen`-related to `d₀` under this relation leaves exactly `d₀`'s active connected component — which
is connected by construction. -/

/-- The active step relation: a vertex- or edge-step between two **active** darts. -/
def activeStep (M : CombMap D) (es : D → EdgeSign) (d e : D) : Prop :=
  (M.σ.SameCycle d e ∨ e = M.α d) ∧ es d ≠ EdgeSign.zero ∧ es e ≠ EdgeSign.zero

/-- `activeStep` is symmetric. -/
theorem activeStep_symm (M : CombMap D) (es : D → EdgeSign)
    {d e : D} (h : activeStep M es d e) : activeStep M es e d := by
  obtain ⟨hstep, hd, he⟩ := h
  refine ⟨?_, he, hd⟩
  rcases hstep with hσ | hα
  · exact Or.inl hσ.symm
  · refine Or.inr ?_
    subst hα
    rw [M.alpha_alpha]

open scoped Classical in
/-- The active-component deletion: everything **not** `EqvGen activeStep`-related to the seed `d₀`. -/
noncomputable def compDel (M : CombMap D) (es : D → EdgeSign) (d₀ : D) : Finset D :=
  Finset.univ.filter (fun d => ¬ Relation.EqvGen (activeStep M es) d₀ d)

@[simp] theorem mem_compDel (M : CombMap D) (es : D → EdgeSign) (d₀ d : D) :
    d ∈ compDel M es d₀ ↔ ¬ Relation.EqvGen (activeStep M es) d₀ d := by
  classical
  rw [compDel, Finset.mem_filter]
  simp

/-- A dart **not** in `compDel` is `EqvGen`-reached from `d₀`. -/
theorem reached_of_notMem_compDel (M : CombMap D) (es : D → EdgeSign) (d₀ d : D)
    (hd : d ∉ compDel M es d₀) : Relation.EqvGen (activeStep M es) d₀ d := by
  by_contra h
  exact hd ((mem_compDel M es d₀ d).2 h)

/-- Any `EqvGen activeStep` pair is either equal or both active. -/
theorem eqvGen_activeStep_active (M : CombMap D) (es : D → EdgeSign) {a b : D}
    (h : Relation.EqvGen (activeStep M es) a b) :
    (es a ≠ EdgeSign.zero ∧ es b ≠ EdgeSign.zero) ∨ a = b := by
  induction h with
  | rel x y hxy => exact Or.inl ⟨hxy.2.1, hxy.2.2⟩
  | refl x => exact Or.inr rfl
  | symm x y _ ih =>
      rcases ih with ⟨hx, hy⟩ | hxy
      · exact Or.inl ⟨hy, hx⟩
      · exact Or.inr hxy.symm
  | trans x y z _ _ ih1 ih2 =>
      rcases ih1 with ⟨hx, hy⟩ | hxy
      · rcases ih2 with ⟨_, hz⟩ | hyz
        · exact Or.inl ⟨hx, hz⟩
        · subst hyz; exact Or.inl ⟨hx, hy⟩
      · subst hxy; exact ih2

/-- Every dart `EqvGen`-reached from the active seed `d₀` is itself active. -/
theorem reached_active (M : CombMap D) (es : D → EdgeSign) {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero)
    {d : D} (h : Relation.EqvGen (activeStep M es) d₀ d) : es d ≠ EdgeSign.zero := by
  rcases eqvGen_activeStep_active M es h with ⟨_, hd⟩ | hd
  · exact hd
  · exact hd ▸ hd₀

/-- The seed `d₀` is reached from itself. -/
theorem reached_refl (M : CombMap D) (es : D → EdgeSign) (d₀ : D) :
    Relation.EqvGen (activeStep M es) d₀ d₀ := Relation.EqvGen.refl _

/-! ## Part 4: orbit-local flip-count transport

`Ch13FlipTransport.flip_transport` assumes the deleted set `Del` is *globally* the zero set
(`hDelZero`/`hKeptNonzero`).  For the active-component deletion `compDel` that fails — `compDel`
also removes the active darts of *other* components.  But on the `M.σ`-orbit of any kept dart the
deleted darts are still exactly the zeros (an active σ-neighbour of a kept dart is in the same
active component, hence kept).  So we generalize the transport to an **orbit-local** zero
hypothesis, copying the three hSzero-using lemmas of `Ch13FlipTransport` with the global
characterization replaced by the orbit-local one.  The structural `deleteSet` manipulations
(`deleteSet_toList_map_val`, `filterMap_toStrict_eq_filter_map`) are hSzero-free and reused as is. -/

open ProofsInTheBook.Ch13FlipTransport in
/-- **Orbit-local kept-strict-list identity** (nontrivial case).  Same as
`Ch13FlipTransport.kept_strict_list_eq` but with the global `hSzero` replaced by the orbit-local
characterization `hSorbit` on the `p`-orbit of `x.1`. -/
theorem kept_strict_list_eq_orbit (p : Equiv.Perm D) (es : D → EdgeSign) (S : Finset D)
    (x : {d : D // d ∉ S})
    (hSorbit : ∀ c, p.SameCycle x.1 c → (c ∈ S ↔ es c = EdgeSign.zero))
    (hL : 0 < (p.toList x.1).length) (hL'pos : 0 < ((Equiv.Perm.deleteSet p S).toList x).length) :
    ((Equiv.Perm.deleteSet p S).toList x).map (fun y => edgeToStrict (es y.1))
      = ((p.toList x.1).map es).filterMap EdgeSign.toStrict := by
  rw [List.filterMap_map, Function.comp_def, filterMap_toStrict_eq_filter_map]
  have hLHS : ((Equiv.Perm.deleteSet p S).toList x).map (fun y => edgeToStrict (es y.1))
      = (((Equiv.Perm.deleteSet p S).toList x).map Subtype.val).map (fun d => edgeToStrict (es d)) := by
    rw [List.map_map]; rfl
  rw [hLHS, deleteSet_toList_map_val p S x hL hL'pos]
  congr 1
  apply List.filter_congr
  intro d hd
  have hsc : p.SameCycle x.1 d := (Equiv.Perm.mem_toList_iff.mp hd).1
  simp only [decide_eq_decide]
  rw [ne_eq, ← hSorbit d hsc]

open ProofsInTheBook.Ch13FlipTransport in
/-- **Orbit-local degenerate case.**  Same as
`Ch13FlipTransport.cyclicFlipCount_filterMap_eq_zero_of_empty` but with orbit-local `hSorbit`. -/
theorem cyclicFlipCount_filterMap_eq_zero_of_empty_orbit (p : Equiv.Perm D) (es : D → EdgeSign)
    (S : Finset D) (x : {d : D // d ∉ S})
    (hSorbit : ∀ c, p.SameCycle x.1 c → (c ∈ S ↔ es c = EdgeSign.zero))
    (hempty : (Equiv.Perm.deleteSet p S).toList x = []) :
    cyclicFlipCount (((p.toList x.1).map es).filterMap EdgeSign.toStrict) = 0 := by
  apply cyclicFlipCount_eq_zero_of_length_le_one
  rw [List.filterMap_map, Function.comp_def, filterMap_toStrict_eq_filter_map, List.length_map]
  have hxfix : (Equiv.Perm.deleteSet p S) x = x := by
    have hnotsupp : x ∉ (Equiv.Perm.deleteSet p S).support := Equiv.Perm.toList_eq_nil_iff.mp hempty
    exact Equiv.Perm.notMem_support.mp hnotsupp
  have hall : ∀ y ∈ (p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero)), y = x.1 := by
    intro y hy
    rw [List.mem_filter, decide_eq_true_iff] at hy
    obtain ⟨hymem, hynz⟩ := hy
    have hscy : p.SameCycle x.1 y := (Equiv.Perm.mem_toList_iff.mp hymem).1
    have hyS : y ∉ S := by rw [hSorbit y hscy]; exact hynz
    have hsc' : (Equiv.Perm.deleteSet p S).SameCycle x ⟨y, hyS⟩ :=
      (Equiv.Perm.sameCycle_deleteSet_iff p S x ⟨y, hyS⟩).2 hscy
    obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := Equiv.Perm.deleteSet p S) hsc'
    have hxx : ((Equiv.Perm.deleteSet p S) ^ k) x = x :=
      Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hxfix k
    have hyx : (⟨y, hyS⟩ : {d : D // d ∉ S}) = x := by rw [← hk, hxx]
    exact congrArg Subtype.val hyx
  have hnodup : ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero))).Nodup :=
    (Equiv.Perm.nodup_toList p x.1).filter _
  by_contra hlen
  push Not at hlen
  obtain ⟨a, b, hab, ha, hb⟩ :
      ∃ a b, a ≠ b ∧ a < ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero))).length
        ∧ b < ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero))).length :=
    ⟨0, 1, by omega, by omega, by omega⟩
  rw [List.nodup_iff_injective_getElem] at hnodup
  apply hab
  have he : ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero)))[a]
      = ((p.toList x.1).filter (fun d => decide (es d ≠ EdgeSign.zero)))[b] := by
    rw [hall _ (List.getElem_mem ha), hall _ (List.getElem_mem hb)]
  have hfin : (⟨a, ha⟩ : Fin _) = ⟨b, hb⟩ := hnodup he
  exact Fin.mk.injEq .. ▸ hfin

open ProofsInTheBook.Ch13FlipTransport in
/-- **Orbit-local cyclic flip-count transport.**  For an orbit-local zero set, the cyclic flip
count of the kept (`deleteSet`) orbit strict signs equals the zero-skipped count of the full
`p`-orbit. -/
theorem cyclicFlipCount_transport_orbit (p : Equiv.Perm D) (es : D → EdgeSign) (S : Finset D)
    (x : {d : D // d ∉ S})
    (hSorbit : ∀ c, p.SameCycle x.1 c → (c ∈ S ↔ es c = EdgeSign.zero)) :
    cyclicFlipCount (((Equiv.Perm.deleteSet p S).toList x).map (fun y => edgeToStrict (es y.1)))
      = cyclicFlipCount (((p.toList x.1).map es).filterMap EdgeSign.toStrict) := by
  by_cases hL'pos : 0 < ((Equiv.Perm.deleteSet p S).toList x).length
  · have hL : 0 < (p.toList x.1).length := by
      by_contra h
      push Not at h
      have hxfix : p x.1 = x.1 := by
        have hns : x.1 ∉ p.support :=
          Equiv.Perm.toList_eq_nil_iff.mp (List.length_eq_zero_iff.mp (by omega))
        exact Equiv.Perm.notMem_support.mp hns
      have hdfix : (Equiv.Perm.deleteSet p S) x = x := by
        apply Subtype.ext
        rw [Equiv.Perm.deleteSet_apply_coe]
        exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hxfix _
      have hns2 : x ∉ (Equiv.Perm.deleteSet p S).support := Equiv.Perm.notMem_support.mpr hdfix
      rw [← Equiv.Perm.toList_eq_nil_iff] at hns2
      rw [hns2] at hL'pos; simp at hL'pos
    rw [kept_strict_list_eq_orbit p es S x hSorbit hL hL'pos]
  · push Not at hL'pos
    have hempty : (Equiv.Perm.deleteSet p S).toList x = [] := List.length_eq_zero_iff.mp (by omega)
    rw [hempty, List.map_nil, cyclicFlipCount,
      cyclicFlipCount_filterMap_eq_zero_of_empty_orbit p es S x hSorbit hempty]

/-! ## Part 5: the active-component deletion bundle

For the seed `d₀` (active), `compDel M es d₀` is `α`-closed (`hsub`/`hclosed`), its kept darts are
exactly the active component of `d₀` (each nonzero-signed: `hKeptNonzero`), and the orbit-local
transport applies at every kept dart.  These feed the modular assembly. -/

variable (M : CombMap D) (es : D → EdgeSign)

/-- `compDel` is `α`-closed (the `hsub` input) when `es` is edge-invariant: a dart and its edge
partner are reachable together (both active, or both inactive hence both deleted). -/
theorem compDel_hsub (hes : ∀ d, es (M.α d) = es d) {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero) :
    ∀ d, d ∈ compDel M es d₀ ↔ M.α d ∈ compDel M es d₀ := by
  intro d
  rw [mem_compDel, mem_compDel, not_iff_not]
  constructor
  · intro h
    have hda : es d ≠ EdgeSign.zero := reached_active M es hd₀ h
    have hαa : es (M.α d) ≠ EdgeSign.zero := by rw [hes d]; exact hda
    refine Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ ?_)
    exact ⟨Or.inr rfl, hda, hαa⟩
  · intro h
    have hαa : es (M.α d) ≠ EdgeSign.zero := reached_active M es hd₀ h
    have hda : es d ≠ EdgeSign.zero := by rw [← hes d]; exact hαa
    refine Relation.EqvGen.trans _ _ _ h (Relation.EqvGen.rel _ _ ?_)
    refine ⟨Or.inr ?_, hαa, hda⟩
    rw [M.alpha_alpha]

/-- `compDel` is `α`-closed (`hclosed` input). -/
theorem compDel_hclosed (hes : ∀ d, es (M.α d) = es d) {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero) :
    ∀ d, d ∈ compDel M es d₀ → M.α d ∈ compDel M es d₀ :=
  fun d hd => (compDel_hsub M es hes hd₀ d).1 hd

/-- Kept darts of `compDel` are active (`hKeptNonzero`). -/
theorem compDel_hKeptNonzero {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero) :
    ∀ d, d ∉ compDel M es d₀ → es d ≠ EdgeSign.zero :=
  fun d hd => reached_active M es hd₀ (reached_of_notMem_compDel M es d₀ d hd)

/-- The orbit-local zero characterization holds on the `M.σ`-orbit of any kept dart:
a σ-neighbour `c` is deleted iff `es c = 0` (active σ-neighbours of a kept dart are in the same
active component, hence kept). -/
theorem compDel_orbit_zero {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero)
    (x : {d : D // d ∉ compDel M es d₀}) :
    ∀ c, M.σ.SameCycle x.1 c → (c ∈ compDel M es d₀ ↔ es c = EdgeSign.zero) := by
  intro c hsc
  rw [mem_compDel]
  constructor
  · -- c deleted ⟹ es c = 0: if es c ≠ 0, c is reached via a vertex-step from kept x
    intro hcdel
    by_contra hcnz
    apply hcdel
    have hxnz : es x.1 ≠ EdgeSign.zero := compDel_hKeptNonzero M es hd₀ x.1 x.2
    have hxr : Relation.EqvGen (activeStep M es) d₀ x.1 :=
      reached_of_notMem_compDel M es d₀ x.1 x.2
    refine Relation.EqvGen.trans _ _ _ hxr (Relation.EqvGen.rel _ _ ?_)
    exact ⟨Or.inl hsc, hxnz, hcnz⟩
  · -- es c = 0 ⟹ c deleted: an inactive dart is never reached
    intro hcz hcr
    exact (reached_active M es hd₀ hcr) hcz

/-- **Orbit-local flip transport for `compDel`.**  The kept submap's `vertexFlip` at a kept dart's
vertex equals the book's skip-zeros count, even though `compDel` deletes darts of other
components. -/
theorem flip_transport_compDel (hes : ∀ d, es (M.α d) = es d) {d₀ : D}
    (hd₀ : es d₀ ≠ EdgeSign.zero)
    (d : {d : D // d ∉ compDel M es d₀}) :
    vertexFlip (keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀))
        (keptSign M es (compDel M es d₀))
        (Quotient.mk (cycleSetoid (keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀)).σ) d)
      = vertexFlipCountSkipZeros M es d.1 := by
  rw [← ProofsInTheBook.Ch13MarkedReduction.vertexFlipCountSkipZeros_strict_eq_vertexFlip
        (keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀)) (keptSign M es (compDel M es d₀)) d]
  rw [vertexFlipCountSkipZeros, vertexSignList, cyclicFlipCountSkipZeros,
      vertexFlipCountSkipZeros, vertexSignList, cyclicFlipCountSkipZeros]
  have hLHSlist :
      (((keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀)).σ.toList d).map
            (fun y => strictToEdge (keptSign M es (compDel M es d₀) y))).filterMap
          EdgeSign.toStrict
      = ((Equiv.Perm.deleteSet M.σ (compDel M es d₀)).toList d).map (fun y => edgeToStrict (es y.1)) := by
    rw [keptMap_sigma]
    rw [show (fun y : {d : D // d ∉ compDel M es d₀} =>
            strictToEdge (keptSign M es (compDel M es d₀) y))
          = strictToEdge ∘ (keptSign M es (compDel M es d₀)) from rfl, ← List.map_map,
        ProofsInTheBook.Ch13MarkedReduction.filterMap_toStrict_map_strictToEdge]
    rfl
  rw [hLHSlist]
  exact cyclicFlipCount_transport_orbit M.σ es (compDel M es d₀) d
    (compDel_orbit_zero M es hd₀ d)

/-! ## Part 6: connectivity of the active component (`hconn`)

The kept map over `compDel M es d₀` is exactly `d₀`'s active component, hence connected.  Every
kept dart is `ReflTransGen activeStep`-reached from `d₀` (the relation is symmetric, so `EqvGen`
collapses to `ReflTransGen`).  Each `activeStep` between reachable darts lifts to a kept dart-step
(`keptStepRel = (keptMap).dartStep`), so the kept walks assemble. -/

/-- Membership-free reachability is symmetric, so `EqvGen activeStep` is `ReflTransGen activeStep`. -/
theorem reflTransGen_activeStep_of_eqvGen {d₀ z : D}
    (h : Relation.EqvGen (activeStep M es) d₀ z) :
    Relation.ReflTransGen (activeStep M es) d₀ z :=
  (eqvGen_iff_reflTransGen (fun _ _ => activeStep_symm M es) d₀ z).1 h

/-- **Every kept dart reaches `d₀` by a kept walk.**  `ReflTransGen activeStep d₀ z` with `z` kept
gives `ReflTransGen keptStepRel ⟨d₀⟩ ⟨z⟩`; intermediates are reachable from `d₀`, hence kept. -/
theorem keptReflTrans_of_reflTransGen_activeStep (hes : ∀ d, es (M.α d) = es d)
    {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero)
    {z : D} (h : Relation.ReflTransGen (activeStep M es) d₀ z) (hz : z ∉ compDel M es d₀) :
    Relation.ReflTransGen
        (ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀)
          (compDel_hsub M es hes hd₀))
        ⟨d₀, by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)⟩ ⟨z, hz⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hb hbc ih =>
      -- `b` reachable from `d₀` (the prefix), so `b ∉ compDel`
      have hbeqv : Relation.EqvGen (activeStep M es) d₀ b :=
        (eqvGen_iff_reflTransGen (fun _ _ => activeStep_symm M es) d₀ b).2 hb
      have hbkept : b ∉ compDel M es d₀ := by rw [mem_compDel]; exact not_not.2 hbeqv
      -- assemble the kept dart-step `⟨b⟩ → ⟨c⟩`
      have hstep : ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀)
          (compDel_hsub M es hes hd₀) ⟨b, hbkept⟩ ⟨c, hz⟩ := by
        obtain ⟨hstepbc, _, _⟩ := hbc
        rcases hstepbc with hσ | hα
        · exact Or.inl ((Equiv.Perm.sameCycle_deleteSet_iff M.σ (compDel M es d₀)
            ⟨b, hbkept⟩ ⟨c, hz⟩).2 hσ)
        · refine Or.inr (Subtype.ext ?_)
          show (c : D) = M.α b
          exact hα
      exact Relation.ReflTransGen.tail (ih hbkept) hstep

/-- **The active component is connected.**  Every pair of kept darts is connected by a kept walk:
route each through the seed `d₀` via `keptReflTrans_of_reflTransGen_activeStep`. -/
theorem compDel_keptMap_connected (hes : ∀ d, es (M.α d) = es d)
    {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero) :
    (keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀)).Connected := by
  intro a b
  -- the kept dart-step of `keptMap` is `keptStepRel` (definitional)
  show Relation.ReflTransGen
      (ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀) (compDel_hsub M es hes hd₀)) a b
  have hd₀kept : d₀ ∉ compDel M es d₀ := by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)
  -- `a` and `b` both reach `d₀`
  have ha : Relation.ReflTransGen (activeStep M es) d₀ a.1 :=
    reflTransGen_activeStep_of_eqvGen M es (reached_of_notMem_compDel M es d₀ a.1 a.2)
  have hb : Relation.ReflTransGen (activeStep M es) d₀ b.1 :=
    reflTransGen_activeStep_of_eqvGen M es (reached_of_notMem_compDel M es d₀ b.1 b.2)
  have hksymm : ∀ u v, ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀)
      (compDel_hsub M es hes hd₀) u v → ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀)
      (compDel_hsub M es hes hd₀) v u :=
    fun u v h => dartStepRel_symm
      (ProofsInTheBook.SubmapPlanar.keptAlpha_invol M (compDel M es d₀)
        (compDel_hsub M es hes hd₀)) h
  -- a → ⟨d₀⟩ (reverse of ⟨d₀⟩ → a) then ⟨d₀⟩ → b
  have hda : Relation.ReflTransGen
      (ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀) (compDel_hsub M es hes hd₀))
      ⟨d₀, hd₀kept⟩ a :=
    keptReflTrans_of_reflTransGen_activeStep M es hes hd₀ ha a.2
  have hdb : Relation.ReflTransGen
      (ProofsInTheBook.SubmapPlanar.keptStepRel M (compDel M es d₀) (compDel_hsub M es hes hd₀))
      ⟨d₀, hd₀kept⟩ b :=
    keptReflTrans_of_reflTransGen_activeStep M es hes hd₀ hb b.2
  exact (reflTransGen_symm hksymm hda).trans hdb

/-! ## Part 7: the no-digon property of a connected simple map with `≥ 2` edges (`hFaceDeg`)

A digon face (`faceLen = 2`) of a simple map forces its representative dart `d` to satisfy
`A.σ d = d` and `A.σ (A.α d) = A.α d`: both `d` and `A.α d` are `σ`-fixed (degree-1 leaves), so the
edge `{d, A.α d}` is an isolated component.  In a **connected** map every dart then lies in
`{d, A.α d}`, giving `Fintype.card = 2`, i.e. `A.E = 1`.  Hence a connected simple map with
`2 ≤ A.E` has all faces of degree `≥ 3`. -/

/-- A digon (`faceLen = 2`) representative `d` of a simple map has both `A.σ d = d` and
`A.σ (A.α d) = A.α d` (both darts of its single edge are `σ`-fixed leaves). -/
theorem digon_sigma_fixed {A : CombMap D} (hA : A.IsSimpleGraph) {d : D}
    (hφ : A.φ d ≠ d) (hcard2 : (A.φ.cycleOf d).support.card = 2) :
    A.σ d = d ∧ A.σ (A.α d) = A.α d := by
  -- φ² d = d (digon)
  have hpow := Equiv.Perm.pow_mod_card_support_cycleOf_self_apply A.φ 2 d
  rw [hcard2] at hpow
  have hsq : A.φ (A.φ d) = d := by
    have h2 : (A.φ ^ 2) d = d := by simpa using hpow.symm
    simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using h2
  -- the two boundary darts share an edge ⟹ φ d = α d
  have he1 : A.dartEdge d = s(A.tail d, A.tail (A.φ d)) := A.dartEdge_eq_mk_tail_tail_phi d
  have he2 : A.dartEdge (A.φ d) = s(A.tail (A.φ d), A.tail d) := by
    rw [A.dartEdge_eq_mk_tail_tail_phi (A.φ d), hsq]
  have hedge : A.dartEdge d = A.dartEdge (A.φ d) := by rw [he1, he2, Sym2.eq_swap]
  have hsc : A.α.SameCycle d (A.φ d) := hA.no_parallel hedge
  have hφα : A.φ d = A.α d := by
    rcases (A.alpha_sameCycle_iff d (A.φ d)).mp hsc with hcase | hcase
    · exact absurd hcase hφ
    · exact hcase
  -- φ = σ * α: φ d = σ (α d) = α d ⟹ σ fixes α d
  have hσαd : A.σ (A.α d) = A.α d := by
    have : A.σ (A.α d) = A.φ d := rfl
    rw [this, hφα]
  -- φ (φ d) = d with φ d = α d: φ (α d) = σ (α (α d)) = σ d = d ⟹ σ fixes d
  have hσd : A.σ d = d := by
    have hφαd : A.φ (A.α d) = d := by rw [← hφα]; exact hsq
    have hcalc : A.σ d = A.φ (A.α d) := by
      show A.σ d = A.σ (A.α (A.α d))
      rw [A.alpha_alpha]
    rw [hcalc, hφαd]
  exact ⟨hσd, hσαd⟩

/-- **A connected simple map with `≥ 2` edges has all faces of degree `≥ 3`** (no digon). -/
theorem three_le_faceDeg_of_connected_simple_twoEdge {A : CombMap D} (hA : A.IsSimpleGraph)
    (hconn : A.Connected) (hE : 2 ≤ A.E) (R : Quotient (cycleSetoid A.φ)) :
    3 ≤ faceDeg A R := by
  obtain ⟨d, rfl⟩ := R.exists_rep
  have hφ : A.φ d ≠ d := phi_ne_self_of_isSimpleGraph A hA d
  rw [faceDeg_eq_faceLen]
  show 3 ≤ A.faceLen (A.dartFace d)
  rw [faceLen_dartFace_eq_card_support_cycleOf A hφ]
  by_contra hlt
  push Not at hlt
  have h2 : 2 ≤ (A.φ.cycleOf d).support.card :=
    (Equiv.Perm.isCycle_cycleOf A.φ hφ).two_le_card_support
  have hcard2 : (A.φ.cycleOf d).support.card = 2 := by omega
  obtain ⟨hσd, hσαd⟩ := digon_sigma_fixed hA hφ hcard2
  -- the edge {d, α d} is the entire (connected) map: every dart is d or α d
  have hαd_ne : A.α d ≠ d := A.α_no_fixed d
  -- dartStep from d stays in {d, α d}
  have hstep_d : ∀ y, A.dartStep d y → y = d ∨ y = A.α d := by
    intro y hy
    rcases hy with hσ | hαe
    · -- same σ-cycle as d; σ fixes d ⟹ y = d
      left
      obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := A.σ) hσ
      have : (A.σ ^ k) d = d := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hσd k
      rw [← hk, this]
    · exact Or.inr hαe
  have hstep_αd : ∀ y, A.dartStep (A.α d) y → y = d ∨ y = A.α d := by
    intro y hy
    rcases hy with hσ | hαe
    · right
      obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := A.σ) hσ
      have : (A.σ ^ k) (A.α d) = A.α d := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hσαd k
      rw [← hk, this]
    · left; rw [hαe, A.alpha_alpha]
  -- every dart reachable from d lies in {d, α d}
  have hall : ∀ y, Relation.ReflTransGen A.dartStep d y → y = d ∨ y = A.α d := by
    intro y h
    induction h with
    | refl => exact Or.inl rfl
    | @tail b c _ hbc ih =>
        rcases ih with rfl | rfl
        · exact hstep_d c hbc
        · exact hstep_αd c hbc
  have hsub : ∀ y : D, y ∈ ({d, A.α d} : Finset D) := by
    intro y
    have := hall y (hconn d y)
    rcases this with rfl | rfl <;> simp
  -- so |D| ≤ 2, hence 2*E = |D| ≤ 2, E ≤ 1, contradicting hE
  have hcardD : Fintype.card D ≤ 2 := by
    have hle : Fintype.card D ≤ ({d, A.α d} : Finset D).card := by
      rw [← Finset.card_univ]
      apply Finset.card_le_card
      intro y _; exact hsub y
    calc Fintype.card D ≤ ({d, A.α d} : Finset D).card := hle
      _ ≤ 2 := by
          calc ({d, A.α d} : Finset D).card ≤ ({A.α d} : Finset D).card + 1 :=
                Finset.card_insert_le _ _
            _ ≤ 2 := by simp
  have h2E : 2 * A.E = Fintype.card D := A.two_mul_E_eq_card
  omega

/-! ## Part 8: the headline assembly

Choose `Del := compDel M es d₀` for an active seed `d₀`.  Connectivity (`hconn`) is
`compDel_keptMap_connected`; the kept map is simple (`keptMap_isSimpleGraph`).  Branch on the kept
edge count:

* `2 ≤ E(keptMap)` — `hFaceDeg` from `three_le_faceDeg_of_connected_simple_twoEdge`, then
  `marked_sphere_low_active_vertex_modular` (with the orbit-local transport `flip_transport_compDel`).
* `E(keptMap) = 1` (single active edge) — `d₀`'s kept vertex is a fixed point of
  `deleteSet M.σ Del` (its α-partner is at a different vertex, `no_loop`), so the skip-zeros count
  at `d₀` is `0 ≤ 2` directly. -/

/-- The modular assembly specialized to `compDel`, transport discharged by `flip_transport_compDel`.
Requires only the two topological residuals on the active component. -/
theorem compDel_low_active_vertex (hsphere : M.IsSphereMap) (hes : ∀ d, es (M.α d) = es d)
    {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero)
    (hFaceDeg : ∀ R, 3 ≤ faceDeg (keptMap M (compDel M es d₀) (compDel_hsub M es hes hd₀)) R) :
    ∃ d : D, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2 := by
  refine marked_sphere_low_active_vertex_modular M es (compDel M es d₀)
    (compDel_hsub M es hes hd₀) (compDel_hclosed M es hes hd₀) hsphere hes
    ⟨d₀, by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)⟩
    (fun d => compDel_hKeptNonzero M es hd₀ d.1 d.2)
    (compDel_keptMap_connected M es hes hd₀) hFaceDeg
    (fun d => flip_transport_compDel M es hes hd₀ d)

/-- **Single-edge component branch.**  When the active component has exactly one edge, `d₀`'s kept
vertex is a singleton (`deleteSet M.σ Del` fixes `d₀`), so its skip-zeros flip count is `0`. -/
theorem single_edge_low_active_vertex {d₀ : D} (hd₀ : es d₀ ≠ EdgeSign.zero)
    (hfix : (Equiv.Perm.deleteSet M.σ (compDel M es d₀))
      ⟨d₀, by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)⟩
        = ⟨d₀, by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)⟩) :
    ∃ d : D, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2 := by
  set d₀' : {d : D // d ∉ compDel M es d₀} :=
    ⟨d₀, by rw [mem_compDel]; exact not_not.2 (reached_refl M es d₀)⟩ with hd₀'def
  refine ⟨d₀, ⟨d₀, Equiv.Perm.SameCycle.refl _ _, hd₀⟩, ?_⟩
  -- the deleteSet orbit of d₀ is empty (fixed point), so the skip-zeros count is 0
  have hempty : (Equiv.Perm.deleteSet M.σ (compDel M es d₀)).toList d₀' = [] := by
    rw [Equiv.Perm.toList_eq_nil_iff]
    exact Equiv.Perm.notMem_support.mpr hfix
  have hzero : vertexFlipCountSkipZeros M es d₀ = 0 := by
    rw [vertexFlipCountSkipZeros, vertexSignList, cyclicFlipCountSkipZeros]
    show cyclicFlipCount (((M.σ.toList d₀).map es).filterMap EdgeSign.toStrict) = 0
    have hval : (d₀ : D) = (d₀' : D) := rfl
    rw [hval]
    exact cyclicFlipCount_filterMap_eq_zero_of_empty_orbit M.σ es (compDel M es d₀) d₀'
      (compDel_orbit_zero M es hd₀ d₀') hempty
  rw [hzero]; omega

/-- **Sole-survivor fixed point.**  If `x` is the only kept dart in its `p`-cycle, `deleteSet p S`
fixes `x`. -/
theorem deleteSet_fix_of_sole_survivor (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S})
    (hsole : ∀ y : {d : D // d ∉ S}, p.SameCycle x.1 y.1 → y = x) :
    Equiv.Perm.deleteSet p S x = x := by
  apply Subtype.ext
  rw [Equiv.Perm.deleteSet_apply_coe]
  set n := Equiv.Perm.DeleteSet.firstOutside p S x with hn
  have hnotmem : (p ^ n) x.1 ∉ S := Equiv.Perm.DeleteSet.firstOutside_notMem p S x
  have hsc : p.SameCycle x.1 ((p ^ n) x.1) := ⟨n, rfl⟩
  have := hsole ⟨(p ^ n) x.1, hnotmem⟩ hsc
  exact congrArg Subtype.val this

/-! ## The headline theorem -/

/-- **Cauchy marked-sphere low active vertex, simple form.**  For a simple triangulated sphere
carrying an edge-invariant `±/0` signing with some nonzero edge, some active vertex has skip-zero
flip count `≤ 2`.  `Del := compDel M es d₀` extracts the seed's active component (connected,
`hconn`); branch on its edge count for `hFaceDeg` (no-digon, ≥2 edges) vs the single-edge
endpoint. -/
theorem cauchy_marked_sphere_low_active_vertex_simple
    (M : CombMap D) (hsphere : M.IsSphereMap) (hTri : M.FaceRegular 3) (hsimple : M.IsSimpleGraph)
    (es : D → EdgeSign) (hes : ∀ d, es (M.α d) = es d) (hnz : ∃ d, es d ≠ EdgeSign.zero) :
    ∃ d, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2 := by
  obtain ⟨d₀, hd₀⟩ := hnz
  set Del := compDel M es d₀ with hDeldef
  set hsub := compDel_hsub M es hes hd₀ with hsubdef
  set A := keptMap M Del hsub with hAdef
  have hd₀kept : d₀ ∉ Del := by rw [hDeldef, mem_compDel]; exact not_not.2 (reached_refl M es d₀)
  set d₀' : {d : D // d ∉ Del} := ⟨d₀, hd₀kept⟩ with hd₀'def
  have hAsimple : A.IsSimpleGraph := keptMap_isSimpleGraph M hsimple Del hsub
  have hAconn : A.Connected := compDel_keptMap_connected M es hes hd₀
  -- branch on the kept edge count
  rcases Nat.lt_or_ge A.E 2 with hE | hE
  · -- E ≤ 1.  E ≥ 1 (the seed edge {d₀, α d₀} survives), so E = 1: single active edge
    have hElt2 : A.E < 2 := hE
    -- exactly 2 kept darts (card = 2 E < 4, and ≥ 2 since d₀', keptAlpha d₀' distinct)
    have h2E : 2 * A.E = Fintype.card {d : D // d ∉ Del} := A.two_mul_E_eq_card
    have hcardlt : Fintype.card {d : D // d ∉ Del} < 4 := by omega
    -- the two distinct kept darts d₀', keptAlpha d₀'
    have hαne : (keptAlpha M Del hsub) d₀' ≠ d₀' := by
      intro h
      apply M.α_no_fixed d₀
      have := congrArg Subtype.val h
      rwa [keptAlpha_apply_coe] at this
    have hcardge2 : 2 ≤ Fintype.card {d : D // d ∉ Del} := by
      have : ({d₀', (keptAlpha M Del hsub) d₀'} : Finset {d : D // d ∉ Del}).card ≤
          Fintype.card {d : D // d ∉ Del} := Finset.card_le_univ _
      rw [Finset.card_insert_of_notMem (by simp [hαne.symm]), Finset.card_singleton] at this
      omega
    -- so card = 2 (E = 1): the only kept darts are d₀' and keptAlpha d₀'
    have hcard2 : Fintype.card {d : D // d ∉ Del} = 2 := by omega
    -- d₀' is the sole kept dart in its M.σ-cycle (its α-partner is at a different vertex: no loop)
    have hsole : ∀ y : {d : D // d ∉ Del}, M.σ.SameCycle d₀'.1 y.1 → y = d₀' := by
      intro y hy
      -- y is one of the two kept darts
      have hmem : y ∈ ({d₀', (keptAlpha M Del hsub) d₀'} : Finset {d : D // d ∉ Del}) := by
        by_contra hnotmem
        have : 3 ≤ Fintype.card {d : D // d ∉ Del} := by
          have hsubset : ({d₀', (keptAlpha M Del hsub) d₀', y} :
              Finset {d : D // d ∉ Del}).card ≤ Fintype.card {d : D // d ∉ Del} :=
            Finset.card_le_univ _
          rw [show ({d₀', (keptAlpha M Del hsub) d₀', y} : Finset {d : D // d ∉ Del}).card = 3 from by
            rw [Finset.card_insert_of_notMem (by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                refine ⟨hαne.symm, ?_⟩
                intro h; exact hnotmem (by rw [← h]; simp)),
              Finset.card_insert_of_notMem (by
                simp only [Finset.mem_singleton]
                intro h; exact hnotmem (by rw [h]; simp)),
              Finset.card_singleton]] at hsubset
          exact hsubset
        omega
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with rfl | rfl
      · rfl
      · -- y = keptAlpha d₀' = α d₀; σ-same-cycle d₀ would be a loop
        exfalso
        have hsc : M.σ.SameCycle d₀ (M.α d₀) := by
          have hval : ((keptAlpha M Del hsub) d₀' : D) = M.α d₀ := keptAlpha_apply_coe M Del hsub d₀'
          rw [hval] at hy; exact hy
        have htail : M.tail d₀ = M.tail (M.α d₀) := Quotient.sound hsc
        rw [M.tail_alpha] at htail
        exact hsimple.no_loop d₀ htail
    -- deleteSet fixes d₀' ⟹ single-edge branch
    have hfix : (Equiv.Perm.deleteSet M.σ Del) d₀' = d₀' :=
      deleteSet_fix_of_sole_survivor M.σ Del d₀' hsole
    exact single_edge_low_active_vertex M es hd₀ hfix
  · -- ≥ 2 edges: no-digon hFaceDeg, then the modular assembly
    have hFaceDeg : ∀ R, 3 ≤ faceDeg A R :=
      three_le_faceDeg_of_connected_simple_twoEdge hAsimple hAconn hE
    exact compDel_low_active_vertex M es hsphere hes hd₀ hFaceDeg

/-! ## Non-vacuity

The tetrahedron `tetraMap` is a genuine simple triangulated sphere (`IsSphereMap`,
`FaceRegular 3`, `IsSimpleGraph`); the all-`plus` signing is edge-invariant and has a nonzero edge.
So `cauchy_marked_sphere_low_active_vertex_simple` is instantiated non-vacuously. -/

/-- `tetraMap` is a simple graph. -/
theorem tetraMap_isSimpleGraph : ProofsInTheBook.Ch13MarkedSphere.tetraMap.IsSimpleGraph := by
  constructor
  · decide
  · intro d e; revert d e; decide

/-- **Non-vacuity witness.**  The headline theorem applies to the tetrahedron with the all-`plus`
edge-invariant signing (which has a nonzero edge), yielding an active vertex with skip-zero flip
count `≤ 2`. -/
theorem cauchy_marked_sphere_low_active_vertex_simple_tetra :
    ∃ d, ActiveVertex ProofsInTheBook.Ch13MarkedSphere.tetraMap (fun _ => EdgeSign.plus) d ∧
      vertexFlipCountSkipZeros ProofsInTheBook.Ch13MarkedSphere.tetraMap
        (fun _ => EdgeSign.plus) d ≤ 2 :=
  cauchy_marked_sphere_low_active_vertex_simple ProofsInTheBook.Ch13MarkedSphere.tetraMap
    ProofsInTheBook.Ch13MarkedSphere.tetraMap_isSphereMap
    ProofsInTheBook.Ch13MarkedSphere.tetraMap_faceRegular_three
    tetraMap_isSimpleGraph (fun _ => EdgeSign.plus) (fun _ => rfl) ⟨0, by decide⟩

end ProofsInTheBook.Ch13ComponentClose
