import Mathlib
import ProofsInTheBook.PlanarMap
import ProofsInTheBook.PlanarMapSimple
import ProofsInTheBook.PlanarMapDelete
import ProofsInTheBook.SubmapPlanar
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Ch13MarkedReduction

/-!
# Ch13 active-component extraction: the with-zeros marked-sphere low active vertex

This file builds the **active subgraph** of a simple triangulated sphere carrying a `±/0`
edge-invariant signing and feeds it to the proven non-triangular core
`Ch13MarkedReduction.active_component_low_vertex` to obtain the with-zeros Cauchy
low-active-vertex conclusion.

The free, clean layers are proved unconditionally here (clean-3); the three genuinely
topological/combinatorial residuals enter `marked_sphere_low_active_vertex_modular` as named
hypotheses:

* `hconn` — the active component (kept map) is connected (so its Euler characteristic is `2`);
* `hFaceDeg` — every face of the active component has degree `≥ 3` (the no-digon property forced by
  simplicity of `M`, valid once the component has `≥ 2` edges; a single active edge is a degenerate
  digon handled separately);
* `htrans` — the flip-count transport: each kept vertex's `vertexFlip` equals the book's skip-zero
  count at the corresponding `M`-vertex (the `deleteSet`-orbit `toList` is the kept sublist of the
  `M.σ`-orbit `toList`, so the skipped darts are exactly the dropped zeros).

`marked_sphere_low_active_vertex_modular` discharges everything else and yields the with-zeros
conclusion `∃ d, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2`.
-/

namespace ProofsInTheBook.Ch13ActiveComponent

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Ch13MarkedReduction
open EdgeSign

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Free layer A: `∑ faceDeg = 2E` is automatic for any combinatorial map

The face-degree-sum hypothesis of `active_component_low_vertex` is not topological content: it is
the orbit-partition identity `∑_faces (size of φ-orbit) = |darts| = 2E`. -/

/-- For any combinatorial map, the sum of face degrees is `2E` (orbit partition). -/
theorem sum_faceDeg_eq_two_mul_E (A : CombMap D) :
    (∑ R : Quotient (cycleSetoid A.φ), faceDeg A R) = 2 * A.E := by
  have h := CombMap.sum_class_card A.φ
  rw [CombMap.two_mul_E_eq_card]
  simpa [faceDeg] using h

/-! ## Free layer B: the inactive dart set is `α`-closed

A signing `es : D → EdgeSign` is **edge-invariant** when `es (α d) = es d`.  The *inactive* darts
(`es d = zero`) then form an `α`-closed set, the input to the `SubmapPlanar` edge-deletion
machinery. -/

/-- The inactive (zero-sign) dart set. -/
noncomputable def inactiveSet (M : CombMap D) (es : D → EdgeSign) : Finset D :=
  Finset.univ.filter (fun d => es d = EdgeSign.zero)

@[simp] theorem mem_inactiveSet (M : CombMap D) (es : D → EdgeSign) (d : D) :
    d ∈ inactiveSet M es ↔ es d = EdgeSign.zero := by
  simp [inactiveSet]

/-- Edge-invariance makes inactivity an `α`-invariant predicate. -/
theorem inactiveSet_sub (M : CombMap D) (es : D → EdgeSign)
    (hes : ∀ d, es (M.α d) = es d) :
    ∀ d, d ∈ inactiveSet M es ↔ M.α d ∈ inactiveSet M es := by
  intro d
  simp only [mem_inactiveSet, hes d]

/-- The inactive set is `α`-closed (the `hclosed` input). -/
theorem inactiveSet_closed (M : CombMap D) (es : D → EdgeSign)
    (hes : ∀ d, es (M.α d) = es d) :
    ∀ d, d ∈ inactiveSet M es → M.α d ∈ inactiveSet M es :=
  fun d hd => (inactiveSet_sub M es hes d).1 hd

/-! ## Layer C: the kept (active) combinatorial map

For any `α`-closed `Del`, the surviving darts `{d ∉ Del}` carry a combinatorial map whose rotation
is `deleteSet M.σ Del` (skip the deleted darts in each vertex cycle) and whose edge involution is
`keptAlpha` (`M.α` restricted).  This is the `CombMap` packaging of the `SubmapPlanar` data. -/

open ProofsInTheBook.SubmapPlanar

/-- The kept (active sub-)combinatorial map on the surviving darts `{d ∉ Del}`. -/
noncomputable def keptMap (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) : CombMap {d : D // d ∉ Del} where
  α := keptAlpha M Del hsub
  σ := Equiv.Perm.deleteSet M.σ Del
  α_invol := keptAlpha_invol M Del hsub
  α_no_fixed := by
    intro d hd
    apply M.α_no_fixed d.1
    have := congrArg Subtype.val hd
    rwa [keptAlpha_apply_coe] at this

@[simp] theorem keptMap_sigma (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    (keptMap M Del hsub).σ = Equiv.Perm.deleteSet M.σ Del := rfl

@[simp] theorem keptMap_alpha (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) :
    (keptMap M Del hsub).α = keptAlpha M Del hsub := rfl

/-- **Euler char of the kept map is `2` when it is connected** (genus-0 certificate from
`SubmapPlanar.keptMap_eulerChar_eq_two`): the active sub-map of a sphere has no handle. -/
theorem keptMap_eulerChar_eq_two_of_connected (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hclosed : ∀ d, d ∈ Del → M.α d ∈ Del) (hsphere : M.IsSphereMap)
    (d : {d : D // d ∉ Del}) (hconn : (keptMap M Del hsub).Connected) :
    (keptMap M Del hsub).eulerChar = 2 :=
  ProofsInTheBook.SubmapPlanar.keptMap_eulerChar_eq_two M Del hsub hclosed hsphere
    (keptMap M Del hsub) rfl rfl d hconn

/-- Euler identity form `(V:ℤ) - E + F = 2` for the connected kept map. -/
theorem keptMap_euler_VEF (M : CombMap D) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hclosed : ∀ d, d ∈ Del → M.α d ∈ Del) (hsphere : M.IsSphereMap)
    (d : {d : D // d ∉ Del}) (hconn : (keptMap M Del hsub).Connected) :
    ((keptMap M Del hsub).V : ℤ) - (keptMap M Del hsub).E + (keptMap M Del hsub).F = 2 := by
  have h := keptMap_eulerChar_eq_two_of_connected M Del hsub hclosed hsphere d hconn
  rwa [CombMap.eulerChar] at h

/-! ## Layer D: the strict signing on kept darts

On the kept (active) darts every dart has nonzero sign, so the `±/0` signing `es` restricts to a
genuine strict `±` signing, still edge-invariant. -/

/-- A nonzero edge sign as a strict sign. -/
def edgeToStrict : EdgeSign → StrictEdgeSign
  | EdgeSign.plus => StrictEdgeSign.plus
  | EdgeSign.minus => StrictEdgeSign.minus
  | EdgeSign.zero => StrictEdgeSign.plus  -- unreachable on active darts

@[simp] theorem strictToEdge_edgeToStrict_of_ne {a : EdgeSign} (h : a ≠ EdgeSign.zero) :
    strictToEdge (edgeToStrict a) = a := by
  cases a with
  | plus => rfl
  | minus => rfl
  | zero => exact absurd rfl h

/-- The strict signing on kept darts: `es` read as a `±`-sign (zeros, absent on active darts,
are sent to `plus` and never arise). -/
def keptSign (M : CombMap D) (es : D → EdgeSign) (Del : Finset D) :
    {d : D // d ∉ Del} → StrictEdgeSign :=
  fun d => edgeToStrict (es d.1)

/-- The kept strict signing is edge-invariant when `es` is. -/
theorem keptSign_edgeInvariant (M : CombMap D) (es : D → EdgeSign) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del) (hes : ∀ d, es (M.α d) = es d) :
    EdgeInvariant (keptMap M Del hsub) (keptSign M es Del) := by
  intro d
  simp only [keptSign, keptMap_alpha, keptAlpha_apply_coe, hes d.1]

/-! ## Layer E: the conditional assembly

Packaging the proven free layers with the proven non-triangular core
`active_component_low_vertex`.  The only inputs left open are the two genuinely topological facts
about the active component: that it is connected (so its Euler characteristic is `2`), and that all
its faces have degree `≥ 3` (the no-digon property forced by simplicity of `M`).  Both are taken as
explicit hypotheses here; they are discharged for the inactive-set component below / isolated as the
remaining construction. -/

/-- **Conditional active-component low vertex.**  For an `α`-closed deleted set `Del` such that the
kept (active) map is connected and has all faces of degree `≥ 3`, the kept strict signing has a kept
vertex with at most two corner changes.  (Free assembly of the proven core over the kept map.) -/
theorem keptMap_low_vertex
    (M : CombMap D) (es : D → EdgeSign) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hclosed : ∀ d, d ∈ Del → M.α d ∈ Del)
    (hsphere : M.IsSphereMap) (hes : ∀ d, es (M.α d) = es d)
    (d₀ : {d : D // d ∉ Del})
    (hconn : (keptMap M Del hsub).Connected)
    (hFaceDeg : ∀ R, 3 ≤ faceDeg (keptMap M Del hsub) R) :
    ∃ Q : Quotient (cycleSetoid (keptMap M Del hsub).σ),
      vertexFlip (keptMap M Del hsub) (keptSign M es Del) Q ≤ 2 := by
  set A := keptMap M Del hsub with hA
  refine active_component_low_vertex A ?_ ?_ hFaceDeg (keptSign M es Del)
    (keptSign_edgeInvariant M es Del hsub hes)
  · exact keptMap_euler_VEF M Del hsub hclosed hsphere d₀ hconn
  · exact sum_faceDeg_eq_two_mul_E A

/-! ## Layer F: the fully-assembled with-zeros theorem (modular form)

The top-level conclusion `∃ d, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2`, assembled
from the proven core via the kept active map.  Beyond the proven free layers it consumes exactly the
three topological residuals as named hypotheses:

* `hconn` — the active component (kept map) is connected;
* `hFaceDeg` — every face of the active component has degree `≥ 3` (no-digon, from `M` simple);
* `htrans` — the flip-count transport: each kept vertex's `vertexFlip` equals the book's skip-zero
  count at the corresponding `M`-vertex.

These are the precise statements isolated for the remaining construction; see the report. -/

/-- **Modular with-zeros marked-sphere low active vertex.**  Given the active component as a
connected, face-degree-`≥ 3` kept map together with the flip-count transport, the book's with-zeros
conclusion follows: some active `M`-vertex has skip-zero flip count `≤ 2`. -/
theorem marked_sphere_low_active_vertex_modular
    (M : CombMap D) (es : D → EdgeSign) (Del : Finset D)
    (hsub : ∀ d, d ∈ Del ↔ M.α d ∈ Del)
    (hclosed : ∀ d, d ∈ Del → M.α d ∈ Del)
    (hsphere : M.IsSphereMap) (hes : ∀ d, es (M.α d) = es d)
    (d₀ : {d : D // d ∉ Del})
    (hDel : ∀ d : {d : D // d ∉ Del}, es d.1 ≠ EdgeSign.zero)
    (hconn : (keptMap M Del hsub).Connected)
    (hFaceDeg : ∀ R, 3 ≤ faceDeg (keptMap M Del hsub) R)
    (htrans : ∀ d : {d : D // d ∉ Del},
      vertexFlip (keptMap M Del hsub) (keptSign M es Del)
        (Quotient.mk (cycleSetoid (keptMap M Del hsub).σ) d) = vertexFlipCountSkipZeros M es d.1) :
    ∃ d : D, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2 := by
  obtain ⟨Q, hQ⟩ := keptMap_low_vertex M es Del hsub hclosed hsphere hes d₀ hconn hFaceDeg
  obtain ⟨d, rfl⟩ := Q.exists_rep
  refine ⟨d.1, ?_, ?_⟩
  · -- the kept dart d.1 is active (nonzero sign) at its own vertex
    exact ⟨d.1, Equiv.Perm.SameCycle.refl _ _, hDel d⟩
  · rw [← htrans d]; exact hQ

/-- **With-zeros low active vertex over the canonical inactive-set deletion.**  Specializes
`marked_sphere_low_active_vertex_modular` to `Del := inactiveSet M es`, where `α`-closure
(`hsub`, `hclosed`) is automatic from edge-invariance.  The remaining inputs are exactly the three
topological residuals on the active map together with the activeness of the kept darts (automatic:
kept = not inactive = nonzero). -/
theorem marked_sphere_low_active_vertex_inactiveSet
    (M : CombMap D) (es : D → EdgeSign)
    (hsphere : M.IsSphereMap) (hes : ∀ d, es (M.α d) = es d)
    (d₀ : {d : D // d ∉ inactiveSet M es})
    (hconn : (keptMap M (inactiveSet M es) (inactiveSet_sub M es hes)).Connected)
    (hFaceDeg : ∀ R, 3 ≤ faceDeg (keptMap M (inactiveSet M es) (inactiveSet_sub M es hes)) R)
    (htrans : ∀ d : {d : D // d ∉ inactiveSet M es},
      vertexFlip (keptMap M (inactiveSet M es) (inactiveSet_sub M es hes))
          (keptSign M es (inactiveSet M es))
          (Quotient.mk (cycleSetoid (keptMap M (inactiveSet M es) (inactiveSet_sub M es hes)).σ) d)
        = vertexFlipCountSkipZeros M es d.1) :
    ∃ d : D, ActiveVertex M es d ∧ vertexFlipCountSkipZeros M es d ≤ 2 := by
  refine marked_sphere_low_active_vertex_modular M es (inactiveSet M es)
    (inactiveSet_sub M es hes) (inactiveSet_closed M es hes) hsphere hes d₀ ?_ hconn hFaceDeg htrans
  -- kept darts are active: not inactive ⇒ nonzero sign
  intro d
  have hd : d.1 ∉ inactiveSet M es := d.2
  rw [mem_inactiveSet] at hd
  exact hd

/-! ## Non-vacuity of the free layers

The free layers are genuinely instantiated on the tetrahedron (a real simple triangulated sphere):
the all-`plus` signing has empty inactive set, which is `α`-closed, and the face-degree sum identity
holds.  End-to-end non-vacuity of `marked_sphere_low_active_vertex_modular` coincides with
discharging the three isolated topological residuals (connectivity, `faceDeg ≥ 3`, transport). -/

/-- The face-degree sum identity is non-vacuously instantiated by the tetrahedron. -/
theorem sum_faceDeg_tetra :
    (∑ R : Quotient (cycleSetoid ProofsInTheBook.Ch13MarkedSphere.tetraMap.φ),
        faceDeg ProofsInTheBook.Ch13MarkedSphere.tetraMap R)
      = 2 * ProofsInTheBook.Ch13MarkedSphere.tetraMap.E :=
  sum_faceDeg_eq_two_mul_E _

/-- The inactive set of the all-`plus` signing on the tetrahedron is empty and `α`-closed. -/
theorem inactiveSet_tetra_closed :
    ∀ d, d ∈ inactiveSet ProofsInTheBook.Ch13MarkedSphere.tetraMap (fun _ => EdgeSign.plus) →
      ProofsInTheBook.Ch13MarkedSphere.tetraMap.α d
        ∈ inactiveSet ProofsInTheBook.Ch13MarkedSphere.tetraMap (fun _ => EdgeSign.plus) :=
  inactiveSet_closed _ _ (fun _ => rfl)

end ProofsInTheBook.Ch13ActiveComponent
