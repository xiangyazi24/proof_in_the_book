import ProofsInTheBook.ZinanCh35ChordlessFull
import ProofsInTheBook.PlanarMapFanConnectivity

/-!
# The σ-BACKWARD chordless fan (Chapter 35)

`ZinanCh35ChordlessFull.forward_fanTriangle_forces_degree_two` is a machine-checked
*obstruction*: the σ-**forward** consecutive pair `(head e, head (σ e))` of an inner
spoke `e` at `v0` admits a `FanTriangle hNT v0 (head e) (head (σ e))` only if
`σ² e = e` (degree ≤ 2).  The natural `φ`-triangle of an inner spoke `e` orients its
edge toward `head (σ⁻¹ e)` — the σ-**predecessor**, never the σ-successor.  Hence the
`IncidentNonOuterFacesExactly` certificate demanded by the existing (σ-forward)
`BoundaryVertexFan` interface cannot be filled for a nontrivial fan.

This file builds the σ-**backward** version, which *is* σ-derivable (no chirality
input), following the ChatGPT-Pro R9 blueprint
(`HANDOFF/ch35-chordless-sigma-backward-R9.md`):

* **§1 `fanTriangle_of_spoke_pred`** (R9 §4): for an inner spoke `e` at `v0`
  (`tail e = v0`, `dartFace e ≠ outerFace`), the `φ`-triangle gives
  `FanTriangle hNT v0 (head e) (head (σ⁻¹ e))`.  This is `spokeFace_head_eq` packaged
  with `inner_face_isFaceTriangle` (via the already-built `fanTriangleOfSpoke`).
* **§3 `backward_incident_faces_exact`** (R9 §4): the σ-predecessor head list
  `backHeads := (vertexDartList d0).reverse.map head` carries
  `IncidentNonOuterFacesExactly hNT v0 backHeads`.  `triangle_of_pair` comes from #1
  (a consecutive backward pair is `(head e, head (σ⁻¹ e))`); `exact_faces` comes from
  the orbit argument (every non-outer face at `v0` has a unique dart with tail `v0`,
  via `dart_eq_of_same_face_same_tail`).
* **§4 direction-free connectivity core** (R9 §5): `FanPathConnectivityData` +
  `deleteVertex_neighborsConnected_of_fanPath` re-prove `DeleteVertexNeighborsConnected`
  from a *path certificate* (faces_exact + neighbor_tail_mem_path + path_has_edge),
  abstracting the existing `deleteVertex_neighborsConnected_of_fan`.  The proof uses
  only the symmetric `VConn` chaining, which is direction-agnostic.
* **§5** the σ-backward path feeds the core: from `hNT` + the outgoing boundary spoke
  (and chordlessness for the no-chord field), the backward fan connectivity datum is
  σ-derived — the orientation obstruction is discharged.

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.

This re-proves connectivity from a path certificate as **new** lemmas; the existing
σ-forward `deleteVertex_neighborsConnected_of_fan` deletion theorem is untouched.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35FanBackward

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}

/-! ## Section 1.  The σ-backward fan triangle from an inner spoke -/

/-- **The σ-backward spoke triangle** (R9 §4).  For an inner spoke `e` at `v0`
(`tail e = v0`, `dartFace e ≠ outerFace`) the `φ`-triangle `(e, φ e, φ² e)` has tails
`(v0, head e, head (σ⁻¹ e))`, i.e. it is a `FanTriangle hNT v0 (head e) (head (σ⁻¹ e))`.
The natural local fan triangle points to the σ-**predecessor**. -/
def fanTriangle_of_spoke_pred {v0 : M.Vertex} {e : D}
    (htail : M.tail e = v0) (hinner : M.dartFace e ≠ hNT.outerFace) :
    FanTriangle hNT v0 (M.head e) (M.head (M.σ.symm e)) where
  d0 := e
  d1 := M.φ e
  d2 := M.φ (M.φ e)
  triangle := hNT.inner_face_isFaceTriangle hinner
  inner := hinner
  tail0 := htail
  tail1 := by simp
  tail2 := by
    -- `tail (φ² e) = head (φ e) = head (σ⁻¹ e)`.
    have hcube : (M.φ ^ 3) e = e :=
      faceLen_three_phi_cube_eq_self M hNT.simpleGraph (hNT.inner_faceLen_eq_three hinner)
    have hpred : M.head (M.φ e) = M.head (M.σ.symm e) :=
      ProofsInTheBook.ZinanCh35ChordlessFull.spokeFace_head_eq hcube
    rw [show M.tail (M.φ (M.φ e)) = M.head (M.φ e) from M.tail_phi _, hpred]

/-- The σ-backward spoke triangle has `d0`-dart `= e`, so its face is `dartFace e`. -/
lemma fanTriangle_of_spoke_pred_face {v0 : M.Vertex} {e : D}
    (htail : M.tail e = v0) (hinner : M.dartFace e ≠ hNT.outerFace) :
    (fanTriangle_of_spoke_pred htail hinner).face = M.dartFace e := rfl

/-- Transport a fan triangle along equalities of its two non-apex vertices. -/
def FanTriangle.cong {v0 a a' b b' : M.Vertex} (ha : a = a') (hb : b = b')
    (T : FanTriangle hNT v0 a b) : FanTriangle hNT v0 a' b' :=
  ha ▸ hb ▸ T

/-- `FanTriangle.cong` preserves the face (it only relabels the index vertices). -/
@[simp] lemma FanTriangle.cong_face {v0 a a' b b' : M.Vertex} (ha : a = a') (hb : b = b')
    (T : FanTriangle hNT v0 a b) :
    (FanTriangle.cong ha hb T).face = T.face := by
  subst ha; subst hb; rfl

/-! ## Section 2.  Index characterization of consecutive fan-path pairs

`consecutivePairs xs = xs.zip xs.tail`.  A pair `(a, b)` is a consecutive pair iff it
appears at some adjacent index pair `(i, i+1)`.  This index form is direction-aware:
it lets us read off the consecutive pairs of a `reverse`d list cleanly. -/

/-- A pair lies in `consecutivePairs xs` iff it occurs at adjacent indices. -/
lemma mem_consecutivePairs_iff {β : Type*} (xs : List β) (a b : β) :
    (a, b) ∈ NearTriangulation.consecutivePairs xs ↔
      ∃ i : ℕ, ∃ (h : i + 1 < xs.length), xs[i] = a ∧ xs[i + 1] = b := by
  rw [NearTriangulation.consecutivePairs, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, hget⟩
    rw [List.length_zip, List.length_tail] at hi
    have hi1 : i + 1 < xs.length := by omega
    have hil : i < xs.length := by omega
    have htl : i < xs.tail.length := by rw [List.length_tail]; omega
    refine ⟨i, hi1, ?_, ?_⟩
    · rw [List.getElem_zip] at hget
      exact (Prod.ext_iff.mp hget).1
    · rw [List.getElem_zip, List.getElem_tail htl] at hget
      exact (Prod.ext_iff.mp hget).2
  · rintro ⟨i, hi1, ha, hb⟩
    have hil : i < xs.length := by omega
    have htl : i < xs.tail.length := by rw [List.length_tail]; omega
    refine ⟨i, ?_, ?_⟩
    · rw [List.length_zip, List.length_tail]; omega
    · rw [List.getElem_zip, List.getElem_tail htl, ha, hb]

/-- Consecutive pairs of a reversed list are the reverses of the consecutive pairs of
the original list.  This is the list-algebra bridge that turns the σ-forward
`consecutive_sigma` enumeration into the σ-backward path's consecutive pairs. -/
lemma mem_consecutivePairs_reverse {β : Type*} (xs : List β) (a b : β) :
    (a, b) ∈ NearTriangulation.consecutivePairs xs.reverse ↔
      (b, a) ∈ NearTriangulation.consecutivePairs xs := by
  rw [mem_consecutivePairs_iff, mem_consecutivePairs_iff]
  constructor
  · rintro ⟨i, hi, ha, hb⟩
    have hilen : i + 1 < xs.length := by rw [List.length_reverse] at hi; exact hi
    -- reverse[i] = xs[len-1-i], reverse[i+1] = xs[len-1-(i+1)] = xs[len-2-i]
    refine ⟨xs.length - 1 - (i + 1), by omega, ?_, ?_⟩
    · -- xs[len-1-(i+1)] = b : from reverse[i+1] = b
      have hrev : xs.reverse[i + 1] = xs[xs.length - 1 - (i + 1)] := List.getElem_reverse hi
      rw [hrev] at hb; exact hb
    · -- xs[len-1-(i+1)+1] = a : from reverse[i] = a
      have hi0 : i < xs.reverse.length := by rw [List.length_reverse]; omega
      have hrev : xs.reverse[i] = xs[xs.length - 1 - i] := List.getElem_reverse hi0
      rw [hrev] at ha
      rw [← ha]; exact getElem_congr rfl (by omega) (by omega)
  · rintro ⟨i, hi, hb, ha⟩
    -- want index j with reverse[j] = a, reverse[j+1] = b
    -- a = xs[i+1], b = xs[i]; reverse[j] = xs[len-1-j]; pick len-1-j = i+1 → j = len-2-i
    have hjrev : xs.length - 1 - (i + 1) < xs.reverse.length := by
      rw [List.length_reverse]; omega
    have hjrev1 : xs.length - 1 - (i + 1) + 1 < xs.reverse.length := by
      rw [List.length_reverse]; omega
    refine ⟨xs.length - 1 - (i + 1), by rw [List.length_reverse]; omega, ?_, ?_⟩
    · have hrev : xs.reverse[xs.length - 1 - (i + 1)] =
          xs[xs.length - 1 - (xs.length - 1 - (i + 1))] := List.getElem_reverse hjrev
      rw [hrev, ← ha]; exact getElem_congr rfl (by omega) (by omega)
    · have hrev : xs.reverse[xs.length - 1 - (i + 1) + 1] =
          xs[xs.length - 1 - (xs.length - 1 - (i + 1) + 1)] := List.getElem_reverse hjrev1
      rw [hrev, ← hb]; exact getElem_congr rfl (by omega) (by omega)

/-! ## Section 3.  The σ-backward incident-faces certificate

Fix the outgoing outer-boundary spoke `d0` at `v0` (`σ d0 ≠ d0`, `tail d0 = v0`,
`dartFace d0 = outerFace`).  The σ-forward head list is `vertexDartList d0 |>.map head`;
the σ-**backward** path is its `reverse`.  Its consecutive pairs are exactly the
`(head e, head (σ⁻¹ e))` pairs of inner spokes, so each carries a fan triangle by
§1, and every non-outer face at `v0` is hit exactly once (orbit / unique-dart). -/

variable (hNT)

/-- The σ-backward fan path: the σ-predecessor head list at `v0`. -/
def backHeads (d0 : D) : List M.Vertex :=
  ((M.vertexDartList d0).map M.head).reverse

variable {hNT}

/-- `(vertexDartList d0)[i+1] = σ (vertexDartList d0)[i]` (consecutive non-wrap). -/
lemma vertexDartList_succ {d0 : D} (i : ℕ)
    (hi : i + 1 < (M.vertexDartList d0).length) :
    (M.vertexDartList d0)[i + 1] = M.σ ((M.vertexDartList d0)[i]) := by
  rw [M.vertexDartList_getElem d0 (i + 1) hi,
      M.vertexDartList_getElem d0 i (by omega), pow_succ', Equiv.Perm.coe_mul,
      Function.comp_apply]

/-- **Forward head pair ⟹ a σ-predecessor spoke.**  If `(b, a)` is a σ-forward
consecutive head pair of the star at `d0`, then there is an inner spoke `e` at `v0`
with `head e = a` and `head (σ⁻¹ e) = b`.  Hence `(a, b)` carries a fan triangle. -/
lemma forward_pair_spoke {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {a b : M.Vertex}
    (hpair : (b, a) ∈ NearTriangulation.consecutivePairs
      ((M.vertexDartList d0).map M.head)) :
    ∃ e : D, M.tail e = v0 ∧ M.dartFace e ≠ hNT.outerFace ∧
      M.head e = a ∧ M.head (M.σ.symm e) = b := by
  rw [mem_consecutivePairs_iff] at hpair
  obtain ⟨i, hi, hb, ha⟩ := hpair
  rw [List.length_map] at hi
  -- the two darts at indices i, i+1
  set D0 := M.vertexDartList d0 with hD0
  have hil : i < D0.length := by omega
  -- D0[i+1] = σ D0[i]
  have hsucc : D0[i + 1] = M.σ (D0[i]) := vertexDartList_succ i hi
  -- the spoke `e := D0[i+1] = σ D0[i]`
  refine ⟨D0[i + 1], ?_, ?_, ?_, ?_⟩
  · -- tail e = v0
    have hmem : D0[i + 1] ∈ D0 := List.getElem_mem _
    rw [M.vertexDartList_tail hσ hmem, htail0]
  · -- inner: e ≠ d0 (since D0[0] = d0 and i+1 ≥ 1, nodup)
    have hmem : D0[i + 1] ∈ D0 := List.getElem_mem _
    have htail_e : M.tail (D0[i + 1]) = M.tail d0 := M.vertexDartList_tail hσ hmem
    refine ProofsInTheBook.ZinanCh35StarConn.nonouter_of_ne_outer (hNT := hNT)
      hface0 htail_e ?_
    -- D0[i+1] ≠ d0
    intro he
    -- d0 = D0[0]
    have hd0 : D0[0]'(M.vertexDartList_length_pos hσ) = d0 := by
      have := M.vertexDartList_getElem d0 0 (M.vertexDartList_length_pos hσ)
      simpa using this
    have hidx : (0 : ℕ) = i + 1 :=
      (List.getElem_inj (h₀ := M.vertexDartList_length_pos hσ) (h₁ := hi)
        (M.vertexDartList_nodup d0)).mp (by rw [hd0]; exact he.symm)
    omega
  · -- head e = a : a = forwardHeads[i+1] = head D0[i+1]
    rw [← ha, List.getElem_map]
  · -- head (σ⁻¹ e) = b : σ⁻¹ e = σ⁻¹ (σ D0[i]) = D0[i] ; b = forwardHeads[i] = head D0[i]
    rw [hsucc, Equiv.symm_apply_apply, ← hb, List.getElem_map]

/-- A backward consecutive pair `(a, b)` gives a forward head pair `(b, a)`. -/
lemma backPair_forward {d0 : D} {a b : M.Vertex}
    (hp : (a, b) ∈ NearTriangulation.consecutivePairs (backHeads (M := M) d0)) :
    (b, a) ∈ NearTriangulation.consecutivePairs ((M.vertexDartList d0).map M.head) := by
  rw [backHeads] at hp; exact (mem_consecutivePairs_reverse _ a b).mp hp

/-- The inner spoke realizing a backward consecutive pair (chosen from
`forward_pair_spoke`). -/
noncomputable def backSpoke {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {a b : M.Vertex}
    (hp : (a, b) ∈ NearTriangulation.consecutivePairs (backHeads (M := M) d0)) : D :=
  (forward_pair_spoke hσ htail0 hface0 (backPair_forward hp)).choose

/-- The defining property of `backSpoke`: it is an inner spoke at `v0` with
`head = a` and `head ∘ σ⁻¹ = b`. -/
lemma backSpoke_spec {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {a b : M.Vertex}
    (hp : (a, b) ∈ NearTriangulation.consecutivePairs (backHeads (M := M) d0)) :
    M.tail (backSpoke hσ htail0 hface0 hp) = v0 ∧
      M.dartFace (backSpoke hσ htail0 hface0 hp) ≠ hNT.outerFace ∧
      M.head (backSpoke hσ htail0 hface0 hp) = a ∧
      M.head (M.σ.symm (backSpoke hσ htail0 hface0 hp)) = b :=
  (forward_pair_spoke hσ htail0 hface0 (backPair_forward hp)).choose_spec

/-- **The σ-backward fan triangle for a consecutive backward pair.**  A backward
consecutive pair `(a, b)` reverses to a forward head pair `(b, a)`, which by
`forward_pair_spoke` comes from an inner spoke `e := backSpoke` with `head e = a`,
`head (σ⁻¹ e) = b`.  `fanTriangle_of_spoke_pred` then gives `FanTriangle hNT v0 a b`,
with `.d0 = backSpoke`. -/
noncomputable def backTriangle {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {a b : M.Vertex}
    (hp : (a, b) ∈ NearTriangulation.consecutivePairs (backHeads (M := M) d0)) :
    FanTriangle hNT v0 a b :=
  FanTriangle.cong (backSpoke_spec hσ htail0 hface0 hp).2.2.1
    (backSpoke_spec hσ htail0 hface0 hp).2.2.2
    (fanTriangle_of_spoke_pred (backSpoke_spec hσ htail0 hface0 hp).1
      (backSpoke_spec hσ htail0 hface0 hp).2.1)

/-- `backTriangle`'s face is the `dartFace` of `backSpoke`. -/
lemma backTriangle_face {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {a b : M.Vertex}
    (hp : (a, b) ∈ NearTriangulation.consecutivePairs (backHeads (M := M) d0)) :
    (backTriangle hσ htail0 hface0 hp).face =
      M.dartFace (backSpoke hσ htail0 hface0 hp) := by
  rw [backTriangle, FanTriangle.cong_face, fanTriangle_of_spoke_pred_face]

/-- Any `FanTriangle` at apex `v0` represents a non-outer face incident at `v0`. -/
lemma fanTriangle_faceIncident {v0 a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    NearTriangulation.FaceIncidentAtVertex M T.face v0 :=
  ⟨T.d0, rfl, T.tail0⟩

/-! ### The `exact_faces` surjection helper

Every inner face incident at `v0` is the face of some backward consecutive pair.  The
spoke `d` realizing the face sits at index `k ≥ 1` of the σ-rotation `vertexDartList
d0` (`d ≠ d0` since `d0` is the unique outer spoke); the backward consecutive pair at
the matching position has its `backTriangle` `.d0` equal to `d` by the unique-dart fact
`dart_eq_of_same_face_same_tail`. -/

/-- The backward consecutive pair realizing an inner face `f` at `v0`.  Returns a pair
`(a, b)` in `consecutivePairs (backHeads d0)` together with the proof that its
`backTriangle` has face `f`. -/
lemma exists_backPair_face {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {f : M.Face}
    (hf : f ≠ hNT.outerFace) (hinc : NearTriangulation.FaceIncidentAtVertex M f v0) :
    ∃ (a b : M.Vertex) (hp : (a, b) ∈
        NearTriangulation.consecutivePairs (backHeads (M := M) d0)),
      (backTriangle hσ htail0 hface0 hp).face = f := by
  obtain ⟨d, hdf, hdt⟩ := hinc
  -- `d` is an inner spoke at `v0`, hence `d ≠ d0` and `d ∈ vertexDartList d0`.
  have hdne : d ≠ d0 := by
    intro h; rw [h] at hdf; exact hf (hdf ▸ hface0)
  have hdmem : d ∈ M.vertexDartList d0 := by
    rw [mem_vertexDartList_iff M hσ]
    exact Quotient.exact (show M.tail d0 = M.tail d by rw [hdt, htail0])
  -- `d = D0[k]` for some `k`; `k ≠ 0` since `D0[0] = d0`.
  obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hdmem
  have hd0_0 : (M.vertexDartList d0)[0]'(M.vertexDartList_length_pos hσ) = d0 := by
    have := M.vertexDartList_getElem d0 0 (M.vertexDartList_length_pos hσ); simpa using this
  have hk0 : k ≠ 0 := by
    intro h; subst h
    exact hdne (hkd.symm.trans hd0_0)
  -- the forward pair at index `k-1`: `(head D0[k-1], head D0[k])`.
  set H := (M.vertexDartList d0).map M.head with hH
  have hHk : k < H.length := by rw [hH, List.length_map]; exact hk
  have hHk1 : k - 1 < H.length := by rw [hH, List.length_map]; omega
  have hfwd : (H[k-1], H[k]) ∈ NearTriangulation.consecutivePairs H := by
    rw [mem_consecutivePairs_iff]
    refine ⟨k - 1, by omega, rfl, ?_⟩
    -- H[(k-1)+1] = H[k]
    exact getElem_congr (c := H) rfl (by omega) (by omega)
  -- the backward pair `(head D0[k], head D0[k-1])`.
  refine ⟨H[k], H[k-1], ?_, ?_⟩
  · rw [backHeads, mem_consecutivePairs_reverse]; exact hfwd
  -- the backTriangle's face = dartFace (backSpoke) = dartFace d = f, by uniqueness.
  rw [backTriangle_face]
  -- `backSpoke` is the spoke at `v0` whose head is `H[k] = head d`; identify with `d`.
  obtain ⟨hsptail, hspinner, hsphead, _⟩ := backSpoke_spec hσ htail0 hface0
    (show (H[k], H[k-1]) ∈ NearTriangulation.consecutivePairs (backHeads (M := M) d0) by
      rw [backHeads, mem_consecutivePairs_reverse]; exact hfwd)
  -- `head (backSpoke) = H[k] = head d`.
  have hHk_eq : H[k] = M.head d := by
    rw [show H[k] = M.head ((M.vertexDartList d0)[k]'(by rwa [List.length_map] at hHk))
        from List.getElem_map M.head, hkd]
  have hsp_eq : backSpoke hσ htail0 hface0 _ = d :=
    ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.head_injOn_sameCycle hNT
      hsptail hdt (by rw [hsphead, hHk_eq])
  rw [hsp_eq, hdf]

/-- **The σ-backward `triangle_of_pair` certificate** (R9 §4): each consecutive
backward path pair `(a, b)` carries a `FanTriangle hNT v0 a b`.  This is the
σ-derivable orientation content the σ-forward interface could not provide
(`forward_fanTriangle_forces_degree_two`).  It is the only `IncidentNonOuterFacesExactly`
field the deletion-connectivity core consumes (the `exact_faces` field is consumed
elsewhere, by the merged-orbit seam). -/
noncomputable def backward_triangle_of_pair {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    ∀ {a b : M.Vertex},
      (a, b) ∈ NearTriangulation.consecutivePairs (backHeads (M := M) d0) →
      FanTriangle hNT v0 a b :=
  fun {_ _} hp => backTriangle hσ htail0 hface0 hp

/-- **The σ-backward exact-faces correspondence** (R9 §4), stated *faithfully* as
`f ≠ outerFace → (Incident ↔ Exists)`.

For every **non-outer** face `f`, `f` is incident at `v0` **iff** it is the face of
some consecutive backward path pair's `backTriangle`.  Forward: `exists_backPair_face`
(orbit/unique-dart).  Backward: a `backTriangle` face is incident at its apex `v0`.

(Stated with the correct quantifier nesting `f ≠ outer → (… ↔ …)`.  The legacy
`IncidentNonOuterFacesExactly.exact_faces` field parses as
`(f ≠ outer → Incident) ↔ Exists` — `↔` binds looser than `→` — which is literally
false at `f = outer` (the outer face *is* incident at `v0`, yet is no backward pair's
face); that quirk is dodged in its sole consumer by an `f ≠ outer` pre-split.  The
σ-derivable mathematical content is exactly the faithful statement below.) -/
theorem backward_exact_faces {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) (f : M.Face) (hf : f ≠ hNT.outerFace) :
    NearTriangulation.FaceIncidentAtVertex M f v0 ↔
      ∃ (a b : M.Vertex) (hp : (a, b) ∈
          NearTriangulation.consecutivePairs (backHeads (M := M) d0)),
        (backTriangle hσ htail0 hface0 hp).face = f := by
  constructor
  · intro hinc
    exact exists_backPair_face hσ htail0 hface0 hf hinc
  · rintro ⟨a, b, hp, hface⟩
    rw [← hface]
    exact fanTriangle_faceIncident (backTriangle hσ htail0 hface0 hp)

/-! ### Section 3b.  The σ-predecessor certificate against the σ-FORWARD path

The fan interface (`FanIncidenceData.heads_eq`, `NeighborRotationOrder.heads_eq`)
fixes the fan path to the σ-**forward** head list `forwardHeads d0 := (vertexDartList
d0).map head`.  The *fixed* `IncidentNonOuterFacesExactly` field
`triangle_of_pair` now asks, for a forward consecutive pair `(a, b)`, for the
**predecessor-oriented** triangle `FanTriangle hNT v0 b a` (apex `v0`, edge `b → a`)
— exactly what `fanTriangle_of_spoke_pred` produces and what
`forward_fanTriangle_forces_degree_two` shows the *forward* orientation cannot.  This
section builds that certificate directly on the forward path, so the σ-forward
`FanIncidenceData` becomes inhabitable with no change to `heads_eq`. -/

/-- The σ-forward head list at `v0` (the order fixed by `heads_eq`). -/
def forwardHeads (d0 : D) : List M.Vertex := (M.vertexDartList d0).map M.head

/-- **The σ-predecessor fan triangle for a forward consecutive pair.**  A forward
consecutive pair `(a, b)` of the σ-rotation head list comes from an inner spoke
`e := forwardSpoke` with `head e = b`, `head (σ⁻¹ e) = a`; `fanTriangle_of_spoke_pred`
gives `FanTriangle hNT v0 b a` (the predecessor orientation). -/
noncomputable def forwardTriangle {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {a b : M.Vertex}
    (hp : (a, b) ∈ NearTriangulation.consecutivePairs (forwardHeads (M := M) d0)) :
    FanTriangle hNT v0 b a :=
  FanTriangle.cong (forward_pair_spoke hσ htail0 hface0 hp).choose_spec.2.2.1
    (forward_pair_spoke hσ htail0 hface0 hp).choose_spec.2.2.2
    (fanTriangle_of_spoke_pred (forward_pair_spoke hσ htail0 hface0 hp).choose_spec.1
      (forward_pair_spoke hσ htail0 hface0 hp).choose_spec.2.1)

/-- `forwardTriangle`'s face is the `dartFace` of the realizing forward spoke. -/
lemma forwardTriangle_face {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {a b : M.Vertex}
    (hp : (a, b) ∈ NearTriangulation.consecutivePairs (forwardHeads (M := M) d0)) :
    (forwardTriangle hσ htail0 hface0 hp).face =
      M.dartFace (forward_pair_spoke hσ htail0 hface0 hp).choose := by
  rw [forwardTriangle, FanTriangle.cong_face, fanTriangle_of_spoke_pred_face]

/-- **Every inner face at `v0` is the face of some forward consecutive pair.**  The
forward analogue of `exists_backPair_face`: the spoke `d` realizing an inner face `f`
sits at index `k ≥ 1` of the σ-rotation, and the forward consecutive pair at indices
`(k-1, k)` has `forwardTriangle` face `f` (the realizing spoke is `d` by uniqueness). -/
lemma exists_forwardPair_face {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) {f : M.Face}
    (hf : f ≠ hNT.outerFace) (hinc : NearTriangulation.FaceIncidentAtVertex M f v0) :
    ∃ (a b : M.Vertex) (hp : (a, b) ∈
        NearTriangulation.consecutivePairs (forwardHeads (M := M) d0)),
      (forwardTriangle hσ htail0 hface0 hp).face = f := by
  obtain ⟨d, hdf, hdt⟩ := hinc
  have hdne : d ≠ d0 := by
    intro h; rw [h] at hdf; exact hf (hdf ▸ hface0)
  have hdmem : d ∈ M.vertexDartList d0 := by
    rw [mem_vertexDartList_iff M hσ]
    exact Quotient.exact (show M.tail d0 = M.tail d by rw [hdt, htail0])
  obtain ⟨k, hk, hkd⟩ := List.getElem_of_mem hdmem
  have hd0_0 : (M.vertexDartList d0)[0]'(M.vertexDartList_length_pos hσ) = d0 := by
    have := M.vertexDartList_getElem d0 0 (M.vertexDartList_length_pos hσ); simpa using this
  have hk0 : k ≠ 0 := by
    intro h; subst h
    exact hdne (hkd.symm.trans hd0_0)
  set H := forwardHeads (M := M) d0 with hH
  have hHlen : H.length = (M.vertexDartList d0).length := by
    rw [hH, forwardHeads, List.length_map]
  have hHk : k < H.length := by rw [hHlen]; exact hk
  have hHk1 : k - 1 < H.length := by rw [hHlen]; omega
  have hfwd : (H[k-1], H[k]) ∈ NearTriangulation.consecutivePairs H := by
    rw [mem_consecutivePairs_iff]
    refine ⟨k - 1, by omega, rfl, ?_⟩
    exact getElem_congr (c := H) rfl (by omega) (by omega)
  refine ⟨H[k-1], H[k], hfwd, ?_⟩
  rw [forwardTriangle_face]
  -- `forwardSpoke` is the spoke at `v0` whose head is `H[k] = head d`; identify with `d`.
  obtain ⟨hsptail, hspinner, hsphead, _⟩ :=
    (forward_pair_spoke hσ htail0 hface0 hfwd).choose_spec
  have hHk_eq : H[k] = M.head d := by
    rw [show H[k] = M.head ((M.vertexDartList d0)[k]'(by rw [← hHlen]; exact hHk))
        from List.getElem_map M.head, hkd]
  have hsp_eq : (forward_pair_spoke hσ htail0 hface0 hfwd).choose = d :=
    ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.head_injOn_sameCycle hNT
      hsptail hdt (by rw [hsphead, hHk_eq])
  rw [hsp_eq, hdf]

/-- **The σ-forward `IncidentNonOuterFacesExactly` certificate (the FIX).**  Builds
the (now-σ-corrected) `IncidentNonOuterFacesExactly hNT v0 (forwardHeads d0)`
structure: `triangle_of_pair` is the predecessor-oriented `forwardTriangle`, and
`exact_faces` is the correctly-parenthesized `f ≠ outer → (Incident ↔ Exists)`.  This
is the σ-derived content the σ-forward `FanIncidenceData` / `BoundaryVertexFan`
interface demands; it was uninhabitable under the legacy (forward-oriented,
mis-parenthesized) field. -/
noncomputable def incidentNonOuterFacesExactly_forward {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    NearTriangulation.IncidentNonOuterFacesExactly hNT v0
      (forwardHeads (M := M) d0) where
  triangle_of_pair {_a _b} hp := forwardTriangle hσ htail0 hface0 hp
  exact_faces f hf := by
    constructor
    · intro hinc
      exact exists_forwardPair_face hσ htail0 hface0 hf hinc
    · rintro ⟨a, b, hp, hface⟩
      rw [← hface]
      exact fanTriangle_faceIncident (forwardTriangle hσ htail0 hface0 hp)

/-! ## Section 4.  The direction-free connectivity core (R9 §5)

The existing `deleteVertex_neighborsConnected_of_fan` consumes the σ-forward fan only
through `fan.incident_faces_exact.triangle_of_pair`, `neighbor_tail_mem_path`, and the
two-element shape of `fan.path`.  We abstract these into a path certificate
`FanPathConnectivityData` carrying *just* a `triangle_of_pair` function, the
neighbour-coverage fact, and a `path_has_edge` shape, and re-prove
`DeleteVertexNeighborsConnected` from it.  The proof uses only the **symmetric** `VConn`
chaining, which is direction-agnostic — so it accepts the σ-backward path verbatim.

The private `VConn` machinery of `PlanarMapFanConnectivity` is re-established here (it
is not exported); the public reductions
(`deleteVertex_dartStep_of_sigma/alpha`, `alpha_notMem_deleteVertexSet`,
`deleteVertex_reachable_symm`, `deleteVertex_connected_of_neighborsConnected`) are
reused. -/

namespace Conn

variable {v0 : M.Vertex}

/-- One deleted-map reachability step from a `σ`-cycle relation between survivors. -/
lemma rel_of_sigma {v : D} (x y : {d : D // d ∉ M.deleteVertexSet v})
    (h : M.σ.SameCycle x.1 y.1) :
    Relation.ReflTransGen (M.deleteVertex v).dartStep x y :=
  Relation.ReflTransGen.single
    (ProofsInTheBook.PlanarMap.CombMap.deleteVertex_dartStep_of_sigma M v x y h)

/-- One deleted-map reachability step from `y = M.α x` between survivors. -/
lemma rel_of_alpha {v : D} (x y : {d : D // d ∉ M.deleteVertexSet v})
    (h : y.1 = M.α x.1) :
    Relation.ReflTransGen (M.deleteVertex v).dartStep x y :=
  Relation.ReflTransGen.single
    (ProofsInTheBook.PlanarMap.CombMap.deleteVertex_dartStep_of_alpha M v x y h)

/-- A dart whose tail and head both differ (as `σ`-orbits) from the vertex of `v`
survives the star deletion. -/
lemma notMem_deleteVertexSet_of_tail_head_ne {v d : D}
    (htail : M.tail d ≠ M.tail v) (hhead : M.head d ≠ M.tail v) :
    d ∉ M.deleteVertexSet v := by
  rw [mem_deleteVertexSet_iff]
  simp only [mem_vertexDarts, not_or]
  refine ⟨?_, ?_⟩
  · intro h; exact htail (Quotient.sound h).symm
  · intro h; exact hhead (Quotient.sound h).symm

/-- The middle dart `T.d1` of a fan triangle `(v0, a, b)` survives the deletion of any
dart `d0` representing `v0`. -/
lemma fanTriangle_edge_dart_survives {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d1 ∉ M.deleteVertexSet d0 := by
  have hdist := T.vertices_pairwiseDistinct
  have htail : M.tail T.d1 ≠ M.tail d0 := by
    rw [T.tail1, htail0]; exact (hdist.1).symm
  have hhead_eq : M.head T.d1 = b := by
    have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
    have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
    rw [hh, T.tail2]
  have hhead : M.head T.d1 ≠ M.tail d0 := by
    rw [hhead_eq, htail0]; exact hdist.2.2
  exact notMem_deleteVertexSet_of_tail_head_ne htail hhead

/-- A fan triangle `(v0, a, b)` connects any surviving dart at `a` to any surviving
dart at `b` via the surviving triangle edge. -/
lemma fanTriangle_connects {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0)
    (p q : {d : D // d ∉ M.deleteVertexSet d0})
    (hp : M.tail p.1 = a) (hq : M.tail q.1 = b) :
    Relation.ReflTransGen (M.deleteVertex d0).dartStep p q := by
  have hd1 : T.d1 ∉ M.deleteVertexSet d0 := fanTriangle_edge_dart_survives T htail0
  have hd1' : M.α T.d1 ∉ M.deleteVertexSet d0 :=
    ProofsInTheBook.PlanarMap.CombMap.alpha_notMem_deleteVertexSet M d0 hd1
  set e1 : {d : D // d ∉ M.deleteVertexSet d0} := ⟨T.d1, hd1⟩
  set e1' : {d : D // d ∉ M.deleteVertexSet d0} := ⟨M.α T.d1, hd1'⟩
  have hpe1 : M.σ.SameCycle p.1 T.d1 :=
    Quotient.exact (show M.tail p.1 = M.tail T.d1 by rw [hp, T.tail1])
  have step1 := rel_of_sigma p e1 hpe1
  have step2 := rel_of_alpha e1 e1' rfl
  have hhead_eq : M.head T.d1 = b := by
    have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
    have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
    rw [hh, T.tail2]
  have he1'q : M.σ.SameCycle (M.α T.d1) q.1 :=
    Quotient.exact (show M.tail (M.α T.d1) = M.tail q.1 by rw [tail_alpha, hhead_eq, hq])
  have step3 := rel_of_sigma e1' q he1'q
  exact (step1.trans step2).trans step3

lemma consecutivePairs_cons_cons {α : Type*} (a b : α) (l : List α) :
    NearTriangulation.consecutivePairs (a :: b :: l) =
      (a, b) :: NearTriangulation.consecutivePairs (b :: l) := by
  simp [NearTriangulation.consecutivePairs]

/-- Symmetric "all survivors at `a` connect to all survivors at `b`". -/
def VConn {d0 : D} (a b : M.Vertex) : Prop :=
  ∀ p q : {d : D // d ∉ M.deleteVertexSet d0},
    M.tail p.1 = a → M.tail q.1 = b →
    Relation.ReflTransGen (M.deleteVertex d0).dartStep p q

lemma VConn.symm {d0 : D} {a b : M.Vertex} (h : VConn (M := M) (d0 := d0) a b) :
    VConn (M := M) (d0 := d0) b a := by
  intro p q hp hq
  exact ProofsInTheBook.PlanarMap.CombMap.deleteVertex_reachable_symm M d0 (h q p hq hp)

lemma fanTriangle_vconn {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    VConn (M := M) (d0 := d0) a b :=
  fun p q hp hq => fanTriangle_connects T htail0 p q hp hq

lemma fanTriangle_witness_snd {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = b := by
  have hd1 : T.d1 ∉ M.deleteVertexSet d0 := fanTriangle_edge_dart_survives T htail0
  have hd1' : M.α T.d1 ∉ M.deleteVertexSet d0 :=
    ProofsInTheBook.PlanarMap.CombMap.alpha_notMem_deleteVertexSet M d0 hd1
  refine ⟨⟨M.α T.d1, hd1'⟩, ?_⟩
  have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
  have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
  show M.tail (M.α T.d1) = b
  rw [tail_alpha, hh, T.tail2]

/-- Every vertex of `hd :: L` is `VConn` to the head `hd`, provided all consecutive
pairs carry fan triangles.  Direction-agnostic (uses `VConn.symm`). -/
lemma vconn_head_of_pairs {d0 : D} (htail0 : M.tail d0 = v0) :
    ∀ (L : List M.Vertex) (hd : M.Vertex),
      (∀ a b : M.Vertex, (a, b) ∈ NearTriangulation.consecutivePairs (hd :: L) →
        FanTriangle hNT v0 a b) →
      ∀ u : M.Vertex, u ∈ (hd :: L) → VConn (M := M) (d0 := d0) u hd := by
  intro L
  induction L with
  | nil =>
      intro hd _ u hu
      have hueq : u = hd := by simpa using hu
      subst hueq
      intro p q hp hq
      exact rel_of_sigma p q
        (Quotient.exact (show M.tail p.1 = M.tail q.1 by rw [hp, hq]))
  | cons b l ih =>
      intro hd htri u hu
      have hpair0 : (hd, b) ∈ NearTriangulation.consecutivePairs (hd :: b :: l) := by
        rw [consecutivePairs_cons_cons]; exact List.mem_cons.mpr (Or.inl rfl)
      have T0 : FanTriangle hNT v0 hd b := htri hd b hpair0
      have hVhd_b : VConn (M := M) (d0 := d0) hd b := fanTriangle_vconn T0 htail0
      have htri' : ∀ a c : M.Vertex,
          (a, c) ∈ NearTriangulation.consecutivePairs (b :: l) →
          FanTriangle hNT v0 a c := by
        intro a c hac
        apply htri a c
        rw [consecutivePairs_cons_cons]; exact List.mem_cons.mpr (Or.inr hac)
      have ihrun := ih b htri'
      rcases List.mem_cons.mp hu with hueq | hurest
      · subst hueq
        intro p q hp hq
        exact rel_of_sigma p q
          (Quotient.exact (show M.tail p.1 = M.tail q.1 by rw [hp, hq]))
      · have hVu_b : VConn (M := M) (d0 := d0) u b := ihrun u hurest
        intro p q hp hq
        obtain ⟨m, hm⟩ : ∃ m : {d : D // d ∉ M.deleteVertexSet d0}, M.tail m.1 = b :=
          fanTriangle_witness_snd T0 htail0
        have h1 := hVu_b p m hp hm
        have h2 := (hVhd_b.symm) m q hm hq
        exact h1.trans h2

/-! ### The path certificate -/

/-- **Direction-free fan-path connectivity certificate** (R9 §5).  A path of
neighbour vertices of `v0` whose consecutive pairs all carry fan triangles, covers all
neighbour-survivors, and has at least two entries.  Carries `triangle_of_pair` as a
plain function (it does *not* require the legacy `IncidentNonOuterFacesExactly` whose
`exact_faces` field is unfillable; the connectivity core never consumes that field). -/
structure FanPathConnectivityData (hNT : NearTriangulation M) (v0 : M.Vertex)
    (path : List M.Vertex) (d0 : D) where
  /-- Each consecutive path pair carries a fan triangle (the orientation content). -/
  triangle_of_pair : ∀ {a b : M.Vertex},
    (a, b) ∈ NearTriangulation.consecutivePairs path → FanTriangle hNT v0 a b
  /-- `d0` represents `v0`. -/
  tail0 : M.tail d0 = v0
  /-- Every neighbour-survivor of `v0` has its tail on the path. -/
  neighbor_tail_mem_path : ∀ {x : {d : D // d ∉ M.deleteVertexSet d0}},
    (∃ e ∈ M.deleteVertexSet d0, M.σ.SameCycle e x.1) → M.tail x.1 ∈ path
  /-- The path has at least two entries (`a :: b :: rest`). -/
  path_has_edge : ∃ a b rest, path = a :: b :: rest

/-- **The fan-path certificate discharges `DeleteVertexNeighborsConnected`** (R9 §5).
A direct re-proof of `deleteVertex_neighborsConnected_of_fan` from the abstract path
certificate: every neighbour-survivor is `VConn` to the path head, then two
neighbour-survivors connect through it.  Accepts the σ-backward path. -/
theorem deleteVertex_neighborsConnected_of_fanPath {path : List M.Vertex} {d0 : D}
    (data : FanPathConnectivityData hNT v0 path d0) :
    M.DeleteVertexNeighborsConnected d0 := by
  obtain ⟨hx0, b0, rest0, hpath⟩ := data.path_has_edge
  -- Each path vertex is `VConn` to the head `hx0`.
  have htri : ∀ a b : M.Vertex,
      (a, b) ∈ NearTriangulation.consecutivePairs (hx0 :: (b0 :: rest0)) →
      FanTriangle hNT v0 a b := by
    intro a b hab
    exact data.triangle_of_pair (by rw [hpath] at *; exact hab)
  have hhead : ∀ u : M.Vertex, u ∈ path → VConn (M := M) (d0 := d0) u hx0 := by
    intro u hu
    have hu' : u ∈ hx0 :: (b0 :: rest0) := by rw [← hpath]; exact hu
    exact vconn_head_of_pairs data.tail0 (b0 :: rest0) hx0 htri u hu'
  -- Assemble.
  intro x y hx hy
  have hxpath : M.tail x.1 ∈ path := data.neighbor_tail_mem_path hx
  have hypath : M.tail y.1 ∈ path := data.neighbor_tail_mem_path hy
  have hVx : VConn (M := M) (d0 := d0) (M.tail x.1) hx0 := hhead _ hxpath
  have hVy : VConn (M := M) (d0 := d0) (M.tail y.1) hx0 := hhead _ hypath
  -- a witness survivor at `hx0`: from the head pair's triangle.
  have hpair0 : (hx0, b0) ∈ NearTriangulation.consecutivePairs (hx0 :: (b0 :: rest0)) := by
    rw [consecutivePairs_cons_cons]; exact List.mem_cons.mpr (Or.inl rfl)
  have T0 : FanTriangle hNT v0 hx0 b0 := htri hx0 b0 hpair0
  obtain ⟨m, hm⟩ : ∃ m : {d : D // d ∉ M.deleteVertexSet d0}, M.tail m.1 = hx0 :=
    ⟨⟨T0.d1, fanTriangle_edge_dart_survives T0 data.tail0⟩, T0.tail1⟩
  have h1 := hVx x m rfl hm
  have h2 := (hVy.symm) m y hm rfl
  exact h1.trans h2

end Conn

/-! ### Neighbour coverage of the σ-backward path -/

/-- **Every neighbour-survivor's tail lies on the σ-backward path.**  Direction-agnostic:
the backward path `backHeads d0` is the reverse of the σ-forward head list, hence has the
same elements; a neighbour-survivor's tail is `head (α e)` for a star dart `α e`, whose
head is in the head list.  (Substantively the private `neighbor_tail_mem_path`, with σ⁻¹
enumerating the same orbit set.) -/
lemma neighbor_tail_mem_backHeads {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (_htail0 : M.tail d0 = v0)
    {x : {d : D // d ∉ M.deleteVertexSet d0}}
    (hx : ∃ e ∈ M.deleteVertexSet d0, M.σ.SameCycle e x.1) :
    M.tail x.1 ∈ backHeads (M := M) d0 := by
  obtain ⟨e, heS, hex⟩ := hx
  rw [mem_deleteVertexSet_iff] at heS
  rcases heS with he | hαe
  · -- `e ∈ vertexDarts d0` ⟹ `x` would be deleted.
    exfalso
    rw [mem_vertexDarts] at he
    have hxsame : M.σ.SameCycle d0 x.1 := he.trans hex
    exact x.2 ((mem_deleteVertexSet_iff M d0 x.1).2
      (Or.inl ((mem_vertexDarts M d0 x.1).2 hxsame)))
  · -- `α e` is a star dart; its head `= tail x.1` is in the head list.
    rw [mem_vertexDarts] at hαe
    have hαe_mem : M.α e ∈ M.vertexDartList d0 :=
      (mem_vertexDartList_iff M hσ (M.α e)).2 hαe
    have htx : M.tail x.1 = M.head (M.α e) := by
      have h1 : M.tail x.1 = M.tail e := (Quotient.sound hex).symm
      rw [h1, head_alpha]
    have hmem : M.head (M.α e) ∈ (M.vertexDartList d0).map M.head :=
      List.mem_map_of_mem hαe_mem
    rw [htx, backHeads, List.mem_reverse]
    exact hmem

/-- The σ-backward path has at least two entries (degree `≥ 2` at a boundary vertex). -/
lemma backHeads_has_edge {d0 : D} (hσ : M.σ d0 ≠ d0) :
    ∃ a b rest, backHeads (M := M) d0 = a :: b :: rest := by
  have hge2 : 2 ≤ (backHeads (M := M) d0).length := by
    rw [backHeads, List.length_reverse, List.length_map]
    exact ProofsInTheBook.ZinanCh35ChordlessFull.vertexDartList_length_ge_two hσ
  -- a list of length ≥ 2 is `a :: b :: rest`.
  match hbh : backHeads (M := M) d0 with
  | [] => rw [hbh] at hge2; simp at hge2
  | [_] => rw [hbh] at hge2; simp at hge2
  | a :: b :: rest => exact ⟨a, b, rest, rfl⟩

/-! ## Section 5.  Assembly: the σ-backward fan-path connectivity datum

From `hNT` and the outgoing boundary spoke `d0` at `v0` (`σ d0 ≠ d0`, `tail d0 = v0`,
`dartFace d0 = outerFace`), the σ-backward path certificate exists — fully σ-derived,
no orientation/chirality input.  Feeding it into `deleteVertex_neighborsConnected_of_fanPath`
discharges `DeleteVertexNeighborsConnected`, and thence connectivity of the deleted map. -/

/-- **The σ-backward fan-path connectivity datum** at a boundary vertex.  Every field
is σ-derivable from `hNT` and the outgoing boundary spoke. -/
noncomputable def fanPathConnectivityData_backward {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    Conn.FanPathConnectivityData hNT v0 (backHeads (M := M) d0) d0 where
  triangle_of_pair {_a _b} hp := backTriangle hσ htail0 hface0 hp
  tail0 := htail0
  neighbor_tail_mem_path {_x} hx := neighbor_tail_mem_backHeads hσ htail0 hx
  path_has_edge := backHeads_has_edge hσ

/-- **σ-backward neighbour reconnection.**  At a boundary vertex `v0` with outgoing
boundary spoke `d0`, the σ-backward fan path discharges `DeleteVertexNeighborsConnected
d0` — the orientation obstruction is resolved with no chirality input. -/
theorem deleteVertex_neighborsConnected_backward {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    M.DeleteVertexNeighborsConnected d0 :=
  Conn.deleteVertex_neighborsConnected_of_fanPath
    (fanPathConnectivityData_backward hσ htail0 hface0)

/-- **The deleted map is connected (σ-backward fan form).**  Deleting the closed star
of a boundary vertex `v0` (with outgoing boundary spoke `d0`) of a near-triangulation
leaves a connected combinatorial map — connectivity is σ-derived through the backward
fan path, no orientation certificate.  This is the deletion-connectivity content the
chordless branch needs, now unconditional in the orientation residue. -/
theorem deleteVertex_connected_backward {v0 : M.Vertex} {d0 : D}
    (hσ : M.σ d0 ≠ d0) (htail0 : M.tail d0 = v0)
    (hface0 : M.dartFace d0 = hNT.outerFace) :
    (M.deleteVertex d0).Connected :=
  ProofsInTheBook.PlanarMap.CombMap.deleteVertex_connected_of_neighborsConnected
    M d0 hNT.sphere.1 (deleteVertex_neighborsConnected_backward hσ htail0 hface0)

/-- **The outgoing boundary spoke exists at any boundary vertex**, so the only input to
the σ-backward connectivity is `hNT` itself: given a boundary vertex `v0`, there is an
outgoing boundary spoke `d0` with `σ d0 ≠ d0`, `tail d0 = v0`, `dartFace d0 = outerFace`. -/
theorem exists_outgoing_boundary_spoke {v0 : M.Vertex}
    (hv0 : hNT.outerCycle.IsBoundaryVertex v0) :
    ∃ d0 : D, M.σ d0 ≠ d0 ∧ M.tail d0 = v0 ∧ M.dartFace d0 = hNT.outerFace :=
  ProofsInTheBook.ZinanCh35ChordlessFull.exists_outgoing_boundary_spoke hNT hv0

/-- **σ-backward neighbour reconnection from a boundary vertex.**  Combining
`exists_outgoing_boundary_spoke` with `deleteVertex_neighborsConnected_backward`: at any
boundary vertex `v0` there is a dart `d0` representing it whose star deletion keeps all
neighbours of `v0` reconnected — σ-derived, no orientation input. -/
theorem boundaryVertex_deletion_neighborsConnected_backward {v0 : M.Vertex}
    (hv0 : hNT.outerCycle.IsBoundaryVertex v0) :
    ∃ d0 : D, M.tail d0 = v0 ∧ M.dartFace d0 = hNT.outerFace ∧
      M.DeleteVertexNeighborsConnected d0 := by
  obtain ⟨d0, hσ, htail0, hface0⟩ := exists_outgoing_boundary_spoke hv0
  exact ⟨d0, htail0, hface0,
    deleteVertex_neighborsConnected_backward hσ htail0 hface0⟩

end ProofsInTheBook.ZinanCh35FanBackward

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35FanBackward.fanTriangle_of_spoke_pred
#print axioms ProofsInTheBook.ZinanCh35FanBackward.forward_pair_spoke
#print axioms ProofsInTheBook.ZinanCh35FanBackward.backTriangle
#print axioms ProofsInTheBook.ZinanCh35FanBackward.backward_triangle_of_pair
#print axioms ProofsInTheBook.ZinanCh35FanBackward.backward_exact_faces
#print axioms ProofsInTheBook.ZinanCh35FanBackward.forwardTriangle
#print axioms ProofsInTheBook.ZinanCh35FanBackward.exists_forwardPair_face
#print axioms ProofsInTheBook.ZinanCh35FanBackward.incidentNonOuterFacesExactly_forward
#print axioms ProofsInTheBook.ZinanCh35FanBackward.Conn.deleteVertex_neighborsConnected_of_fanPath
#print axioms ProofsInTheBook.ZinanCh35FanBackward.fanPathConnectivityData_backward
#print axioms ProofsInTheBook.ZinanCh35FanBackward.deleteVertex_neighborsConnected_backward
#print axioms ProofsInTheBook.ZinanCh35FanBackward.deleteVertex_connected_backward
#print axioms ProofsInTheBook.ZinanCh35FanBackward.boundaryVertex_deletion_neighborsConnected_backward
