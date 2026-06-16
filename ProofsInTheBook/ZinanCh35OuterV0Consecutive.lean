import ProofsInTheBook.PlanarMapOuterArc
import ProofsInTheBook.PlanarMapBoundaryArcSplit

/-!
# The two consecutive outer darts at a deleted boundary vertex (Ch35 R6a keystone)

This file proves the isolated keystone of the merged-outer-arc seam
(`MergedOuterArcData`, `PlanarMapOuterArc.lean`): on the outer boundary cycle
`C := hNT.outerCycle`, a boundary vertex `v0` is touched by **exactly two**
boundary darts, and they are `M.φ`-consecutive:

* a unique outer dart `bin ∈ C.darts` with `M.head bin = v0`;
* a unique outer dart `bout ∈ C.darts` with `M.tail bout = v0`;
* `bout = M.φ bin` (the in-dart's `φ`-successor is the out-dart).

## Where the hypotheses are used

The only planarity input consumed is `hNT.outer_simple : C.VertexNodup` (the
boundary vertex list is simple — a Jordan-curve fact already packaged in the
near-triangulation).  Everything else is the orbit-algebra of the cyclic dart
list `C.darts`:

* **Uniqueness of `bout`** — `tail_injective_on_darts`
  (`PlanarMapNearTriangulation.lean:108`), which is exactly `VertexNodup` pushed
  through `vertices_eq : C.vertices = C.darts.map M.tail`.
* **Uniqueness of `bin`** — `C.darts` is closed under `M.φ`
  (`mem_darts_iff` + `dartFace_phi`), and `M.head d = M.tail (M.φ d)`
  (`tail_phi`), so head-uniqueness reduces to tail-uniqueness of `M.φ d`.
* **φ-adjacency `bout = M.φ bin`** — purely the cyclic structure: the cyclic
  predecessor `bin` of `bout` satisfies `M.φ bin = bout` (`consecutive_phi`) and
  `M.head bin = M.tail bout = v0` (`consecutive_vertex`).

`BoundaryChordless` is **not** needed for the in/out adjacency itself: on a
*simple* boundary cycle the two darts incident to a vertex are automatically
`φ`-consecutive.  (Chordlessness enters the larger `MergedOuterArcData`
construction — identifying these darts with the fan endpoints — not this
keystone, so the statement here is proved under the weaker, cleaner hypothesis
`VertexNodup`.)

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.  The
only inputs are the near-triangulation `hNT` and the boundary-vertex fact for
`v0`.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}

/-- **Cyclic predecessor witness.**  Every listed dart has a cyclic predecessor on
the cyclic dart list: a dart `bin ∈ C.darts` with `M.φ bin = bout` (and hence
`M.head bin = M.tail bout`, by `consecutive_vertex`). -/
lemma exists_phi_pred (C : BoundaryCycle M f) {bout : D} (hbout : bout ∈ C.darts) :
    ∃ bin : D, bin ∈ C.darts ∧ M.φ bin = bout ∧ M.head bin = M.tail bout := by
  classical
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  -- the position of `bout`
  rw [List.mem_iff_getElem] at hbout
  obtain ⟨q, hq, hgetq⟩ := hbout
  -- its cyclic predecessor index `p = (q + L - 1) % L`
  set p : ℕ := (q + L - 1) % L with hp
  have hpL : p < L := by rw [hp]; exact Nat.mod_lt _ hLpos
  -- cyclicNext p = q
  have hcyc : (cyclicNext C.normalized.length_pos ⟨p, hpL⟩ : Fin L) = ⟨q, hq⟩ := by
    apply Fin.ext
    show (p + 1) % L = q
    rw [hp]
    -- ((q + L - 1) % L + 1) % L = q
    rw [Nat.mod_add_mod, show q + L - 1 + 1 = q + L from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  refine ⟨C.darts[p]'hpL, List.getElem_mem hpL, ?_, ?_⟩
  · -- `M.φ bin = bout` from `consecutive_phi`
    have hcp := C.consecutive_phi ⟨p, hpL⟩
    rw [hcyc] at hcp
    have hq' : C.darts.get ⟨q, hq⟩ = C.darts[q]'hq := rfl
    have hp' : C.darts.get ⟨p, hpL⟩ = C.darts[p]'hpL := rfl
    rw [hq', hp', hgetq] at hcp
    -- hcp : bout = M.φ (C.darts[p])
    exact hcp.symm
  · -- `M.head bin = M.tail bout` from `consecutive_vertex`
    have hcv := C.consecutive_vertex ⟨p, hpL⟩
    rw [hcyc] at hcv
    have hq' : C.darts.get ⟨q, hq⟩ = C.darts[q]'hq := rfl
    have hp' : C.darts.get ⟨p, hpL⟩ = C.darts[p]'hpL := rfl
    rw [hq', hp', hgetq] at hcv
    -- hcv : M.tail bout = M.head (C.darts[p])
    exact hcv.symm

/-- `C.darts` is closed under `M.φ`: the face of `M.φ d` equals the face of `d`. -/
lemma phi_mem_darts (C : BoundaryCycle M f) {d : D} (hd : d ∈ C.darts) :
    M.φ d ∈ C.darts := by
  rw [C.mem_darts_iff] at hd ⊢
  rw [dartFace_phi, hd]

end BoundaryCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M) {v0 : M.Vertex}

/-- **Unique outer out-dart at `v0`.**  Exactly one boundary dart has tail `v0`.
This is `tail_injective_on_darts` (i.e. `outer_simple`) packaged as existence and
uniqueness. -/
lemma exists_unique_outer_tail (hv0 : hNT.outerCycle.IsBoundaryVertex v0) :
    ∃! bout : D, bout ∈ hNT.outerCycle.darts ∧ M.tail bout = v0 := by
  classical
  obtain ⟨p, hp⟩ := hNT.outerCycle.exists_pos_of_isBoundaryVertex hv0
  refine ⟨hNT.outerCycle.darts[p.1]'p.2, ⟨List.getElem_mem p.2, hp⟩, ?_⟩
  rintro b ⟨hbmem, hbtail⟩
  exact hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hbmem
    (List.getElem_mem p.2) (by rw [hbtail, hp])

/-- **Unique outer in-dart at `v0`.**  Exactly one boundary dart has head `v0`.
Head-uniqueness reduces to tail-uniqueness of the `φ`-successor (`tail_phi` +
`phi_mem_darts` + `tail_injective_on_darts`). -/
lemma exists_unique_outer_head (hv0 : hNT.outerCycle.IsBoundaryVertex v0) :
    ∃! bin : D, bin ∈ hNT.outerCycle.darts ∧ M.head bin = v0 := by
  classical
  -- the unique out-dart `bout`
  obtain ⟨bout, ⟨hboutmem, hbouttail⟩, _⟩ := hNT.exists_unique_outer_tail hv0
  -- its cyclic predecessor is an in-dart
  obtain ⟨bin, hbinmem, hphi, hhead⟩ := hNT.outerCycle.exists_phi_pred hboutmem
  have hbinhead : M.head bin = v0 := by rw [hhead, hbouttail]
  refine ⟨bin, ⟨hbinmem, hbinhead⟩, ?_⟩
  rintro b ⟨hbmem, hbhead⟩
  -- head b = head bin = v0 ⟹ tail (φ b) = tail (φ bin), and both φ-images are listed
  have hφb : M.φ b ∈ hNT.outerCycle.darts := hNT.outerCycle.phi_mem_darts hbmem
  have hφbin : M.φ bin ∈ hNT.outerCycle.darts := hNT.outerCycle.phi_mem_darts hbinmem
  have htails : M.tail (M.φ b) = M.tail (M.φ bin) := by
    rw [tail_phi, tail_phi, hbhead, hbinhead]
  have hφeq : M.φ b = M.φ bin :=
    hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφb hφbin htails
  exact M.φ.injective hφeq

/-- **The two consecutive outer darts at a boundary vertex `v0` (Ch35 R6a
keystone).**  On the outer cycle there is a unique in-dart `bin` (head `v0`) and
a unique out-dart `bout` (tail `v0`), and `bout = M.φ bin`.

All consumed planarity input is `hNT.outer_simple : VertexNodup`; the φ-adjacency
is the cyclic structure of `C.darts`.  This discharges the seam keystone of
`MergedOuterArcData` (see `PlanarMapOuterArc.lean`). -/
theorem outer_v0_darts_consecutive (hv0 : hNT.outerCycle.IsBoundaryVertex v0) :
    ∃ bin bout : D,
      -- the in-dart, unique with head v0
      (bin ∈ hNT.outerCycle.darts ∧ M.head bin = v0) ∧
      (∀ b, b ∈ hNT.outerCycle.darts → M.head b = v0 → b = bin) ∧
      -- the out-dart, unique with tail v0
      (bout ∈ hNT.outerCycle.darts ∧ M.tail bout = v0) ∧
      (∀ b, b ∈ hNT.outerCycle.darts → M.tail b = v0 → b = bout) ∧
      -- and they are φ-consecutive
      M.φ bin = bout := by
  classical
  obtain ⟨bout, ⟨hboutmem, hbouttail⟩, hboutuniq⟩ := hNT.exists_unique_outer_tail hv0
  obtain ⟨bin, ⟨hbinmem, hbinhead⟩, hbinuniq⟩ := hNT.exists_unique_outer_head hv0
  -- The cyclic predecessor of `bout` is an in-dart, hence equals `bin`; so φ bin = bout.
  obtain ⟨bpred, hbpredmem, hphi, hhead⟩ := hNT.outerCycle.exists_phi_pred hboutmem
  have hpredhead : M.head bpred = v0 := by rw [hhead, hbouttail]
  have hpred_eq_bin : bpred = bin := hbinuniq bpred ⟨hbpredmem, hpredhead⟩
  refine ⟨bin, bout, ⟨hbinmem, hbinhead⟩, ?_, ⟨hboutmem, hbouttail⟩, ?_, ?_⟩
  · intro b hbmem hbhead; exact hbinuniq b ⟨hbmem, hbhead⟩
  · intro b hbmem hbtail; exact hboutuniq b ⟨hbmem, hbtail⟩
  · rw [← hpred_eq_bin]; exact hphi

/-! ## The easy `MergedOuterArcData` fields from the keystone

We now draft the `MergedOuterArcData` bundle.  The keystone identifies the seam
`bin/bout`; the **exit survivor** `o_pre` is the cyclic predecessor of `bin` (the
last outer survivor, with `M.φ o_pre = bin`).  Two of the four `exit_*` fields are
immediate from the keystone + outer-cycle bookkeeping:

* `exit_face` — `o_pre ∈ C.darts`, so its `M.dartFace` is the outer face;
* `exit_next_deleted` — `M.φ o_pre = bin` and `M.head bin = v0 = M.tail d0`, so the
  successor `bin` touches `v0` and is deleted (the `head = v0` ⟹ deleted fact).

The remaining two fields are the genuinely planar seam facts, **not** produced by
this keystone and isolated here as named hypotheses (they are discharged by the
fan layer — `PlanarMapFanMergedOrbit` Case-B + `fanTriangle_shared_spoke` — and the
surviving-arc contiguity walk):

* `exit_jump` — `M.σ (M.φ o_pre) = M.σ bin = M.φ (M.α bin) = r` (the spoke `M.α bin`
  at `v0` is the head triangle's `d0`, identified via the shared-spoke fact);
* `arc_run` — every surviving outer dart reaches `o_pre` along a contiguous forward
  `M.φ`-run of survivors (the surviving outer arc is one `M.φ`-block).

The first two we prove; the last two we package as a precise interface so the
bundle is `sorry`-free and the residual content is named, not faked. -/

/-- A dart whose head is `v0 = M.tail d0` is deleted by the star deletion of `d0`
(it is `α` of a dart at `v0`).  Mirrors `fanTriangle_d2_deleted`. -/
lemma mem_deleteVertexSet_of_head {d d0 : D} (htail0 : M.tail d0 = v0)
    (hhead : M.head d = v0) : d ∈ M.deleteVertexSet d0 := by
  rw [mem_deleteVertexSet_iff]; right
  rw [mem_vertexDarts]
  exact Quotient.exact (show M.tail d0 = M.tail (M.α d) by
    rw [tail_alpha, hhead, htail0])

/-- **The two derivable `exit_*` facts for the exit survivor.**  Let `oPre` be a
surviving dart on the outer face whose `M.φ`-successor `bin` has head `v0` (the
exit survivor `o_pre`, cyclic predecessor of the in-dart).  Then its `M.dartFace`
is the outer face and `M.φ oPre` is deleted — the two `MergedOuterArcData` fields
`exit_face`/`exit_next_deleted` discharged directly from the keystone geometry. -/
lemma exit_face_and_next_deleted {d0 : D} (htail0 : M.tail d0 = v0)
    (oPre : {d : D // d ∉ M.deleteVertexSet d0})
    (hface : oPre.1 ∈ hNT.outerCycle.darts)
    (hnexthead : M.head (M.φ oPre.1) = v0) :
    M.dartFace oPre.1 = hNT.outerFace ∧
      M.φ oPre.1 ∈ M.deleteVertexSet d0 :=
  ⟨hNT.outerCycle.dartFace_of_mem_darts hface,
    mem_deleteVertexSet_of_head (v0 := v0) htail0 hnexthead⟩

/-- **Assemble `MergedOuterArcData` from the keystone, given the two genuinely
planar residual fields.**  The keystone supplies the seam `bin/bout` and the exit
survivor `oPre` (cyclic predecessor of `bin`, `M.φ oPre = bin`, `M.head bin = v0`);
this lemma derives `exit_face` and `exit_next_deleted` from it, and consumes the
two remaining seam facts — the Case-B spoke jump (`exit_jump`) and the surviving-arc
contiguity (`arc_run`) — as the precisely-stated residual interface they genuinely
are (discharged by the `PlanarMapFanMergedOrbit` Case-B calculus +
`fanTriangle_shared_spoke`, not by this keystone). -/
def mergedOuterArcData_of_exit {d0 : D}
    (r : {d : D // d ∉ M.deleteVertexSet d0})
    (htail0 : M.tail d0 = v0)
    (oPre : {d : D // d ∉ M.deleteVertexSet d0})
    (hface : oPre.1 ∈ hNT.outerCycle.darts)
    (hnexthead : M.head (M.φ oPre.1) = v0)
    -- residual seam fields (NOT from the keystone; supplied by the fan layer):
    (hjump : M.σ (M.φ oPre.1) = r.1)
    (harc : ∀ x : {d : D // d ∉ M.deleteVertexSet d0},
      M.dartFace x.1 = hNT.outerFace →
      ∃ k : ℕ, (∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet d0) ∧
        (M.φ ^ k) x.1 = oPre.1) :
    MergedOuterArcData M d0 r hNT.outerFace where
  exit := oPre
  exit_face := (hNT.exit_face_and_next_deleted htail0 oPre hface hnexthead).1
  exit_next_deleted := (hNT.exit_face_and_next_deleted htail0 oPre hface hnexthead).2
  exit_jump := hjump
  arc_run := harc

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
