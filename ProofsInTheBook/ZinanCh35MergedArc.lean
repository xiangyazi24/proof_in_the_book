import ProofsInTheBook.ZinanCh35OuterV0Consecutive
import ProofsInTheBook.ZinanCh35ChordlessClose

/-!
# Head seam facts for the chordless boundary deletion

This file contains the non-circular, dart-level seam facts used by the
`MergedOuterArcData` producer.  It deliberately stays below
`DeletedSeamData`: the merged orbit and clean-face fields consume these facts
later, so they cannot be used here.
-/

set_option linter.unusedSectionVars false

namespace ProofsInTheBook.ZinanCh35MergedArc

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open Equiv

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]
variable {M : CombMap D} {hNT : NearTriangulation M}

/-- The Case-B seam jump at the old outer exit, once the incoming outer dart is
identified with the first fan spoke.  This is the algebraic core:
`σ bin = φ (α bin) = T.d1`. -/
lemma incoming_outer_exit_jumps_to_head_fan_edge {v0 a b : M.Vertex} {bin : D}
    (hbin_head : M.head bin = v0) (hbin_tail : M.tail bin = a)
    (T : FanTriangle hNT v0 a b) :
    M.σ bin = T.d1 := by
  have hαbin_tail : M.tail (M.α bin) = v0 := by
    rw [tail_alpha, hbin_head]
  have hαbin_head : M.head (M.α bin) = a := by
    rw [head_alpha, hbin_tail]
  have hT0_head : M.head T.d0 = a := by
    calc
      M.head T.d0 = M.tail (M.φ T.d0) := by rw [tail_phi]
      _ = M.tail T.d1 := by rw [T.triangle.1]
      _ = a := T.tail1
  have hspoke : M.α bin = T.d0 :=
    head_injOn_sameCycle hNT hαbin_tail T.tail0
      (hαbin_head.trans hT0_head.symm)
  calc
    M.σ bin = M.φ (M.α bin) := by rw [sigma_apply]
    _ = M.φ T.d0 := by rw [hspoke]
    _ = T.d1 := T.triangle.1

/-- On the old outer cycle, the darts deleted by deleting `v0` are exactly the
incoming and outgoing outer darts at `v0`. -/
lemma old_outer_deleted_iff_eq_bin_or_bout {v0 : M.Vertex} {dDel bin bout d : D}
    (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin)
    (hd : d ∈ hNT.outerCycle.darts) :
    d ∈ M.deleteVertexSet dDel ↔ d = bin ∨ d = bout := by
  have hbout_mem : bout ∈ hNT.outerCycle.darts := by
    rw [hbout]
    exact hNT.outerCycle.phi_mem_darts hbin_mem
  have hbout_tail : M.tail bout = v0 := by
    rw [hbout, tail_phi, hbin_head]
  constructor
  · intro hdel
    rw [mem_deleteVertexSet_iff] at hdel
    rcases hdel with htail | hhead
    · have hd_tail : M.tail d = v0 := by
        rw [← htailDel]
        exact (Quotient.sound ((mem_vertexDarts M dDel d).mp htail)).symm
      right
      exact hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hd hbout_mem
        (hd_tail.trans hbout_tail.symm)
    · have hd_head : M.head d = v0 := by
        rw [← htailDel]
        exact (Quotient.sound ((mem_vertexDarts M dDel (M.α d)).mp hhead)).symm
      have hφd_mem : M.φ d ∈ hNT.outerCycle.darts :=
        hNT.outerCycle.phi_mem_darts hd
      have hφd_tail : M.tail (M.φ d) = v0 := by
        rw [tail_phi, hd_head]
      have hφd_eq :
          M.φ d = bout :=
        hNT.outerCycle.tail_injective_on_darts hNT.outer_simple hφd_mem hbout_mem
          (hφd_tail.trans hbout_tail.symm)
      left
      apply M.φ.injective
      rw [hφd_eq, hbout]
  · intro h
    rcases h with h | h
    · subst d
      exact mem_deleteVertexSet_of_head (M := M) (v0 := v0) htailDel hbin_head
    · subst d
      rw [mem_deleteVertexSet_iff]
      left
      rw [mem_vertexDarts]
      exact Quotient.exact (show M.tail dDel = M.tail bout by
        rw [htailDel, hbout_tail])

/-- If `dOut` is the outgoing outer dart at `v0` and `bin` is the incoming outer
dart with `M.φ bin = dOut`, then the tail of `bin` is the other fan endpoint
`head (σ⁻¹ dOut)`. -/
lemma incoming_outer_tail_eq_head_sigma_symm {v0 : M.Vertex} {dOut bin : D}
    (hfaceOut : M.dartFace dOut = hNT.outerFace)
    (htailOut : M.tail dOut = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (_hphi : M.φ bin = dOut) :
    M.tail bin = M.head (M.σ.symm dOut) := by
  have hv0 : hNT.outerCycle.IsBoundaryVertex v0 := by
    simpa [htailOut] using
      (ProofsInTheBook.ZinanCh35StarConn.isBoundaryVertex_tail_of_outer
        (hNT := hNT) hfaceOut)
  obtain ⟨_bin0, _hb0, huniq⟩ := hNT.exists_unique_outer_head hv0
  have hαface : M.dartFace (M.α (M.σ.symm dOut)) = hNT.outerFace := by
    have hkey : M.dartFace (M.σ (M.σ.symm dOut)) =
        M.dartFace (M.α (M.σ.symm dOut)) := by
      have hφeq : M.φ (M.α (M.σ.symm dOut)) = M.σ (M.σ.symm dOut) := by
        simp [φ, Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
      calc M.dartFace (M.σ (M.σ.symm dOut))
          = M.dartFace (M.φ (M.α (M.σ.symm dOut))) := by rw [hφeq]
        _ = M.dartFace (M.α (M.σ.symm dOut)) := M.dartFace_phi _
    rw [Equiv.apply_symm_apply] at hkey
    rw [← hkey]
    exact hfaceOut
  have hαmem : M.α (M.σ.symm dOut) ∈ hNT.outerCycle.darts :=
    (hNT.outerCycle.mem_darts_iff _).2 hαface
  have hαhead : M.head (M.α (M.σ.symm dOut)) = v0 := by
    rw [head_alpha]
    have htail : M.tail (M.σ.symm dOut) = M.tail dOut := by
      have h := M.tail_sigma (M.σ.symm dOut)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    rw [htail, htailOut]
  have hinc : M.α (M.σ.symm dOut) = bin :=
    huniq (M.α (M.σ.symm dOut)) ⟨hαmem, hαhead⟩ |>.trans
      (huniq bin ⟨hbin_mem, hbin_head⟩).symm
  rw [← hinc, tail_alpha]

/-- The cyclic predecessor `oPre` of the incoming outer dart survives the deletion:
the only deleted darts on the old outer face are `bin` and `bout = φ bin`, and
`outer_len ≥ 3` rules out `oPre` being either of them. -/
lemma old_outer_predecessor_survives {v0 : M.Vertex} {dDel bin bout oPre : D}
    (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin)
    (hoPre_mem : oPre ∈ hNT.outerCycle.darts)
    (hoPre_phi : M.φ oPre = bin) :
    oPre ∉ M.deleteVertexSet dDel := by
  intro hdel
  have hclass :=
    (old_outer_deleted_iff_eq_bin_or_bout (hNT := hNT) htailDel hbin_mem
      hbin_head hbout hoPre_mem).1 hdel
  rcases hclass with hopre_bin | hopre_bout
  · have hφbin : M.φ bin = bin := by
      simpa [hopre_bin] using hoPre_phi
    exact phi_ne_self_of_isSimpleGraph M hNT.simpleGraph bin hφbin
  · have hφ2 : M.φ (M.φ bin) = bin := by
      calc
        M.φ (M.φ bin) = M.φ bout := by rw [← hbout]
        _ = M.φ oPre := by rw [hopre_bout]
        _ = bin := hoPre_phi
    have hφ : M.φ bin ≠ bin :=
      phi_ne_self_of_isSimpleGraph M hNT.simpleGraph bin
    have hcard2 : (M.φ.cycleOf bin).support.card = 2 :=
      card_support_cycleOf_eq_two_of_apply_apply_eq_self M.φ hφ hφ2
    have hbin_face : M.dartFace bin = hNT.outerFace :=
      hNT.outerCycle.dartFace_of_mem_darts hbin_mem
    have hface2 : M.faceLen hNT.outerFace = 2 := by
      have hsupport := faceLen_dartFace_eq_card_support_cycleOf M hφ
      rw [hbin_face, hcard2] at hsupport
      exact hsupport
    have hlen2 : hNT.outerCycle.length = 2 :=
      hNT.outerCycle.faceLen_eq_length.symm.trans hface2
    have hge : 3 ≤ hNT.outerCycle.length := hNT.outer_len
    omega

/-- Every surviving old-outer dart reaches the predecessor `oPre` of the incoming
outer dart `bin` by a forward `M.φ`-run that stays outside the deleted star.  This
uses the previous classification of deleted old-outer darts and a first-hit
argument for `bin`, avoiding any global list equality for the rotated boundary
cycle. -/
lemma old_outer_survivor_run_to_exit {v0 : M.Vertex} {dDel bin bout oPre : D}
    (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbout : bout = M.φ bin)
    (hoPre_phi : M.φ oPre = bin)
    (x : {d : D // d ∉ M.deleteVertexSet dDel})
    (hxouter : M.dartFace x.1 = hNT.outerFace) :
    ∃ k : ℕ, (∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet dDel) ∧
      (M.φ ^ k) x.1 = oPre := by
  have hbin_face : M.dartFace bin = hNT.outerFace :=
    hNT.outerCycle.dartFace_of_mem_darts hbin_mem
  have hsame : M.φ.SameCycle x.1 bin := by
    exact Quotient.exact (show M.dartFace x.1 = M.dartFace bin by
      rw [hxouter, hbin_face])
  obtain ⟨n0, hn0⟩ := hsame.exists_nat_pow_eq
  let hhit : ∃ n : ℕ, (M.φ ^ n) x.1 = bin := ⟨n0, hn0⟩
  set n := Nat.find hhit with hn_def
  have hn : (M.φ ^ n) x.1 = bin := by
    rw [hn_def]
    exact Nat.find_spec hhit
  have hbin_deleted : bin ∈ M.deleteVertexSet dDel :=
    mem_deleteVertexSet_of_head (M := M) (v0 := v0) htailDel hbin_head
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    have hxbin : x.1 = bin := by simpa [hn0] using hn
    exact x.2 (hxbin ▸ hbin_deleted)
  have hface_iter_all : ∀ j : ℕ, M.dartFace ((M.φ ^ j) x.1) = hNT.outerFace := by
    intro j
    induction j with
    | zero => simpa using hxouter
    | succ j ih =>
        have hsucc : (M.φ ^ Nat.succ j) x.1 = M.φ ((M.φ ^ j) x.1) := by
          rw [Nat.succ_eq_add_one, pow_succ']; rfl
        rw [hsucc, dartFace_phi]
        exact ih
  set k := n - 1 with hkdef
  have hn_eq : n = k + 1 := by omega
  refine ⟨k, ?_, ?_⟩
  · intro j hj hdel
    have hface_iter : M.dartFace ((M.φ ^ j) x.1) = hNT.outerFace := hface_iter_all j
    have hmem_iter : (M.φ ^ j) x.1 ∈ hNT.outerCycle.darts :=
      (hNT.outerCycle.mem_darts_iff _).2 hface_iter
    have hclass :=
      (old_outer_deleted_iff_eq_bin_or_bout (hNT := hNT) htailDel hbin_mem
        hbin_head hbout hmem_iter).1 hdel
    rcases hclass with hhit_bin | hhit_bout
    · have hjlt : j < n := by omega
      exact (Nat.find_min (p := fun m => (M.φ ^ m) x.1 = bin)
        hhit hjlt) hhit_bin
    · cases j with
      | zero =>
          have hx_bout : x.1 = bout := by simpa using hhit_bout
          have hbout_mem : bout ∈ hNT.outerCycle.darts := by
            rw [hbout]
            exact hNT.outerCycle.phi_mem_darts hbin_mem
          have hbout_deleted : bout ∈ M.deleteVertexSet dDel :=
            (old_outer_deleted_iff_eq_bin_or_bout (hNT := hNT) htailDel hbin_mem
              hbin_head hbout hbout_mem).2 (Or.inr rfl)
          exact x.2 (hx_bout ▸ hbout_deleted)
      | succ j' =>
          have hprev : (M.φ ^ j') x.1 = bin := by
            have hsucc : (M.φ ^ Nat.succ j') x.1 = M.φ ((M.φ ^ j') x.1) := by
              rw [Nat.succ_eq_add_one, pow_succ']; rfl
            apply M.φ.injective
            rw [← hsucc, hhit_bout, hbout]
          have hjlt : j' < n := by omega
          exact (Nat.find_min (p := fun m => (M.φ ^ m) x.1 = bin)
            hhit hjlt) hprev
  · apply M.φ.injective
    have hsucc : (M.φ ^ (k + 1)) x.1 = M.φ ((M.φ ^ k) x.1) := by
      rw [pow_succ']; rfl
    rw [← hsucc, ← hn_eq, hn, hoPre_phi]

/-- Assemble `MergedOuterArcData` from the endpoint seam facts.  This is the
non-circular STAGE-A constructor: the old-outer survivor run and the Case-B jump
are proved above; the remaining inputs are exactly the endpoint alignments between
the old incoming boundary dart and the fan triangle edge where the seam actually
enters the fan chain. -/
def mergedOuterArcData_of_head_seam {v0 a b : M.Vertex}
    {dDel bin bout oPre : D}
    (r : {d : D // d ∉ M.deleteVertexSet dDel})
    (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    (hbin_tail : M.tail bin = a)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet dDel)
    (hoPre_phi : M.φ oPre = bin)
    (T : FanTriangle hNT v0 a b)
    (hr : r.1 = T.d1) :
    MergedOuterArcData M dDel r hNT.outerFace :=
  hNT.mergedOuterArcData_of_exit (v0 := v0) r htailDel
    ⟨oPre, hoPre_surv⟩
    (by
      rw [hNT.outerCycle.mem_darts_iff]
      rw [← hNT.outerCycle.dartFace_of_mem_darts hbin_mem, ← hoPre_phi, dartFace_phi])
    (by rw [hoPre_phi, hbin_head])
    (by rw [hoPre_phi, incoming_outer_exit_jumps_to_head_fan_edge hbin_head hbin_tail T, ← hr])
    (old_outer_survivor_run_to_exit (hNT := hNT) htailDel hbin_mem hbin_head hbout hoPre_phi)

/-- The same seam constructor specialized to a canonical edge of a boundary fan.
For a consecutive pair `(a,b)` in the fan path, the stored triangle has type
`FanTriangle hNT v0 b a`; hence the incoming old-outer dart must have tail `b`.
This is the actual-seam form used when the Case-B jump enters at the end of the
fan chain rather than at the head. -/
noncomputable def mergedOuterArcData_of_fan_pair_seam
    (fan : BoundaryVertexFan hNT v0) {dDel bin bout oPre : D}
    (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet dDel)
    (hoPre_phi : M.φ oPre = bin) :
    MergedOuterArcData M dDel
      ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
        ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
          (fan.incident_faces_exact.triangle_of_pair hp) htailDel⟩
      hNT.outerFace :=
  mergedOuterArcData_of_head_seam
    (r := ⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htailDel⟩)
    htailDel hbin_mem hbin_head hbin_tail hbout hoPre_surv hoPre_phi
    (fan.incident_faces_exact.triangle_of_pair hp) rfl

/-- The fan-pair seam data is attached to a canonical fan edge. -/
lemma fanPairSeamEdge_is_fan_edge
    (fan : BoundaryVertexFan hNT v0) {dDel : D} (htailDel : M.tail dDel = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path) :
    FanTriangleEdge fan
      (⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
        ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
          (fan.incident_faces_exact.triangle_of_pair hp) htailDel⟩ :
        {d : D // d ∉ M.deleteVertexSet dDel}) :=
  ⟨a, b, hp, rfl⟩

/-- STAGE A+B seam closure from the actual fan-edge package.  The old outer arc
may enter at any canonical fan edge; the fan-chain theorem transports that entry
edge to the whole merged orbit. -/
theorem deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
    (fan : BoundaryVertexFan hNT v0) (hchord : BoundaryChordless hNT.outerCycle)
    {dDel bin bout oPre : D} (htailDel : M.tail dDel = v0)
    (hbin_mem : bin ∈ hNT.outerCycle.darts)
    (hbin_head : M.head bin = v0)
    {a b : M.Vertex} (hp : (a, b) ∈ consecutivePairs fan.path)
    (hbin_tail : M.tail bin = b)
    (hbout : bout = M.φ bin)
    (hoPre_surv : oPre ∉ M.deleteVertexSet dDel)
    (hoPre_phi : M.φ oPre = bin) :
    DeleteVertexMergedFaceSingleOrbit M dDel :=
  deleteVertexMergedFaceSingleOrbit_of_fan_of_outerArc_edge fan hchord htailDel
    (⟨(fan.incident_faces_exact.triangle_of_pair hp).d1,
      ProofsInTheBook.ZinanCh35FanBackward.Conn.fanTriangle_edge_dart_survives
        (fan.incident_faces_exact.triangle_of_pair hp) htailDel⟩)
    (fanPairSeamEdge_is_fan_edge fan htailDel hp)
    (mergedOuterArcData_of_fan_pair_seam fan htailDel hbin_mem hbin_head hp hbin_tail
      hbout hoPre_surv hoPre_phi)

end ProofsInTheBook.ZinanCh35MergedArc

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35MergedArc.incoming_outer_exit_jumps_to_head_fan_edge
#print axioms ProofsInTheBook.ZinanCh35MergedArc.old_outer_deleted_iff_eq_bin_or_bout
#print axioms ProofsInTheBook.ZinanCh35MergedArc.incoming_outer_tail_eq_head_sigma_symm
#print axioms ProofsInTheBook.ZinanCh35MergedArc.old_outer_predecessor_survives
#print axioms ProofsInTheBook.ZinanCh35MergedArc.old_outer_survivor_run_to_exit
#print axioms ProofsInTheBook.ZinanCh35MergedArc.mergedOuterArcData_of_head_seam
#print axioms ProofsInTheBook.ZinanCh35MergedArc.mergedOuterArcData_of_fan_pair_seam
#print axioms ProofsInTheBook.ZinanCh35MergedArc.deleteVertexMergedFaceSingleOrbit_of_fan_pair_seam
