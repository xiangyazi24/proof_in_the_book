import ProofsInTheBook.ZinanCh35Gates

/-!
# The chord-cycle wrapper (Chapter 35 endgame)

`ZinanCh35Gates.lean` discharged the connectivity gates and exported
`NearTriangulation.separates_closed`, which consumes a *chord-cycle datum*: a
`SimplePrimalCycle` `C` whose edges are the chord `s(u,v)` plus boundary edges
(`hsub`), an index `i₀` whose two incident faces are the two chord-dart faces
(`hleft`, `hright`).  Every prior file *takes* this datum as a hypothesis; nobody
had **built** it from a bare `Chord` of the outer cycle.

This file builds it.  We package the datum as `ChordCycleData`, prove it always
exists (`chordCycleData_exists` / the constructor `chordCycleData`), and compose
with `separates_closed` to get `separates_of_chord`.

## The construction

Fix a chord `h : hNT.outerCycle.Chord u v` and let `c₀ := hNT.chordDart h` (edge
`s(u,v)`, some orientation).  Put `x := M.tail c₀`, `y := M.head c₀`; these are the
two chord endpoints (`{x, y} = {u, v}`), distinct boundary vertices, and `s(x, y)`
is **not** a boundary edge (it is the chord).

We build a **dart-level boundary arc** `A : DartArc … y x` from `y` to `x` along
the outer cycle, using the *cyclic* forward run of the boundary dart list from the
position of `y` to the position of `x`.  Because `s(x, y)` is not a boundary edge,
that run has length `≥ 2` (a length-`1` run would make `s(x, y)` a boundary edge).

Then `ofDartArc A c₀` (with `hc_tail : M.tail c₀ = x`, `hc_head : M.head c₀ = y`,
both `rfl`) is a `SimplePrimalCycle` whose index `0` dart is *exactly* `c₀`, so the
two `i₀ = 0` faces are *definitionally* the chord-dart faces — `hleft`/`hright` are
`rfl`.  `hsub` holds because every non-chord dart is an arc dart, hence lies on the
outer cycle, hence its edge is a boundary edge.

No orientation case-split is needed: the arc is built between `M.head c₀` and
`M.tail c₀` *as they are*, so `dart 0 = c₀` always.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}

/-! ## 1. A cyclic dart-level boundary arc

Given a boundary cycle `C` (vertices simple), a start position `p`, and a *cyclic*
run length `k` with `1 ≤ k ≤ C.darts.length`, the darts `C.darts[(p + j) % L]`
(`j < k`) form a `DartArc` from `M.tail (C.darts[p])` to `M.tail (C.darts[(p+k)%L])`.

This is the cyclic analogue of `DartArc.boundaryDartArc` (which only handles the
*non-wrapping* slice `p + k < L`); here the run may wrap past index `0`.  The
chaining is exactly `consecutive_vertex` evaluated at `(p + j) % L` (whose
`cyclicNext` is `(p + j + 1) % L`), so the wrap step is handled uniformly. -/
noncomputable def cyclicDartArc (C : BoundaryCycle M f) (hC : C.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < C.darts.length)
    (hp : p < C.darts.length) :
    DartArc M C (M.tail (C.darts[p]'hp))
      (M.tail (C.darts[(p + k) % C.darts.length]'(Nat.mod_lt _ (by omega)))) where
  len := k
  len_pos := hk
  arcDart j := C.darts[(p + j.1) % C.darts.length]'(Nat.mod_lt _ (by omega))
  boundary j := List.getElem_mem _
  chain j hj := by
    -- head (darts[(p+j)%L]) = tail (darts[((p+j)+1)%L]) = tail (darts[(p+(j+1))%L]).
    set L := C.darts.length with hL
    have hLpos : 0 < L := C.darts_length_pos
    have hpos : (p + (j : ℕ)) % L < L := Nat.mod_lt _ hLpos
    have hcv := C.consecutive_vertex ⟨(p + (j : ℕ)) % L, hpos⟩
    -- cyclicNext of ((p+j)%L) is (((p+j)%L)+1)%L = ((p+j)+1)%L = (p+(j+1))%L.
    have hcyc : (cyclicNext C.normalized.length_pos ⟨(p + (j : ℕ)) % L, hpos⟩ : Fin L)
        = ⟨(p + ((j : ℕ) + 1)) % L, Nat.mod_lt _ hLpos⟩ := by
      apply Fin.ext
      show ((p + (j : ℕ)) % L + 1) % L = (p + ((j : ℕ) + 1)) % L
      rw [Nat.mod_add_mod]
      congr 1
    rw [hcyc] at hcv
    -- Translate `.get` to `[…]` and conclude.
    show M.head (C.darts[(p + (j : ℕ)) % L]'_)
        = M.tail (C.darts[(p + ((j : ℕ) + 1)) % L]'_)
    rw [show (C.darts.get ⟨(p + (j : ℕ)) % L, hpos⟩) = C.darts[(p + (j : ℕ)) % L]'hpos from rfl,
      show (C.darts.get ⟨(p + ((j : ℕ) + 1)) % L, Nat.mod_lt _ hLpos⟩)
          = C.darts[(p + ((j : ℕ) + 1)) % L]'(Nat.mod_lt _ hLpos) from rfl] at hcv
    exact hcv.symm
  tail_first := by
    have hLpos : 0 < C.darts.length := C.darts_length_pos
    have heq : (p + (0 : ℕ)) % C.darts.length = p := by
      rw [Nat.add_zero, Nat.mod_eq_of_lt hp]
    show M.tail (C.darts[(p + (0 : ℕ)) % C.darts.length]'_) = M.tail (C.darts[p]'hp)
    simp only [heq]
  head_last := by
    set L := C.darts.length with hL
    have hLpos : 0 < L := C.darts_length_pos
    -- head (darts[(p+(k-1))%L]) = tail (darts[(p+k)%L]) via consecutive_vertex.
    have hpos : (p + (k - 1)) % L < L := Nat.mod_lt _ hLpos
    have hcv := C.consecutive_vertex ⟨(p + (k - 1)) % L, hpos⟩
    have hcyc : (cyclicNext C.normalized.length_pos ⟨(p + (k - 1)) % L, hpos⟩ : Fin L)
        = ⟨(p + k) % L, Nat.mod_lt _ hLpos⟩ := by
      apply Fin.ext
      show ((p + (k - 1)) % L + 1) % L = (p + k) % L
      rw [Nat.mod_add_mod]
      congr 1
      omega
    rw [hcyc] at hcv
    show M.head (C.darts[(p + ((k : ℕ) - 1)) % L]'_) = M.tail (C.darts[(p + k) % L]'_)
    rw [show (C.darts.get ⟨(p + (k - 1)) % L, hpos⟩) = C.darts[(p + (k - 1)) % L]'hpos from rfl,
      show (C.darts.get ⟨(p + k) % L, Nat.mod_lt _ hLpos⟩)
          = C.darts[(p + k) % L]'(Nat.mod_lt _ hLpos) from rfl] at hcv
    exact hcv.symm
  tail_nodup := by
    -- positions (p+i)%L (i < k ≤ L) are pairwise distinct, so darts and tails are.
    set L := C.darts.length with hL
    have hmap : (C.darts.map M.tail).Nodup := by
      simpa [BoundaryCycle.VertexNodup, C.vertices_eq] using hC
    intro i₁ i₂ htail
    have hi₁ : (i₁ : ℕ) < k := i₁.isLt
    have hi₂ : (i₂ : ℕ) < k := i₂.isLt
    have h1 : (p + (i₁ : ℕ)) % L < L := Nat.mod_lt _ C.darts_length_pos
    have h2 : (p + (i₂ : ℕ)) % L < L := Nat.mod_lt _ C.darts_length_pos
    have hdarts : C.darts[(p + (i₁ : ℕ)) % L]'h1 = C.darts[(p + (i₂ : ℕ)) % L]'h2 := by
      have hinj := List.inj_on_of_nodup_map hmap (List.getElem_mem h1) (List.getElem_mem h2)
      exact hinj htail
    have hpos_eq : (p + (i₁ : ℕ)) % L = (p + (i₂ : ℕ)) % L :=
      (C.normalized.nodup.getElem_inj_iff).mp hdarts
    -- both residues equal and both `< L` with `i < k ≤ L`: the `i`'s coincide.
    have hi₁L0 : (i₁ : ℕ) < L := lt_of_lt_of_le hi₁ (le_of_lt hkL)
    have hi₂L0 : (i₂ : ℕ) < L := lt_of_lt_of_le hi₂ (le_of_lt hkL)
    have hmodeq : Nat.ModEq L (p + (i₁ : ℕ)) (p + (i₂ : ℕ)) := hpos_eq
    have hcancel : Nat.ModEq L (i₁ : ℕ) (i₂ : ℕ) :=
      Nat.ModEq.add_left_cancel' p hmodeq
    have hi₁L : (i₁ : ℕ) % L = (i₁ : ℕ) := Nat.mod_eq_of_lt hi₁L0
    have hi₂L : (i₂ : ℕ) % L = (i₂ : ℕ) := Nat.mod_eq_of_lt hi₂L0
    apply Fin.ext
    have := hcancel
    rw [Nat.ModEq, hi₁L, hi₂L] at this
    exact this
  head_last_ne_tail := by
    set L := C.darts.length with hL
    have hmap : (C.darts.map M.tail).Nodup := by
      simpa [BoundaryCycle.VertexNodup, C.vertices_eq] using hC
    intro i htail
    -- v = tail darts[(p+k)%L]; tail darts[(p+i)%L] with i < k.  Positions distinct.
    have hi : (i : ℕ) < k := i.isLt
    have hposk : (p + k) % L < L := Nat.mod_lt _ C.darts_length_pos
    have hposi : (p + (i : ℕ)) % L < L := Nat.mod_lt _ C.darts_length_pos
    have hdarts : C.darts[(p + k) % L]'hposk = C.darts[(p + (i : ℕ)) % L]'hposi := by
      have hinj := List.inj_on_of_nodup_map hmap (List.getElem_mem hposk) (List.getElem_mem hposi)
      exact hinj htail
    have hpos_eq : (p + k) % L = (p + (i : ℕ)) % L :=
      (C.normalized.nodup.getElem_inj_iff).mp hdarts
    -- residues equal ⟹ k ≡ i [MOD L]; but i < k < L: contradiction.
    have hiltL : (i : ℕ) < L := lt_trans hi hkL
    have hmodeq : Nat.ModEq L (p + k) (p + (i : ℕ)) := hpos_eq
    have hcancel : Nat.ModEq L k (i : ℕ) := Nat.ModEq.add_left_cancel' p hmodeq
    have hkL' : k % L = k := Nat.mod_eq_of_lt hkL
    have hiL : (i : ℕ) % L = (i : ℕ) := Nat.mod_eq_of_lt hiltL
    rw [Nat.ModEq, hkL', hiL] at hcancel
    omega

@[simp] lemma cyclicDartArc_len (C : BoundaryCycle M f) (hC : C.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < C.darts.length) (hp : p < C.darts.length) :
    (cyclicDartArc C hC p k hk hkL hp).len = k := rfl

@[simp] lemma cyclicDartArc_arcDart (C : BoundaryCycle M f) (hC : C.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < C.darts.length) (hp : p < C.darts.length)
    (j : Fin k) :
    (cyclicDartArc C hC p k hk hkL hp).arcDart j
      = C.darts[(p + j.1) % C.darts.length]'(Nat.mod_lt _ (by omega)) := rfl

end BoundaryCycle

/-! ## 2. A boundary arc between two endpoints of a non-boundary edge

From two *distinct* boundary vertices `a, b` whose unoriented edge `s(a, b)` is not
a boundary edge, we build a `DartArc … a b` of length `≥ 2`.  The positions of `a`
and `b` on the cyclic dart list give a forward cyclic run; its length is `≥ 1` and,
were it `= 1`, the consecutive-vertex law would make `s(a, b)` a boundary edge. -/

namespace BoundaryCycle

variable {M : CombMap D} {f : M.Face}

/-- The position of a boundary vertex on the cyclic dart list (as the tail of a
listed dart), as a single existential over `Fin`. -/
lemma exists_pos_of_isBoundaryVertex (C : BoundaryCycle M f) {a : M.Vertex}
    (ha : C.IsBoundaryVertex a) :
    ∃ p : Fin C.darts.length, M.tail (C.darts[p.1]'p.2) = a := by
  have ha' : a ∈ C.darts.map M.tail := by
    simpa [BoundaryCycle.IsBoundaryVertex, C.vertices_eq] using ha
  rw [List.mem_iff_getElem] at ha'
  obtain ⟨p, hp, hget⟩ := ha'
  rw [List.length_map] at hp
  refine ⟨⟨p, hp⟩, ?_⟩
  rwa [List.getElem_map] at hget

/-- **The boundary arc of a non-boundary edge.**  From two distinct boundary
vertices `a, b` with `s(a, b)` not a boundary edge, the forward cyclic dart run
from `a` to `b` is a `DartArc … a b` of length `≥ 2`. -/
noncomputable def dartArcOfNonBoundaryEdge (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {a b : M.Vertex} (hab : a ≠ b) (ha : C.IsBoundaryVertex a) (hb : C.IsBoundaryVertex b)
    (hnbe : ¬ C.IsBoundaryEdge s(a, b)) :
    { A : DartArc M C a b // 2 ≤ A.len } := by
  classical
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  -- positions of a, b (extracted as data via choice).
  set paF := (C.exists_pos_of_isBoundaryVertex ha).choose with hpaF
  have hpaeq0 := (C.exists_pos_of_isBoundaryVertex ha).choose_spec
  set pbF := (C.exists_pos_of_isBoundaryVertex hb).choose with hpbF
  have hpbeq0 := (C.exists_pos_of_isBoundaryVertex hb).choose_spec
  set pa := paF.1 with hpaval
  set pb := pbF.1 with hpbval
  have hpa : pa < C.darts.length := paF.2
  have hpb : pb < C.darts.length := pbF.2
  have hpaeq : M.tail (C.darts[pa]'hpa) = a := hpaeq0
  have hpbeq : M.tail (C.darts[pb]'hpb) = b := hpbeq0
  -- forward cyclic distance from pa to pb.
  set k := (pb + L - pa) % L with hk
  have hkL : k < L := Nat.mod_lt _ hLpos
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · -- k = 0 ⟹ L ∣ (pb+L-pa) ⟹ (since 0 < pb+L-pa < 2L) pb = pa ⟹ a = b.
      exfalso
      have hmod0 : (pb + L - pa) % L = 0 := by rw [← hk]; exact h0
      have hdvd : L ∣ (pb + L - pa) := Nat.dvd_of_mod_eq_zero hmod0
      obtain ⟨m, hm⟩ := hdvd
      have hpapb : pa = pb := by
        have hb1 : pb + L - pa < 2 * L := by omega
        have hb2 : 0 < pb + L - pa := by omega
        -- L*m = pb+L-pa, 0 < L*m < 2L ⟹ m = 1 ⟹ pb+L-pa = L ⟹ pa = pb.
        have hm1 : m = 1 := by nlinarith [hm, hb1, hb2, hLpos]
        rw [hm1, Nat.mul_one] at hm; omega
      apply hab
      have hgeteq : C.darts.get ⟨pa, hpa⟩ = C.darts.get ⟨pb, hpb⟩ := by
        congr 1; exact Fin.ext hpapb
      calc a = M.tail (C.darts[pa]'hpa) := hpaeq.symm
        _ = M.tail (C.darts.get ⟨pa, hpa⟩) := rfl
        _ = M.tail (C.darts.get ⟨pb, hpb⟩) := by rw [hgeteq]
        _ = M.tail (C.darts[pb]'hpb) := rfl
        _ = b := hpbeq
    · exact h0
  -- endpoints: tail darts[pa] = a, tail darts[(pa+k)%L] = b.
  have hend : (pa + k) % L = pb := by
    rw [hk]
    -- (pa + (pb+L-pa)%L) % L = (pa + (pb+L-pa)) % L = (pb+L) % L = pb.
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl L)]
    rw [← Nat.add_mod]
    have h1 : pa + (pb + L - pa) = pb + L := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hpb]
  -- length k ≥ 2: if k = 1 then darts[pa] has head b, so s(a,b) is a boundary edge.
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hlt' : k < 2 := Nat.lt_of_not_le hlt
    have hk1 : k = 1 := by omega
    -- tail darts[(pa+1)%L] = head darts[pa] by consecutive_vertex; (pa+1)%L = (pa+k)%L = pb.
    have hcv := C.consecutive_vertex ⟨pa, hpa⟩
    have hcyc : (cyclicNext C.normalized.length_pos ⟨pa, hpa⟩ : Fin L)
        = ⟨pb, hpb⟩ := by
      apply Fin.ext
      show (pa + 1) % L = pb
      have hkk : (pa + k) % L = pb := hend
      rw [hk1] at hkk; exact hkk
    rw [hcyc] at hcv
    -- hcv : tail darts[pb] = head darts[pa].  So s(a,b) = dartEdge darts[pa] ∈ edges.
    apply hnbe
    show s(a, b) ∈ C.edges
    rw [C.edges_eq]
    have hge : C.darts.get ⟨pa, hpa⟩ = C.darts[pa]'hpa := rfl
    have hgb : C.darts.get ⟨pb, hpb⟩ = C.darts[pb]'hpb := rfl
    rw [hge, hgb] at hcv
    -- M.dartEdge (darts[pa]) = s(tail darts[pa], head darts[pa]) = s(a, b).
    have hedge2 : M.dartEdge (C.darts[pa]'hpa) = s(a, b) := by
      show s(M.tail (C.darts[pa]'hpa), M.head (C.darts[pa]'hpa)) = s(a, b)
      rw [hpaeq, ← hcv, hpbeq]
    rw [← hedge2]
    exact List.mem_map_of_mem (List.getElem_mem hpa)
  -- The arc's head endpoint is `tail darts[(pa+k)%L] = tail darts[pb] = b`.
  have hbend : M.tail (C.darts[(pa + k) % C.darts.length]'(Nat.mod_lt _ hLpos)) = b := by
    have hcongr : C.darts.get ⟨(pa + k) % C.darts.length, Nat.mod_lt _ hLpos⟩
        = C.darts.get ⟨pb, hpb⟩ := by
      congr 1
      apply Fin.ext
      show (pa + k) % C.darts.length = pb
      simpa [hL] using hend
    have h1 : C.darts[(pa + k) % C.darts.length]'(Nat.mod_lt _ hLpos)
        = C.darts.get ⟨(pa + k) % C.darts.length, Nat.mod_lt _ hLpos⟩ := rfl
    have h2 : C.darts[pb]'hpb = C.darts.get ⟨pb, hpb⟩ := rfl
    rw [h1, hcongr, ← h2]; exact hpbeq
  -- Rewrite the goal's endpoints `a`, `b` back to the tail expressions and bundle.
  rw [show a = M.tail (C.darts[pa]'hpa) from hpaeq.symm,
      show b = M.tail (C.darts[(pa + k) % C.darts.length]'(Nat.mod_lt _ hLpos)) from hbend.symm]
  exact ⟨C.cyclicDartArc hC pa k hkpos hkL hpa, hk2⟩

end BoundaryCycle

/-! ## 3. The `ChordCycleData` structure and its existence -/

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle

/-- **Chord-cycle datum.**  The exact bundle `separates_closed` consumes: a simple
primal cycle made of the chord edge `s(u,v)` plus a boundary arc (`hsub`), with an
index `i₀` whose two incident faces are the two chord-dart faces. -/
structure ChordCycleData {u v : M.Vertex} (h : hNT.outerCycle.Chord u v) where
  /-- The chord ∪ arc simple primal cycle. -/
  C : CombMap.SimplePrimalCycle M
  /-- Every cycle edge is the chord or a boundary edge. -/
  hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e
  /-- The chord index. -/
  i₀ : Fin C.len
  /-- The left face at `i₀` is the chord-dart face. -/
  hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h)
  /-- The right face at `i₀` is the reverse-chord-dart face. -/
  hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h))

variable {u v : M.Vertex}

/-- **The chord-cycle datum exists.**  Built from the boundary arc between the two
endpoints of the chord dart `c₀ := hNT.chordDart h`, with `c₀` placed at index `0`
of `ofDartArc`.  Then `dart 0 = c₀`, so the two `i₀ = 0` faces are *definitionally*
the chord-dart faces. -/
noncomputable def chordCycleData (h : hNT.outerCycle.Chord u v) :
    hNT.ChordCycleData h := by
  classical
  -- The chord dart and its (boundary) endpoints.  We keep `M.tail c₀`/`M.head c₀`
  -- inline (no `set`) to avoid reverting let-bound variables in rewrites.
  set c₀ := hNT.chordDart h with hc₀
  -- c₀ has edge s(u, v); its endpoints are the two boundary chord endpoints.
  have hedge : M.dartEdge c₀ = s(u, v) := hNT.chordDart_edge h
  have hxy_edge : s(M.tail c₀, M.head c₀) = s(u, v) := hedge
  -- the endpoints are distinct and both boundary vertices.
  have hxy_ne : M.tail c₀ ≠ M.head c₀ := by
    intro hcontra
    have h1 : s(M.head c₀, M.head c₀) = s(u, v) := hcontra ▸ hxy_edge
    have huv : u = v := by
      rcases Sym2.eq_iff.mp h1.symm with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · rw [hl, hr]
      · rw [hl, hr]
    exact h.endpoints_ne huv
  have hx_bv : hNT.outerCycle.IsBoundaryVertex (M.tail c₀) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨hxu, _⟩ | ⟨hxv, _⟩
    · rw [hxu]; exact h.left_boundary
    · rw [hxv]; exact h.right_boundary
  have hy_bv : hNT.outerCycle.IsBoundaryVertex (M.head c₀) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨_, hyv⟩ | ⟨_, hyu⟩
    · rw [hyv]; exact h.right_boundary
    · rw [hyu]; exact h.left_boundary
  -- s(head, tail) = s(tail, head) = s(u, v) is not a boundary edge.
  have hnbe : ¬ hNT.outerCycle.IsBoundaryEdge s(M.head c₀, M.tail c₀) := by
    rw [show (s(M.head c₀, M.tail c₀) : Sym2 M.Vertex) = s(M.tail c₀, M.head c₀) from Sym2.eq_swap,
      hxy_edge]
    exact h.not_boundary_edge
  -- Build the boundary arc from `head c₀` to `tail c₀` (so c₀ : tail→...→head closes it).
  obtain ⟨A, hAlen⟩ := hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple
    (Ne.symm hxy_ne) hy_bv hx_bv hnbe
  -- The chord ∪ arc cycle: dart 0 = c₀.  ofDartArc needs tail c₀ = (arc's `v`-end),
  -- head c₀ = (arc's `u`-end); the arc `A : DartArc … (head c₀) (tail c₀)` matches.
  have hc_tail : M.tail c₀ = M.tail c₀ := rfl
  have hc_head : M.head c₀ = M.head c₀ := rfl
  -- index 0 (the chord dart) of the chord∪arc cycle.  `dart 0 = c₀` definitionally.
  have hi0 : (0 : ℕ) < (SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).len :=
    (SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).len_pos
  have hdart0 : (SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).dart ⟨0, hi0⟩ = c₀ := by
    show SimplePrimalCycle.chordArcDart A c₀ ⟨0, hi0⟩ = c₀
    exact SimplePrimalCycle.chordArcDart_zero A c₀
  refine
    { C := SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head
      hsub := ?_
      i₀ := ⟨0, hi0⟩
      hleft := ?_
      hright := ?_ }
  · -- hsub: every cycle edge is the chord or a boundary edge.
    intro e he
    rw [SimplePrimalCycle.mem_edgeSet_iff] at he
    obtain ⟨i, hi⟩ := he
    rw [hi]
    -- edge i = dartEdge (dart i); dart i is either c₀ (i = 0) or an arc dart.
    have hedge_i : (SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).edge i
        = M.dartEdge ((SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).dart i) := rfl
    rw [hedge_i, SimplePrimalCycle.ofDartArc_dart]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · -- chord edge.
      left
      rw [SimplePrimalCycle.chordArcDart_zero]
      exact hedge
    · -- arc dart: lies on the outer cycle, so its edge is a boundary edge.
      right
      rw [SimplePrimalCycle.chordArcDart_succ]
      show M.dartEdge (A.arcDart i') ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq]
      exact List.mem_map_of_mem (A.boundary i')
  · -- hleft: faceLeft 0 = dartFace (dart 0) = dartFace c₀ = dartFace (chordDart h).
    show M.dartFace ((SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).dart ⟨0, hi0⟩)
        = M.dartFace (hNT.chordDart h)
    rw [hdart0]
  · -- hright: faceRight 0 = dartFace (α (dart 0)) = dartFace (α c₀) = dartFace (α (chordDart h)).
    show M.dartFace (M.α ((SimplePrimalCycle.ofDartArc A c₀ hAlen hc_tail hc_head).dart ⟨0, hi0⟩))
        = M.dartFace (M.α (hNT.chordDart h))
    rw [hdart0]

/-- **The chord-cycle datum exists** (`Nonempty` form). -/
theorem chordCycleData_exists (h : hNT.outerCycle.Chord u v) :
    Nonempty (hNT.ChordCycleData h) :=
  ⟨hNT.chordCycleData h⟩

/-- **The chord separates, from a chord-cycle datum.**  Composes `ChordCycleData`
with `separates_closed` (the connectivity-gate-discharged separation). -/
theorem separates_of_chord (data : hNT.ChordSplitData u v)
    (cc : hNT.ChordCycleData data.chord) : data.Separates :=
  hNT.separates_closed data cc.C cc.hsub cc.i₀ cc.hleft cc.hright

/-- **The chord separates, unconditionally on the chord-cycle datum** (built
internally). -/
theorem separates_of_chordSplitData (data : hNT.ChordSplitData u v) :
    data.Separates :=
  hNT.separates_of_chord data (hNT.chordCycleData data.chord)

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.chordCycleData
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.chordCycleData_exists
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.separates_of_chord
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.separates_of_chordSplitData
