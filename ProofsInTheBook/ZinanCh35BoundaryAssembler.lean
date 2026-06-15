import ProofsInTheBook.ZinanCh35Aligned
import ProofsInTheBook.PlanarMapDeletedBoundary

/-!
# Chapter 35: the genus-0 boundary-cycle foundation (R10 §3/§4/§5)

This file builds the two *reusable* genus-0 boundary-cycle pieces that the R10
handoff (`HANDOFF/ch35-boundaryCycle-genus0-R10.md`) isolated as the shared
foundation for **both** the chord-side `ContiguousInterval` and the chordless
`DeletedOuterBoundary`:

* **Piece 1** — `arcSplit_of_nodup_nonBoundaryEdge`: from a `BoundaryCycle`'s
  vertex list being `Nodup` (simple) — i.e. `VertexNodup` — produce a
  `BoundaryArcSplit` for any two distinct boundary vertices whose unoriented pair
  `s(u, v)` is **not** a boundary edge.  This is *pure list combinatorics*: split
  the simple cyclic dart list at the two endpoint positions into the two
  complementary cyclic runs, both of length `≥ 2`.  It reuses the proven
  `mod_cover` modular covering, `cyclicDartArc`, and `bpOfDartArc` machinery; the
  only `Chord`-specific input the existing `normalizedArcSplit` used was
  `not_boundary_edge` (adjacency `adj` is never touched), so the construction
  drops the adjacency requirement entirely.

* **Piece 2** — `nearTriangulation_of_explicit_boundary_classification`: the
  shared assembler.  Given a simple sphere map `K`, an outer face with a root dart
  whose `φ`-orbit tail list is simple and of length `≥ 3`, the universal
  arc-splitting certificate `arcSplit`, and the inner-face triangularity, build the
  full `NearTriangulation K` via `boundaryCycleOfFace` + the `NearTriangulation`
  constructor.

## The faithfulness boundary (R10 §4, verified here as a theorem)

R10 §4 hoped Piece 1 would discharge the **entire** `arcSplit` field of
`BoundaryCycle` (which is universally quantified over *all* distinct boundary
vertices) from `Nodup` alone.  It does **not**, and cannot: for a pair `u, v`
whose `s(u, v)` *is* a boundary edge (consecutive on the cycle), the
`BoundaryArcSplit` fields `path₁_internal_iff_proper`/`path₂_internal_iff_proper`
force *both* arcs to have **no** internal vertex, while
`boundary_vertices_covered` forces every boundary vertex to lie on one of the two
arcs.  On a cycle of length `≥ 3` there is a third vertex, which must then be an
internal vertex of one arc — a contradiction.  We record this obstruction as the
theorem `boundaryArcSplit_consecutive_unsatisfiable`: the universal `arcSplit`
field is genuinely *data* (a Jordan-curve fact), not a `Nodup` consequence —
exactly as `DeletedOuterBoundary.ofMergedFace`, `side₁OuterTraceData_canonical`,
and `NearTriangulation.outerCycle` already treat it.  Hence Piece 2's assembler
takes `arcSplit` as an input (the genuine reusable interface), and Piece 1
services precisely the non-boundary-edge sub-case — which is all that any
downstream consumer (`two_arcs`, `two_arcs_internally_nonempty_of_chord`) ever
invokes.

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35BoundaryAssembler

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.ZinanCh35Aligned

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}

/-! ## 1. Piece 1 — the arc-split from `Nodup` for a non-boundary-edge pair

We mirror the proven `normalizedRuns`/`normalizedArcSplit` construction of
`ZinanCh35Aligned`, but on a *bare* `BoundaryCycle C` with `C.VertexNodup` and the
four facts `u ≠ v`, `u, v ∈ C.vertices`, `s(u, v) ∉ C.edges`.  The only piece the
chord version derived from the `Chord` structure is the not-a-boundary-edge fact;
adjacency is never used. -/

namespace BoundaryCycle

variable {f : M.Face}

/-- **No `1`-step between the two endpoint positions** (the non-boundary-edge
analogue of `not_consecutive_of_chord`).  If `s(u, v)` is not a boundary edge then
the positions `p` (tail `u`) and `q` (tail `v`) cannot be cyclic-consecutive. -/
lemma not_consecutive_of_nonBoundaryEdge (C : BoundaryCycle M f) {u v : M.Vertex}
    (hnbe : ¬ C.IsBoundaryEdge s(u, v)) {p q : ℕ}
    (hp : p < C.darts.length) (hq : q < C.darts.length)
    (htu : M.tail (C.darts[p]'hp) = u)
    (htv : M.tail (C.darts[q]'hq) = v)
    (hadj : (p + 1) % C.darts.length = q) : False := by
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  have hcv := C.consecutive_vertex ⟨p, hp⟩
  have hcyc : (cyclicNext C.normalized.length_pos ⟨p, hp⟩ : Fin L) = ⟨q, hq⟩ := by
    apply Fin.ext; show (p + 1) % L = q; exact hadj
  rw [hcyc] at hcv
  have hhead : M.head (C.darts[p]'hp) = v := by
    rw [show (C.darts.get ⟨q, hq⟩) = C.darts[q]'hq from rfl,
        show (C.darts.get ⟨p, hp⟩) = C.darts[p]'hp from rfl] at hcv
    rw [← hcv, htv]
  apply hnbe
  show s(u, v) ∈ C.edges
  rw [C.edges_eq, show (s(u, v) : Sym2 M.Vertex) = M.dartEdge (C.darts[p]'hp) from by
    show s(u, v) = s(M.tail _, M.head _); rw [htu, hhead]]
  exact List.mem_map_of_mem (List.getElem_mem hp)

/-- The two complementary boundary runs for a non-boundary-edge pair `u, v`, with
their tail-covering and tail-disjointness of `C.vertices` — the chord-free
analogue of `NormalizedRuns`. -/
structure NonEdgeRuns (C : BoundaryCycle M f) (hC : C.VertexNodup) {u v : M.Vertex}
    (hne : u ≠ v) (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v)
    (hnbe : ¬ C.IsBoundaryEdge s(u, v)) where
  /-- The `u → v` boundary run. -/
  arcUV : DartArc M C u v
  /-- The `v → u` boundary run. -/
  arcVU : DartArc M C v u
  /-- Both runs have length `≥ 2`. -/
  lenUV : 2 ≤ arcUV.len
  lenVU : 2 ≤ arcVU.len
  /-- Every boundary vertex is a tail of one of the two runs, or an endpoint. -/
  covering : ∀ {w : M.Vertex}, C.IsBoundaryVertex w →
    (∃ i, M.tail (arcUV.arcDart i) = w) ∨ (∃ i, M.tail (arcVU.arcDart i) = w) ∨ w = u ∨ w = v
  /-- A vertex that is a tail of *both* runs is an endpoint. -/
  disjoint : ∀ {w : M.Vertex}, (∃ i, M.tail (arcUV.arcDart i) = w) →
    (∃ i, M.tail (arcVU.arcDart i) = w) → w = u ∨ w = v

/-- **Build the complementary runs from the non-boundary-edge data.**  Mirrors
`ZinanCh35Aligned.normalizedRuns`, with `not_consecutive_of_chord` replaced by
`not_consecutive_of_nonBoundaryEdge` and `Chord` fields replaced by the four bare
facts. -/
noncomputable def nonEdgeRuns (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {u v : M.Vertex} (hne : u ≠ v) (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v)
    (hnbe : ¬ C.IsBoundaryEdge s(u, v)) : NonEdgeRuns C hC hne hu hv hnbe := by
  classical
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  -- positions of u, v
  set puF := (C.exists_pos_of_isBoundaryVertex hu).choose with hpuF
  have eu0 := (C.exists_pos_of_isBoundaryVertex hu).choose_spec
  set pvF := (C.exists_pos_of_isBoundaryVertex hv).choose with hpvF
  have ev0 := (C.exists_pos_of_isBoundaryVertex hv).choose_spec
  set pu := puF.1 with hpuval
  set pv := pvF.1 with hpvval
  have hpu : pu < L := puF.2
  have hpv : pv < L := pvF.2
  have eu : M.tail (C.darts[pu]'hpu) = u := eu0
  have ev : M.tail (C.darts[pv]'hpv) = v := ev0
  have hpune : pu ≠ pv := by
    intro hpe; apply hne
    rw [← eu, ← ev]
    have : C.darts[pu]'hpu = C.darts[pv]'hpv := getElem_congr rfl hpe hpu
    rw [this]
  -- run lengths
  set kf := (pv + L - pu) % L with hkf
  set kb := (pu + L - pv) % L with hkb
  obtain ⟨hkf1, hkb1, hsum, hpfkf, hcov⟩ :=
    ZinanCh35Aligned.mod_cover L pu pv hLpos hpu hpv hpune kf kb hkf hkb
  obtain ⟨_, _, _, hpvkb, _⟩ :=
    ZinanCh35Aligned.mod_cover L pv pu hLpos hpv hpu (Ne.symm hpune) kb kf hkb hkf
  have hkfL : kf < L := by rw [hkf]; exact Nat.mod_lt _ hLpos
  have hkbL : kb < L := by rw [hkb]; exact Nat.mod_lt _ hLpos
  -- kf ≥ 2
  have hkf2 : 2 ≤ kf := by
    rcases Nat.lt_or_ge kf 2 with hlt | hge
    · exfalso
      have hkf1' : kf = 1 := by omega
      apply not_consecutive_of_nonBoundaryEdge C hnbe hpu hpv eu ev
      rw [show (pu + 1) % L = (pu + kf) % L from by rw [hkf1'], hpfkf]
    · exact hge
  have hkb2 : 2 ≤ kb := by
    rcases Nat.lt_or_ge kb 2 with hlt | hge
    · exfalso
      have hkb1' : kb = 1 := by omega
      have hnbe' : ¬ C.IsBoundaryEdge s(v, u) := by rw [Sym2.eq_swap]; exact hnbe
      exact not_consecutive_of_nonBoundaryEdge C hnbe' hpv hpu ev eu
        (by rw [show (pv + 1) % L = (pv + kb) % L from by rw [hkb1'], hpvkb])
    · exact hge
  -- the two raw runs
  set AUV := C.cyclicDartArc hC pu kf hkf1 hkfL hpu with hAUV
  set AVU := C.cyclicDartArc hC pv kb hkb1 hkbL hpv with hAVU
  -- endpoint equalities for casting
  have euv2 : M.tail (C.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega))) = v := by
    have : C.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega)) = C.darts[pv]'hpv := by congr 1
    rw [this]; exact ev
  have evu2 : M.tail (C.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega))) = u := by
    have : C.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega)) = C.darts[pu]'hpu := by congr 1
    rw [this]; exact eu
  -- tail characterizations of the casted runs
  have htailUV : ∀ i : Fin (daCast AUV eu euv2).len,
      M.tail ((daCast AUV eu euv2).arcDart i)
        = M.tail (C.darts[(pu + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCast_cyclic_tail C hC pu kf hkf1 hkfL hpu eu euv2 i
  have htailVU : ∀ i : Fin (daCast AVU ev evu2).len,
      M.tail ((daCast AVU ev evu2).arcDart i)
        = M.tail (C.darts[(pv + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCast_cyclic_tail C hC pv kb hkb1 hkbL hpv ev evu2 i
  have htailUV_fwd : ∀ j : ℕ, (hj : j < kf) →
      ∃ i : Fin (daCast AUV eu euv2).len,
        M.tail ((daCast AUV eu euv2).arcDart i)
          = M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCast AUV eu euv2).len := by rw [daCast_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailUV ⟨j, hjlen⟩⟩
  have htailVU_fwd : ∀ j : ℕ, (hj : j < kb) →
      ∃ i : Fin (daCast AVU ev evu2).len,
        M.tail ((daCast AVU ev evu2).arcDart i)
          = M.tail (C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCast AVU ev evu2).len := by rw [daCast_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailVU ⟨j, hjlen⟩⟩
  have htailUV_bwd : ∀ i : Fin (daCast AUV eu euv2).len,
      ∃ j : ℕ, j < kf ∧
        M.tail ((daCast AUV eu euv2).arcDart i)
          = M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kf := lt_of_lt_of_eq i.2 (daCast_len AUV eu euv2)
    exact ⟨i.1, hi, htailUV i⟩
  have htailVU_bwd : ∀ i : Fin (daCast AVU ev evu2).len,
      ∃ j : ℕ, j < kb ∧
        M.tail ((daCast AVU ev evu2).arcDart i)
          = M.tail (C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kb := lt_of_lt_of_eq i.2 (daCast_len AVU ev evu2)
    exact ⟨i.1, hi, htailVU i⟩
  refine
    { arcUV := daCast AUV eu euv2
      arcVU := daCast AVU ev evu2
      lenUV := ?_
      lenVU := ?_
      covering := ?_
      disjoint := ?_ }
  · rw [daCast_len]; exact hkf2
  · rw [daCast_len]; exact hkb2
  · -- covering
    intro w hw
    obtain ⟨q, hqt⟩ := C.exists_pos_of_isBoundaryVertex hw
    rcases hcov q.1 q.2 with ⟨j, hj, hjq⟩ | ⟨j, hj, hjq⟩
    · left
      obtain ⟨i, hi⟩ := htailUV_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) = C.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
    · right; left
      obtain ⟨i, hi⟩ := htailVU_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega)) = C.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
  · -- disjoint
    rintro w ⟨i, hiw⟩ ⟨i', hi'w⟩
    obtain ⟨j, hj, hjeq⟩ := htailUV_bwd i
    obtain ⟨j', hj', hj'eq⟩ := htailVU_bwd i'
    have heq : M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)))
        = M.tail (C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega))) := by
      rw [← hjeq, ← hj'eq, hiw, hi'w]
    have hmap : (C.darts.map M.tail).Nodup := by
      have := hC
      rwa [BoundaryCycle.VertexNodup, C.vertices_eq] at this
    have hposeq : (pu + j) % L = (pv + j') % L := by
      have hmem1 : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) ∈ C.darts :=
        List.getElem_mem _
      have hmem2 : C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) ∈ C.darts :=
        List.getElem_mem _
      have hdarts : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))
          = C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) :=
        List.inj_on_of_nodup_map hmap hmem1 hmem2 heq
      exact (C.normalized.nodup.getElem_inj_iff).mp hdarts
    by_cases hj0 : j = 0
    · left
      rw [← hiw, hjeq, hj0]
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hpu]
      exact eu
    · by_cases hj'0 : j' = 0
      · right
        rw [← hi'w, hj'eq, hj'0]
        simp only [Nat.add_zero, Nat.mod_eq_of_lt hpv]
        exact ev
      · exfalso
        have hpvmod : pv % L = (pu + kf) % L := by rw [hpfkf, Nat.mod_eq_of_lt hpv]
        have h2 : Nat.ModEq L pv (pu + kf) := by
          show pv % L = (pu + kf) % L; exact hpvmod
        have hcong : Nat.ModEq L (pu + j) (pu + (kf + j')) := by
          have h1 : Nat.ModEq L (pu + j) (pv + j') := hposeq
          have h3 : Nat.ModEq L (pv + j') (pu + kf + j') := h2.add_right j'
          have h4 : Nat.ModEq L (pu + j) (pu + kf + j') := h1.trans h3
          rwa [show pu + kf + j' = pu + (kf + j') from by ring] at h4
        have hcong' : Nat.ModEq L j (kf + j') := Nat.ModEq.add_left_cancel' pu hcong
        have hjlt : j < L := by omega
        have hkfj' : kf + j' < L := by omega
        have : j = kf + j' := by
          have hj1 : j % L = j := Nat.mod_eq_of_lt hjlt
          have hj2 : (kf + j') % L = kf + j' := Nat.mod_eq_of_lt hkfj'
          rw [Nat.ModEq, hj1, hj2] at hcong'; exact hcong'
        omega

/-- **Piece 1 — the arc-split from `Nodup` for a non-boundary-edge pair.**
From a boundary cycle whose vertex list is simple (`VertexNodup`) and two distinct
boundary vertices `u, v` whose pair is not a boundary edge, the two complementary
cyclic runs assemble a `BoundaryArcSplit M C.vertices C.edges u v`.  Pure list
combinatorics — no Jordan/Schoenflies data. -/
noncomputable def arcSplit_of_nodup_nonBoundaryEdge (C : BoundaryCycle M f)
    (hC : C.VertexNodup) {u v : M.Vertex} (hne : u ≠ v)
    (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v)
    (hnbe : ¬ C.IsBoundaryEdge s(u, v)) :
    BoundaryArcSplit M C.vertices C.edges u v :=
  let R := nonEdgeRuns C hC hne hu hv hnbe
  { path₁ := bpOfDartArc R.arcUV
    path₂ := bpOfDartArc R.arcVU
    path₁_boundary_vertices := fun {w} hw =>
      bpOfDartArc_boundary_vertices R.arcUV hv hw
    path₂_boundary_vertices := fun {w} hw =>
      bpOfDartArc_boundary_vertices R.arcVU hu hw
    boundary_vertices_covered := by
      intro w
      constructor
      · intro hw
        rcases R.covering hw with ⟨i, hi⟩ | ⟨i, hi⟩ | hwu | hwv
        · left
          rw [bpOfDartArc_vertices, List.mem_append]
          refine Or.inl ?_
          rw [← hi]
          show M.tail (R.arcUV.arcDart i) ∈ R.arcUV.dartList.map M.tail
          exact List.mem_map_of_mem (by
            show R.arcUV.arcDart i ∈ R.arcUV.dartList
            rw [DartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange i))
        · right
          rw [bpOfDartArc_vertices, List.mem_append]
          refine Or.inl ?_
          rw [← hi]
          show M.tail (R.arcVU.arcDart i) ∈ R.arcVU.dartList.map M.tail
          exact List.mem_map_of_mem (by
            show R.arcVU.arcDart i ∈ R.arcVU.dartList
            rw [DartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange i))
        · left
          rw [bpOfDartArc_vertices, List.mem_append]
          refine Or.inl ?_
          have hu_tail : M.tail (R.arcUV.arcDart R.arcUV.firstIdx) = w :=
            R.arcUV.tail_first.trans hwu.symm
          have hmem : M.tail (R.arcUV.arcDart R.arcUV.firstIdx) ∈ R.arcUV.dartList.map M.tail :=
            List.mem_map_of_mem (by
              rw [DartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange _))
          exact hu_tail ▸ hmem
        · left
          rw [bpOfDartArc_vertices, List.mem_append]
          exact Or.inr (by rw [hwv]; exact List.mem_singleton_self _)
      · intro hw
        rcases hw with hw | hw
        · exact bpOfDartArc_boundary_vertices R.arcUV hv hw
        · exact bpOfDartArc_boundary_vertices R.arcVU hu hw
    internally_disjoint := by
      intro w hw1 hw2
      obtain ⟨i, hi⟩ := bpOfDartArc_internal_tail R.arcUV hw1
      obtain ⟨i', hi'⟩ := bpOfDartArc_internal_tail R.arcVU hw2
      have hwuv : w = u ∨ w = v := R.disjoint ⟨i, hi⟩ ⟨i', hi'⟩
      have hwu : w ≠ u := (bpOfDartArc R.arcUV).internalVertex_ne_start hw1
      have hwv : w ≠ v := (bpOfDartArc R.arcUV).internalVertex_ne_end hw1
      rcases hwuv with h' | h'
      · exact hwu h'
      · exact hwv h'
    path₁_internal_iff_proper := by
      constructor
      · intro _; exact hnbe
      · intro _; exact bpOfDartArc_hasInternal R.arcUV R.lenUV
    path₂_internal_iff_proper := by
      constructor
      · intro _; exact hnbe
      · intro _; exact bpOfDartArc_hasInternal R.arcVU R.lenVU }

end BoundaryCycle

/-! ## 2. The faithfulness obstruction (R10 §4)

The universal `arcSplit` field of `BoundaryCycle` is *not* a `Nodup` consequence:
for a consecutive pair on a cycle of length `≥ 3` it is unsatisfiable. -/

/-- A non-endpoint member of a path's vertex list is an internal vertex.  If `w` is
in `P.vertices`, `w ≠ a` (the head), and `w ≠ b` (the last), then
`w ∈ P.internalVertices = P.vertices.tail.dropLast`. -/
lemma mem_internalVertices_of_ne_endpoints {a b : M.Vertex} (P : BoundaryPath M a b)
    {w : M.Vertex} (hw : w ∈ P.vertices) (hwa : w ≠ a) (hwb : w ≠ b) :
    w ∈ P.internalVertices := by
  show w ∈ P.vertices.tail.dropLast
  have hhead : P.vertices.head? = some a := P.starts_at
  have hlast : P.vertices.getLast? = some b := P.ends_at
  rcases List.eq_nil_or_concat P.vertices with hnil | ⟨ini, lst, hcat⟩
  · rw [hnil] at hw; simp at hw
  · rw [hcat] at hhead hlast hw ⊢
    simp only [List.concat_eq_append] at hhead hlast hw ⊢
    have hlstb : lst = b := by
      rw [List.getLast?_append_cons, List.getLast?_singleton] at hlast
      exact Option.some.inj hlast
    rw [hlstb] at hw ⊢
    rcases ini with _ | ⟨c, ini'⟩
    · -- ini = []: vertices = [b]; w ∈ [b] contradicts hwb.
      simp only [List.nil_append, List.mem_singleton] at hw
      exact absurd hw hwb
    · -- head = c so c = a.
      simp only [List.cons_append, List.head?_cons] at hhead
      have hca : c = a := Option.some.inj hhead
      -- (c::ini'++[b]).tail.dropLast = (ini'++[b]).dropLast = ini'.
      have htail : (c :: ini' ++ [b]).tail = ini' ++ [b] := by simp [List.tail_cons]
      rw [htail, List.dropLast_concat]
      rw [List.cons_append, List.mem_cons, List.mem_append, List.mem_singleton] at hw
      rcases hw with hwc | hwini' | hwb'
      · exact absurd (hwc.trans hca) hwa
      · exact hwini'
      · exact absurd hwb' hwb

/-- **The universal `arcSplit` field is genuine data, not a `Nodup` consequence.**
If `s(u, v)` *is* a boundary edge and the boundary has a third vertex
`w ∉ {u, v}`, no `BoundaryArcSplit M C.vertices C.edges u v` can exist: `w` must be
covered by one of the two arcs (`boundary_vertices_covered`), hence is an internal
vertex of that arc (it is neither endpoint), forcing `HasInternalVertex`, which by
`path_internal_iff_proper` forces `s(u, v) ∉ C.edges` — contradicting that it is a
boundary edge.  This is why `boundaryCycleOfFace` / `NearTriangulation.outerCycle`
/ `DeletedOuterBoundary` take `arcSplit` as data. -/
theorem boundaryArcSplit_consecutive_unsatisfiable {f : M.Face}
    (C : BoundaryCycle M f) {u v w : M.Vertex}
    (hbe : C.IsBoundaryEdge s(u, v))
    (hwu : w ≠ u) (hwv : w ≠ v) (hw : C.IsBoundaryVertex w)
    (S : BoundaryArcSplit M C.vertices C.edges u v) : False := by
  -- `w` is a boundary vertex, hence on `path₁` or `path₂`.
  have hwmem : w ∈ C.vertices := hw
  rcases (S.boundary_vertices_covered w).mp hwmem with hw1 | hw2
  · -- `w` is on `path₁` (u → v) and is neither endpoint, so it is internal.
    have hint : w ∈ S.path₁.internalVertices :=
      mem_internalVertices_of_ne_endpoints S.path₁ hw1 hwu hwv
    have hhas : S.path₁.HasInternalVertex := by
      rw [BoundaryPath.hasInternalVertex_iff]; exact List.ne_nil_of_mem hint
    exact (S.path₁_internal_iff_proper.mp hhas) hbe
  · -- symmetric: `w` on `path₂` (v → u).
    have hint : w ∈ S.path₂.internalVertices :=
      mem_internalVertices_of_ne_endpoints S.path₂ hw2 hwv hwu
    have hhas : S.path₂.HasInternalVertex := by
      rw [BoundaryPath.hasInternalVertex_iff]; exact List.ne_nil_of_mem hint
    exact (S.path₂_internal_iff_proper.mp hhas) hbe

/-! ## 3. Piece 2 — the shared `NearTriangulation` assembler (R10 §3/§5)

Given the explicit boundary + inner-triangle data — a simple sphere map `K`, an
outer face with a root dart whose tail list is simple of length `≥ 3`, the
universal arc-splitting certificate, and inner triangularity — assemble the full
`NearTriangulation K`.  This is the input that the genus-0 itineraries (R10 Layer
B/C) and count (Layer D) supply, for both the side maps and the deleted maps. -/

/-- **Piece 2 — the explicit-boundary near-triangulation assembler.**
`outerCycle` is `boundaryCycleOfFace` rooted at `root`; the arc-split certificate
is the genuine Jordan data `arcSplit` (R10 §4: not derivable from `Nodup` for
consecutive pairs — see `boundaryArcSplit_consecutive_unsatisfiable`).  Every other
field is the listed explicit hypothesis. -/
noncomputable def nearTriangulation_of_explicit_boundary_classification
    {DK : Type u} [Fintype DK] [DecidableEq DK] (K : CombMap DK)
    (hsphere : K.IsSphereMap) (hsimple : K.IsSimpleGraph)
    (outerFace : K.Face) (root : DK) (houterOrbit : K.dartFace root = outerFace)
    (arcSplit :
      ∀ ⦃p q : K.Vertex⦄, p ≠ q →
        p ∈ (K.faceDartList root).map K.tail →
        q ∈ (K.faceDartList root).map K.tail →
        BoundaryArcSplit K ((K.faceDartList root).map K.tail)
          ((K.faceDartList root).map K.dartEdge) p q)
    (houter_simple : ((K.faceDartList root).map K.tail).Nodup)
    (houter_len : 3 ≤ (K.faceDartList root).length)
    (hinner_tri : ∀ f : K.Face, f ≠ outerFace → K.faceLen f = 3) :
    NearTriangulation K where
  sphere := hsphere
  simpleGraph := hsimple
  outerFace := outerFace
  outerCycle :=
    K.boundaryCycleOfFace outerFace
      (K.phi_ne_self_of_isSimpleGraph hsimple root) houterOrbit arcSplit
  outer_simple := houter_simple
  outer_len := houter_len
  inner_tri := hinner_tri

/-! ## 4. Non-vacuity checks

We confirm both pieces fire on genuine data (rule out the vacuous-interface
failure mode of §3.3): Piece 1 outputs a real `BoundaryArcSplit` whose `path₁`
starts at `u`, and Piece 2's `outerCycle` is the explicit `φ`-orbit cycle. -/

/-- Piece 1's output is a genuine `BoundaryArcSplit`: its `path₁` starts at `u`
and `path₂` starts at `v` — not a degenerate constant. -/
theorem arcSplit_of_nodup_nonBoundaryEdge_nondegenerate {f : M.Face}
    (C : BoundaryCycle M f) (hC : C.VertexNodup) {u v : M.Vertex} (hne : u ≠ v)
    (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v)
    (hnbe : ¬ C.IsBoundaryEdge s(u, v)) :
    (BoundaryCycle.arcSplit_of_nodup_nonBoundaryEdge C hC hne hu hv hnbe).path₁.vertices.head?
        = some u ∧
      (BoundaryCycle.arcSplit_of_nodup_nonBoundaryEdge C hC hne hu hv hnbe).path₂.vertices.head?
        = some v :=
  ⟨(BoundaryCycle.arcSplit_of_nodup_nonBoundaryEdge C hC hne hu hv hnbe).path₁.starts_at,
    (BoundaryCycle.arcSplit_of_nodup_nonBoundaryEdge C hC hne hu hv hnbe).path₂.starts_at⟩

/-- Piece 2's `outerCycle` is the explicit `φ`-orbit dart list rooted at `root`
(`faceDartList root`) — the construction genuinely fires, it is not vacuous. -/
theorem nearTriangulation_of_explicit_boundary_classification_outerCycle_darts
    {DK : Type u} [Fintype DK] [DecidableEq DK] (K : CombMap DK)
    (hsphere : K.IsSphereMap) (hsimple : K.IsSimpleGraph)
    (outerFace : K.Face) (root : DK) (houterOrbit : K.dartFace root = outerFace)
    (arcSplit :
      ∀ ⦃p q : K.Vertex⦄, p ≠ q →
        p ∈ (K.faceDartList root).map K.tail →
        q ∈ (K.faceDartList root).map K.tail →
        BoundaryArcSplit K ((K.faceDartList root).map K.tail)
          ((K.faceDartList root).map K.dartEdge) p q)
    (houter_simple : ((K.faceDartList root).map K.tail).Nodup)
    (houter_len : 3 ≤ (K.faceDartList root).length)
    (hinner_tri : ∀ f : K.Face, f ≠ outerFace → K.faceLen f = 3) :
    (nearTriangulation_of_explicit_boundary_classification K hsphere hsimple outerFace root
        houterOrbit arcSplit houter_simple houter_len hinner_tri).outerCycle.darts
      = K.faceDartList root :=
  rfl

/-! ## 5. Axiom audit -/

#print axioms BoundaryCycle.arcSplit_of_nodup_nonBoundaryEdge
#print axioms boundaryArcSplit_consecutive_unsatisfiable
#print axioms nearTriangulation_of_explicit_boundary_classification
#print axioms arcSplit_of_nodup_nonBoundaryEdge_nondegenerate
#print axioms nearTriangulation_of_explicit_boundary_classification_outerCycle_darts

end ProofsInTheBook.ZinanCh35BoundaryAssembler
