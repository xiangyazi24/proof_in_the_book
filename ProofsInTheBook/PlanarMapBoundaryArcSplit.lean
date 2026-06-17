import ProofsInTheBook.PlanarMapBoundary

/-!
# Chapter 35 — the universal arc-split over the boundary-cycle CORE

This file proves the universal arc-split certificate **over the orbit-algebraic core**
`BoundaryCycleData` (defined in `PlanarMapBoundary.lean`), discharging the
`BoundaryCycle.arcSplit` field as a *consequence* of `VertexNodup` (simplicity) alone.

It is a faithful, self-contained adaptation of the proven `BoundaryCycle`-level
construction (`ZinanCh35ArcSplitUniversal.arcSplit_of_nodup`), performed entirely over
the core so that the result can be installed into the full `BoundaryCycle` without the
`boundaryCycleOfFace ↔ arcSplit` self-reference.  Everything is copied mechanically from:

* `ZinanCh35Aligned.modCoverD` (pure Nat arithmetic);
* `DartArc.lean` (`structure DartArc`) → renamed `DataDartArc` over the core;
* `ZinanCh35ArcDartRun.lean` (`dartList`/`dartList_length`/`dartList_ne_nil`/
  `dartList_getElem`/`mem_dartList`);
* `ZinanCh35ChordCycle.lean` (`cyclicDartArc`/`cyclicDartArc_arcDart`/
  `exists_pos_of_isBoundaryVertex`) → `cyclicDataDartArc`, over the core;
* `ZinanCh35Aligned.lean` (`daCastD` + its lemmas, `bpOfDDA` + its lemmas);
* `PlanarMapChordSplit.lean` (`BoundaryPath.internalVertexNeStartD`/`_end` + helpers);
* `ZinanCh35BoundaryAssembler.lean` (`not_consecutive_of_nonBoundaryEdge`, `NonEdgeRuns`,
  `nonEdgeRuns`);
* `ZinanCh35ArcSplitUniversal.lean` (the `arcSplit_of_nodup` body).

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## 0. Core-record convenience definitions (mirroring `BoundaryCycle.*`) -/

namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}

/-- Boundary vertices are represented by the exposed cyclic vertex list. -/
def IsBoundaryVertex (K : BoundaryCycleData M f) (v : M.Vertex) : Prop :=
  v ∈ K.vertices

/-- Boundary edges are represented by the exposed cyclic edge list. -/
def IsBoundaryEdge (K : BoundaryCycleData M f) (e : Sym2 M.Vertex) : Prop :=
  e ∈ K.edges

/-- The boundary vertex list is simple. -/
def VertexNodup (K : BoundaryCycleData M f) : Prop :=
  K.vertices.Nodup

/-- Boundary length, measured in darts/edges. -/
def length (K : BoundaryCycleData M f) : ℕ :=
  K.darts.length

lemma darts_nodup (K : BoundaryCycleData M f) : K.darts.Nodup :=
  K.normalized.nodup

lemma darts_length_pos (K : BoundaryCycleData M f) : 0 < K.darts.length :=
  K.normalized.length_pos

end BoundaryCycleData

/-! ## 1. `modCoverD` (verbatim, pure Nat arithmetic)

Two complementary cyclic runs cover the residues mod `L`. -/

theorem modCoverD (L pf pt : ℕ) (hLpos : 0 < L) (hpf : pf < L) (hpt : pt < L) (hne : pf ≠ pt)
    (kf kb : ℕ) (hkf_eq : kf = (pt + L - pf) % L) (hkb_eq : kb = (pf + L - pt) % L) :
    1 ≤ kf ∧ 1 ≤ kb ∧ kf + kb = L ∧ (pf + kf) % L = pt ∧
    ∀ q, q < L → (∃ j, j < kf ∧ (pf + j) % L = q) ∨ (∃ j, j < kb ∧ (pt + j) % L = q) := by
  have hkf1 : 1 ≤ kf := by
    rw [hkf_eq]
    rcases Nat.eq_zero_or_pos ((pt + L - pf) % L) with h0 | h0
    · exfalso
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h0
      have hlt : pt + L - pf < 2 * L := by omega
      have hgt : 0 < pt + L - pf := by omega
      have : m = 1 := by nlinarith
      rw [this, Nat.mul_one] at hm; omega
    · exact h0
  have hkb1 : 1 ≤ kb := by
    rw [hkb_eq]
    rcases Nat.eq_zero_or_pos ((pf + L - pt) % L) with h0 | h0
    · exfalso
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero h0
      have hlt : pf + L - pt < 2 * L := by omega
      have hgt : 0 < pf + L - pt := by omega
      have : m = 1 := by nlinarith
      rw [this, Nat.mul_one] at hm; omega
    · exact h0
  have hkfval : kf = if pf ≤ pt then pt - pf else pt + L - pf := by
    rw [hkf_eq]; split
    · next h => rw [show pt + L - pf = (pt - pf) + L from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · next h => rw [Nat.mod_eq_of_lt (by omega)]
  have hkbval : kb = if pt ≤ pf then pf - pt else pf + L - pt := by
    rw [hkb_eq]; split
    · next h => rw [show pf + L - pt = (pf - pt) + L from by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
    · next h => rw [Nat.mod_eq_of_lt (by omega)]
  have hsum : kf + kb = L := by rw [hkfval, hkbval]; split <;> split <;> omega
  have hpfkf : (pf + kf) % L = pt := by
    rw [hkf_eq]
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl L)]
    rw [← Nat.add_mod]
    have : pf + (pt + L - pf) = pt + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hpt]
  refine ⟨hkf1, hkb1, hsum, hpfkf, ?_⟩
  intro q hq
  set df := (q + L - pf) % L with hdf
  have hdfL : df < L := Nat.mod_lt _ hLpos
  have hpfdf : (pf + df) % L = q := by
    rw [hdf]
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl L)]
    rw [← Nat.add_mod]
    have : pf + (q + L - pf) = q + L := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hq]
  by_cases hd : df < kf
  · exact Or.inl ⟨df, hd, hpfdf⟩
  · refine Or.inr ⟨df - kf, by omega, ?_⟩
    calc (pt + (df - kf)) % L = ((pf + kf) % L + (df - kf)) % L := by rw [hpfkf]
      _ = (pf + kf + (df - kf)) % L := by
            rw [Nat.add_mod, Nat.mod_mod_of_dvd _ (dvd_refl L), ← Nat.add_mod]
      _ = (pf + df) % L := by rw [show pf + kf + (df - kf) = pf + df from by omega]
      _ = q := hpfdf

/-! ## 2. The dart-level boundary arc over the CORE (`DataDartArc`)

A dart-level boundary arc from `u` to `v` whose darts all lie on the core's `K.darts`,
chaining head→tail internally and simple as a tail/head vertex list.  This is the
core-record analogue of `DartArc` (renamed to avoid clashing). -/

/-- A dart-level boundary arc from `u` to `v` on the boundary-cycle core `K`. -/
structure DataDartArc (M : CombMap D) {f : M.Face} (K : BoundaryCycleData M f)
    (u v : M.Vertex) where
  /-- Number of darts on the arc. -/
  len : ℕ
  /-- The arc is nonempty (at least one dart). -/
  len_pos : 0 < len
  /-- The directed arc darts `e_0, …, e_{len-1}`. -/
  arcDart : Fin len → D
  /-- Every arc dart lies on the boundary cycle. -/
  boundary : ∀ i : Fin len, arcDart i ∈ K.darts
  /-- Consecutive arc darts chain head→tail (no wraparound — this is a *path*). -/
  chain : ∀ i : Fin len, (h : (i : ℕ) + 1 < len) →
    M.head (arcDart i) = M.tail (arcDart ⟨i + 1, h⟩)
  /-- The first dart's tail is `u`. -/
  tail_first : M.tail (arcDart ⟨0, len_pos⟩) = u
  /-- The last dart's head is `v`. -/
  head_last : M.head (arcDart ⟨len - 1, by omega⟩) = v
  /-- The tail vertices of the arc darts are pairwise distinct (simplicity). -/
  tail_nodup : Function.Injective (fun i : Fin len => M.tail (arcDart i))
  /-- The final head `v` is distinct from every tail (the arc does not revisit its
  endpoint). -/
  head_last_ne_tail : ∀ i : Fin len, v ≠ M.tail (arcDart i)

namespace DataDartArc

variable {M : CombMap D} {f : M.Face} {K : BoundaryCycleData M f} {u v : M.Vertex}

/-- The last index of the arc. -/
def lastIdx (A : DataDartArc M K u v) : Fin A.len := ⟨A.len - 1, by have := A.len_pos; omega⟩

/-- The first index of the arc. -/
def firstIdx (A : DataDartArc M K u v) : Fin A.len := ⟨0, A.len_pos⟩

@[simp] lemma tail_firstIdx (A : DataDartArc M K u v) :
    M.tail (A.arcDart A.firstIdx) = u := A.tail_first

@[simp] lemma head_lastIdx (A : DataDartArc M K u v) :
    M.head (A.arcDart A.lastIdx) = v := A.head_last

/-- The explicit `List D` of a `DataDartArc`'s darts, `[arcDart 0, …, arcDart (len-1)]`. -/
def dartList (A : DataDartArc M K u v) : List D :=
  (List.finRange A.len).map A.arcDart

@[simp] lemma dartList_length (A : DataDartArc M K u v) : A.dartList.length = A.len := by
  simp [DataDartArc.dartList]

lemma dartList_ne_nil (A : DataDartArc M K u v) : A.dartList ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, DataDartArc.dartList_length]; exact A.len_pos

lemma dartList_getElem (A : DataDartArc M K u v) (j : ℕ) (hj : j < A.len) :
    A.dartList[j]'(by rw [DataDartArc.dartList_length]; exact hj) = A.arcDart ⟨j, hj⟩ := by
  simp only [DataDartArc.dartList, List.getElem_map, List.getElem_finRange]
  congr 1

lemma mem_dartList (A : DataDartArc M K u v) {d : D} (hd : d ∈ A.dartList) :
    ∃ i : Fin A.len, A.arcDart i = d := by
  rw [DataDartArc.dartList, List.mem_map] at hd
  obtain ⟨i, _, hi⟩ := hd
  exact ⟨i, hi⟩

end DataDartArc

/-! ## 3. The cyclic dart-level boundary arc over the core (`cyclicDataDartArc`) -/

namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}

/-- The position of a boundary vertex on the cyclic dart list (as the tail of a
listed dart), as a single existential over `Fin`. -/
lemma exists_pos_of_isBoundaryVertex (K : BoundaryCycleData M f) {a : M.Vertex}
    (ha : K.IsBoundaryVertex a) :
    ∃ p : Fin K.darts.length, M.tail (K.darts[p.1]'p.2) = a := by
  have ha' : a ∈ K.darts.map M.tail := by
    simpa [BoundaryCycleData.IsBoundaryVertex, K.vertices_eq] using ha
  rw [List.mem_iff_getElem] at ha'
  obtain ⟨p, hp, hget⟩ := ha'
  rw [List.length_map] at hp
  refine ⟨⟨p, hp⟩, ?_⟩
  rwa [List.getElem_map] at hget

/-- Given a boundary-cycle core `K` (vertices simple), a start position `p`, and a
*cyclic* run length `k` with `1 ≤ k ≤ K.darts.length`, the darts `K.darts[(p + j) % L]`
(`j < k`) form a `DataDartArc` from `M.tail (K.darts[p])` to `M.tail (K.darts[(p+k)%L])`. -/
noncomputable def cyclicDataDartArc (K : BoundaryCycleData M f) (hK : K.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < K.darts.length)
    (hp : p < K.darts.length) :
    DataDartArc M K (M.tail (K.darts[p]'hp))
      (M.tail (K.darts[(p + k) % K.darts.length]'(Nat.mod_lt _ (by omega)))) where
  len := k
  len_pos := hk
  arcDart j := K.darts[(p + j.1) % K.darts.length]'(Nat.mod_lt _ (by omega))
  boundary j := List.getElem_mem _
  chain j hj := by
    set L := K.darts.length with hL
    have hLpos : 0 < L := K.darts_length_pos
    have hpos : (p + (j : ℕ)) % L < L := Nat.mod_lt _ hLpos
    have hcv := K.consecutive_vertex ⟨(p + (j : ℕ)) % L, hpos⟩
    have hcyc : (cyclicNext K.normalized.length_pos ⟨(p + (j : ℕ)) % L, hpos⟩ : Fin L)
        = ⟨(p + ((j : ℕ) + 1)) % L, Nat.mod_lt _ hLpos⟩ := by
      apply Fin.ext
      show ((p + (j : ℕ)) % L + 1) % L = (p + ((j : ℕ) + 1)) % L
      rw [Nat.mod_add_mod]
      congr 1
    rw [hcyc] at hcv
    show M.head (K.darts[(p + (j : ℕ)) % L]'_)
        = M.tail (K.darts[(p + ((j : ℕ) + 1)) % L]'_)
    rw [show (K.darts.get ⟨(p + (j : ℕ)) % L, hpos⟩) = K.darts[(p + (j : ℕ)) % L]'hpos from rfl,
      show (K.darts.get ⟨(p + ((j : ℕ) + 1)) % L, Nat.mod_lt _ hLpos⟩)
          = K.darts[(p + ((j : ℕ) + 1)) % L]'(Nat.mod_lt _ hLpos) from rfl] at hcv
    exact hcv.symm
  tail_first := by
    have hLpos : 0 < K.darts.length := K.darts_length_pos
    have heq : (p + (0 : ℕ)) % K.darts.length = p := by
      rw [Nat.add_zero, Nat.mod_eq_of_lt hp]
    show M.tail (K.darts[(p + (0 : ℕ)) % K.darts.length]'_) = M.tail (K.darts[p]'hp)
    simp only [heq]
  head_last := by
    set L := K.darts.length with hL
    have hLpos : 0 < L := K.darts_length_pos
    have hpos : (p + (k - 1)) % L < L := Nat.mod_lt _ hLpos
    have hcv := K.consecutive_vertex ⟨(p + (k - 1)) % L, hpos⟩
    have hcyc : (cyclicNext K.normalized.length_pos ⟨(p + (k - 1)) % L, hpos⟩ : Fin L)
        = ⟨(p + k) % L, Nat.mod_lt _ hLpos⟩ := by
      apply Fin.ext
      show ((p + (k - 1)) % L + 1) % L = (p + k) % L
      rw [Nat.mod_add_mod]
      congr 1
      omega
    rw [hcyc] at hcv
    show M.head (K.darts[(p + ((k : ℕ) - 1)) % L]'_) = M.tail (K.darts[(p + k) % L]'_)
    rw [show (K.darts.get ⟨(p + (k - 1)) % L, hpos⟩) = K.darts[(p + (k - 1)) % L]'hpos from rfl,
      show (K.darts.get ⟨(p + k) % L, Nat.mod_lt _ hLpos⟩)
          = K.darts[(p + k) % L]'(Nat.mod_lt _ hLpos) from rfl] at hcv
    exact hcv.symm
  tail_nodup := by
    set L := K.darts.length with hL
    have hmap : (K.darts.map M.tail).Nodup := by
      simpa [BoundaryCycleData.VertexNodup, K.vertices_eq] using hK
    intro i₁ i₂ htail
    have hi₁ : (i₁ : ℕ) < k := i₁.isLt
    have hi₂ : (i₂ : ℕ) < k := i₂.isLt
    have h1 : (p + (i₁ : ℕ)) % L < L := Nat.mod_lt _ K.darts_length_pos
    have h2 : (p + (i₂ : ℕ)) % L < L := Nat.mod_lt _ K.darts_length_pos
    have hdarts : K.darts[(p + (i₁ : ℕ)) % L]'h1 = K.darts[(p + (i₂ : ℕ)) % L]'h2 := by
      have hinj := List.inj_on_of_nodup_map hmap (List.getElem_mem h1) (List.getElem_mem h2)
      exact hinj htail
    have hpos_eq : (p + (i₁ : ℕ)) % L = (p + (i₂ : ℕ)) % L :=
      (K.normalized.nodup.getElem_inj_iff).mp hdarts
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
    set L := K.darts.length with hL
    have hmap : (K.darts.map M.tail).Nodup := by
      simpa [BoundaryCycleData.VertexNodup, K.vertices_eq] using hK
    intro i htail
    have hi : (i : ℕ) < k := i.isLt
    have hposk : (p + k) % L < L := Nat.mod_lt _ K.darts_length_pos
    have hposi : (p + (i : ℕ)) % L < L := Nat.mod_lt _ K.darts_length_pos
    have hdarts : K.darts[(p + k) % L]'hposk = K.darts[(p + (i : ℕ)) % L]'hposi := by
      have hinj := List.inj_on_of_nodup_map hmap (List.getElem_mem hposk) (List.getElem_mem hposi)
      exact hinj htail
    have hpos_eq : (p + k) % L = (p + (i : ℕ)) % L :=
      (K.normalized.nodup.getElem_inj_iff).mp hdarts
    have hiltL : (i : ℕ) < L := lt_trans hi hkL
    have hmodeq : Nat.ModEq L (p + k) (p + (i : ℕ)) := hpos_eq
    have hcancel : Nat.ModEq L k (i : ℕ) := Nat.ModEq.add_left_cancel' p hmodeq
    have hkL' : k % L = k := Nat.mod_eq_of_lt hkL
    have hiL : (i : ℕ) % L = (i : ℕ) := Nat.mod_eq_of_lt hiltL
    rw [Nat.ModEq, hkL', hiL] at hcancel
    omega

@[simp] lemma cyclicDataDartArc_len (K : BoundaryCycleData M f) (hK : K.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < K.darts.length) (hp : p < K.darts.length) :
    (cyclicDataDartArc K hK p k hk hkL hp).len = k := rfl

@[simp] lemma cyclicDataDartArc_arcDart (K : BoundaryCycleData M f) (hK : K.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < K.darts.length) (hp : p < K.darts.length)
    (j : Fin k) :
    (cyclicDataDartArc K hK p k hk hkL hp).arcDart j
      = K.darts[(p + j.1) % K.darts.length]'(Nat.mod_lt _ (by omega)) := rfl

end BoundaryCycleData

/-! ## 4. Endpoint retyping casts (`daCastD`) and the `BoundaryPath` of a dart arc -/

section Casts

variable {M : CombMap D}

/-- Retype a `DataDartArc`'s endpoints along equalities. -/
noncomputable def daCastD {f : M.Face} {K : BoundaryCycleData M f} {a a' b b' : M.Vertex}
    (A : DataDartArc M K a b) (ha : a = a') (hb : b = b') : DataDartArc M K a' b' := ha ▸ hb ▸ A

@[simp] lemma daCastD_len {f : M.Face} {K : BoundaryCycleData M f} {a a' b b' : M.Vertex}
    (A : DataDartArc M K a b) (ha : a = a') (hb : b = b') : (daCastD A ha hb).len = A.len := by
  subst ha; subst hb; rfl

lemma daCastD_arcDart {f : M.Face} {K : BoundaryCycleData M f} {a a' b b' : M.Vertex}
    (A : DataDartArc M K a b) (ha : a = a') (hb : b = b') (i : Fin (daCastD A ha hb).len) :
    M.tail ((daCastD A ha hb).arcDart i)
      = M.tail (A.arcDart (Fin.cast (daCastD_len A ha hb) i)) := by
  subst ha; subst hb; rfl

/-- The arc-dart of a casted dart-arc equals the original at the cast index. -/
lemma daCastD_arcDart_eq {f : M.Face} {K : BoundaryCycleData M f} {a a' b b' : M.Vertex}
    (A : DataDartArc M K a b) (ha : a = a') (hb : b = b') (i : Fin (daCastD A ha hb).len) :
    (daCastD A ha hb).arcDart i = A.arcDart (Fin.cast (daCastD_len A ha hb) i) := by
  subst ha; subst hb; rfl

/-- **The tail of a casted cyclic dart-arc at index `i` is the cyclic-slice tail `darts[(p+i)%L]`.** -/
lemma daCastD_cyclic_tail {f : M.Face} (K : BoundaryCycleData M f) (hK : K.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < K.darts.length) (hp : p < K.darts.length)
    {a' b' : M.Vertex}
    (ha : M.tail (K.darts[p]'hp) = a')
    (hb : M.tail (K.darts[(p + k) % K.darts.length]'(Nat.mod_lt _ (by omega))) = b')
    (i : Fin (daCastD (K.cyclicDataDartArc hK p k hk hkL hp) ha hb).len) :
    M.tail ((daCastD (K.cyclicDataDartArc hK p k hk hkL hp) ha hb).arcDart i)
      = M.tail (K.darts[(p + i.1) % K.darts.length]'(Nat.mod_lt _ (by omega))) := by
  rw [daCastD_arcDart, BoundaryCycleData.cyclicDataDartArc_arcDart]; rfl

end Casts

/-! ### `BoundaryPath` internal-vertex witnesses (adapted from `PlanarMapChordSplit`) -/

/-- Under `Nodup`, the last element of a list does not occur in its `dropLast`. -/
lemma getLastNotMemDropLastD {α : Type*} {l : List α} (hl : l ≠ [])
    (hnd : l.Nodup) : l.getLast hl ∉ l.dropLast := by
  have hsplit : l.dropLast ++ [l.getLast hl] = l := List.dropLast_append_getLast hl
  have hnd' : (l.dropLast ++ [l.getLast hl]).Nodup := by rw [hsplit]; exact hnd
  intro hmem
  exact (List.disjoint_of_nodup_append hnd') hmem (by simp)

/-- A generic list fact: if `l.head? = some a` and `l.Nodup`, then `a ∉ l.tail`. -/
lemma headNotMemTailD {α : Type*} {a : α} {l : List α}
    (hh : l.head? = some a) (hnd : l.Nodup) : a ∉ l.tail := by
  cases l with
  | nil => simp at hh
  | cons b t =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      simpa using (List.nodup_cons.mp hnd).1

/-- A generic list fact: if `l.getLast? = some a` and `l.tail ≠ []`, then `a` is
the last element of `l.tail`. -/
lemma getLast_tail_of_getLast? {α : Type*} {a : α} {l : List α}
    (hl : l.getLast? = some a) (ht : l.tail ≠ []) :
    l.tail.getLast ht = a := by
  cases l with
  | nil => exact absurd rfl ht
  | cons b s =>
      simp only [List.tail_cons] at ht ⊢
      have hs : (b :: s).getLast? = some a := hl
      rw [List.getLast?_eq_some_getLast (by simp)] at hs
      simp only [Option.some.injEq] at hs
      rw [← hs, List.getLast_cons ht]

namespace BoundaryPath

variable {M : CombMap D} {u v : M.Vertex}

/-- An internal vertex of a path is a listed vertex of the path. -/
lemma internalVerticesSubsetD (P : BoundaryPath M u v) {w : M.Vertex}
    (hw : w ∈ P.internalVertices) : w ∈ P.vertices :=
  List.tail_subset _ (List.dropLast_subset _ hw)

/-- An internal vertex is distinct from the initial endpoint. -/
lemma internalVertexNeStartD (P : BoundaryPath M u v) {w : M.Vertex}
    (hw : w ∈ P.internalVertices) : w ≠ u := by
  have hutail : u ∉ P.vertices.tail :=
    headNotMemTailD P.starts_at P.simple
  have hwtail : w ∈ P.vertices.tail := List.dropLast_subset _ hw
  intro hwu; subst hwu; exact hutail hwtail

/-- An internal vertex is distinct from the terminal endpoint. -/
lemma internalVertexNeEndD (P : BoundaryPath M u v) {w : M.Vertex}
    (hw : w ∈ P.internalVertices) : w ≠ v := by
  have hwtail_dropLast : w ∈ P.vertices.tail.dropLast := hw
  have htail_ne : P.vertices.tail ≠ [] := fun h => by rw [h] at hwtail_dropLast; simp at hwtail_dropLast
  have hnodup_tail : P.vertices.tail.Nodup := P.simple.sublist (List.tail_sublist _)
  have hlast_tail : P.vertices.tail.getLast htail_ne = v :=
    getLast_tail_of_getLast? P.ends_at htail_ne
  have hnotmem : P.vertices.tail.getLast htail_ne ∉ P.vertices.tail.dropLast :=
    getLastNotMemDropLastD htail_ne hnodup_tail
  intro hwv; subst hwv
  exact hnotmem (hlast_tail.symm ▸ hwtail_dropLast)

end BoundaryPath

/-! ### A `BoundaryPath` from a `DataDartArc` (`bpOfDDA`) -/

section BPOfDartArc

variable {M : CombMap D}

/-- **The `BoundaryPath` of a dart arc.**  Its vertices are the arc-dart tails followed by the
terminal endpoint `b`; its edges are the arc-dart graph edges. -/
noncomputable def bpOfDDA {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) : BoundaryPath M a b where
  vertices := A.dartList.map M.tail ++ [b]
  edges := A.dartList.map M.dartEdge
  starts_at := by
    have hne : (A.dartList.map M.tail) ≠ [] := by simp [A.dartList_ne_nil]
    have h0 : 0 < A.dartList.length := by rw [DataDartArc.dartList_length]; exact A.len_pos
    rw [List.head?_append_of_ne_nil _ hne, List.head?_map, List.head?_eq_getElem?,
      List.getElem?_eq_getElem h0, A.dartList_getElem 0 A.len_pos]
    simp only [Option.map_some]; rw [A.tail_first]
  ends_at := by simp
  simple := by
    rw [List.nodup_append]
    refine ⟨?_, by simp, ?_⟩
    · rw [DataDartArc.dartList, List.map_map, List.nodup_map_iff_inj_on (List.nodup_finRange A.len)]
      intro i _ j _ hij; exact A.tail_nodup hij
    · intro x hx y hy
      rw [List.mem_singleton] at hy; subst hy
      rw [List.mem_map] at hx
      obtain ⟨d, hd, hdt⟩ := hx
      obtain ⟨i, hi⟩ := A.mem_dartList hd
      rw [← hi] at hdt
      exact fun hxb => A.head_last_ne_tail i (hxb ▸ hdt.symm)

@[simp] lemma bpOfDDA_vertices {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) : (bpOfDDA A).vertices = A.dartList.map M.tail ++ [b] := rfl

@[simp] lemma bpOfDDA_edges {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) : (bpOfDDA A).edges = A.dartList.map M.dartEdge := rfl

/-- The internal vertices of `bpOfDDA A` are the tails of the arc darts with index `≥ 1`. -/
lemma bpOfDDA_internal {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) :
    (bpOfDDA A).internalVertices = (A.dartList.map M.tail).tail := by
  show (A.dartList.map M.tail ++ [b]).tail.dropLast = (A.dartList.map M.tail).tail
  have hne : (A.dartList.map M.tail) ≠ [] := by simp [A.dartList_ne_nil]
  rw [List.tail_append_of_ne_nil hne, List.dropLast_concat]

/-- Every vertex of `bpOfDDA A` is a tail of an arc dart, or the terminal endpoint `b`. -/
lemma bpOfDDA_mem_vertices {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) {w : M.Vertex} (hw : w ∈ (bpOfDDA A).vertices) :
    (∃ i : Fin A.len, M.tail (A.arcDart i) = w) ∨ w = b := by
  rw [bpOfDDA_vertices, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | hw
  · left
    rw [List.mem_map] at hw
    obtain ⟨d, hd, hdt⟩ := hw
    obtain ⟨i, hi⟩ := A.mem_dartList hd
    exact ⟨i, hi ▸ hdt⟩
  · right; exact hw

/-- An internal vertex of `bpOfDDA A` is a tail of an arc dart. -/
lemma bpOfDDA_internal_tail {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) {w : M.Vertex} (hw : w ∈ (bpOfDDA A).internalVertices) :
    ∃ i : Fin A.len, M.tail (A.arcDart i) = w := by
  rw [bpOfDDA_internal] at hw
  have hsub : w ∈ A.dartList.map M.tail := List.tail_subset _ hw
  rw [List.mem_map] at hsub
  obtain ⟨d, hd, hdt⟩ := hsub
  obtain ⟨i, hi⟩ := A.mem_dartList hd
  exact ⟨i, hi ▸ hdt⟩

/-- An arc-dart tail is a boundary vertex (`A`'s darts lie on the cycle). -/
lemma arcDartTailMemVD {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) (i : Fin A.len) : M.tail (A.arcDart i) ∈ K.vertices := by
  rw [K.vertices_eq]; exact List.mem_map_of_mem (A.boundary i)

/-- Every vertex of `bpOfDDA A` is a boundary vertex, provided the terminal endpoint `b` is. -/
lemma bpOfDDA_boundary_vertices {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) (hb : b ∈ K.vertices) {w : M.Vertex}
    (hw : w ∈ (bpOfDDA A).vertices) : w ∈ K.vertices := by
  rcases bpOfDDA_mem_vertices A hw with ⟨i, hi⟩ | hwb
  · rw [← hi]; exact arcDartTailMemVD A i
  · rw [hwb]; exact hb

/-- `bpOfDDA A` has an internal vertex when `2 ≤ A.len`. -/
lemma bpOfDDA_hasInternal {f : M.Face} {K : BoundaryCycleData M f} {a b : M.Vertex}
    (A : DataDartArc M K a b) (hlen : 2 ≤ A.len) : (bpOfDDA A).HasInternalVertex := by
  rw [BoundaryPath.hasInternalVertex_iff, bpOfDDA_internal]
  intro hcontra
  have hlenlist : (A.dartList.map M.tail).length = A.len := by
    rw [List.length_map, DataDartArc.dartList_length]
  have htl : (A.dartList.map M.tail).tail.length = (A.dartList.map M.tail).length - 1 :=
    List.length_tail
  rw [hcontra] at htl
  simp only [List.length_nil] at htl
  omega

end BPOfDartArc

/-! ## 5. No `1`-step between non-boundary-edge endpoints, and the complementary runs -/

namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}

/-- **No `1`-step between the two endpoint positions.**  If `s(u, v)` is not a boundary
edge then the positions `p` (tail `u`) and `q` (tail `v`) cannot be cyclic-consecutive. -/
lemma not_consecutive_of_nonBoundaryEdge (K : BoundaryCycleData M f) {u v : M.Vertex}
    (hnbe : ¬ K.IsBoundaryEdge s(u, v)) {p q : ℕ}
    (hp : p < K.darts.length) (hq : q < K.darts.length)
    (htu : M.tail (K.darts[p]'hp) = u)
    (htv : M.tail (K.darts[q]'hq) = v)
    (hadj : (p + 1) % K.darts.length = q) : False := by
  set L := K.darts.length with hL
  have hLpos : 0 < L := K.darts_length_pos
  have hcv := K.consecutive_vertex ⟨p, hp⟩
  have hcyc : (cyclicNext K.normalized.length_pos ⟨p, hp⟩ : Fin L) = ⟨q, hq⟩ := by
    apply Fin.ext; show (p + 1) % L = q; exact hadj
  rw [hcyc] at hcv
  have hhead : M.head (K.darts[p]'hp) = v := by
    rw [show (K.darts.get ⟨q, hq⟩) = K.darts[q]'hq from rfl,
        show (K.darts.get ⟨p, hp⟩) = K.darts[p]'hp from rfl] at hcv
    rw [← hcv, htv]
  apply hnbe
  show s(u, v) ∈ K.edges
  rw [K.edges_eq, show (s(u, v) : Sym2 M.Vertex) = M.dartEdge (K.darts[p]'hp) from by
    show s(u, v) = s(M.tail _, M.head _); rw [htu, hhead]]
  exact List.mem_map_of_mem (List.getElem_mem hp)

/-- The two complementary boundary runs for a non-boundary-edge pair `u, v`, with
their tail-covering and tail-disjointness of `K.vertices`. -/
structure NonEdgeRuns (K : BoundaryCycleData M f) (hK : K.VertexNodup) {u v : M.Vertex}
    (hne : u ≠ v) (hu : K.IsBoundaryVertex u) (hv : K.IsBoundaryVertex v)
    (hnbe : ¬ K.IsBoundaryEdge s(u, v)) where
  /-- The `u → v` boundary run. -/
  arcUV : DataDartArc M K u v
  /-- The `v → u` boundary run. -/
  arcVU : DataDartArc M K v u
  /-- Both runs have length `≥ 2`. -/
  lenUV : 2 ≤ arcUV.len
  lenVU : 2 ≤ arcVU.len
  /-- Every boundary vertex is a tail of one of the two runs, or an endpoint. -/
  covering : ∀ {w : M.Vertex}, K.IsBoundaryVertex w →
    (∃ i, M.tail (arcUV.arcDart i) = w) ∨ (∃ i, M.tail (arcVU.arcDart i) = w) ∨ w = u ∨ w = v
  /-- A vertex that is a tail of *both* runs is an endpoint. -/
  disjoint : ∀ {w : M.Vertex}, (∃ i, M.tail (arcUV.arcDart i) = w) →
    (∃ i, M.tail (arcVU.arcDart i) = w) → w = u ∨ w = v

/-- **Build the complementary runs from the non-boundary-edge data.** -/
noncomputable def nonEdgeRuns (K : BoundaryCycleData M f) (hK : K.VertexNodup)
    {u v : M.Vertex} (hne : u ≠ v) (hu : K.IsBoundaryVertex u) (hv : K.IsBoundaryVertex v)
    (hnbe : ¬ K.IsBoundaryEdge s(u, v)) : NonEdgeRuns K hK hne hu hv hnbe := by
  classical
  set L := K.darts.length with hL
  have hLpos : 0 < L := K.darts_length_pos
  set puF := (K.exists_pos_of_isBoundaryVertex hu).choose with hpuF
  have eu0 := (K.exists_pos_of_isBoundaryVertex hu).choose_spec
  set pvF := (K.exists_pos_of_isBoundaryVertex hv).choose with hpvF
  have ev0 := (K.exists_pos_of_isBoundaryVertex hv).choose_spec
  set pu := puF.1 with hpuval
  set pv := pvF.1 with hpvval
  have hpu : pu < L := puF.2
  have hpv : pv < L := pvF.2
  have eu : M.tail (K.darts[pu]'hpu) = u := eu0
  have ev : M.tail (K.darts[pv]'hpv) = v := ev0
  have hpune : pu ≠ pv := by
    intro hpe; apply hne
    rw [← eu, ← ev]
    have : K.darts[pu]'hpu = K.darts[pv]'hpv := getElem_congr rfl hpe hpu
    rw [this]
  set kf := (pv + L - pu) % L with hkf
  set kb := (pu + L - pv) % L with hkb
  obtain ⟨hkf1, hkb1, hsum, hpfkf, hcov⟩ :=
    modCoverD L pu pv hLpos hpu hpv hpune kf kb hkf hkb
  obtain ⟨_, _, _, hpvkb, _⟩ :=
    modCoverD L pv pu hLpos hpv hpu (Ne.symm hpune) kb kf hkb hkf
  have hkfL : kf < L := by rw [hkf]; exact Nat.mod_lt _ hLpos
  have hkbL : kb < L := by rw [hkb]; exact Nat.mod_lt _ hLpos
  have hkf2 : 2 ≤ kf := by
    rcases Nat.lt_or_ge kf 2 with hlt | hge
    · exfalso
      have hkf1' : kf = 1 := by omega
      apply not_consecutive_of_nonBoundaryEdge K hnbe hpu hpv eu ev
      rw [show (pu + 1) % L = (pu + kf) % L from by rw [hkf1'], hpfkf]
    · exact hge
  have hkb2 : 2 ≤ kb := by
    rcases Nat.lt_or_ge kb 2 with hlt | hge
    · exfalso
      have hkb1' : kb = 1 := by omega
      have hnbe' : ¬ K.IsBoundaryEdge s(v, u) := by rw [Sym2.eq_swap]; exact hnbe
      exact not_consecutive_of_nonBoundaryEdge K hnbe' hpv hpu ev eu
        (by rw [show (pv + 1) % L = (pv + kb) % L from by rw [hkb1'], hpvkb])
    · exact hge
  set AUV := K.cyclicDataDartArc hK pu kf hkf1 hkfL hpu with hAUV
  set AVU := K.cyclicDataDartArc hK pv kb hkb1 hkbL hpv with hAVU
  have euv2 : M.tail (K.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega))) = v := by
    have : K.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega)) = K.darts[pv]'hpv := by congr 1
    rw [this]; exact ev
  have evu2 : M.tail (K.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega))) = u := by
    have : K.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega)) = K.darts[pu]'hpu := by congr 1
    rw [this]; exact eu
  have htailUV : ∀ i : Fin (daCastD AUV eu euv2).len,
      M.tail ((daCastD AUV eu euv2).arcDart i)
        = M.tail (K.darts[(pu + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCastD_cyclic_tail K hK pu kf hkf1 hkfL hpu eu euv2 i
  have htailVU : ∀ i : Fin (daCastD AVU ev evu2).len,
      M.tail ((daCastD AVU ev evu2).arcDart i)
        = M.tail (K.darts[(pv + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCastD_cyclic_tail K hK pv kb hkb1 hkbL hpv ev evu2 i
  have htailUV_fwd : ∀ j : ℕ, (hj : j < kf) →
      ∃ i : Fin (daCastD AUV eu euv2).len,
        M.tail ((daCastD AUV eu euv2).arcDart i)
          = M.tail (K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCastD AUV eu euv2).len := by rw [daCastD_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailUV ⟨j, hjlen⟩⟩
  have htailVU_fwd : ∀ j : ℕ, (hj : j < kb) →
      ∃ i : Fin (daCastD AVU ev evu2).len,
        M.tail ((daCastD AVU ev evu2).arcDart i)
          = M.tail (K.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCastD AVU ev evu2).len := by rw [daCastD_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailVU ⟨j, hjlen⟩⟩
  have htailUV_bwd : ∀ i : Fin (daCastD AUV eu euv2).len,
      ∃ j : ℕ, j < kf ∧
        M.tail ((daCastD AUV eu euv2).arcDart i)
          = M.tail (K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kf := lt_of_lt_of_eq i.2 (daCastD_len AUV eu euv2)
    exact ⟨i.1, hi, htailUV i⟩
  have htailVU_bwd : ∀ i : Fin (daCastD AVU ev evu2).len,
      ∃ j : ℕ, j < kb ∧
        M.tail ((daCastD AVU ev evu2).arcDart i)
          = M.tail (K.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kb := lt_of_lt_of_eq i.2 (daCastD_len AVU ev evu2)
    exact ⟨i.1, hi, htailVU i⟩
  refine
    { arcUV := daCastD AUV eu euv2
      arcVU := daCastD AVU ev evu2
      lenUV := ?_
      lenVU := ?_
      covering := ?_
      disjoint := ?_ }
  · rw [daCastD_len]; exact hkf2
  · rw [daCastD_len]; exact hkb2
  · intro w hw
    obtain ⟨q, hqt⟩ := K.exists_pos_of_isBoundaryVertex hw
    rcases hcov q.1 q.2 with ⟨j, hj, hjq⟩ | ⟨j, hj, hjq⟩
    · left
      obtain ⟨i, hi⟩ := htailUV_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) = K.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
    · right; left
      obtain ⟨i, hi⟩ := htailVU_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : K.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega)) = K.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
  · rintro w ⟨i, hiw⟩ ⟨i', hi'w⟩
    obtain ⟨j, hj, hjeq⟩ := htailUV_bwd i
    obtain ⟨j', hj', hj'eq⟩ := htailVU_bwd i'
    have heq : M.tail (K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)))
        = M.tail (K.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega))) := by
      rw [← hjeq, ← hj'eq, hiw, hi'w]
    have hmap : (K.darts.map M.tail).Nodup := by
      have := hK; rwa [BoundaryCycleData.VertexNodup, K.vertices_eq] at this
    have hposeq : (pu + j) % L = (pv + j') % L := by
      have hmem1 : K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) ∈ K.darts :=
        List.getElem_mem _
      have hmem2 : K.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) ∈ K.darts :=
        List.getElem_mem _
      have hdarts : K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))
          = K.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) :=
        List.inj_on_of_nodup_map hmap hmem1 hmem2 heq
      exact (K.normalized.nodup.getElem_inj_iff).mp hdarts
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

end BoundaryCycleData

/-! ## 6. The universal arc-split over the core (`arcSplit_of_nodup`) -/

namespace BoundaryCycleData

variable {M : CombMap D} {f : M.Face}

/-- **The universal arc-split from `VertexNodup`, over the CORE.**  For any two distinct
listed boundary vertices `u, v` (no adjacency restriction), the two complementary cyclic
runs assemble a `BoundaryArcSplit M K.vertices K.edges u v`.  Pure list combinatorics from
simplicity. -/
noncomputable def arcSplit_of_nodup (K : BoundaryCycleData M f) (hK : K.vertices.Nodup)
    ⦃u v : M.Vertex⦄ (hne : u ≠ v)
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) :
    BoundaryArcSplit M K.vertices K.edges u v := by
  classical
  set L := K.darts.length with hL
  have hLpos : 0 < L := K.darts_length_pos
  set puF := (K.exists_pos_of_isBoundaryVertex hu).choose with hpuF
  have eu0 := (K.exists_pos_of_isBoundaryVertex hu).choose_spec
  set pvF := (K.exists_pos_of_isBoundaryVertex hv).choose with hpvF
  have ev0 := (K.exists_pos_of_isBoundaryVertex hv).choose_spec
  set pu := puF.1 with hpuval
  set pv := pvF.1 with hpvval
  have hpu : pu < L := puF.2
  have hpv : pv < L := pvF.2
  have eu : M.tail (K.darts[pu]'hpu) = u := eu0
  have ev : M.tail (K.darts[pv]'hpv) = v := ev0
  have hpune : pu ≠ pv := by
    intro hpe; apply hne
    rw [← eu, ← ev]
    have : K.darts[pu]'hpu = K.darts[pv]'hpv := getElem_congr rfl hpe hpu
    rw [this]
  set kf := (pv + L - pu) % L with hkf
  set kb := (pu + L - pv) % L with hkb
  obtain ⟨hkf1, hkb1, hsum, hpfkf, hcov⟩ :=
    modCoverD L pu pv hLpos hpu hpv hpune kf kb hkf hkb
  obtain ⟨_, _, _, hpvkb, _⟩ :=
    modCoverD L pv pu hLpos hpv hpu (Ne.symm hpune) kb kf hkb hkf
  have hkfL : kf < L := by rw [hkf]; exact Nat.mod_lt _ hLpos
  have hkbL : kb < L := by rw [hkb]; exact Nat.mod_lt _ hLpos
  set AUV := K.cyclicDataDartArc hK pu kf hkf1 hkfL hpu with hAUV
  set AVU := K.cyclicDataDartArc hK pv kb hkb1 hkbL hpv with hAVU
  have euv2 : M.tail (K.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega))) = v := by
    have : K.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega)) = K.darts[pv]'hpv := by congr 1
    rw [this]; exact ev
  have evu2 : M.tail (K.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega))) = u := by
    have : K.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega)) = K.darts[pu]'hpu := by congr 1
    rw [this]; exact eu
  have htailUV : ∀ i : Fin (daCastD AUV eu euv2).len,
      M.tail ((daCastD AUV eu euv2).arcDart i)
        = M.tail (K.darts[(pu + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCastD_cyclic_tail K hK pu kf hkf1 hkfL hpu eu euv2 i
  have htailVU : ∀ i : Fin (daCastD AVU ev evu2).len,
      M.tail ((daCastD AVU ev evu2).arcDart i)
        = M.tail (K.darts[(pv + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCastD_cyclic_tail K hK pv kb hkb1 hkbL hpv ev evu2 i
  have htailUV_fwd : ∀ j : ℕ, (hj : j < kf) →
      ∃ i : Fin (daCastD AUV eu euv2).len,
        M.tail ((daCastD AUV eu euv2).arcDart i)
          = M.tail (K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCastD AUV eu euv2).len := by rw [daCastD_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailUV ⟨j, hjlen⟩⟩
  have htailVU_fwd : ∀ j : ℕ, (hj : j < kb) →
      ∃ i : Fin (daCastD AVU ev evu2).len,
        M.tail ((daCastD AVU ev evu2).arcDart i)
          = M.tail (K.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro j hj
    have hjlen : j < (daCastD AVU ev evu2).len := by rw [daCastD_len]; exact hj
    exact ⟨⟨j, hjlen⟩, htailVU ⟨j, hjlen⟩⟩
  have htailUV_bwd : ∀ i : Fin (daCastD AUV eu euv2).len,
      ∃ j : ℕ, j < kf ∧
        M.tail ((daCastD AUV eu euv2).arcDart i)
          = M.tail (K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kf := lt_of_lt_of_eq i.2 (daCastD_len AUV eu euv2)
    exact ⟨i.1, hi, htailUV i⟩
  have htailVU_bwd : ∀ i : Fin (daCastD AVU ev evu2).len,
      ∃ j : ℕ, j < kb ∧
        M.tail ((daCastD AVU ev evu2).arcDart i)
          = M.tail (K.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i
    have hi : i.1 < kb := lt_of_lt_of_eq i.2 (daCastD_len AVU ev evu2)
    exact ⟨i.1, hi, htailVU i⟩
  -- covering and disjointness of the two runs' tails (no length-≥2 needed)
  have hmap : (K.darts.map M.tail).Nodup := by
    have := hK; rwa [K.vertices_eq] at this
  have covering : ∀ {w : M.Vertex}, w ∈ K.vertices →
      (∃ i, M.tail ((daCastD AUV eu euv2).arcDart i) = w) ∨
      (∃ i, M.tail ((daCastD AVU ev evu2).arcDart i) = w) ∨ w = u ∨ w = v := by
    intro w hw
    obtain ⟨q, hqt⟩ := K.exists_pos_of_isBoundaryVertex hw
    rcases hcov q.1 q.2 with ⟨j, hj, hjq⟩ | ⟨j, hj, hjq⟩
    · left
      obtain ⟨i, hi⟩ := htailUV_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) = K.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
    · right; left
      obtain ⟨i, hi⟩ := htailVU_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : K.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega)) = K.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
  have disjoint : ∀ {w : M.Vertex},
      (∃ i, M.tail ((daCastD AUV eu euv2).arcDart i) = w) →
      (∃ i, M.tail ((daCastD AVU ev evu2).arcDart i) = w) → w = u ∨ w = v := by
    rintro w ⟨i, hiw⟩ ⟨i', hi'w⟩
    obtain ⟨j, hj, hjeq⟩ := htailUV_bwd i
    obtain ⟨j', hj', hj'eq⟩ := htailVU_bwd i'
    have heq : M.tail (K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)))
        = M.tail (K.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega))) := by
      rw [← hjeq, ← hj'eq, hiw, hi'w]
    have hposeq : (pu + j) % L = (pv + j') % L := by
      have hmem1 : K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) ∈ K.darts :=
        List.getElem_mem _
      have hmem2 : K.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) ∈ K.darts :=
        List.getElem_mem _
      have hdarts : K.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega))
          = K.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega)) :=
        List.inj_on_of_nodup_map hmap hmem1 hmem2 heq
      exact (K.normalized.nodup.getElem_inj_iff).mp hdarts
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
  -- length-≥2 from non-adjacency (only needed inside `internal_of_proper`)
  have hkf2_of_proper : s(u, v) ∉ K.edges → 2 ≤ kf := by
    intro hnbe
    rcases Nat.lt_or_ge kf 2 with hlt | hge
    · exfalso
      have hkf1' : kf = 1 := by omega
      apply not_consecutive_of_nonBoundaryEdge K hnbe hpu hpv eu ev
      rw [show (pu + 1) % L = (pu + kf) % L from by rw [hkf1'], hpfkf]
    · exact hge
  have hkb2_of_proper : s(u, v) ∉ K.edges → 2 ≤ kb := by
    intro hnbe
    rcases Nat.lt_or_ge kb 2 with hlt | hge
    · exfalso
      have hkb1' : kb = 1 := by omega
      have hnbe' : ¬ K.IsBoundaryEdge s(v, u) := by rw [Sym2.eq_swap]; exact hnbe
      exact not_consecutive_of_nonBoundaryEdge K hnbe' hpv hpu ev eu
        (by rw [show (pv + 1) % L = (pv + kb) % L from by rw [hkb1'], hpvkb])
    · exact hge
  refine
    { path₁ := bpOfDDA (daCastD AUV eu euv2)
      path₂ := bpOfDDA (daCastD AVU ev evu2)
      path₁_boundary_vertices := fun {w} hw => bpOfDDA_boundary_vertices (daCastD AUV eu euv2) hv hw
      path₂_boundary_vertices := fun {w} hw => bpOfDDA_boundary_vertices (daCastD AVU ev evu2) hu hw
      boundary_vertices_covered := ?_
      internally_disjoint := ?_
      path₁_internal_of_proper := ?_
      path₂_internal_of_proper := ?_ }
  · intro w
    constructor
    · intro hw
      rcases covering hw with ⟨i, hi⟩ | ⟨i, hi⟩ | hwu | hwv
      · left
        rw [bpOfDDA_vertices, List.mem_append]
        refine Or.inl ?_
        rw [← hi]
        exact List.mem_map_of_mem (by
          rw [DataDartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange i))
      · right
        rw [bpOfDDA_vertices, List.mem_append]
        refine Or.inl ?_
        rw [← hi]
        exact List.mem_map_of_mem (by
          rw [DataDartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange i))
      · left
        rw [bpOfDDA_vertices, List.mem_append]
        refine Or.inl ?_
        have hu_tail : M.tail ((daCastD AUV eu euv2).arcDart (daCastD AUV eu euv2).firstIdx) = w :=
          (daCastD AUV eu euv2).tail_first.trans hwu.symm
        have hmem : M.tail ((daCastD AUV eu euv2).arcDart (daCastD AUV eu euv2).firstIdx)
            ∈ (daCastD AUV eu euv2).dartList.map M.tail :=
          List.mem_map_of_mem (by
            rw [DataDartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange _))
        exact hu_tail ▸ hmem
      · left
        rw [bpOfDDA_vertices, List.mem_append]
        exact Or.inr (by rw [hwv]; exact List.mem_singleton_self _)
    · intro hw
      rcases hw with hw | hw
      · exact bpOfDDA_boundary_vertices (daCastD AUV eu euv2) hv hw
      · exact bpOfDDA_boundary_vertices (daCastD AVU ev evu2) hu hw
  · intro w hw1 hw2
    obtain ⟨i, hi⟩ := bpOfDDA_internal_tail (daCastD AUV eu euv2) hw1
    obtain ⟨i', hi'⟩ := bpOfDDA_internal_tail (daCastD AVU ev evu2) hw2
    have hwuv : w = u ∨ w = v := disjoint ⟨i, hi⟩ ⟨i', hi'⟩
    have hwu : w ≠ u := (bpOfDDA (daCastD AUV eu euv2)).internalVertexNeStartD hw1
    have hwv : w ≠ v := (bpOfDDA (daCastD AUV eu euv2)).internalVertexNeEndD hw1
    rcases hwuv with h' | h'
    · exact hwu h'
    · exact hwv h'
  · intro hnbe
    exact bpOfDDA_hasInternal (daCastD AUV eu euv2)
      (by rw [daCastD_len]; exact hkf2_of_proper hnbe)
  · intro hnbe
    exact bpOfDDA_hasInternal (daCastD AVU ev evu2)
      (by rw [daCastD_len]; exact hkb2_of_proper hnbe)

/-- **Promote a core + `VertexNodup` to a full `BoundaryCycle`** (the `arcSplit`
certificate is derived from simplicity by `arcSplit_of_nodup`). -/
noncomputable def toBoundaryCycle (K : BoundaryCycleData M f) (hK : K.vertices.Nodup) :
    BoundaryCycle M f :=
  { toBoundaryCycleData := K
    arcSplit := fun u v hne hu hv => K.arcSplit_of_nodup hK hne hu hv }

end BoundaryCycleData

end CombMap

end ProofsInTheBook.PlanarMap

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.BoundaryCycleData.arcSplit_of_nodup
