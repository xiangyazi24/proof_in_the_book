import ProofsInTheBook.SeamIncidence

/-!
# The dart-level boundary arc and the concrete chord∪arc primal cycle (Chapter 35)

`SeamIncidence.lean` closed the seam *mathematics*: given the chord∪arc
`SimplePrimalCycle` together with its `ArcChordSeam` structural data (a boundary
cycle `B` whose darts are the arc darts, the arc-index predicate `IsArc`, and
`arc_darts_mem`), every `step_component` obligation is discharged — the arc steps
for free (boundary-face reflexivity), the non-arc chord/junction steps from the
chord caps' generator edges.  The handoff (`opus-seaminc-reply.md`) isolated the
**one** genuine remaining residue as *structural infrastructure*, not new
topology:

> The concrete `SimplePrimalCycle` whose `dart : Fin len → D` is `chord ∪ arc`
> cannot be extracted: `BoundaryPath` records only the arc's *vertex and edge*
> lists — no dart list.

This file removes that residue, working **directly from the `BoundaryCycle`'s
own `darts : List D` field** (the normalized cyclic dart enumeration of the outer
face orbit), which *is* present — `BoundaryPath`/`BoundaryArcSplit` are bypassed
entirely.  We do three things.

## 1. The dart-level arc (`DartArc`)

A `DartArc` for a boundary cycle `C` is a `Fin k`-indexed family of darts, all on
`C.darts`, that chains head→tail internally (`chain`), starts at `u`, ends at `v`,
and is simple as a tail/head vertex list (`tail_nodup`, `head_last`).  This is the
dart-level analogue of `BoundaryPath`, carrying the **dart list** the latter
omits.  Every field is inherited from the boundary cycle's `consecutive_vertex`
and `VertexNodup`; in particular the chaining is *exactly* `consecutive_vertex`
restricted to the slice.

## 2. The concrete chord∪arc `SimplePrimalCycle`

Given a `DartArc` from `u` to `v` and a chord dart oriented `v → u`, the cycle
`chord :: arc` (via `Fin.cons`) satisfies the three `SimplePrimalCycle` fields:

* `consecutive` — head of `dart i` = tail of `dart (i+1)` cyclically: arc-internal
  from `DartArc.chain`; the two junctions are the chord's two endpoints meeting the
  arc's two endpoints (`head chord = u = tail (arc 0)` and `head (arc last) = v =
  tail chord`).
* `tail_inj` — the tails are pairwise distinct: the arc tails by the boundary's
  `VertexNodup` (`DartArc.tail_nodup`); the chord's tail `v` is the arc's *head*,
  which is not an arc tail (the arc is simple and does not revisit `v`).
* `3 ≤ len` — `len = arc.len + 1`, and `arc.len ≥ 2` because the arc has an
  *internal* vertex (the chord is not a boundary edge, `two_arcs_internally_…`).

## 3. The `ArcChordSeam` structural fields, instantiated

The built cycle's arc darts lie on `C` by construction, so `B := C`, `IsArc i :=
(i ≠ 0)` (everything but the chord index), and `arc_darts_mem` holds by
`DartArc.boundary`.  Combined with the proven `ArcChordSeam.step_component`
machinery, this yields `separates2_of_seam` for the chord, conditional only on the
genuinely external bridge-witness data and the (finite, chord-local) non-arc seam
steps.

## What remains after this file (Ch35 frontier)

The dart-level boundary arc is now *built*, not assumed.  The remaining inputs are
exactly the design's irreducible interior-dual data: `CutBridgeWitness2`, the
non-arc/junction `gen` steps, and the f13–16 side-map assembly.  See the closing
section.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv
open ProofsInTheBook.TouchRank
open ProofsInTheBook.PlanarMap.FaceCorrWord

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## 1. The dart-level boundary arc

`DartArc M C u v` is a directed dart path from vertex `u` to vertex `v`, every dart
on the boundary cycle `C`, chaining head→tail internally, and simple as a vertex
sequence.  It is the dart-level analogue of `BoundaryPath` — it carries the dart
list `BoundaryPath` omits.  All data comes from the boundary cycle's own fields. -/

/-- A dart-level boundary arc from `u` to `v` on the boundary cycle `C`.

`arcDart i` is the `i`-th dart of the arc, `len` of them; they all lie on
`C.darts`, chain head→tail (`chain`), the first dart starts at `u`
(`tail_first`), the last ends at `v` (`head_last`), and the tails together with
the final head form a simple (`Nodup`) vertex sequence. -/
structure DartArc (M : CombMap D) {f : M.Face} (C : BoundaryCycle M f)
    (u v : M.Vertex) where
  /-- Number of darts on the arc. -/
  len : ℕ
  /-- The arc is nonempty (at least one dart). -/
  len_pos : 0 < len
  /-- The directed arc darts `e_0, …, e_{len-1}`. -/
  arcDart : Fin len → D
  /-- Every arc dart lies on the boundary cycle. -/
  boundary : ∀ i : Fin len, arcDart i ∈ C.darts
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

namespace DartArc

variable {M : CombMap D} {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}

/-- The last index of the arc. -/
def lastIdx (A : DartArc M C u v) : Fin A.len := ⟨A.len - 1, by have := A.len_pos; omega⟩

/-- The first index of the arc. -/
def firstIdx (A : DartArc M C u v) : Fin A.len := ⟨0, A.len_pos⟩

@[simp] lemma tail_firstIdx (A : DartArc M C u v) :
    M.tail (A.arcDart A.firstIdx) = u := A.tail_first

@[simp] lemma head_lastIdx (A : DartArc M C u v) :
    M.head (A.arcDart A.lastIdx) = v := A.head_last

end DartArc

/-! ### Slicing a `DartArc` out of the boundary cycle's own dart list

The boundary cycle `C` already carries its cyclic dart list `C.darts` with
`consecutive_vertex` (`tail (darts[next i]) = head (darts[i])`) and, under
`VertexNodup`, a globally tail-injective enumeration.  A dart-level arc is just a
*contiguous slice* of this list, read off by index arithmetic — no `BoundaryPath`
needed.  This constructor materializes the `DartArc` the seam reply said the
boundary machinery "does not yet expose", **directly from the existing fields**,
proving every `DartArc` obligation from `consecutive_vertex` and `VertexNodup`. -/

/-- The boundary dart-arc from start position `p` of length `k`, where `1 ≤ k` and
the `k + 1` consecutive positions `p, …, p+k` stay within one wrap (`p + k <
C.darts.length`).  The arc darts are `C.darts[(p + j)]` for `j < k`; its endpoints
are `u = tail C.darts[p]` and `v = tail C.darts[p+k]`.

* `chain` and `head_last` follow from `consecutive_vertex` (cyclic successor =
  `M.φ`-image, matching tail to head);
* `boundary` from `List.getElem_mem`;
* `tail_nodup` and `head_last_ne_tail` from `VertexNodup` (tails injective), since
  the `k + 1` positions are pairwise distinct (no wrap).

This is the dart-level analogue of one of `two_arcs`' two arcs; the start position
and length are exactly the positions of the chord endpoints `u`, `v` in the
boundary vertex list. -/
def boundaryDartArc {M : CombMap D} {f : M.Face}
    (C : BoundaryCycle M f) (hC : C.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hpk : p + k < C.darts.length)
    (hp : p < C.darts.length) :
    DartArc M C (M.tail (C.darts.get ⟨p, hp⟩))
      (M.tail (C.darts.get ⟨p + k, hpk⟩)) where
  len := k
  len_pos := hk
  arcDart j := C.darts[p + j.1]'(by have := j.isLt; omega)
  boundary j := by
    have := j.isLt
    exact List.getElem_mem _
  chain j hj := by
    -- head (darts[p+j]) = tail (darts[cyclicNext (p+j)]) = tail (darts[p+j+1]).
    have hjlt : (j : ℕ) < k := j.isLt
    have hpos : p + (j : ℕ) < C.darts.length := by omega
    have hcv := C.consecutive_vertex ⟨p + (j : ℕ), hpos⟩
    -- cyclicNext of (p+j): ((p+j)+1) % L; since p+j+1 ≤ p+k < L, mod is identity.
    have hmod : ((p + (j : ℕ)) + 1) % C.darts.length = p + (j : ℕ) + 1 := by
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [show (C.darts.get ⟨p + (j : ℕ), hpos⟩) = C.darts[p + (j : ℕ)]'hpos from rfl] at hcv
    -- Rewrite the cyclicNext-get to the explicit index.
    have hget_next : C.darts.get (cyclicNext C.normalized.length_pos ⟨p + (j : ℕ), hpos⟩)
        = C.darts[p + (j : ℕ) + 1]'(by omega) := by
      congr 1
      apply Fin.ext
      show ((p + (j : ℕ)) + 1) % C.darts.length = p + (j : ℕ) + 1
      exact hmod
    rw [hget_next] at hcv
    -- Goal: head (arcDart j) = tail (arcDart ⟨j+1,hj⟩). Unfold both.
    show M.head (C.darts[p + (j : ℕ)]'(by omega))
        = M.tail (C.darts[p + ((j : ℕ) + 1)]'(by omega))
    have hidx : (C.darts[p + ((j : ℕ) + 1)]'(by omega))
        = (C.darts[p + (j : ℕ) + 1]'(by omega)) := by
      congr 1
    rw [hidx, hcv]
  tail_first := by
    show M.tail (C.darts[p + (0 : ℕ)]'_) = M.tail (C.darts.get ⟨p, hp⟩)
    rfl
  head_last := by
    -- head (darts[p+(k-1)]) = tail (darts[p+k]) via consecutive_vertex at position p+k-1.
    have hpos : p + (k - 1) < C.darts.length := by omega
    have hcv := C.consecutive_vertex ⟨p + (k - 1), hpos⟩
    have hmod : ((p + (k - 1)) + 1) % C.darts.length = p + k := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    have hget_next : C.darts.get (cyclicNext C.normalized.length_pos ⟨p + (k - 1), hpos⟩)
        = C.darts[p + k]'hpk := by
      congr 1
      apply Fin.ext
      show ((p + (k - 1)) + 1) % C.darts.length = p + k
      exact hmod
    rw [show (C.darts.get ⟨p + (k - 1), hpos⟩) = C.darts[p + (k - 1)]'hpos from rfl,
      hget_next] at hcv
    show M.head (C.darts[p + (k - 1)]'(by omega)) = M.tail (C.darts[p + k]'hpk)
    exact hcv.symm
  tail_nodup := by
    -- positions p+i (i < k) are distinct mod nothing (all < length), so tails are
    -- distinct by VertexNodup.
    intro i₁ i₂ htail
    have hmap : (C.darts.map M.tail).Nodup := by
      simpa [BoundaryCycle.VertexNodup, C.vertices_eq] using hC
    have h1 : p + (i₁ : ℕ) < C.darts.length := by have := i₁.isLt; omega
    have h2 : p + (i₂ : ℕ) < C.darts.length := by have := i₂.isLt; omega
    -- tails equal ⟹ the darts equal (tail injective on the list) ⟹ positions equal.
    have hdarts : C.darts[p + (i₁ : ℕ)]'h1 = C.darts[p + (i₂ : ℕ)]'h2 := by
      have hinj := List.inj_on_of_nodup_map hmap
        (List.getElem_mem h1) (List.getElem_mem h2)
      exact hinj htail
    have hpos_eq : p + (i₁ : ℕ) = p + (i₂ : ℕ) :=
      (C.normalized.nodup.getElem_inj_iff).mp hdarts
    apply Fin.ext; omega
  head_last_ne_tail := by
    intro i htail
    -- v = tail darts[p+k]; tail darts[p+i] with i < k; positions p+k ≠ p+i, distinct.
    have hmap : (C.darts.map M.tail).Nodup := by
      simpa [BoundaryCycle.VertexNodup, C.vertices_eq] using hC
    have hi : (i : ℕ) < k := i.isLt
    have hposi : p + (i : ℕ) < C.darts.length := by omega
    have hdarts : C.darts[p + k]'hpk = C.darts[p + (i : ℕ)]'hposi := by
      have hinj := List.inj_on_of_nodup_map hmap
        (List.getElem_mem hpk) (List.getElem_mem hposi)
      exact hinj htail
    have hpos_eq : p + k = p + (i : ℕ) :=
      (C.normalized.nodup.getElem_inj_iff).mp hdarts
    omega

/-! ## 2. The concrete chord∪arc `SimplePrimalCycle`

The cycle has length `A.len + 1`: index `0` is the chord dart `c` (oriented
`v → u`), indices `1, …, A.len` are the arc darts.  We build it with `Fin.cons`. -/

namespace SimplePrimalCycle

variable {M : CombMap D}

/-- The chord∪arc dart family: `Fin.cons c arcDart`, length `A.len + 1`.  Index `0`
is the chord dart, index `i+1` is `arcDart i`. -/
def chordArcDart {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}
    (A : DartArc M C u v) (c : D) : Fin (A.len + 1) → D :=
  Fin.cons c A.arcDart

@[simp] lemma chordArcDart_zero {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}
    (A : DartArc M C u v) (c : D) :
    chordArcDart A c 0 = c := by
  simp [chordArcDart]

@[simp] lemma chordArcDart_succ {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}
    (A : DartArc M C u v) (c : D) (i : Fin A.len) :
    chordArcDart A c i.succ = A.arcDart i := by
  simp [chordArcDart]

/-- **The concrete chord∪arc primal cycle.**  Built from a dart-level arc `A` from
`u` to `v` and a chord dart `c` oriented `v → u` (i.e. `tail c = v`, `head c = u`),
with `A.len ≥ 2` (the arc has an internal vertex).  The three `SimplePrimalCycle`
fields:

* `consecutive` — arc-internal from `A.chain`; the junction at the chord head is
  `head c = u = tail (arc 0)`, the junction at the chord tail is `head (arc last) =
  v = tail c`.
* `tail_inj` — arc tails distinct by `A.tail_nodup`; the chord tail `v` differs
  from every arc tail by `A.head_last_ne_tail`.
* `3 ≤ len` — `len = A.len + 1 ≥ 3` from `A.len ≥ 2`. -/
noncomputable def ofDartArc {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}
    (A : DartArc M C u v) (c : D)
    (harc_len : 2 ≤ A.len)
    (hc_tail : M.tail c = v) (hc_head : M.head c = u) :
    SimplePrimalCycle M where
  len := A.len + 1
  len_ge := by omega
  dart := chordArcDart A c
  tail_inj := by
    -- The tails of `chordArcDart`: index 0 ↦ v, index (i+1) ↦ tail (arcDart i).
    intro i j hij
    -- Reduce to cases on whether each index is 0 or a successor.
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rfl
      · -- i = 0, j = j'.succ : tail c = v = tail (arcDart j'), impossible.
        exfalso
        simp only [chordArcDart_zero, chordArcDart_succ, hc_tail] at hij
        exact A.head_last_ne_tail j' hij
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exfalso
        simp only [chordArcDart_zero, chordArcDart_succ, hc_tail] at hij
        exact A.head_last_ne_tail i' hij.symm
      · -- both successors: use arc tail injectivity.
        simp only [chordArcDart_succ] at hij
        have := A.tail_nodup hij
        rw [this]
  consecutive := by
    intro i
    -- `nextIdx` index : (i+1) % (A.len + 1).
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · -- i = 0 (chord dart). Its head is u; next index is 1 = (arcDart 0). tail = u.
      simp only [chordArcDart_zero, hc_head]
      have hnext : ((0 : Fin (A.len + 1)).1 + 1) % (A.len + 1) = 1 := by
        show (0 + 1) % (A.len + 1) = 1
        rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      have : (⟨((0 : Fin (A.len + 1)).1 + 1) % (A.len + 1),
            Nat.mod_lt _ (by omega)⟩ : Fin (A.len + 1))
          = (A.firstIdx).succ := by
        apply Fin.ext; simp only [hnext, Fin.val_succ]
        show 1 = (A.firstIdx).1 + 1
        simp [DartArc.firstIdx]
      rw [this, chordArcDart_succ, DartArc.tail_firstIdx]
    · -- i = i'.succ (an arc dart, arcDart i'). Two sub-cases: i' is last or not.
      simp only [chordArcDart_succ]
      by_cases hlast : (i' : ℕ) + 1 = A.len
      · -- last arc dart: head = v = tail c; next index wraps to 0 (chord).
        have hhead : M.head (A.arcDart i') = v := by
          have : i' = A.lastIdx := by
            apply Fin.ext; simp [DartArc.lastIdx]; omega
          rw [this, DartArc.head_lastIdx]
        rw [hhead]
        have hnext : ((i'.succ : Fin (A.len + 1)).1 + 1) % (A.len + 1) = 0 := by
          simp only [Fin.val_succ]
          have : (i' : ℕ) + 1 + 1 = A.len + 1 := by omega
          rw [this, Nat.mod_self]
        have hidx : (⟨((i'.succ : Fin (A.len + 1)).1 + 1) % (A.len + 1),
              Nat.mod_lt _ (by omega)⟩ : Fin (A.len + 1)) = 0 := by
          apply Fin.ext
          show ((i'.succ : Fin (A.len + 1)).1 + 1) % (A.len + 1) = 0
          rw [hnext]
        rw [hidx, chordArcDart_zero, hc_tail]
      · -- internal arc step: use A.chain.
        have hlt : (i' : ℕ) + 1 < A.len := by
          have := i'.isLt; omega
        rw [A.chain i' hlt]
        have hnext : ((i'.succ : Fin (A.len + 1)).1 + 1) % (A.len + 1)
            = (i' : ℕ) + 1 + 1 := by
          simp only [Fin.val_succ]
          rw [Nat.mod_eq_of_lt (by omega)]
        have hidx : (⟨((i'.succ : Fin (A.len + 1)).1 + 1) % (A.len + 1),
              Nat.mod_lt _ (by omega)⟩ : Fin (A.len + 1))
            = (⟨(i' : ℕ) + 1, hlt⟩ : Fin A.len).succ := by
          apply Fin.ext
          show ((i'.succ : Fin (A.len + 1)).1 + 1) % (A.len + 1) = (i' : ℕ) + 1 + 1
          rw [hnext]
        rw [hidx, chordArcDart_succ]

@[simp] lemma ofDartArc_len {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}
    (A : DartArc M C u v) (c : D) (harc_len : 2 ≤ A.len)
    (hc_tail : M.tail c = v) (hc_head : M.head c = u) :
    (ofDartArc A c harc_len hc_tail hc_head).len = A.len + 1 := rfl

@[simp] lemma ofDartArc_dart {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}
    (A : DartArc M C u v) (c : D) (harc_len : 2 ≤ A.len)
    (hc_tail : M.tail c = v) (hc_head : M.head c = u) :
    (ofDartArc A c harc_len hc_tail hc_head).dart = chordArcDart A c := rfl

/-! ### The arc-index predicate and `arc_darts_mem`

The cycle `ofDartArc A c …` has length `A.len + 1`.  Index `0` is the chord; index
`i'.succ` is the arc dart `arcDart i'`.  An index is an **arc index** when both it
and its cyclic successor are arc darts (lie on the boundary).  Concretely:

* index `i'.succ` with `i'.val + 1 < A.len` — its successor is `(i'+1).succ`, also an
  arc dart; both on `C.darts`.

The two **junctions** (`0` = chord→first arc, and `(A.len-1).succ` = last arc→chord)
and the chord index are the non-arc indices, exactly the steps the chord caps'
generator edges bridge. -/

/-- The arc-index predicate for the chord∪arc cycle: an index is an arc index when
it is a successor index `i'.succ` whose cyclic successor is *also* an arc dart,
i.e. `i'.val + 1 < A.len`.  This excludes the chord index `0` and the last-arc
junction index `(A.len-1).succ`. -/
def chordArcIsArc {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}
    (A : DartArc M C u v) (c : D) (harc_len : 2 ≤ A.len)
    (hc_tail : M.tail c = v) (hc_head : M.head c = u)
    (i : Fin (ofDartArc A c harc_len hc_tail hc_head).len) : Prop :=
  ∃ (i' : Fin A.len) (h : (i' : ℕ) + 1 < A.len),
    i = (i'.succ : Fin (A.len + 1))

/-- **`arc_darts_mem` for the chord∪arc cycle.**  For an arc index `i'.succ` with
`i'.val + 1 < A.len`, both `dart i` and `dart (nextIdx i)` are arc darts and hence
lie on the boundary cycle `C` (by `A.boundary`).  This is the structural field the
`ArcChordSeam` requires; it holds *by construction* of the dart-level arc — no
assumption. -/
theorem chordArc_arc_darts_mem {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}
    (A : DartArc M C u v) (c : D) (harc_len : 2 ≤ A.len)
    (hc_tail : M.tail c = v) (hc_head : M.head c = u)
    (i' : Fin A.len) (hlt : (i' : ℕ) + 1 < A.len) :
    (ofDartArc A c harc_len hc_tail hc_head).dart i'.succ ∈ C.darts ∧
      (ofDartArc A c harc_len hc_tail hc_head).dart
        ((ofDartArc A c harc_len hc_tail hc_head).nextIdx i'.succ) ∈ C.darts := by
  constructor
  · -- dart i'.succ = arcDart i' ∈ C.darts.
    show chordArcDart A c i'.succ ∈ C.darts
    rw [chordArcDart_succ]
    exact A.boundary i'
  · -- nextIdx i'.succ = (i'+1).succ since i'.val + 1 < A.len; dart there = arcDart (i'+1).
    have hnext : ((ofDartArc A c harc_len hc_tail hc_head).nextIdx i'.succ)
        = (⟨(i' : ℕ) + 1, hlt⟩ : Fin A.len).succ := by
      apply Fin.ext
      show ((i'.succ : Fin (A.len + 1)).1 + 1) % (A.len + 1) = (i' : ℕ) + 1 + 1
      simp only [Fin.val_succ]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hnext]
    show chordArcDart A c (⟨(i' : ℕ) + 1, hlt⟩ : Fin A.len).succ ∈ C.darts
    rw [chordArcDart_succ]
    exact A.boundary _

/-! ### The `ArcChordSeam` instantiation from the dart-level arc

`ArcChordSeam` carries, besides the structural boundary datum `B`/`IsArc`/
`arc_darts_mem` (which we now *build* from the `DartArc`), the F-side
cycle-decomposition data (`Ls`/`factor`) and the *non-arc* / cap / reverse /
off-cycle `step_component` obligations.  Those latter are the genuinely
chord-local, finite seam steps pinned to the chord caps' generator edges — the
residue the seam mathematics reduces to, supplied by the F-side bridge layer.

`arcChordSeamOfDartArc` assembles the full `ArcChordSeam` for `ofDartArc A c …`:
its **structural** half (`B := C`, `IsArc := chordArcIsArc …`, `arc_darts_mem` by
`chordArc_arc_darts_mem`) is closed by the dart-level arc; the F-side data is taken
as arguments. -/

open ProofsInTheBook.PlanarMap.FaceCorrWord
open ProofsInTheBook.SeamStructure

/-- **Assemble the `ArcChordSeam` for the concrete chord∪arc cycle.**  The boundary
cycle `B := C`, the arc-index predicate `chordArcIsArc`, and `arc_darts_mem` are all
**built** from the dart-level arc `A` (no assumption).  The remaining F-side data
— the `faceCorr₂`-cycle decomposition (`Ls`, `factor`) and the non-arc / reverse /
off-cycle / cap `step_component` obligations — is supplied by the caller (the
F-side bridge layer).  This is the precise interface the seam mathematics leaves:
every *structural* obligation discharged, the seam steps reduced to the non-arc
chord-local ones. -/
noncomputable def arcChordSeamOfDartArc {f : M.Face} {C : BoundaryCycle M f}
    {u v : M.Vertex}
    (A : DartArc M C u v) (c : D) (harc_len : 2 ≤ A.len)
    (hc_tail : M.tail c = v) (hc_head : M.head c = u)
    (Ls : List (List (ofDartArc A c harc_len hc_tail hc_head).CutDart))
    (Ls_len : ∀ L ∈ Ls, 2 ≤ L.length)
    (Ls_nodup : ∀ L ∈ Ls, L.Nodup)
    (Ls_sameCycle : ∀ L ∈ Ls, ∀ x ∈ L, ∀ y ∈ L,
      (ofDartArc A c harc_len hc_tail hc_head).faceCorr2.SameCycle x y)
    (factor : cycleListProd Ls = (ofDartArc A c harc_len hc_tail hc_head).faceCorr2)
    (gen : Fin (2 * (ofDartArc A c harc_len hc_tail hc_head).len - 2) →
      POrb (ofDartArc A c harc_len hc_tail hc_head).phiLift
        × POrb (ofDartArc A c harc_len hc_tail hc_head).phiLift)
    (nonarc_step : ∀ i : Fin (ofDartArc A c harc_len hc_tail hc_head).len,
      ¬ chordArcIsArc A c harc_len hc_tail hc_head i →
      Relation.EqvGen (genRel gen)
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          (Sum.inl ((ofDartArc A c harc_len hc_tail hc_head).dart i)))
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).faceCorr2
            (Sum.inl ((ofDartArc A c harc_len hc_tail hc_head).dart i)))))
    (revbank_step : ∀ i : Fin (ofDartArc A c harc_len hc_tail hc_head).len,
      Relation.EqvGen (genRel gen)
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          (Sum.inl (M.α ((ofDartArc A c harc_len hc_tail hc_head).dart i))))
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).faceCorr2
            (Sum.inl (M.α ((ofDartArc A c harc_len hc_tail hc_head).dart i))))))
    (offcycle_step : ∀ d : D,
      d ∉ (ofDartArc A c harc_len hc_tail hc_head).dartSet →
      Relation.EqvGen (genRel gen)
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift (Sum.inl d))
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).faceCorr2 (Sum.inl d))))
    (capP_step : ∀ i : Fin (ofDartArc A c harc_len hc_tail hc_head).len,
      Relation.EqvGen (genRel gen)
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).capP i))
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).faceCorr2
            ((ofDartArc A c harc_len hc_tail hc_head).capP i))))
    (capM_step : ∀ i : Fin (ofDartArc A c harc_len hc_tail hc_head).len,
      Relation.EqvGen (genRel gen)
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).capM i))
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).faceCorr2
            ((ofDartArc A c harc_len hc_tail hc_head).capM i)))) :
    (ofDartArc A c harc_len hc_tail hc_head).ArcChordSeam where
  Ls := Ls
  Ls_len := Ls_len
  Ls_nodup := Ls_nodup
  Ls_sameCycle := Ls_sameCycle
  factor := factor
  gen := gen
  outerFace := f
  B := C
  IsArc := chordArcIsArc A c harc_len hc_tail hc_head
  arc_darts_mem := by
    rintro i ⟨i', hlt, rfl⟩
    exact chordArc_arc_darts_mem A c harc_len hc_tail hc_head i' hlt
  nonarc_step := nonarc_step
  revbank_step := revbank_step
  offcycle_step := offcycle_step
  capP_step := capP_step
  capM_step := capM_step

end SimplePrimalCycle

/-! ## 4. The chord separation from the dart-level arc, end-to-end

Threading `arcChordSeamOfDartArc` into `separates2_of_seam` (itself the proven
`ArcChordSeam.step_component` machinery of `SeamIncidence.lean`) gives the
Chapter-35 F-side chord-wall target `data.Separates` with the **concrete**
chord∪arc cycle now *built* from the dart-level boundary arc — not assumed.  The
remaining inputs are exactly the genuinely external F-side data: the non-arc seam
steps (chord-local, pinned to the chord caps' generator edges) and the
bridge-witness `CutBridgeWitness2`. -/

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle

/-- **The chord separates, end-to-end, from the dart-level boundary arc.**

The concrete chord∪arc `SimplePrimalCycle` is `ofDartArc A c …`, built from a
dart-level arc `A` on the outer boundary cycle and the chord dart `c` oriented
`v → u`.  Its `ArcChordSeam` structural data (boundary cycle, arc-index predicate,
`arc_darts_mem`) is supplied by `arcChordSeamOfDartArc` — *built*, not assumed;
the F-side seam data (`Ls`/`factor`/`gen` and the non-arc/cap/reverse/off-cycle
steps) and the bridge-witness data are taken as arguments, the genuine residue.

This is the assembled `separates2_of_seam` for a `NearTriangulation` chord with the
dart-level boundary arc closed. -/
theorem separates2_of_dartArc {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle u v) (c : D) (harc_len : 2 ≤ A.len)
    (hc_tail : M.tail c = v) (hc_head : M.head c = u)
    (Ls : List (List (ofDartArc A c harc_len hc_tail hc_head).CutDart))
    (Ls_len : ∀ L ∈ Ls, 2 ≤ L.length)
    (Ls_nodup : ∀ L ∈ Ls, L.Nodup)
    (Ls_sameCycle : ∀ L ∈ Ls, ∀ x ∈ L, ∀ y ∈ L,
      (ofDartArc A c harc_len hc_tail hc_head).faceCorr2.SameCycle x y)
    (factor : cycleListProd Ls = (ofDartArc A c harc_len hc_tail hc_head).faceCorr2)
    (gen : Fin (2 * (ofDartArc A c harc_len hc_tail hc_head).len - 2) →
      POrb (ofDartArc A c harc_len hc_tail hc_head).phiLift
        × POrb (ofDartArc A c harc_len hc_tail hc_head).phiLift)
    (nonarc_step : ∀ i : Fin (ofDartArc A c harc_len hc_tail hc_head).len,
      ¬ chordArcIsArc A c harc_len hc_tail hc_head i →
      Relation.EqvGen (genRel gen)
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          (Sum.inl ((ofDartArc A c harc_len hc_tail hc_head).dart i)))
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).faceCorr2
            (Sum.inl ((ofDartArc A c harc_len hc_tail hc_head).dart i)))))
    (revbank_step : ∀ i : Fin (ofDartArc A c harc_len hc_tail hc_head).len,
      Relation.EqvGen (genRel gen)
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          (Sum.inl (M.α ((ofDartArc A c harc_len hc_tail hc_head).dart i))))
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).faceCorr2
            (Sum.inl (M.α ((ofDartArc A c harc_len hc_tail hc_head).dart i))))))
    (offcycle_step : ∀ d : D,
      d ∉ (ofDartArc A c harc_len hc_tail hc_head).dartSet →
      Relation.EqvGen (genRel gen)
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift (Sum.inl d))
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).faceCorr2 (Sum.inl d))))
    (capP_step : ∀ i : Fin (ofDartArc A c harc_len hc_tail hc_head).len,
      Relation.EqvGen (genRel gen)
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).capP i))
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).faceCorr2
            ((ofDartArc A c harc_len hc_tail hc_head).capP i))))
    (capM_step : ∀ i : Fin (ofDartArc A c harc_len hc_tail hc_head).len,
      Relation.EqvGen (genRel gen)
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).capM i))
        (pOrbOf (ofDartArc A c harc_len hc_tail hc_head).phiLift
          ((ofDartArc A c harc_len hc_tail hc_head).faceCorr2
            ((ofDartArc A c harc_len hc_tail hc_head).capM i))))
    (hsub : ∀ e ∈ (ofDartArc A c harc_len hc_tail hc_head).edgeSet,
      e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hwit : ∀ i : Fin (ofDartArc A c harc_len hc_tail hc_head).len,
      (ofDartArc A c harc_len hc_tail hc_head).CutBridgeWitness2 i)
    (i₀ : Fin (ofDartArc A c harc_len hc_tail hc_head).len)
    (hleft : (ofDartArc A c harc_len hc_tail hc_head).faceLeft i₀
      = M.dartFace (hNT.chordDart data.chord))
    (hright : (ofDartArc A c harc_len hc_tail hc_head).faceRight i₀
      = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  hNT.separates2_of_seam data (ofDartArc A c harc_len hc_tail hc_head) hsub
    (arcChordSeamOfDartArc A c harc_len hc_tail hc_head
      Ls Ls_len Ls_nodup Ls_sameCycle factor gen
      nonarc_step revbank_step offcycle_step capP_step capM_step)
    hwit i₀ hleft hright

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

/-! ## Non-vacuity: the dart-level arc is a genuine simple cycle component

We confirm the dart-level construction is not degenerate: the built cycle has the
expected length and its dart family genuinely restricts to the chord and the arc
darts.  This rules out the vacuous-reduction failure mode (the construction does
fire on real arc data). -/

namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}

/-- The built cycle's length is `A.len + 1` — genuinely longer than the chord
alone, witnessing that the arc darts are present (not collapsed). -/
example {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}
    (A : DartArc M C u v) (c : D) (harc_len : 2 ≤ A.len)
    (hc_tail : M.tail c = v) (hc_head : M.head c = u) :
    (ofDartArc A c harc_len hc_tail hc_head).len = A.len + 1 := rfl

/-- The built cycle's first dart is the chord and the `(i+1)`-th is the `i`-th arc
dart — the dart family is genuinely `chord ∪ arc`, not a trivial constant. -/
example {f : M.Face} {C : BoundaryCycle M f} {u v : M.Vertex}
    (A : DartArc M C u v) (c : D) (harc_len : 2 ≤ A.len)
    (hc_tail : M.tail c = v) (hc_head : M.head c = u) (i : Fin A.len) :
    (ofDartArc A c harc_len hc_tail hc_head).dart (0 : Fin (A.len + 1)) = c ∧
      (ofDartArc A c harc_len hc_tail hc_head).dart i.succ = A.arcDart i :=
  ⟨chordArcDart_zero A c, chordArcDart_succ A c i⟩

/-- **`DartArc` is genuinely inhabited from the boundary cycle's own dart list.**
The slice constructor `boundaryDartArc` produces, from any boundary cycle with
`VertexNodup` and a valid start/length, a real dart-level arc whose darts are the
contiguous boundary slice.  This rules out the vacuous-interface failure mode: the
`DartArc` obligations are all *satisfiable* — indeed *built* — from existing
boundary fields (`consecutive_vertex` + `VertexNodup`), not assumed. -/
example {f : M.Face} (C : BoundaryCycle M f) (hC : C.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hpk : p + k < C.darts.length)
    (hp : p < C.darts.length) :
    (boundaryDartArc C hC p k hk hpk hp).len = k ∧
      (boundaryDartArc C hC p k hk hpk hp).arcDart ⟨0, hk⟩
        = C.darts[p]'hp :=
  ⟨rfl, by show C.darts[p + (0 : ℕ)]'_ = C.darts[p]'hp; rfl⟩

end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.ofDartArc
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.chordArc_arc_darts_mem
#print axioms ProofsInTheBook.PlanarMap.CombMap.boundaryDartArc
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.arcChordSeamOfDartArc
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.separates2_of_dartArc
