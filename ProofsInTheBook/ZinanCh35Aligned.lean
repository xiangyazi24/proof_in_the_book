import ProofsInTheBook.ZinanCh35ArcSide

/-!
# Chapter 35: discharging `ForwardRunAligned` by CONSTRUCTION — both confinements UNCONDITIONAL

`ZinanCh35ArcSide.lean` proved everything UNCONDITIONAL except the orientation predicates
`ForwardRunAligned₁/₂`: that the *free* arc-split label `data.arc.path₁/path₂` is aligned with the
backward/forward boundary run.  For an arbitrary `data : hNT.ChordSplitData u v` this is genuinely
not provable — `ChordSplitData.arc` is the free `BoundaryArcSplit` field supplied by
`outerCycle.arcSplit`, and nothing ties its `path₁`/`path₂` labelling to the chord-dart-derived side
orientation (`ZinanCh35BankOrient.bank_datum_substrate_symmetric`).

## The fix: a NORMALIZED `ChordSplitData` whose `arc` IS the forward/backward run

We *construct* a chord-split datum `normalizedChordSplitData h` whose `arc.path₂` is the
cyclically-forward `v → u` boundary run and whose `arc.path₁` is the backward `u → v` run, both built
directly from the boundary cycle's own dart list (`outerCycle.darts`).  For that datum
`ArcSideIdentification` holds **by construction**, and the two confinements become UNCONDITIONAL.

This is legitimate because `face₁`, `face₂`, `side₁`, `side₂`, `sideRegion₁`, `sideRegion₂`, and
`Separates` are defined from the chord dart alone — the `arc` field does *not* enter them.  So a
custom `arc` keeps every bank-side fact of `ZinanCh35ArcSide` valid, while pinning the labelling.

## Structure

* §1 — `bpOfDartArc`: a `BoundaryPath` from a `DartArc` (vertices = dart tails ++ terminal endpoint).
* §2 — the bank-side facts generalized to an ARBITRARY forward/backward `DartArc` (the C₂/C₁ bank
  theorem applied to the explicit run, avoiding the choice-recomputation of `fwdArc data`).
* §3 — the two complementary cyclic runs (`fwdRun`, `bwdRun`) built from explicit positions, with
  their tails partitioning the boundary vertices (`covering` + `internally_disjoint`).
* §4 — the normalized `BoundaryArcSplit` and `normalizedChordSplitData`.
* §5 — `ArcSideIdentification` for the normalized datum, and BOTH confinements, UNCONDITIONAL
  (modulo the proven separation hypothesis `Separates`, which is the chord-level keystone, not the
  arc orientation).

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Aligned

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35CycleBank
open ProofsInTheBook.ZinanCh35BankLabels
open ProofsInTheBook.ZinanCh35ArcDartRun

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}

/-! ## 0. Endpoint retyping casts -/

/-- Retype a `BoundaryPath`'s endpoints along equalities. -/
noncomputable def bpCast {a a' b b' : M.Vertex} (P : BoundaryPath M a b)
    (ha : a = a') (hb : b = b') : BoundaryPath M a' b' := ha ▸ hb ▸ P

@[simp] lemma bpCast_vertices {a a' b b' : M.Vertex} (P : BoundaryPath M a b)
    (ha : a = a') (hb : b = b') : (bpCast P ha hb).vertices = P.vertices := by
  subst ha; subst hb; rfl

@[simp] lemma bpCast_edges {a a' b b' : M.Vertex} (P : BoundaryPath M a b)
    (ha : a = a') (hb : b = b') : (bpCast P ha hb).edges = P.edges := by
  subst ha; subst hb; rfl

@[simp] lemma bpCast_internal {a a' b b' : M.Vertex} (P : BoundaryPath M a b)
    (ha : a = a') (hb : b = b') : (bpCast P ha hb).internalVertices = P.internalVertices := by
  subst ha; subst hb; rfl

/-- Retype a `DartArc`'s endpoints along equalities. -/
noncomputable def daCast {f : M.Face} {C : BoundaryCycle M f} {a a' b b' : M.Vertex}
    (A : DartArc M C a b) (ha : a = a') (hb : b = b') : DartArc M C a' b' := ha ▸ hb ▸ A

@[simp] lemma daCast_len {f : M.Face} {C : BoundaryCycle M f} {a a' b b' : M.Vertex}
    (A : DartArc M C a b) (ha : a = a') (hb : b = b') : (daCast A ha hb).len = A.len := by
  subst ha; subst hb; rfl

lemma daCast_arcDart {f : M.Face} {C : BoundaryCycle M f} {a a' b b' : M.Vertex}
    (A : DartArc M C a b) (ha : a = a') (hb : b = b') (i : Fin (daCast A ha hb).len) :
    M.tail ((daCast A ha hb).arcDart i)
      = M.tail (A.arcDart (Fin.cast (daCast_len A ha hb) i)) := by
  subst ha; subst hb; rfl

/-- The arc-dart of a casted dart-arc equals the original at the cast index. -/
lemma daCast_arcDart_eq {f : M.Face} {C : BoundaryCycle M f} {a a' b b' : M.Vertex}
    (A : DartArc M C a b) (ha : a = a') (hb : b = b') (i : Fin (daCast A ha hb).len) :
    (daCast A ha hb).arcDart i = A.arcDart (Fin.cast (daCast_len A ha hb) i) := by
  subst ha; subst hb; rfl

/-- **The tail of a casted cyclic dart-arc at index `i` is the cyclic-slice tail `darts[(p+i)%L]`.** -/
lemma daCast_cyclic_tail {f : M.Face} (C : BoundaryCycle M f) (hC : C.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hkL : k < C.darts.length) (hp : p < C.darts.length)
    {a' b' : M.Vertex}
    (ha : M.tail (C.darts[p]'hp) = a')
    (hb : M.tail (C.darts[(p + k) % C.darts.length]'(Nat.mod_lt _ (by omega))) = b')
    (i : Fin (daCast (C.cyclicDartArc hC p k hk hkL hp) ha hb).len) :
    M.tail ((daCast (C.cyclicDartArc hC p k hk hkL hp) ha hb).arcDart i)
      = M.tail (C.darts[(p + i.1) % C.darts.length]'(Nat.mod_lt _ (by omega))) := by
  rw [daCast_arcDart, BoundaryCycle.cyclicDartArc_arcDart]; rfl

/-! ## 1. A `BoundaryPath` from a `DartArc` -/

/-- **The `BoundaryPath` of a dart arc.**  Its vertices are the arc-dart tails followed by the
terminal endpoint `b`; its edges are the arc-dart graph edges.  Simplicity from `tail_nodup`
together with `head_last_ne_tail`. -/
noncomputable def bpOfDartArc {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) : BoundaryPath M a b where
  vertices := A.dartList.map M.tail ++ [b]
  edges := A.dartList.map M.dartEdge
  starts_at := by
    have hne : (A.dartList.map M.tail) ≠ [] := by simp [A.dartList_ne_nil]
    have h0 : 0 < A.dartList.length := by rw [DartArc.dartList_length]; exact A.len_pos
    rw [List.head?_append_of_ne_nil _ hne, List.head?_map, List.head?_eq_getElem?,
      List.getElem?_eq_getElem h0, A.dartList_getElem 0 A.len_pos]
    simp only [Option.map_some]; rw [A.tail_first]
  ends_at := by simp
  simple := by
    rw [List.nodup_append]
    refine ⟨?_, by simp, ?_⟩
    · rw [DartArc.dartList, List.map_map, List.nodup_map_iff_inj_on (List.nodup_finRange A.len)]
      intro i _ j _ hij; exact A.tail_nodup hij
    · intro x hx y hy
      rw [List.mem_singleton] at hy; subst hy
      rw [List.mem_map] at hx
      obtain ⟨d, hd, hdt⟩ := hx
      obtain ⟨i, hi⟩ := A.mem_dartList hd
      rw [← hi] at hdt
      exact fun hxb => A.head_last_ne_tail i (hxb ▸ hdt.symm)

@[simp] lemma bpOfDartArc_vertices {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) : (bpOfDartArc A).vertices = A.dartList.map M.tail ++ [b] := rfl

@[simp] lemma bpOfDartArc_edges {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) : (bpOfDartArc A).edges = A.dartList.map M.dartEdge := rfl

/-- The internal vertices of `bpOfDartArc A` are the tails of the arc darts with index `≥ 1`. -/
lemma bpOfDartArc_internal {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) :
    (bpOfDartArc A).internalVertices = (A.dartList.map M.tail).tail := by
  show (A.dartList.map M.tail ++ [b]).tail.dropLast = (A.dartList.map M.tail).tail
  have hne : (A.dartList.map M.tail) ≠ [] := by simp [A.dartList_ne_nil]
  rw [List.tail_append_of_ne_nil hne, List.dropLast_concat]

/-- Every vertex of `bpOfDartArc A` is a tail of an arc dart, or the terminal endpoint `b`. -/
lemma bpOfDartArc_mem_vertices {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) {w : M.Vertex} (hw : w ∈ (bpOfDartArc A).vertices) :
    (∃ i : Fin A.len, M.tail (A.arcDart i) = w) ∨ w = b := by
  rw [bpOfDartArc_vertices, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | hw
  · left
    rw [List.mem_map] at hw
    obtain ⟨d, hd, hdt⟩ := hw
    obtain ⟨i, hi⟩ := A.mem_dartList hd
    exact ⟨i, hi ▸ hdt⟩
  · right; exact hw

/-- An internal vertex of `bpOfDartArc A` is a tail of an arc dart. -/
lemma bpOfDartArc_internal_tail {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) {w : M.Vertex} (hw : w ∈ (bpOfDartArc A).internalVertices) :
    ∃ i : Fin A.len, M.tail (A.arcDart i) = w := by
  rw [bpOfDartArc_internal] at hw
  have hsub : w ∈ A.dartList.map M.tail := List.tail_subset _ hw
  rw [List.mem_map] at hsub
  obtain ⟨d, hd, hdt⟩ := hsub
  obtain ⟨i, hi⟩ := A.mem_dartList hd
  exact ⟨i, hi ▸ hdt⟩

/-- An arc-dart tail is a boundary vertex (`A`'s darts lie on the cycle). -/
lemma arcDart_tail_mem_vertices {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) (i : Fin A.len) : M.tail (A.arcDart i) ∈ C.vertices := by
  rw [C.vertices_eq]; exact List.mem_map_of_mem (A.boundary i)

/-- Every vertex of `bpOfDartArc A` is a boundary vertex, provided the terminal endpoint `b` is. -/
lemma bpOfDartArc_boundary_vertices {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) (hb : b ∈ C.vertices) {w : M.Vertex}
    (hw : w ∈ (bpOfDartArc A).vertices) : w ∈ C.vertices := by
  rcases bpOfDartArc_mem_vertices A hw with ⟨i, hi⟩ | hwb
  · rw [← hi]; exact arcDart_tail_mem_vertices A i
  · rw [hwb]; exact hb

/-- `bpOfDartArc A` has an internal vertex when `2 ≤ A.len`. -/
lemma bpOfDartArc_hasInternal {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}
    (A : DartArc M C a b) (hlen : 2 ≤ A.len) : (bpOfDartArc A).HasInternalVertex := by
  rw [BoundaryPath.hasInternalVertex_iff, bpOfDartArc_internal]
  -- (A.dartList.map M.tail).tail ≠ []: dartList has length A.len ≥ 2.
  intro hcontra
  have hlenlist : (A.dartList.map M.tail).length = A.len := by
    rw [List.length_map, DartArc.dartList_length]
  have htl : (A.dartList.map M.tail).tail.length = (A.dartList.map M.tail).length - 1 :=
    List.length_tail
  rw [hcontra] at htl
  simp only [List.length_nil] at htl
  omega

/-! ## 2. The bank-side facts for an ARBITRARY forward/backward run

We replicate the `ZinanCh35ArcSide` C₂ bank chain for an *arbitrary* dart arc `A` on the outer
cycle whose endpoints are `(head data.dart, tail data.dart)` (so `chord ∪ A` closes), avoiding the
choice-recomputation of `fwdArc data`.  Every step uses only that `A` is such a `DartArc` plus the
landed bank theorem; nothing references `data.arc`. -/

namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}

/-- `C₂[A] = chord ∪ A`, for an arbitrary forward run `A : DartArc (head dart) (tail dart)`. -/
noncomputable def C₂A (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    SimplePrimalCycle M :=
  SimplePrimalCycle.ofDartArc A data.dart hlen rfl rfl

lemma C₂A_dart_zero (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    (C₂A data A hlen).dart ⟨0, (C₂A data A hlen).len_pos⟩ = data.dart := by
  show SimplePrimalCycle.chordArcDart A data.dart ⟨0, (C₂A data A hlen).len_pos⟩ = data.dart
  exact SimplePrimalCycle.chordArcDart_zero _ _

lemma C₂A_faceRight_zero (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    (C₂A data A hlen).faceRight ⟨0, (C₂A data A hlen).len_pos⟩ = data.face₂ := by
  show M.dartFace (M.α ((C₂A data A hlen).dart ⟨0, (C₂A data A hlen).len_pos⟩))
      = M.dartFace (M.α data.dart)
  rw [C₂A_dart_zero]

lemma C₂A_edge_chord_or_boundary (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len)
    (i : Fin (C₂A data A hlen).len) :
    (C₂A data A hlen).edge i = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge ((C₂A data A hlen).edge i) := by
  have hedge : M.dartEdge data.dart = s(u, v) := hNT.chordDart_edge data.chord
  show M.dartEdge (SimplePrimalCycle.chordArcDart A data.dart i) = s(u, v) ∨
    hNT.outerCycle.IsBoundaryEdge (M.dartEdge (SimplePrimalCycle.chordArcDart A data.dart i))
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · left; rw [SimplePrimalCycle.chordArcDart_zero]; exact hedge
  · right
    rw [SimplePrimalCycle.chordArcDart_succ]
    show M.dartEdge (A.arcDart i') ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    exact List.mem_map_of_mem (A.boundary i')

lemma chord_mem_C₂A_edgeSet (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    (s(u, v) : Sym2 M.Vertex) ∈ (C₂A data A hlen).edgeSet := by
  rw [SimplePrimalCycle.mem_edgeSet_iff]
  refine ⟨⟨0, (C₂A data A hlen).len_pos⟩, ?_⟩
  show (s(u, v) : Sym2 M.Vertex) = M.dartEdge ((C₂A data A hlen).dart ⟨0, (C₂A data A hlen).len_pos⟩)
  rw [C₂A_dart_zero]; exact (hNT.chordDart_edge data.chord).symm

noncomputable def arcIdx₀A (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    Fin (C₂A data A hlen).len :=
  (A.firstIdx).succ

lemma faceLeft_arcIdx₀A (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    (C₂A data A hlen).faceLeft (arcIdx₀A data A hlen) = hNT.outerFace := by
  show M.dartFace (SimplePrimalCycle.chordArcDart A data.dart (A.firstIdx).succ) = hNT.outerFace
  rw [SimplePrimalCycle.chordArcDart_succ]
  exact (hNT.outerCycle.mem_darts_iff _).mp (A.boundary _)

noncomputable def bankC₂A (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    SimpleCycleBankTheorem M (C₂A data A hlen) :=
  simpleCycleBankTheorem_holds (C₂A data A hlen) hNT.sphere hNT.simpleGraph

lemma not_bankReach_face₂_outerFaceA (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len) :
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen)) data.face₂ hNT.outerFace := by
  intro hreach
  have hreach' : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen))
      ((C₂A data A hlen).faceRight ⟨0, (C₂A data A hlen).len_pos⟩)
      ((C₂A data A hlen).faceLeft (arcIdx₀A data A hlen)) := by
    rw [C₂A_faceRight_zero, faceLeft_arcIdx₀A]; exact hreach
  have hsym : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen))
      ((C₂A data A hlen).faceLeft (arcIdx₀A data A hlen))
      ((C₂A data A hlen).faceRight ⟨0, (C₂A data A hlen).len_pos⟩) :=
    Relation.ReflTransGen.symmetric
      (fun _ _ h => dualAvoidsCycleStep_symm (C₂A data A hlen) h) hreach'
  exact (bankC₂A data A hlen).left_right_sep (arcIdx₀A data A hlen)
    ⟨0, (C₂A data A hlen).len_pos⟩ hsym

lemma chordSplitAdj_imp_dualStepA (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len)
    {f g : M.Face} (h : hNT.ChordSplitAdj u v f g) :
    DualAvoidsCycleStep M (C₂A data A hlen) f g := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := h
  refine ⟨d, ?_, hdf, hdg⟩
  intro hmem
  rw [SimplePrimalCycle.mem_edgeSet_iff] at hmem
  obtain ⟨i, hi⟩ := hmem
  rcases C₂A_edge_chord_or_boundary data A hlen i with hc | hb
  · exact hch (by rw [hi, hc])
  · exact hbe (by rw [hi]; exact hb)

lemma chordSplitAdj_reach_imp_dualReachA (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len)
    {f g : M.Face} (h : Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g) :
    Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen)) f g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (chordSplitAdj_imp_dualStepA data A hlen hstep)

lemma bankReach_face₂_lifts_to_chordSplitAdjA (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len)
    {g : M.Face}
    (h : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen)) data.face₂ g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₂ g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail f g' hpre hstep ih =>
      obtain ⟨d, hdedge, hdf, hdg⟩ := hstep
      have hf_ne : f ≠ hNT.outerFace :=
        hNT.side_subset_nonouter data.face₂_not_outer (g := f) ih
      have hch : M.dartEdge d ≠ s(u, v) := by
        intro he; exact hdedge (he ▸ chord_mem_C₂A_edgeSet data A hlen)
      have hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
        intro hbedge
        rcases ProofsInTheBook.ZinanCh35InnerConn.boundaryEdge_dart_outer hbedge with ho | ho
        · exact hf_ne (hdf ▸ ho)
        · have hg'_outer : g' = hNT.outerFace := hdg ▸ ho
          apply not_bankReach_face₂_outerFaceA data A hlen
          have hbankf : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen))
              data.face₂ f := chordSplitAdj_reach_imp_dualReachA data A hlen ih
          have : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen)) data.face₂ g' :=
            hbankf.tail ⟨d, hdedge, hdf, hdg⟩
          rwa [hg'_outer] at this
      exact ih.tail ⟨d, hdf, hdg, hbe, hch⟩

/-- **The reverse-face side-2 fact for an ARBITRARY forward run** (generalizes
`ZinanCh35ArcSide.fwdArc_reverse_face_mem_side₂`).  For each arc dart of a run
`A : DartArc (head dart) (tail dart)`, the bounded reverse face lies in `side₂`. -/
theorem fwdRun_reverse_face_mem_side₂ (data : hNT.ChordSplitData u v)
    (A : DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart)) (hlen : 2 ≤ A.len)
    (i : Fin A.len) :
    M.dartFace (M.α (A.arcDart i)) ∈ data.side₂ := by
  have hface : (C₂A data A hlen).faceRight i.succ = M.dartFace (M.α (A.arcDart i)) := by
    show M.dartFace (M.α (SimplePrimalCycle.chordArcDart A data.dart i.succ))
        = M.dartFace (M.α (A.arcDart i))
    rw [SimplePrimalCycle.chordArcDart_succ]
  have hbank : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂A data A hlen))
      data.face₂ ((C₂A data A hlen).faceRight i.succ) := by
    rw [← C₂A_faceRight_zero data A hlen]
    exact (bankC₂A data A hlen).right_bank ⟨0, (C₂A data A hlen).len_pos⟩ i.succ
  rw [hface] at hbank
  exact bankReach_face₂_lifts_to_chordSplitAdjA data A hlen hbank

/-! ### The side-1 mirror, for an arbitrary backward run `B : DartArc (tail dart) (head dart)` -/

/-- `C₁[B] = chord(reversed) ∪ B`, for an arbitrary backward run `B`. -/
noncomputable def C₁B (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    SimplePrimalCycle M :=
  SimplePrimalCycle.ofDartArc B (M.α data.dart) hlen (by rw [M.tail_alpha]) (by rw [M.head_alpha])

lemma C₁B_dart_zero (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    (C₁B data B hlen).dart ⟨0, (C₁B data B hlen).len_pos⟩ = M.α data.dart := by
  show SimplePrimalCycle.chordArcDart B (M.α data.dart) ⟨0, (C₁B data B hlen).len_pos⟩ = M.α data.dart
  exact SimplePrimalCycle.chordArcDart_zero _ _

lemma C₁B_faceRight_zero (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    (C₁B data B hlen).faceRight ⟨0, (C₁B data B hlen).len_pos⟩ = data.face₁ := by
  show M.dartFace (M.α ((C₁B data B hlen).dart ⟨0, (C₁B data B hlen).len_pos⟩)) = M.dartFace data.dart
  rw [C₁B_dart_zero, M.alpha_alpha]

lemma C₁B_edge_chord_or_boundary (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len)
    (i : Fin (C₁B data B hlen).len) :
    (C₁B data B hlen).edge i = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge ((C₁B data B hlen).edge i) := by
  have hedge : M.dartEdge (M.α data.dart) = s(u, v) := by
    rw [M.dartEdge_alpha]; exact hNT.chordDart_edge data.chord
  show M.dartEdge (SimplePrimalCycle.chordArcDart B (M.α data.dart) i) = s(u, v) ∨
    hNT.outerCycle.IsBoundaryEdge (M.dartEdge (SimplePrimalCycle.chordArcDart B (M.α data.dart) i))
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · left; rw [SimplePrimalCycle.chordArcDart_zero]; exact hedge
  · right
    rw [SimplePrimalCycle.chordArcDart_succ]
    show M.dartEdge (B.arcDart i') ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    exact List.mem_map_of_mem (B.boundary i')

lemma chord_mem_C₁B_edgeSet (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    (s(u, v) : Sym2 M.Vertex) ∈ (C₁B data B hlen).edgeSet := by
  rw [SimplePrimalCycle.mem_edgeSet_iff]
  refine ⟨⟨0, (C₁B data B hlen).len_pos⟩, ?_⟩
  show (s(u, v) : Sym2 M.Vertex) = M.dartEdge ((C₁B data B hlen).dart ⟨0, (C₁B data B hlen).len_pos⟩)
  rw [C₁B_dart_zero, M.dartEdge_alpha]; exact (hNT.chordDart_edge data.chord).symm

noncomputable def arcIdx₀B (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    Fin (C₁B data B hlen).len :=
  (B.firstIdx).succ

lemma faceLeft_arcIdx₀B (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    (C₁B data B hlen).faceLeft (arcIdx₀B data B hlen) = hNT.outerFace := by
  show M.dartFace (SimplePrimalCycle.chordArcDart B (M.α data.dart) (B.firstIdx).succ) = hNT.outerFace
  rw [SimplePrimalCycle.chordArcDart_succ]
  exact (hNT.outerCycle.mem_darts_iff _).mp (B.boundary _)

noncomputable def bankC₁B (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    SimpleCycleBankTheorem M (C₁B data B hlen) :=
  simpleCycleBankTheorem_holds (C₁B data B hlen) hNT.sphere hNT.simpleGraph

lemma not_bankReach_face₁_outerFaceB (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len) :
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen)) data.face₁ hNT.outerFace := by
  intro hreach
  have hreach' : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen))
      ((C₁B data B hlen).faceRight ⟨0, (C₁B data B hlen).len_pos⟩)
      ((C₁B data B hlen).faceLeft (arcIdx₀B data B hlen)) := by
    rw [C₁B_faceRight_zero, faceLeft_arcIdx₀B]; exact hreach
  have hsym : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen))
      ((C₁B data B hlen).faceLeft (arcIdx₀B data B hlen))
      ((C₁B data B hlen).faceRight ⟨0, (C₁B data B hlen).len_pos⟩) :=
    Relation.ReflTransGen.symmetric
      (fun _ _ h => dualAvoidsCycleStep_symm (C₁B data B hlen) h) hreach'
  exact (bankC₁B data B hlen).left_right_sep (arcIdx₀B data B hlen)
    ⟨0, (C₁B data B hlen).len_pos⟩ hsym

lemma chordSplitAdj_imp_dualStepB (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len)
    {f g : M.Face} (h : hNT.ChordSplitAdj u v f g) :
    DualAvoidsCycleStep M (C₁B data B hlen) f g := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := h
  refine ⟨d, ?_, hdf, hdg⟩
  intro hmem
  rw [SimplePrimalCycle.mem_edgeSet_iff] at hmem
  obtain ⟨i, hi⟩ := hmem
  rcases C₁B_edge_chord_or_boundary data B hlen i with hc | hb
  · exact hch (by rw [hi, hc])
  · exact hbe (by rw [hi]; exact hb)

lemma chordSplitAdj_reach_imp_dualReachB (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len)
    {f g : M.Face} (h : Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g) :
    Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen)) f g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (chordSplitAdj_imp_dualStepB data B hlen hstep)

lemma bankReach_face₁_lifts_to_chordSplitAdjB (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len)
    {g : M.Face}
    (h : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen)) data.face₁ g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail f g' hpre hstep ih =>
      obtain ⟨d, hdedge, hdf, hdg⟩ := hstep
      have hf_ne : f ≠ hNT.outerFace :=
        hNT.side_subset_nonouter data.face₁_not_outer (g := f) ih
      have hch : M.dartEdge d ≠ s(u, v) := by
        intro he; exact hdedge (he ▸ chord_mem_C₁B_edgeSet data B hlen)
      have hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
        intro hbedge
        rcases ProofsInTheBook.ZinanCh35InnerConn.boundaryEdge_dart_outer hbedge with ho | ho
        · exact hf_ne (hdf ▸ ho)
        · have hg'_outer : g' = hNT.outerFace := hdg ▸ ho
          apply not_bankReach_face₁_outerFaceB data B hlen
          have hbankf : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen))
              data.face₁ f := chordSplitAdj_reach_imp_dualReachB data B hlen ih
          have : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen)) data.face₁ g' :=
            hbankf.tail ⟨d, hdedge, hdf, hdg⟩
          rwa [hg'_outer] at this
      exact ih.tail ⟨d, hdf, hdg, hbe, hch⟩

/-- **The reverse-face side-1 fact for an ARBITRARY backward run** (generalizes
`ZinanCh35ArcSide.bwdArc_reverse_face_mem_side₁`). -/
theorem bwdRun_reverse_face_mem_side₁ (data : hNT.ChordSplitData u v)
    (B : DartArc M hNT.outerCycle (M.tail data.dart) (M.head data.dart)) (hlen : 2 ≤ B.len)
    (i : Fin B.len) :
    M.dartFace (M.α (B.arcDart i)) ∈ data.side₁ := by
  have hface : (C₁B data B hlen).faceRight i.succ = M.dartFace (M.α (B.arcDart i)) := by
    show M.dartFace (M.α (SimplePrimalCycle.chordArcDart B (M.α data.dart) i.succ))
        = M.dartFace (M.α (B.arcDart i))
    rw [SimplePrimalCycle.chordArcDart_succ]
  have hbank : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁B data B hlen))
      data.face₁ ((C₁B data B hlen).faceRight i.succ) := by
    rw [← C₁B_faceRight_zero data B hlen]
    exact (bankC₁B data B hlen).right_bank ⟨0, (C₁B data B hlen).len_pos⟩ i.succ
  rw [hface] at hbank
  exact bankReach_face₁_lifts_to_chordSplitAdjB data B hlen hbank

end NearTriangulation

/-! ## 3. The pure modular covering of the cyclic dart list -/

/-- **The two complementary forward cyclic runs cover the cycle.**  From two positions `pf ≠ pt` on
a length-`L` cyclic list, the forward run from `pf` of length `kf = (pt - pf) mod L` and the forward
run from `pt` of length `kb = (pf - pt) mod L` are complementary: `kf, kb ≥ 1`, `kf + kb = L`,
`(pf + kf) mod L = pt`, and every position `q < L` lies in one of the two runs. -/
theorem mod_cover (L pf pt : ℕ) (hLpos : 0 < L) (hpf : pf < L) (hpt : pt < L) (hne : pf ≠ pt)
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

/-! ## 4. The two complementary boundary runs `arcUV`, `arcVU` keyed on `u, v`

We slice two complementary cyclic runs of `hNT.outerCycle.darts`: `arcUV` from `u` to `v` and
`arcVU` from `v` to `u`, both of length `≥ 2` (length `1` would make the chord `s(u,v)` a boundary
edge).  Their tails partition `outerCycle.vertices` (`mod_cover`). -/

namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}

/-- A boundary chord is symmetric in its endpoints. -/
def chord_symm (h : hNT.outerCycle.Chord u v) : hNT.outerCycle.Chord v u where
  endpoints_ne := h.endpoints_ne.symm
  left_boundary := h.right_boundary
  right_boundary := h.left_boundary
  adj := h.adj.symm
  not_boundary_edge := by rw [Sym2.eq_swap]; exact h.not_boundary_edge

/-- A position of a boundary vertex on the cyclic dart list. -/
noncomputable def vpos (h : hNT.outerCycle.Chord u v) {a : M.Vertex}
    (ha : hNT.outerCycle.IsBoundaryVertex a) : ℕ :=
  (hNT.outerCycle.exists_pos_of_isBoundaryVertex ha).choose.1

lemma vpos_lt (h : hNT.outerCycle.Chord u v) {a : M.Vertex}
    (ha : hNT.outerCycle.IsBoundaryVertex a) : vpos h ha < hNT.outerCycle.darts.length :=
  (hNT.outerCycle.exists_pos_of_isBoundaryVertex ha).choose.2

lemma vpos_tail (h : hNT.outerCycle.Chord u v) {a : M.Vertex}
    (ha : hNT.outerCycle.IsBoundaryVertex a) :
    M.tail (hNT.outerCycle.darts[vpos h ha]'(vpos_lt h ha)) = a :=
  (hNT.outerCycle.exists_pos_of_isBoundaryVertex ha).choose_spec

/-- Consecutive positions of a chord's endpoints cannot be adjacent: a `1`-step would make the chord
a boundary edge. -/
lemma not_consecutive_of_chord (h : hNT.outerCycle.Chord u v) {p q : ℕ}
    (hp : p < hNT.outerCycle.darts.length) (hq : q < hNT.outerCycle.darts.length)
    (htu : M.tail (hNT.outerCycle.darts[p]'hp) = u)
    (htv : M.tail (hNT.outerCycle.darts[q]'hq) = v)
    (hadj : (p + 1) % hNT.outerCycle.darts.length = q) : False := by
  set C := hNT.outerCycle
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
  apply h.not_boundary_edge
  show s(u, v) ∈ C.edges
  rw [C.edges_eq, show (s(u, v) : Sym2 M.Vertex) = M.dartEdge (C.darts[p]'hp) from by
    show s(u, v) = s(M.tail _, M.head _); rw [htu, hhead]]
  exact List.mem_map_of_mem (List.getElem_mem hp)

/-! ### The bundled normalized runs

`NormalizedRuns h` packages, from a chord `h`, the two complementary boundary runs `arcUV : DartArc
u v` and `arcVU : DartArc v u` (each length `≥ 2`), together with their tail-covering and
tail-disjointness of `outerCycle.vertices`.  Built from `cyclicDartArc` at the endpoint positions
and `mod_cover`. -/

structure NormalizedRuns (h : hNT.outerCycle.Chord u v) where
  /-- The `u → v` boundary run. -/
  arcUV : DartArc M hNT.outerCycle u v
  /-- The `v → u` boundary run. -/
  arcVU : DartArc M hNT.outerCycle v u
  /-- Both runs have length `≥ 2`. -/
  lenUV : 2 ≤ arcUV.len
  lenVU : 2 ≤ arcVU.len
  /-- Every boundary vertex is a tail of one of the two runs, or an endpoint. -/
  covering : ∀ {w : M.Vertex}, hNT.outerCycle.IsBoundaryVertex w →
    (∃ i, M.tail (arcUV.arcDart i) = w) ∨ (∃ i, M.tail (arcVU.arcDart i) = w) ∨ w = u ∨ w = v
  /-- A vertex that is a tail of *both* runs is a chord endpoint. -/
  disjoint : ∀ {w : M.Vertex}, (∃ i, M.tail (arcUV.arcDart i) = w) →
    (∃ i, M.tail (arcVU.arcDart i) = w) → w = u ∨ w = v

/-- **Build the normalized runs from a chord.** -/
noncomputable def normalizedRuns (h : hNT.outerCycle.Chord u v) : NormalizedRuns h := by
  classical
  set C := hNT.outerCycle with hC
  set L := C.darts.length with hL
  have hLpos : 0 < L := C.darts_length_pos
  -- positions of u, v
  have eu0 := (C.exists_pos_of_isBoundaryVertex h.left_boundary).choose_spec
  have ev0 := (C.exists_pos_of_isBoundaryVertex h.right_boundary).choose_spec
  set puF := (C.exists_pos_of_isBoundaryVertex h.left_boundary).choose with hpuF
  set pvF := (C.exists_pos_of_isBoundaryVertex h.right_boundary).choose with hpvF
  set pu := puF.1 with hpuval
  set pv := pvF.1 with hpvval
  have hpu : pu < L := puF.2
  have hpv : pv < L := pvF.2
  have eu : M.tail (C.darts[pu]'hpu) = u := eu0
  have ev : M.tail (C.darts[pv]'hpv) = v := ev0
  have hpune : pu ≠ pv := by
    intro hpe; apply h.endpoints_ne
    rw [← eu, ← ev]
    have : C.darts[pu]'hpu = C.darts[pv]'hpv := getElem_congr rfl hpe hpu
    rw [this]
  -- run lengths
  set kf := (pv + L - pu) % L with hkf
  set kb := (pu + L - pv) % L with hkb
  obtain ⟨hkf1, hkb1, hsum, hpfkf, hcov⟩ := mod_cover L pu pv hLpos hpu hpv hpune kf kb hkf hkb
  -- (pv + kb) % L = pu, from the symmetric mod_cover call
  obtain ⟨_, _, _, hpvkb, _⟩ := mod_cover L pv pu hLpos hpv hpu (Ne.symm hpune) kb kf hkb hkf
  have hkfL : kf < L := by rw [hkf]; exact Nat.mod_lt _ hLpos
  have hkbL : kb < L := by rw [hkb]; exact Nat.mod_lt _ hLpos
  -- kf ≥ 2
  have hkf2 : 2 ≤ kf := by
    rcases Nat.lt_or_ge kf 2 with hlt | hge
    · exfalso
      have hkf1' : kf = 1 := by omega
      apply not_consecutive_of_chord h hpu hpv eu ev
      rw [show (pu + 1) % L = (pu + kf) % L from by rw [hkf1'], hpfkf]
    · exact hge
  have hkb2 : 2 ≤ kb := by
    rcases Nat.lt_or_ge kb 2 with hlt | hge
    · exfalso
      have hkb1' : kb = 1 := by omega
      exact not_consecutive_of_chord (chord_symm h) hpv hpu ev eu
        (by rw [show (pv + 1) % L = (pv + kb) % L from by rw [hkb1'], hpvkb])
    · exact hge
  -- the two raw runs
  set AUV := C.cyclicDartArc hNT.outer_simple pu kf hkf1 hkfL hpu with hAUV
  set AVU := C.cyclicDartArc hNT.outer_simple pv kb hkb1 hkbL hpv with hAVU
  -- endpoint equalities for casting
  have euv2 : M.tail (C.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega))) = v := by
    have : C.darts[(pu + kf) % L]'(Nat.mod_lt _ (by omega)) = C.darts[pv]'hpv := by congr 1
    rw [this]; exact ev
  have evu2 : M.tail (C.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega))) = u := by
    have : C.darts[(pv + kb) % L]'(Nat.mod_lt _ (by omega)) = C.darts[pu]'hpu := by congr 1
    rw [this]; exact eu
  -- arcUV : DartArc u v, arcVU : DartArc v u (via daCast through the raw runs)
  -- We use bpCast-style transport at the DartArc level via subst inside the structure proofs;
  -- here we just record the runs typed as cyclicDartArc and rewrite endpoints by `eu`/`euv2`.
  -- tail characterizations: the casted runs' tails are exactly the cyclic-slice tails.
  have htailUV : ∀ i : Fin (daCast AUV eu euv2).len,
      M.tail ((daCast AUV eu euv2).arcDart i)
        = M.tail (C.darts[(pu + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCast_cyclic_tail C hNT.outer_simple pu kf hkf1 hkfL hpu eu euv2 i
  have htailVU : ∀ i : Fin (daCast AVU ev evu2).len,
      M.tail ((daCast AVU ev evu2).arcDart i)
        = M.tail (C.darts[(pv + i.1) % L]'(Nat.mod_lt _ (by omega))) := by
    intro i; exact daCast_cyclic_tail C hNT.outer_simple pv kb hkb1 hkbL hpv ev evu2 i
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
    -- w is tail of darts[q] for some q < L
    obtain ⟨q, hqt⟩ := C.exists_pos_of_isBoundaryVertex hw
    rcases hcov q.1 q.2 with ⟨j, hj, hjq⟩ | ⟨j, hj, hjq⟩
    · -- w on arcUV (positions pu+j)
      left
      obtain ⟨i, hi⟩ := htailUV_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)) = C.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
    · -- w on arcVU (positions pv+j)
      right; left
      obtain ⟨i, hi⟩ := htailVU_fwd j hj
      refine ⟨i, ?_⟩
      rw [hi]
      have : C.darts[(pv + j) % L]'(Nat.mod_lt _ (by omega)) = C.darts[q.1]'q.2 :=
        getElem_congr rfl hjq _
      rw [this, hqt]
  · -- disjoint: a vertex on both runs is u or v
    rintro w ⟨i, hiw⟩ ⟨i', hi'w⟩
    obtain ⟨j, hj, hjeq⟩ := htailUV_bwd i
    obtain ⟨j', hj', hj'eq⟩ := htailVU_bwd i'
    -- tail darts[(pu+j)%L] = w = tail darts[(pv+j')%L]
    have heq : M.tail (C.darts[(pu + j) % L]'(Nat.mod_lt _ (by omega)))
        = M.tail (C.darts[(pv + j') % L]'(Nat.mod_lt _ (by omega))) := by
      rw [← hjeq, ← hj'eq, hiw, hi'w]
    -- by VertexNodup, the dart positions coincide: (pu+j)%L = (pv+j')%L
    have hmap : (C.darts.map M.tail).Nodup := by
      have := hNT.outer_simple
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
    -- positions: pu+j with j<kf and pv+j' with j'<kb, kf+kb=L, complementary ⟹ j=0 or j'=0.
    -- (pu+0)%L=pu↦u, (pv+0)%L=pv↦v. Since ranges are complementary, equality forces a boundary.
    -- We show w ∈ {u,v} by: the only shared position is when one of j,j' is 0.
    -- pu+j ≡ pv+j' (mod L). Using (pv+kb)%L=pu i.e. pv ≡ pu - kb, get j ≡ j' - kb (mod L);
    -- with 0≤j<kf, 0≤j'<kb, kf+kb=L: j' - kb ∈ (-kb, kf-kb] so j ≡ that; the only solution in
    -- [0,kf) is j = j' + kf (impossible unless ...). Cleanest: case j=0 ∨ j'=0.
    by_cases hj0 : j = 0
    · -- w = tail darts[pu] = u
      left
      rw [← hiw, hjeq, hj0]
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hpu]
      exact eu
    · by_cases hj'0 : j' = 0
      · right
        rw [← hi'w, hj'eq, hj'0]
        simp only [Nat.add_zero, Nat.mod_eq_of_lt hpv]
        exact ev
      · -- both j,j' ≥ 1: derive contradiction from complementary ranges
        exfalso
        -- (pu+j) ≡ (pv+j') (mod L), and pv ≡ (pu+kf) (mod L), so j ≡ kf+j' (mod L).
        have hpvmod : pv % L = (pu + kf) % L := by rw [hpfkf, Nat.mod_eq_of_lt hpv]
        -- pu+j ≡ pu+kf+j' (mod L)
        have h2 : Nat.ModEq L pv (pu + kf) := by
          show pv % L = (pu + kf) % L; exact hpvmod
        have hcong : Nat.ModEq L (pu + j) (pu + (kf + j')) := by
          have h1 : Nat.ModEq L (pu + j) (pv + j') := hposeq
          have h3 : Nat.ModEq L (pv + j') (pu + kf + j') := h2.add_right j'
          have h4 : Nat.ModEq L (pu + j) (pu + kf + j') := h1.trans h3
          rwa [show pu + kf + j' = pu + (kf + j') from by ring] at h4
        -- cancel pu: j ≡ kf + j' (mod L)
        have hcong' : Nat.ModEq L j (kf + j') := Nat.ModEq.add_left_cancel' pu hcong
        -- both sides < L; equal
        have hjlt : j < L := by omega
        have hkfj' : kf + j' < L := by omega
        have : j = kf + j' := by
          have hj1 : j % L = j := Nat.mod_eq_of_lt hjlt
          have hj2 : (kf + j') % L = kf + j' := Nat.mod_eq_of_lt hkfj'
          rw [Nat.ModEq, hj1, hj2] at hcong'; exact hcong'
        omega

/-! ## 5. The normalized `BoundaryArcSplit` and `ChordSplitData`

`path₁ := bpOfDartArc arcUV : BoundaryPath u v` and `path₂ := bpOfDartArc arcVU : BoundaryPath v u`.
The covering / disjointness come from `NormalizedRuns`; the internal-iff-proper from `2 ≤ len` and
the chord-not-boundary-edge property. -/

/-- **The normalized boundary arc-split**: `path₂` is the `v → u` run, `path₁` the `u → v` run. -/
noncomputable def normalizedArcSplit (h : hNT.outerCycle.Chord u v) :
    BoundaryArcSplit M hNT.outerCycle.vertices hNT.outerCycle.edges u v :=
  let R := normalizedRuns h
  { path₁ := bpOfDartArc R.arcUV
    path₂ := bpOfDartArc R.arcVU
    path₁_boundary_vertices := fun {w} hw =>
      bpOfDartArc_boundary_vertices R.arcUV h.right_boundary hw
    path₂_boundary_vertices := fun {w} hw =>
      bpOfDartArc_boundary_vertices R.arcVU h.left_boundary hw
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
        · -- w = u: u is the tail of arcUV's first dart.
          left
          rw [bpOfDartArc_vertices, List.mem_append]
          refine Or.inl ?_
          have hu_tail : M.tail (R.arcUV.arcDart R.arcUV.firstIdx) = w :=
            R.arcUV.tail_first.trans hwu.symm
          have hmem : M.tail (R.arcUV.arcDart R.arcUV.firstIdx) ∈ R.arcUV.dartList.map M.tail :=
            List.mem_map_of_mem (by
              rw [DartArc.dartList]; exact List.mem_map_of_mem (List.mem_finRange _))
          exact hu_tail ▸ hmem
        · -- w = v: v is the terminal endpoint of path₁.
          left
          rw [bpOfDartArc_vertices, List.mem_append]
          exact Or.inr (by rw [hwv]; exact List.mem_singleton_self _)
      · intro hw
        rcases hw with hw | hw
        · exact bpOfDartArc_boundary_vertices R.arcUV h.right_boundary hw
        · exact bpOfDartArc_boundary_vertices R.arcVU h.left_boundary hw
    internally_disjoint := by
      intro w hw1 hw2
      obtain ⟨i, hi⟩ := bpOfDartArc_internal_tail R.arcUV hw1
      obtain ⟨i', hi'⟩ := bpOfDartArc_internal_tail R.arcVU hw2
      -- w ∈ {u, v} by disjoint; but w is internal to path₁, so w ≠ u, w ≠ v.
      have hwuv : w = u ∨ w = v := R.disjoint ⟨i, hi⟩ ⟨i', hi'⟩
      have hwu : w ≠ u := (bpOfDartArc R.arcUV).internalVertex_ne_start hw1
      have hwv : w ≠ v := (bpOfDartArc R.arcUV).internalVertex_ne_end hw1
      rcases hwuv with h' | h'
      · exact hwu h'
      · exact hwv h'
    path₁_internal_iff_proper := by
      constructor
      · intro _; exact h.not_boundary_edge
      · intro _; exact bpOfDartArc_hasInternal R.arcUV R.lenUV
    path₂_internal_iff_proper := by
      constructor
      · intro _; exact h.not_boundary_edge
      · intro _; exact bpOfDartArc_hasInternal R.arcVU R.lenVU }

/-- **The normalized chord-split datum** built from a chord. -/
noncomputable def normalizedChordSplitData (h : hNT.outerCycle.Chord u v) :
    hNT.ChordSplitData u v :=
  { chord := h
    arc := normalizedArcSplit h
    arc₁_internal := bpOfDartArc_hasInternal (normalizedRuns h).arcUV (normalizedRuns h).lenUV
    arc₂_internal := bpOfDartArc_hasInternal (normalizedRuns h).arcVU (normalizedRuns h).lenVU }

@[simp] lemma normalizedChordSplitData_chord (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData h).chord = h := rfl

/-! ### `ArcSideIdentification` for the normalized datum (case `tail dart = u`, `head dart = v`)

In the chord-dart orientation `tail dart = u, head dart = v`, the `v → u` run `arcVU` is the forward
run `DartArc (head dart) (tail dart)` whose reverse faces lie in `side₂`
(`fwdRun_reverse_face_mem_side₂`), and the `u → v` run `arcUV` is the backward run whose reverse
faces lie in `side₁`.  Hence `path₂`-internal `⊆ sideRegion₂` and `path₁`-internal `⊆ sideRegion₁` —
`ArcSideIdentification` holds by construction. -/

/-- **`ArcSideIdentification` for the normalized datum, given the aligned chord-dart orientation.** -/
theorem arcSideIdentification_normalized (h : hNT.outerCycle.Chord u v)
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v) :
    ProofsInTheBook.ZinanCh35BankOrient.ArcSideIdentification (normalizedChordSplitData h) := by
  classical
  set data := normalizedChordSplitData h with hdata
  set R := normalizedRuns h with hR
  refine ⟨?_, ?_⟩
  · -- path₁-internal ⊆ sideRegion₁ (arcUV is the backward run u → v = DartArc (tail dart)(head dart))
    intro w hw
    have hw' : w ∈ (bpOfDartArc R.arcUV).internalVertices := hw
    obtain ⟨i, hi⟩ := bpOfDartArc_internal_tail R.arcUV hw'
    -- arcUV : DartArc u v = DartArc (tail dart)(head dart); reverse faces ∈ side₁.
    have hB : M.dartFace (M.α ((daCast R.arcUV htu.symm hhv.symm).arcDart
        (Fin.cast (daCast_len R.arcUV htu.symm hhv.symm).symm i))) ∈ data.side₁ :=
      bwdRun_reverse_face_mem_side₁ data (daCast R.arcUV htu.symm hhv.symm) (by rw [daCast_len]; exact R.lenUV) _
    -- the casted dart is the same dart: tail = w, reverse face ∈ side₁.
    have hsame : (daCast R.arcUV htu.symm hhv.symm).arcDart
        (Fin.cast (daCast_len R.arcUV htu.symm hhv.symm).symm i) = R.arcUV.arcDart i := by
      rw [daCast_arcDart_eq]; congr 1
    rw [hsame] at hB
    have hchord : M.dartEdge (R.arcUV.arcDart i) ≠ s(u, v) := by
      intro he
      apply h.not_boundary_edge
      rw [← he]; show M.dartEdge (R.arcUV.arcDart i) ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq]; exact List.mem_map_of_mem (R.arcUV.boundary i)
    have := ProofsInTheBook.ZinanCh35Side2Confine.endpoints_mem_sideRegion₁_of_face data hsep
      (by rw [M.dartEdge_alpha]; exact hchord) hB
    rw [M.head_alpha] at this
    rw [← hi]; exact this.2
  · -- path₂-internal ⊆ sideRegion₂ (arcVU is the forward run v → u = DartArc (head dart)(tail dart))
    intro w hw
    have hw' : w ∈ (bpOfDartArc R.arcVU).internalVertices := hw
    obtain ⟨i, hi⟩ := bpOfDartArc_internal_tail R.arcVU hw'
    have hF : M.dartFace (M.α ((daCast R.arcVU hhv.symm htu.symm).arcDart
        (Fin.cast (daCast_len R.arcVU hhv.symm htu.symm).symm i))) ∈ data.side₂ :=
      fwdRun_reverse_face_mem_side₂ data (daCast R.arcVU hhv.symm htu.symm) (by rw [daCast_len]; exact R.lenVU) _
    have hsame : (daCast R.arcVU hhv.symm htu.symm).arcDart
        (Fin.cast (daCast_len R.arcVU hhv.symm htu.symm).symm i) = R.arcVU.arcDart i := by
      rw [daCast_arcDart_eq]; congr 1
    rw [hsame] at hF
    have hchord : M.dartEdge (R.arcVU.arcDart i) ≠ s(u, v) := by
      intro he
      apply h.not_boundary_edge
      rw [← he]; show M.dartEdge (R.arcVU.arcDart i) ∈ hNT.outerCycle.edges
      rw [hNT.outerCycle.edges_eq]; exact List.mem_map_of_mem (R.arcVU.boundary i)
    have := ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.dartRun_tail_mem_sideRegion₂_of_face
      data hsep hchord hF
    rw [← hi]; exact this

/-- **Both Chapter-35 confinements for the normalized datum** (aligned chord-dart orientation).
`ArcSideIdentification` is discharged BY CONSTRUCTION — `path₂` *is* the forward `v → u` run, so its
internal vertices are bank-side-2 facts, not a free Jordan input — and routed through
`ZinanCh35BankOrient.bothConfinements_of_arcSide`.  The only remaining hypotheses are the chord-level
`Separates` keystone and the 2-valued chord-dart orientation `tail dart = u`, `head dart = v` (a
finite combinatorial selector on the opaque `chordDart` choice, NOT the discrete-Jordan datum). -/
theorem bothConfinements_normalized (h : hNT.outerCycle.Chord u v)
    (hsep : (normalizedChordSplitData h).Separates)
    (htu : M.tail (normalizedChordSplitData h).dart = u)
    (hhv : M.head (normalizedChordSplitData h).dart = v) :
    ProofsInTheBook.ZinanCh35Schoenflies.Side₁StarConfinement (normalizedChordSplitData h) ∧
      ProofsInTheBook.ZinanCh35Side2.Side₂SchoenfliesConfinementInput
        (normalizedChordSplitData h) hsep :=
  ProofsInTheBook.ZinanCh35BankOrient.bothConfinements_of_arcSide (normalizedChordSplitData h) hsep
    (arcSideIdentification_normalized h hsep htu hhv)

/-- The chord-dart orientation dichotomy: `chordDart h` realizes the unordered edge `s(u, v)`, so it
is oriented `u → v` or `v → u`. -/
theorem chordDart_orientation (h : hNT.outerCycle.Chord u v) :
    (M.tail (normalizedChordSplitData h).dart = u ∧
        M.head (normalizedChordSplitData h).dart = v) ∨
      (M.tail (normalizedChordSplitData h).dart = v ∧
        M.head (normalizedChordSplitData h).dart = u) := by
  have hedge : M.dartEdge (normalizedChordSplitData h).dart = s(u, v) :=
    hNT.chordDart_edge h
  have hxy : s(M.tail (normalizedChordSplitData h).dart, M.head (normalizedChordSplitData h).dart)
      = s(u, v) := hedge
  rcases Sym2.eq_iff.mp hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-- **The normalized datum realizes the arc↔side identification in one of the two orientations,
UNCONDITIONALLY** (no Jordan input, only the chord-level `Separates`).  Either the standard labelling
holds (`tail dart = u`: `path₂ ⊆ side₂`, `path₁ ⊆ side₁`), or — when the opaque chord-dart points the
other way — the swapped labelling holds.  In the standard branch both confinements are discharged. -/
theorem arcSideIdentification_normalized_unconditional (h : hNT.outerCycle.Chord u v)
    (hsep : (normalizedChordSplitData h).Separates) :
    ProofsInTheBook.ZinanCh35BankOrient.ArcSideIdentification (normalizedChordSplitData h) ∨
      (M.tail (normalizedChordSplitData h).dart = v ∧
        M.head (normalizedChordSplitData h).dart = u) := by
  rcases chordDart_orientation h with ⟨htu, hhv⟩ | hswap
  · exact Or.inl (arcSideIdentification_normalized h hsep htu hhv)
  · exact Or.inr hswap

/-! ### Non-vacuity audit: the normalized datum is genuine (not degenerate/vacuous). -/

-- Both arcs of the normalized arc-split carry genuine internal vertices (the construction fires).
example (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData h).arc.path₂.HasInternalVertex ∧
      (normalizedChordSplitData h).arc.path₁.HasInternalVertex :=
  ⟨(normalizedChordSplitData h).arc₂_internal, (normalizedChordSplitData h).arc₁_internal⟩

-- `Separates` for the normalized datum is the genuine chord keystone `face₂ ∉ side₁` (not trivial).
example (h : hNT.outerCycle.Chord u v) :
    (normalizedChordSplitData h).Separates
      = ((normalizedChordSplitData h).face₂ ∉ (normalizedChordSplitData h).side₁) := rfl

-- The datum's chord is the GIVEN chord, so `side₁`/`side₂` are the real chord sides.
example (h : hNT.outerCycle.Chord u v) : (normalizedChordSplitData h).chord = h := rfl

-- The two runs have length ≥ 2 (genuinely longer than the chord — the arcs carry interior vertices).
example (h : hNT.outerCycle.Chord u v) :
    2 ≤ (normalizedRuns h).arcUV.len ∧ 2 ≤ (normalizedRuns h).arcVU.len :=
  ⟨(normalizedRuns h).lenUV, (normalizedRuns h).lenVU⟩

end NearTriangulation

end ProofsInTheBook.ZinanCh35Aligned

/-! ## Axiom audit (expect clean-3: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.fwdRun_reverse_face_mem_side₂
#print axioms ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.bwdRun_reverse_face_mem_side₁
#print axioms ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedRuns
#print axioms ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedArcSplit
#print axioms ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.normalizedChordSplitData
#print axioms ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.arcSideIdentification_normalized
#print axioms ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.bothConfinements_normalized
#print axioms ProofsInTheBook.ZinanCh35Aligned.NearTriangulation.arcSideIdentification_normalized_unconditional
