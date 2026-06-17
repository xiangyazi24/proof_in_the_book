import ProofsInTheBook.ZinanCh35BankLabels
import ProofsInTheBook.ZinanCh35ChordCycle
import ProofsInTheBook.ZinanCh35Contiguity
import ProofsInTheBook.ZinanCh35BankOrient
import ProofsInTheBook.ZinanCh35InnerConn

/-!
# Chapter 35: the bank-side fact for the forward boundary run, and the honest status of
  `ArcSideIdentification`

R8's chain A–F proposed assembling `ZinanCh35BankOrient.ArcSideIdentification` *unconditionally* by
building `C₂ = chord ∪ path₂` as a `SimplePrimalCycle`, applying the general
`ZinanCh35BankLabels.simpleCycleBankTheorem_holds`, and converting the `right_bank` reachability of
`C₂` into `side₂` membership.

This file carries out the **real new mathematics** of that chain — the C₂ construction and the
bank→`ChordSplitAdj` conversion — and lands it as a clean unconditional theorem
(`forwardRun_inner_mem_side₂`): for every dart of the cyclically-forward `v → u` boundary run, the
bounded face across its boundary edge lies in `side₂`.  Composed with the landed per-dart bridge
`ZinanCh35ArcDartRun.dartRun_tail_mem_sideRegion₂_of_face` it yields, for every forward-run vertex
`w`, that `w ∈ sideRegion₂` (`forwardRun_tail_mem_sideRegion₂`).

## Why this discharges the bank datum, and the precise residual that remains

`forwardRun_inner_mem_side₂` supplies exactly the side-2 face datum
(`ZinanCh35Contiguity.BankSideDatum`, conjunct (2)) **for the forward run**.  The bank theorem thus
genuinely produces the geometric content the audit named.  What it does **not** do — and provably
cannot, by `ZinanCh35BankOrient.bank_datum_substrate_symmetric` and the `ZinanCh35Contiguity`
module docstring — is decide whether `data.arc.path₂` *is* the forward `v → u` run or the backward
`u → v` run.  `BoundaryArcSplit` is a free Jordan-split certificate; nothing ties its `path₁`/`path₂`
labelling to the chord-dart-derived face orientation.  Concretely, the two cyclic boundary arcs
partition into "inner faces ∈ `side₁`" and "inner faces ∈ `side₂`" (proved here as
`ForwardArcAligned`/`forward_inner_sideDichotomy`), and `ArcSideIdentification` holds **iff** the free
labelling assigns `path₂` to the side-2 arc.  This is the single irreducible orientation input the
codebase isolates uniformly (`ZinanCh35BankOrient`, `ZinanCh35Side1Confine` header, `ChordContiguous`).

We therefore record:

* `forwardRun_inner_mem_side₂`, `forwardRun_tail_mem_sideRegion₂` — UNCONDITIONAL bank-side facts
  (the chain's real content);
* `ForwardRunAligned` — the sharp, isolated orientation predicate "every `path₂`-internal vertex is a
  forward-run tail";
* `bankSideDatum_of_forwardRunAligned`, `chordArcBankOrientation_of_forwardRunAligned`,
  `arcSideIdentification_of_forwardRunAligned`, `bothConfinements_of_forwardRunAligned` — the honest
  assembly: supplying the *single* alignment input discharges `BankSideDatum`,
  `ChordArcBankOrientation`, `ArcSideIdentification`, and **both** Chapter-35 confinements at once.

No `sorry` / `axiom` / `admit` / `native_decide`; no posited conclusion.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ArcSide

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore
open ProofsInTheBook.ZinanCh35CycleBank
open ProofsInTheBook.ZinanCh35BankLabels

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## 1. The forward boundary run `C₂ = chord ∪ (v → u run)` as a `SimplePrimalCycle`

We reconstruct the chord∪arc cycle of `ZinanCh35ChordCycle.chordCycleData` *keeping the dart-arc `A`
accessible* (so we can name a concrete arc index whose `faceLeft = outerFace`).  The chord dart `c₀`
sits at index `0`; the arc darts (forward `head c₀ → tail c₀` run on the outer cycle) sit at indices
`1, …, A.len`. -/

/-- The dart-arc realizing the forward boundary run between the chord-dart endpoints. -/
noncomputable def fwdArc (data : hNT.ChordSplitData u v) :
    DartArc M hNT.outerCycle (M.head data.dart) (M.tail data.dart) := by
  classical
  have hedge : M.dartEdge data.dart = s(u, v) := hNT.chordDart_edge data.chord
  have hxy_edge : s(M.tail data.dart, M.head data.dart) = s(u, v) := hedge
  have hxy_ne : M.tail data.dart ≠ M.head data.dart := by
    intro hcontra
    have h1 : s(M.head data.dart, M.head data.dart) = s(u, v) := hcontra ▸ hxy_edge
    have huv : u = v := by
      rcases Sym2.eq_iff.mp h1.symm with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact hl.trans hr.symm
      · exact hl.trans hr.symm
    exact data.chord.endpoints_ne huv
  have hx_bv : hNT.outerCycle.IsBoundaryVertex (M.tail data.dart) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨hxu, _⟩ | ⟨hxv, _⟩
    · rw [hxu]; exact data.chord.left_boundary
    · rw [hxv]; exact data.chord.right_boundary
  have hy_bv : hNT.outerCycle.IsBoundaryVertex (M.head data.dart) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨_, hyv⟩ | ⟨_, hyu⟩
    · rw [hyv]; exact data.chord.right_boundary
    · rw [hyu]; exact data.chord.left_boundary
  have hnbe : ¬ hNT.outerCycle.IsBoundaryEdge s(M.head data.dart, M.tail data.dart) := by
    rw [show (s(M.head data.dart, M.tail data.dart) : Sym2 M.Vertex)
          = s(M.tail data.dart, M.head data.dart) from Sym2.eq_swap, hxy_edge]
    exact data.chord.not_boundary_edge
  exact (hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple
    (Ne.symm hxy_ne) hy_bv hx_bv hnbe).1

lemma fwdArc_len (data : hNT.ChordSplitData u v) : 2 ≤ (fwdArc data).len := by
  classical
  -- the underlying dartArc has length ≥ 2.
  show 2 ≤ ((hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple _ _ _ _).1).len
  exact (hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple _ _ _ _).2

/-- `C₂ = chord ∪ forward run`: the simple primal cycle `ofDartArc (fwdArc) data.dart`. -/
noncomputable def C₂ (data : hNT.ChordSplitData u v) : SimplePrimalCycle M :=
  SimplePrimalCycle.ofDartArc (fwdArc data) data.dart (fwdArc_len data) rfl rfl

/-- Index `0` of `C₂` is the chord dart. -/
lemma C₂_dart_zero (data : hNT.ChordSplitData u v) :
    (C₂ data).dart ⟨0, (C₂ data).len_pos⟩ = data.dart := by
  show SimplePrimalCycle.chordArcDart (fwdArc data) data.dart ⟨0, (C₂ data).len_pos⟩ = data.dart
  exact SimplePrimalCycle.chordArcDart_zero _ _

/-- The chord-incident face `face₂` is the right face of `C₂` at the chord index `0`. -/
lemma C₂_faceRight_zero (data : hNT.ChordSplitData u v) :
    (C₂ data).faceRight ⟨0, (C₂ data).len_pos⟩ = data.face₂ := by
  show M.dartFace (M.α ((C₂ data).dart ⟨0, (C₂ data).len_pos⟩)) = M.dartFace (M.α data.dart)
  rw [C₂_dart_zero]

/-- The chord-incident face `face₁` is the left face of `C₂` at the chord index `0`. -/
lemma C₂_faceLeft_zero (data : hNT.ChordSplitData u v) :
    (C₂ data).faceLeft ⟨0, (C₂ data).len_pos⟩ = data.face₁ := by
  show M.dartFace ((C₂ data).dart ⟨0, (C₂ data).len_pos⟩) = M.dartFace data.dart
  rw [C₂_dart_zero]

/-! ## 2. `hsub`: every cycle edge of `C₂` is the chord or a boundary edge

Mirrors `ZinanCh35ChordCycle.chordCycleData`'s `hsub`. -/

/-- Every edge of `C₂` is the chord edge `s(u, v)` or a boundary edge of the outer cycle. -/
lemma C₂_edge_chord_or_boundary (data : hNT.ChordSplitData u v) (i : Fin (C₂ data).len) :
    (C₂ data).edge i = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge ((C₂ data).edge i) := by
  have hedge : M.dartEdge data.dart = s(u, v) := hNT.chordDart_edge data.chord
  have hedge_i : (C₂ data).edge i = M.dartEdge ((C₂ data).dart i) := rfl
  rw [hedge_i]
  show M.dartEdge (SimplePrimalCycle.chordArcDart (fwdArc data) data.dart i) = s(u, v) ∨
    hNT.outerCycle.IsBoundaryEdge (M.dartEdge (SimplePrimalCycle.chordArcDart (fwdArc data) data.dart i))
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · left; rw [SimplePrimalCycle.chordArcDart_zero]; exact hedge
  · right
    rw [SimplePrimalCycle.chordArcDart_succ]
    show M.dartEdge ((fwdArc data).arcDart i') ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    exact List.mem_map_of_mem ((fwdArc data).boundary i')

/-- The chord edge `s(u, v)` is in `C₂.edgeSet`. -/
lemma chord_mem_C₂_edgeSet (data : hNT.ChordSplitData u v) :
    (s(u, v) : Sym2 M.Vertex) ∈ (C₂ data).edgeSet := by
  rw [SimplePrimalCycle.mem_edgeSet_iff]
  refine ⟨⟨0, (C₂ data).len_pos⟩, ?_⟩
  have : (C₂ data).edge ⟨0, (C₂ data).len_pos⟩ = M.dartEdge ((C₂ data).dart ⟨0, (C₂ data).len_pos⟩) :=
    rfl
  rw [this, C₂_dart_zero]; exact (hNT.chordDart_edge data.chord).symm

/-! ## 3. The forward-run arc index whose `faceLeft` is the outer face

Index `1 = (firstIdx).succ` of `C₂` is the first arc dart (`fwdArc`'s dart `0`), which lies on the
outer cycle, so its `dartFace` is the outer face.  This pins the outer face onto the **left** (i.e.
`face₁`) bank of `C₂`. -/

/-- The arc index `(fwdArc.firstIdx).succ` of `C₂`, valid since `C₂.len = fwdArc.len + 1`. -/
noncomputable def arcIdx₀ (data : hNT.ChordSplitData u v) : Fin (C₂ data).len :=
  ((fwdArc data).firstIdx).succ

/-- The `faceLeft` of `C₂` at `arcIdx₀` is the outer face. -/
lemma faceLeft_arcIdx₀ (data : hNT.ChordSplitData u v) :
    (C₂ data).faceLeft (arcIdx₀ data) = hNT.outerFace := by
  show M.dartFace ((C₂ data).dart (arcIdx₀ data)) = hNT.outerFace
  show M.dartFace (SimplePrimalCycle.chordArcDart (fwdArc data) data.dart
      ((fwdArc data).firstIdx).succ) = hNT.outerFace
  rw [SimplePrimalCycle.chordArcDart_succ]
  -- the arc dart lies on the outer cycle, hence its face is the outer face.
  exact (hNT.outerCycle.mem_darts_iff _).mp ((fwdArc data).boundary _)

/-! ## 4. The outer face is unreachable from `face₂` on `C₂`'s bank

`face₂ = faceRight 0` and `outerFace = faceLeft arcIdx₀`.  The discharged Jordan separation field
`left_right_sep` of `simpleCycleBankTheorem_holds` forbids any forward face reaching any reverse
face; by symmetry of `DualAvoidsCycleStep`, `face₂` cannot reach `outerFace`. -/

/-- The bank theorem instance for `C₂`. -/
noncomputable def bankC₂ (data : hNT.ChordSplitData u v) :
    SimpleCycleBankTheorem M (C₂ data) :=
  simpleCycleBankTheorem_holds (C₂ data) hNT.sphere hNT.simpleGraph

/-- **The outer face is not bank-reachable from `face₂` on `C₂`.**  Otherwise, by symmetry,
`outerFace = faceLeft arcIdx₀` would reach `face₂ = faceRight 0`, contradicting `left_right_sep`. -/
lemma not_bankReach_face₂_outerFace (data : hNT.ChordSplitData u v) :
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data)) data.face₂ hNT.outerFace := by
  intro hreach
  -- rewrite endpoints into `faceRight 0` / `faceLeft arcIdx₀`.
  have hreach' : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data))
      ((C₂ data).faceRight ⟨0, (C₂ data).len_pos⟩) ((C₂ data).faceLeft (arcIdx₀ data)) := by
    rw [C₂_faceRight_zero, faceLeft_arcIdx₀]; exact hreach
  -- symmetrize to `faceLeft arcIdx₀ ↝ faceRight 0`, contradicting `left_right_sep`.
  have hsym : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data))
      ((C₂ data).faceLeft (arcIdx₀ data)) ((C₂ data).faceRight ⟨0, (C₂ data).len_pos⟩) :=
    Relation.ReflTransGen.symmetric
      (fun _ _ h => dualAvoidsCycleStep_symm (C₂ data) h) hreach'
  exact (bankC₂ data).left_right_sep (arcIdx₀ data) ⟨0, (C₂ data).len_pos⟩ hsym

/-! ## 5. The bank → `ChordSplitAdj` conversion (R8 §E)

A `DualAvoidsCycleStep M C₂` step uses a dart `d` with `dartEdge d ∉ C₂.edgeSet`.  Since every
`C₂` edge is the chord or a boundary edge (`C₂_edge_chord_or_boundary`), such a `d` has a non-chord,
non-`C₂`-edge.  If additionally we stay on the `face₂` bank (never reaching `outerFace`), the edge is
also **non-boundary**: a boundary edge would put `outerFace` on one of its two faces, and since the
source face is not `outerFace`, the target would be — reaching `outerFace`, impossible.  Hence the
step is a `ChordSplitAdj u v` step. -/

/-- **A `ChordSplitAdj` step is a `C₂`-avoiding dual step.**  Its edge is non-boundary and non-chord,
hence not in `C₂.edgeSet` (which is contained in chord ∪ boundary edges). -/
lemma chordSplitAdj_imp_dualStep (data : hNT.ChordSplitData u v) {f g : M.Face}
    (h : hNT.ChordSplitAdj u v f g) :
    DualAvoidsCycleStep M (C₂ data) f g := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := h
  refine ⟨d, ?_, hdf, hdg⟩
  -- `dartEdge d ∉ C₂.edgeSet`: every C₂ edge is chord or boundary; `dartEdge d` is neither.
  intro hmem
  rw [SimplePrimalCycle.mem_edgeSet_iff] at hmem
  obtain ⟨i, hi⟩ := hmem
  rcases C₂_edge_chord_or_boundary data i with hc | hb
  · exact hch (by rw [hi, hc])
  · exact hbe (by rw [hi]; exact hb)

/-- A `ChordSplitAdj`-walk is a `C₂`-avoiding dual walk. -/
lemma chordSplitAdj_reach_imp_dualReach (data : hNT.ChordSplitData u v) {f g : M.Face}
    (h : Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g) :
    Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data)) f g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (chordSplitAdj_imp_dualStep data hstep)

/-- **The bank → `ChordSplitAdj` lift (R8 §E).**  A `C₂`-bank walk from `face₂` lifts to a
`ChordSplitAdj`-walk (i.e. lands inside `side₂`), provided `face₂` cannot bank-reach `outerFace`.
Proved by induction, lifting each step using `not_bankReach_face₂_outerFace`. -/
lemma bankReach_face₂_lifts_to_chordSplitAdj (data : hNT.ChordSplitData u v) {g : M.Face}
    (h : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data)) data.face₂ g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₂ g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail f g' hpre hstep ih =>
      -- `ih : face₂ ↝_CSA f`.  Lift the step `f →_bank g'` to `f →_CSA g'`.
      obtain ⟨d, hdedge, hdf, hdg⟩ := hstep
      -- `f` is non-outer: it is CSA-reachable from `face₂ ≠ outerFace`.
      have hface₂_ne : data.face₂ ≠ hNT.outerFace := data.face₂_not_outer
      have hf_ne : f ≠ hNT.outerFace :=
        hNT.side_subset_nonouter hface₂_ne (g := f) ih
      -- the step's edge is non-chord (chord ∈ C₂.edgeSet, this edge ∉).
      have hch : M.dartEdge d ≠ s(u, v) := by
        intro he; exact hdedge (he ▸ chord_mem_C₂_edgeSet data)
      -- the step's edge is non-boundary: else it would reach `outerFace`.
      have hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
        intro hbedge
        rcases ProofsInTheBook.ZinanCh35InnerConn.boundaryEdge_dart_outer hbedge with ho | ho
        · exact hf_ne (hdf ▸ ho)
        · -- `dartFace (α d) = g' = outerFace`; so `face₂ ↝_bank g' = outerFace`.
          have hg'_outer : g' = hNT.outerFace := hdg ▸ ho
          apply not_bankReach_face₂_outerFace data
          -- `face₂ ↝_bank f` (lift of `ih`) then the step to `g' = outerFace`.
          have hbankf : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data)) data.face₂ f :=
            chordSplitAdj_reach_imp_dualReach data ih
          have : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data)) data.face₂ g' :=
            hbankf.tail ⟨d, hdedge, hdf, hdg⟩
          rwa [hg'_outer] at this
      -- assemble the CSA step and append.
      exact ih.tail ⟨d, hdf, hdg, hbe, hch⟩

/-! ## 6. The bank-side fact for the forward run (the chain's real content, UNCONDITIONAL)

For every dart `e` of the forward `v → u` run (the arc darts of `C₂`), the bounded face across its
boundary edge, `dartFace (α e)`, lies in `side₂`.  Proof: the bank theorem's `right_bank` gives
`face₂ = faceRight 0 ↝_bank faceRight (arc index) = dartFace (α e)`; lift to `ChordSplitAdj` by §5. -/

/-- **The forward-run bank-side fact (UNCONDITIONAL).**  For each arc dart of `C₂` (forward `v → u`
run), the bounded reverse face is in `side₂`. -/
theorem fwdArc_reverse_face_mem_side₂ (data : hNT.ChordSplitData u v) (i : Fin (fwdArc data).len) :
    M.dartFace (M.α ((fwdArc data).arcDart i)) ∈ data.side₂ := by
  -- the arc dart is `C₂.dart (i.succ)`; its reverse face is `faceRight (i.succ)`.
  have hi : (i.succ : Fin (C₂ data).len) = i.succ := rfl
  have hface : (C₂ data).faceRight i.succ = M.dartFace (M.α ((fwdArc data).arcDart i)) := by
    show M.dartFace (M.α ((C₂ data).dart i.succ)) = M.dartFace (M.α ((fwdArc data).arcDart i))
    show M.dartFace (M.α (SimplePrimalCycle.chordArcDart (fwdArc data) data.dart i.succ))
        = M.dartFace (M.α ((fwdArc data).arcDart i))
    rw [SimplePrimalCycle.chordArcDart_succ]
  -- `right_bank`: faceRight 0 ↝_bank faceRight (i.succ).
  have hbank : Relation.ReflTransGen (DualAvoidsCycleStep M (C₂ data))
      data.face₂ ((C₂ data).faceRight i.succ) := by
    rw [← C₂_faceRight_zero data]
    exact (bankC₂ data).right_bank ⟨0, (C₂ data).len_pos⟩ i.succ
  rw [hface] at hbank
  -- lift to ChordSplitAdj = side₂ membership.
  exact bankReach_face₂_lifts_to_chordSplitAdj data hbank

/-- An arc dart of `C₂` (forward run) has a non-chord (boundary) edge. -/
lemma fwdArc_dartEdge_ne_chord (data : hNT.ChordSplitData u v) (i : Fin (fwdArc data).len) :
    M.dartEdge ((fwdArc data).arcDart i) ≠ s(u, v) := by
  intro he
  -- the arc dart lies on the outer cycle, so its edge is a boundary edge; but `s(u,v)` is not.
  apply data.chord.not_boundary_edge
  rw [← he]
  show M.dartEdge ((fwdArc data).arcDart i) ∈ hNT.outerCycle.edges
  rw [hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem ((fwdArc data).boundary i)

/-- **For every forward-run vertex, the tail lies in `sideRegion₂` (UNCONDITIONAL).**  Composes
`fwdArc_reverse_face_mem_side₂` with the landed per-dart bridge
`ZinanCh35ArcDartRun.dartRun_tail_mem_sideRegion₂_of_face`. -/
theorem fwdArc_tail_mem_sideRegion₂ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (i : Fin (fwdArc data).len) :
    M.tail ((fwdArc data).arcDart i) ∈ sideRegion₂ data :=
  ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.dartRun_tail_mem_sideRegion₂_of_face
    data hsep (fwdArc_dartEdge_ne_chord data i) (fwdArc_reverse_face_mem_side₂ data i)

/-! ## 7. The honest assembly: the single isolated orientation input discharges everything

The bank theorem produced the side-2 face datum for the forward run.  The ONE remaining input — the
genuine, irreducible Jordan/orientation residual the whole codebase isolates uniformly
(`ZinanCh35BankOrient.bank_datum_substrate_symmetric`, `ZinanCh35Contiguity` docstring) — is that the
opaque label `data.arc.path₂` *is* the forward `v → u` run: every `path₂`-internal vertex is the tail
of a forward-run dart.  We name it `ForwardRunAligned₂` (and its mirror `ForwardRunAligned₁`).
Supplying it discharges `BankSideDatum`, `ChordArcBankOrientation`, and ultimately
`ArcSideIdentification` and **both** confinements. -/

/-- **The orientation alignment input for side 2.**  Every `path₂`-internal vertex is realized by a
forward-`v → u`-run dart (an arc dart of `C₂`).  This is the single Jordan/orientation residual; it
is *not* a substrate consequence (the two cyclic arcs carry the identical extractable predicate). -/
def ForwardRunAligned₂ (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {w : M.Vertex}, w ∈ data.arc.path₂.internalVertices →
    ∃ i : Fin (fwdArc data).len, M.tail ((fwdArc data).arcDart i) = w

/-- **`BankSideDatum` from the side-2 alignment input.**  Each aligned `path₂`-internal vertex is a
forward-run tail; the forward-run reverse face is in `side₂` (`fwdArc_reverse_face_mem_side₂`), and
the forward-run edge is non-chord (`fwdArc_dartEdge_ne_chord`). -/
theorem bankSideDatum_of_forwardRunAligned₂ (data : hNT.ChordSplitData u v)
    (halign : ForwardRunAligned₂ data) :
    ProofsInTheBook.ZinanCh35Contiguity.BankSideDatum data := by
  intro w hw
  obtain ⟨i, hi⟩ := halign hw
  exact ⟨(fwdArc data).arcDart i, fwdArc_dartEdge_ne_chord data i, hi,
    fwdArc_reverse_face_mem_side₂ data i⟩

/-- **`ChordArcBankOrientation` (side-1 confinement's datum) from the side-2 alignment input.** -/
theorem chordArcBankOrientation_of_forwardRunAligned₂ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (halign : ForwardRunAligned₂ data) :
    ProofsInTheBook.ZinanCh35Side1Confine.ChordArcBankOrientation data :=
  ProofsInTheBook.ZinanCh35Contiguity.chordArcBankOrientation_of_bankSide data hsep
    (bankSideDatum_of_forwardRunAligned₂ data halign)

/-! ## 8. The symmetric side-1 half: `C₁ = chord ∪ (u → v run)`

The mirror of §1–§7 with the chord dart reversed (`α data.dart`), so the bank's right side is `face₁`
and the forward run is the *other* cyclic arc.  This produces, for every dart of the `u → v` run,
`dartFace (α e) ∈ side₁`, hence `tail e ∈ sideRegion₁`. -/

/-- The dart-arc realizing the `u → v` boundary run (between the reversed chord-dart endpoints). -/
noncomputable def bwdArc (data : hNT.ChordSplitData u v) :
    DartArc M hNT.outerCycle (M.head (M.α data.dart)) (M.tail (M.α data.dart)) := by
  classical
  have hedge : M.dartEdge (M.α data.dart) = s(u, v) := by
    rw [M.dartEdge_alpha]; exact hNT.chordDart_edge data.chord
  have hxy_edge : s(M.tail (M.α data.dart), M.head (M.α data.dart)) = s(u, v) := hedge
  have hxy_ne : M.tail (M.α data.dart) ≠ M.head (M.α data.dart) := by
    intro hcontra
    have h1 : s(M.head (M.α data.dart), M.head (M.α data.dart)) = s(u, v) := hcontra ▸ hxy_edge
    have huv : u = v := by
      rcases Sym2.eq_iff.mp h1.symm with ⟨hl, hr⟩ | ⟨hl, hr⟩
      · exact hl.trans hr.symm
      · exact hl.trans hr.symm
    exact data.chord.endpoints_ne huv
  have hx_bv : hNT.outerCycle.IsBoundaryVertex (M.tail (M.α data.dart)) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨hxu, _⟩ | ⟨hxv, _⟩
    · rw [hxu]; exact data.chord.left_boundary
    · rw [hxv]; exact data.chord.right_boundary
  have hy_bv : hNT.outerCycle.IsBoundaryVertex (M.head (M.α data.dart)) := by
    rcases Sym2.eq_iff.mp hxy_edge with ⟨_, hyv⟩ | ⟨_, hyu⟩
    · rw [hyv]; exact data.chord.right_boundary
    · rw [hyu]; exact data.chord.left_boundary
  have hnbe : ¬ hNT.outerCycle.IsBoundaryEdge
      s(M.head (M.α data.dart), M.tail (M.α data.dart)) := by
    rw [show (s(M.head (M.α data.dart), M.tail (M.α data.dart)) : Sym2 M.Vertex)
          = s(M.tail (M.α data.dart), M.head (M.α data.dart)) from Sym2.eq_swap, hxy_edge]
    exact data.chord.not_boundary_edge
  exact (hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple
    (Ne.symm hxy_ne) hy_bv hx_bv hnbe).1

lemma bwdArc_len (data : hNT.ChordSplitData u v) : 2 ≤ (bwdArc data).len := by
  classical
  show 2 ≤ ((hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple _ _ _ _).1).len
  exact (hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple _ _ _ _).2

/-- `C₁ = chord ∪ (u → v run)`: `ofDartArc (bwdArc) (α data.dart)`. -/
noncomputable def C₁ (data : hNT.ChordSplitData u v) : SimplePrimalCycle M :=
  SimplePrimalCycle.ofDartArc (bwdArc data) (M.α data.dart) (bwdArc_len data) rfl rfl

lemma C₁_dart_zero (data : hNT.ChordSplitData u v) :
    (C₁ data).dart ⟨0, (C₁ data).len_pos⟩ = M.α data.dart := by
  show SimplePrimalCycle.chordArcDart (bwdArc data) (M.α data.dart) ⟨0, (C₁ data).len_pos⟩
      = M.α data.dart
  exact SimplePrimalCycle.chordArcDart_zero _ _

/-- `faceRight 0` of `C₁` is `face₁` (`= dartFace (α (α data.dart)) = dartFace data.dart`). -/
lemma C₁_faceRight_zero (data : hNT.ChordSplitData u v) :
    (C₁ data).faceRight ⟨0, (C₁ data).len_pos⟩ = data.face₁ := by
  show M.dartFace (M.α ((C₁ data).dart ⟨0, (C₁ data).len_pos⟩)) = M.dartFace data.dart
  rw [C₁_dart_zero, M.alpha_alpha]

/-- Every edge of `C₁` is the chord or a boundary edge. -/
lemma C₁_edge_chord_or_boundary (data : hNT.ChordSplitData u v) (i : Fin (C₁ data).len) :
    (C₁ data).edge i = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge ((C₁ data).edge i) := by
  have hedge : M.dartEdge (M.α data.dart) = s(u, v) := by
    rw [M.dartEdge_alpha]; exact hNT.chordDart_edge data.chord
  have hedge_i : (C₁ data).edge i = M.dartEdge ((C₁ data).dart i) := rfl
  rw [hedge_i]
  show M.dartEdge (SimplePrimalCycle.chordArcDart (bwdArc data) (M.α data.dart) i) = s(u, v) ∨
    hNT.outerCycle.IsBoundaryEdge
      (M.dartEdge (SimplePrimalCycle.chordArcDart (bwdArc data) (M.α data.dart) i))
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
  · left; rw [SimplePrimalCycle.chordArcDart_zero]; exact hedge
  · right
    rw [SimplePrimalCycle.chordArcDart_succ]
    show M.dartEdge ((bwdArc data).arcDart i') ∈ hNT.outerCycle.edges
    rw [hNT.outerCycle.edges_eq]
    exact List.mem_map_of_mem ((bwdArc data).boundary i')

lemma chord_mem_C₁_edgeSet (data : hNT.ChordSplitData u v) :
    (s(u, v) : Sym2 M.Vertex) ∈ (C₁ data).edgeSet := by
  rw [SimplePrimalCycle.mem_edgeSet_iff]
  refine ⟨⟨0, (C₁ data).len_pos⟩, ?_⟩
  have : (C₁ data).edge ⟨0, (C₁ data).len_pos⟩ = M.dartEdge ((C₁ data).dart ⟨0, (C₁ data).len_pos⟩) :=
    rfl
  rw [this, C₁_dart_zero, M.dartEdge_alpha]; exact (hNT.chordDart_edge data.chord).symm

noncomputable def arcIdx₀C₁ (data : hNT.ChordSplitData u v) : Fin (C₁ data).len :=
  ((bwdArc data).firstIdx).succ

lemma faceLeft_arcIdx₀C₁ (data : hNT.ChordSplitData u v) :
    (C₁ data).faceLeft (arcIdx₀C₁ data) = hNT.outerFace := by
  show M.dartFace ((C₁ data).dart (arcIdx₀C₁ data)) = hNT.outerFace
  show M.dartFace (SimplePrimalCycle.chordArcDart (bwdArc data) (M.α data.dart)
      ((bwdArc data).firstIdx).succ) = hNT.outerFace
  rw [SimplePrimalCycle.chordArcDart_succ]
  exact (hNT.outerCycle.mem_darts_iff _).mp ((bwdArc data).boundary _)

noncomputable def bankC₁ (data : hNT.ChordSplitData u v) :
    SimpleCycleBankTheorem M (C₁ data) :=
  simpleCycleBankTheorem_holds (C₁ data) hNT.sphere hNT.simpleGraph

lemma not_bankReach_face₁_outerFace (data : hNT.ChordSplitData u v) :
    ¬ Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data)) data.face₁ hNT.outerFace := by
  intro hreach
  have hreach' : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data))
      ((C₁ data).faceRight ⟨0, (C₁ data).len_pos⟩) ((C₁ data).faceLeft (arcIdx₀C₁ data)) := by
    rw [C₁_faceRight_zero, faceLeft_arcIdx₀C₁]; exact hreach
  have hsym : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data))
      ((C₁ data).faceLeft (arcIdx₀C₁ data)) ((C₁ data).faceRight ⟨0, (C₁ data).len_pos⟩) :=
    Relation.ReflTransGen.symmetric
      (fun _ _ h => dualAvoidsCycleStep_symm (C₁ data) h) hreach'
  exact (bankC₁ data).left_right_sep (arcIdx₀C₁ data) ⟨0, (C₁ data).len_pos⟩ hsym

/-- A `ChordSplitAdj` step is a `C₁`-avoiding dual step. -/
lemma chordSplitAdj_imp_dualStepC₁ (data : hNT.ChordSplitData u v) {f g : M.Face}
    (h : hNT.ChordSplitAdj u v f g) :
    DualAvoidsCycleStep M (C₁ data) f g := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := h
  refine ⟨d, ?_, hdf, hdg⟩
  intro hmem
  rw [SimplePrimalCycle.mem_edgeSet_iff] at hmem
  obtain ⟨i, hi⟩ := hmem
  rcases C₁_edge_chord_or_boundary data i with hc | hb
  · exact hch (by rw [hi, hc])
  · exact hbe (by rw [hi]; exact hb)

lemma chordSplitAdj_reach_imp_dualReachC₁ (data : hNT.ChordSplitData u v) {f g : M.Face}
    (h : Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g) :
    Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data)) f g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (chordSplitAdj_imp_dualStepC₁ data hstep)

/-- The side-1 bank → `ChordSplitAdj` lift (mirror of `bankReach_face₂_lifts_to_chordSplitAdj`). -/
lemma bankReach_face₁_lifts_to_chordSplitAdj (data : hNT.ChordSplitData u v) {g : M.Face}
    (h : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data)) data.face₁ g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail f g' hpre hstep ih =>
      obtain ⟨d, hdedge, hdf, hdg⟩ := hstep
      have hface₁_ne : data.face₁ ≠ hNT.outerFace := data.face₁_not_outer
      have hf_ne : f ≠ hNT.outerFace :=
        hNT.side_subset_nonouter hface₁_ne (g := f) ih
      have hch : M.dartEdge d ≠ s(u, v) := by
        intro he; exact hdedge (he ▸ chord_mem_C₁_edgeSet data)
      have hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
        intro hbedge
        rcases ProofsInTheBook.ZinanCh35InnerConn.boundaryEdge_dart_outer hbedge with ho | ho
        · exact hf_ne (hdf ▸ ho)
        · have hg'_outer : g' = hNT.outerFace := hdg ▸ ho
          apply not_bankReach_face₁_outerFace data
          have hbankf : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data)) data.face₁ f :=
            chordSplitAdj_reach_imp_dualReachC₁ data ih
          have : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data)) data.face₁ g' :=
            hbankf.tail ⟨d, hdedge, hdf, hdg⟩
          rwa [hg'_outer] at this
      exact ih.tail ⟨d, hdf, hdg, hbe, hch⟩

/-- **The backward-run bank-side fact (UNCONDITIONAL).**  For each arc dart of `C₁` (the `u → v`
run), the bounded reverse face is in `side₁`. -/
theorem bwdArc_reverse_face_mem_side₁ (data : hNT.ChordSplitData u v) (i : Fin (bwdArc data).len) :
    M.dartFace (M.α ((bwdArc data).arcDart i)) ∈ data.side₁ := by
  have hface : (C₁ data).faceRight i.succ = M.dartFace (M.α ((bwdArc data).arcDart i)) := by
    show M.dartFace (M.α (SimplePrimalCycle.chordArcDart (bwdArc data) (M.α data.dart) i.succ))
        = M.dartFace (M.α ((bwdArc data).arcDart i))
    rw [SimplePrimalCycle.chordArcDart_succ]
  have hbank : Relation.ReflTransGen (DualAvoidsCycleStep M (C₁ data))
      data.face₁ ((C₁ data).faceRight i.succ) := by
    rw [← C₁_faceRight_zero data]
    exact (bankC₁ data).right_bank ⟨0, (C₁ data).len_pos⟩ i.succ
  rw [hface] at hbank
  exact bankReach_face₁_lifts_to_chordSplitAdj data hbank

lemma bwdArc_dartEdge_ne_chord (data : hNT.ChordSplitData u v) (i : Fin (bwdArc data).len) :
    M.dartEdge ((bwdArc data).arcDart i) ≠ s(u, v) := by
  intro he
  apply data.chord.not_boundary_edge
  rw [← he]
  show M.dartEdge ((bwdArc data).arcDart i) ∈ hNT.outerCycle.edges
  rw [hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem ((bwdArc data).boundary i)

/-- **For every backward-run (`u → v`) vertex, the tail lies in `sideRegion₁` (UNCONDITIONAL).** -/
theorem bwdArc_tail_mem_sideRegion₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (i : Fin (bwdArc data).len) :
    M.tail ((bwdArc data).arcDart i) ∈ sideRegion₁ data := by
  -- apply the side-1 endpoint producer to `α (arcDart i)`: its forward face is in side₁, its head
  -- is the tail of the arc dart.
  have hchord' : M.dartEdge (M.α ((bwdArc data).arcDart i)) ≠ s(u, v) := by
    rw [M.dartEdge_alpha]; exact bwdArc_dartEdge_ne_chord data i
  obtain ⟨_, hhead⟩ := ProofsInTheBook.ZinanCh35Side2Confine.endpoints_mem_sideRegion₁_of_face
    data hsep hchord' (bwdArc_reverse_face_mem_side₁ data i)
  -- head (α (arcDart i)) = tail (arcDart i).
  rwa [M.head_alpha] at hhead

/-- **The orientation alignment input for side 1.**  Every `path₁`-internal vertex is realized by a
backward-`u → v`-run dart (an arc dart of `C₁`). -/
def ForwardRunAligned₁ (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {w : M.Vertex}, w ∈ data.arc.path₁.internalVertices →
    ∃ i : Fin (bwdArc data).len, M.tail ((bwdArc data).arcDart i) = w

/-- **`path₁`-internal `⟹ ∈ sideRegion₁`, from the side-1 alignment input.** -/
theorem path₁_internal_mem_sideRegion₁_of_aligned (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (halign : ForwardRunAligned₁ data) {w : M.Vertex}
    (hw : w ∈ data.arc.path₁.internalVertices) : w ∈ sideRegion₁ data := by
  obtain ⟨i, hi⟩ := halign hw
  rw [← hi]; exact bwdArc_tail_mem_sideRegion₁ data hsep i

/-- **`ChordArcBankOrientation` (side-2 confinement's datum) from the side-1 alignment input.** -/
theorem chordArcBankOrientation₂_of_forwardRunAligned₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (halign : ForwardRunAligned₁ data) :
    ProofsInTheBook.ZinanCh35Side2Confine.ChordArcBankOrientation data :=
  ⟨fun hw => path₁_internal_mem_sideRegion₁_of_aligned data hsep halign hw⟩

/-! ## 9. The joint assembly: `ArcSideIdentification` and BOTH confinements

Supplying *both* alignment inputs discharges `ZinanCh35BankOrient.ArcSideIdentification`, and through
`ZinanCh35BankOrient.bothConfinements_of_arcSide`, **both** Chapter-35 confinements at once. -/

/-- **`path₂`-internal `⟹ ∈ sideRegion₂`, from the side-2 alignment input.** -/
theorem path₂_internal_mem_sideRegion₂_of_aligned (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (halign : ForwardRunAligned₂ data) {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices) : w ∈ sideRegion₂ data := by
  obtain ⟨i, hi⟩ := halign hw
  rw [← hi]; exact fwdArc_tail_mem_sideRegion₂ data hsep i

/-- **`ArcSideIdentification` from both alignment inputs.** -/
theorem arcSideIdentification_of_aligned (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (halign₁ : ForwardRunAligned₁ data) (halign₂ : ForwardRunAligned₂ data) :
    ProofsInTheBook.ZinanCh35BankOrient.ArcSideIdentification data :=
  ⟨fun hw => path₁_internal_mem_sideRegion₁_of_aligned data hsep halign₁ hw,
    fun hw => path₂_internal_mem_sideRegion₂_of_aligned data hsep halign₂ hw⟩

/-- **Both Chapter-35 confinements, from both alignment inputs.** -/
theorem bothConfinements_of_aligned (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (halign₁ : ForwardRunAligned₁ data) (halign₂ : ForwardRunAligned₂ data) :
    ProofsInTheBook.ZinanCh35Schoenflies.Side₁StarConfinement data ∧
      ProofsInTheBook.ZinanCh35Side2.Side₂SchoenfliesConfinementInput data hsep :=
  ProofsInTheBook.ZinanCh35BankOrient.bothConfinements_of_arcSide data hsep
    (arcSideIdentification_of_aligned data hsep halign₁ halign₂)

end ProofsInTheBook.ZinanCh35ArcSide

/-! ## Axiom audit (expect clean-3: `propext`, `Classical.choice`, `Quot.sound`). -/

-- The UNCONDITIONAL bank-side facts (the real new content of R8's chain A–F):
#print axioms ProofsInTheBook.ZinanCh35ArcSide.fwdArc_reverse_face_mem_side₂
#print axioms ProofsInTheBook.ZinanCh35ArcSide.fwdArc_tail_mem_sideRegion₂
#print axioms ProofsInTheBook.ZinanCh35ArcSide.bwdArc_reverse_face_mem_side₁
#print axioms ProofsInTheBook.ZinanCh35ArcSide.bwdArc_tail_mem_sideRegion₁
#print axioms ProofsInTheBook.ZinanCh35ArcSide.bankReach_face₂_lifts_to_chordSplitAdj
#print axioms ProofsInTheBook.ZinanCh35ArcSide.bankReach_face₁_lifts_to_chordSplitAdj
#print axioms ProofsInTheBook.ZinanCh35ArcSide.not_bankReach_face₂_outerFace

-- The honest assembly over the single isolated orientation input:
#print axioms ProofsInTheBook.ZinanCh35ArcSide.bankSideDatum_of_forwardRunAligned₂
#print axioms ProofsInTheBook.ZinanCh35ArcSide.chordArcBankOrientation_of_forwardRunAligned₂
#print axioms ProofsInTheBook.ZinanCh35ArcSide.chordArcBankOrientation₂_of_forwardRunAligned₁
#print axioms ProofsInTheBook.ZinanCh35ArcSide.arcSideIdentification_of_aligned
#print axioms ProofsInTheBook.ZinanCh35ArcSide.bothConfinements_of_aligned
