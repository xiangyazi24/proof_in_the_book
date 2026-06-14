import ProofsInTheBook.ZinanCh35EdgeCore

/-!
# Chapter 35 face-coverage: `BoundedFacePartition` from inner-face dual connectivity

This file works toward the **coverage bridge** `BoundedFacePartition`
(`ZinanCh35EdgeCore.lean`): every non-outer face lies in `side₁` or `side₂`, i.e. is
`ChordSplitAdj`-reachable from `face₁` or from `face₂`.

## The reduction (clean, unconditional)

`ChordSplitAdj u v` is "share an edge that is **neither a boundary edge nor the chord**".
Relax it to **`InnerAdj`** = "share an edge that is **not a boundary edge**" (the inner-face
dual adjacency).  Then `ChordSplitAdj` is exactly `InnerAdj` with the single dual edge
`{face₁, face₂}` removed: the only `InnerAdj`-step carrying the chord edge `s(u,v)` runs between
`face₁` and `face₂` (the chord has exactly two darts, `dart` and `α dart`, with faces `face₁`,
`face₂`).

An abstract graph fact — *removing one edge `{a,b}` from a relation leaves every `a`-reachable
vertex reachable from `a` or from `b` in the smaller relation* (`reflTransGen_removeEdge`) — then
gives: if every non-outer face is `InnerAdj`-reachable from `face₁`, then every non-outer face is
`ChordSplitAdj`-reachable from `face₁` or `face₂`, i.e. `BoundedFacePartition`.

So `BoundedFacePartition` is **reduced, clean-3 and unconditionally**, to the single sharper
planar fact

  `InnerFaceConnectedFromFace₁` :  every non-outer face is `InnerAdj`-reachable from `face₁`,

the connectivity of the inner-face dual graph (faces glued along non-boundary edges).  This is the
honest residual: it is the cut-component identification the `ZinanCh35EdgeCore` header flagged as
missing, now isolated as inner-face *dual connectivity* with the chord-exclusion algebra fully
discharged.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Coverage

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## 1. Abstract one-edge-removal lemma

Removing a single (undirected) edge `{a, b}` from a relation `r` keeps every `a`-reachable
vertex reachable — from `a` or from `b` — in the smaller relation. -/

section Abstract

variable {V : Type*} (r : V → V → Prop)

/-- `r` with the single undirected edge `{a, b}` removed. -/
def removeEdge (a b : V) : V → V → Prop :=
  fun x y => r x y ∧ ¬ ((x = a ∧ y = b) ∨ (x = b ∧ y = a))

/-- **One-edge removal.**  If `w` is reachable from `a` in `r`, then `w` is reachable from `a` or
from `b` in `r` with the edge `{a, b}` removed. -/
theorem reflTransGen_removeEdge {a b : V} {w : V}
    (h : Relation.ReflTransGen r a w) :
    Relation.ReflTransGen (removeEdge r a b) a w ∨
      Relation.ReflTransGen (removeEdge r a b) b w := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail x w hax hxw ih =>
      by_cases hedge : (x = a ∧ w = b) ∨ (x = b ∧ w = a)
      · -- The last step is exactly the removed edge `{a, b}`.
        rcases hedge with ⟨hxa, hwb⟩ | ⟨hxb, hwa⟩
        · subst hwb; exact Or.inr Relation.ReflTransGen.refl
        · subst hwa; exact Or.inl Relation.ReflTransGen.refl
      · -- The last step survives in `removeEdge`.
        have hstep : removeEdge r a b x w := ⟨hxw, hedge⟩
        rcases ih with hA | hB
        · exact Or.inl (hA.tail hstep)
        · exact Or.inr (hB.tail hstep)

end Abstract

/-! ## 2. `InnerAdj`: the inner-face dual adjacency (non-boundary edges only)

`InnerAdj f g`: `f` and `g` share an edge that is not a boundary edge.  This is `ChordSplitAdj`
*without* the chord exclusion. -/

/-- **Inner-face dual adjacency.**  Two faces share an edge that is not a boundary edge. -/
def InnerAdj (hNT : NearTriangulation M) (f g : M.Face) : Prop :=
  ∃ d : D,
    M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧
      ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d)

variable (hNT) in
/-- A `ChordSplitAdj`-step is an `InnerAdj`-step. -/
lemma innerAdj_of_chordSplitAdj {f g : M.Face} (h : hNT.ChordSplitAdj u v f g) :
    InnerAdj hNT f g := by
  obtain ⟨d, hdf, hdg, hbe, _⟩ := h
  exact ⟨d, hdf, hdg, hbe⟩

/-! ## 3. The chord-edge algebra: an `InnerAdj`-step carrying the chord runs `face₁ ↔ face₂`

A dart whose edge is the chord `s(u, v)` is `dart` or `α dart` (simple graph, `no_parallel`); so its
face / `α`-face pair is `{face₁, face₂}`. -/

/-- A dart with the chord edge is `data.dart` or `M.α data.dart`. -/
lemma eq_dart_or_alpha_of_chordEdge (data : hNT.ChordSplitData u v) {d : D}
    (hd : M.dartEdge d = s(u, v)) : d = data.dart ∨ d = M.α data.dart := by
  have hsame : M.dartEdge d = M.dartEdge data.dart := by
    rw [hd]; exact (hNT.chordDart_edge data.chord).symm
  have hsc : M.α.SameCycle data.dart d :=
    M.alpha_sameCycle_of_dartEdge_eq hNT.simpleGraph hsame.symm
  exact (M.alpha_sameCycle_iff data.dart d).1 hsc

/-- **The chord `InnerAdj`-edge runs between `face₁` and `face₂`.**  If `d` witnesses an
`InnerAdj`-step `f → g` and carries the chord edge, then `{f, g} = {face₁, face₂}` (as the ordered
pair `(face₁, face₂)` or `(face₂, face₁)`). -/
lemma face_pair_of_chordEdge (data : hNT.ChordSplitData u v) {d : D} {f g : M.Face}
    (hdf : M.dartFace d = f) (hdg : M.dartFace (M.α d) = g)
    (hd : M.dartEdge d = s(u, v)) :
    (f = data.face₁ ∧ g = data.face₂) ∨ (f = data.face₂ ∧ g = data.face₁) := by
  rcases eq_dart_or_alpha_of_chordEdge data hd with hcase | hcase
  · -- `d = dart`: `f = face₁`, `g = face₂`.
    left
    refine ⟨?_, ?_⟩
    · rw [← hdf, hcase]; rfl
    · rw [← hdg, hcase]; rfl
  · -- `d = α dart`: `f = face₂`, `g = face₁`.
    right
    refine ⟨?_, ?_⟩
    · rw [← hdf, hcase]; rfl
    · rw [← hdg, hcase, M.alpha_alpha]; rfl

/-- **`InnerAdj` minus the `{face₁, face₂}` edge is `ChordSplitAdj`.**  An `InnerAdj`-step whose
ordered face-pair is neither `(face₁, face₂)` nor `(face₂, face₁)` is a genuine `ChordSplitAdj`-step
(its edge cannot be the chord). -/
lemma chordSplitAdj_of_removeEdge_innerAdj (data : hNT.ChordSplitData u v) {f g : M.Face}
    (h : removeEdge (InnerAdj hNT) data.face₁ data.face₂ f g) :
    hNT.ChordSplitAdj u v f g := by
  obtain ⟨⟨d, hdf, hdg, hbe⟩, hne⟩ := h
  refine ⟨d, hdf, hdg, hbe, ?_⟩
  intro hchord
  -- chord edge ⟹ `(f, g)` is `(face₁, face₂)` or `(face₂, face₁)`, contradicting `hne`.
  exact hne (face_pair_of_chordEdge data hdf hdg hchord)

/-! ## 4. Transporting reachability through the relation inclusion `removeEdge InnerAdj ⊆ ChordSplitAdj` -/

/-- A `removeEdge InnerAdj`-walk lifts to a `ChordSplitAdj`-walk (pointwise inclusion of steps). -/
lemma reflTransGen_chordSplitAdj_of_removeEdge (data : hNT.ChordSplitData u v) {s g : M.Face}
    (h : Relation.ReflTransGen (removeEdge (InnerAdj hNT) data.face₁ data.face₂) s g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) s g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact ih.tail (chordSplitAdj_of_removeEdge_innerAdj data hstep)

/-! ## 5. The sharp residual + the reduction to it -/

/-- **The sharp residual: inner-face dual connectivity from `face₁`.**  Every non-outer face is
`InnerAdj`-reachable from `face₁` (the inner-face dual graph is connected, seeded at the chord-face
`face₁`).  This is the only genuinely-missing planar input behind face coverage. -/
def InnerFaceConnectedFromFace₁ (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {f : M.Face}, f ≠ hNT.outerFace →
    Relation.ReflTransGen (InnerAdj hNT) data.face₁ f

/-- **`BoundedFacePartition` from inner-face dual connectivity (the reduction).**
Given that every non-outer face is `InnerAdj`-reachable from `face₁`, every non-outer face is
`ChordSplitAdj`-reachable from `face₁` or `face₂`.  Proof: `InnerAdj`-reach `face₁ → f`, remove the
`{face₁, face₂}` edge (`reflTransGen_removeEdge`) to get `removeEdge`-reach from `face₁` or `face₂`,
then lift through `removeEdge InnerAdj ⊆ ChordSplitAdj`. -/
theorem boundedFacePartition_of_innerConnected (data : hNT.ChordSplitData u v)
    (hconn : InnerFaceConnectedFromFace₁ data) :
    BoundedFacePartition data := by
  intro f hf
  -- `InnerAdj`-reach `face₁ → f`.
  have hreach : Relation.ReflTransGen (InnerAdj hNT) data.face₁ f := hconn hf
  -- remove the chord dual edge `{face₁, face₂}`.
  rcases reflTransGen_removeEdge (InnerAdj hNT) (a := data.face₁) (b := data.face₂) hreach with
    hA | hB
  · -- `removeEdge`-reach from `face₁` ⟹ `ChordSplitAdj`-reach from `face₁` ⟹ `f ∈ side₁`.
    exact Or.inl (reflTransGen_chordSplitAdj_of_removeEdge data hA)
  · -- `removeEdge`-reach from `face₂` ⟹ `ChordSplitAdj`-reach from `face₂` ⟹ `f ∈ side₂`.
    exact Or.inr (reflTransGen_chordSplitAdj_of_removeEdge data hB)

/-! ## 6. End-to-end: the `edge_core` field, with the coverage bridge discharged by the residual

`edge_core_field` (`ZinanCh35EdgeCore`) needs the two bridges `BoundedFacePartition` and
`SideRegionInterChordEnds`.  Here the **coverage** bridge is discharged from the single inner-face
dual-connectivity residual; only the (independent) vertex-region intersection bridge remains a
hypothesis.  This certifies that closing the residual closes the coverage half of `edge_core`. -/

/-- **The `edge_core` field, with coverage supplied by inner-face dual connectivity.**  The only
remaining planar hypotheses are the sharp inner-face connectivity residual `hconn` and the
independent vertex-region intersection bridge `hinter`. -/
theorem edge_core_field_of_innerConnected (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hconn : InnerFaceConnectedFromFace₁ data)
    (hinter : SideRegionInterChordEnds data) :
    ∀ {e : D},
      M.dartEdge e ≠ s(u, v) →
      M.dartFace e ≠ hNT.outerFace →
      M.tail e ∈ ProofsInTheBook.ChordReconClose.sideRegion₁ data →
      M.head e ∈ ProofsInTheBook.ChordReconClose.sideRegion₁ data →
        M.dartFace e ∈ data.side₁ :=
  ProofsInTheBook.ZinanCh35EdgeCore.edge_core_field data hsep
    (boundedFacePartition_of_innerConnected data hconn) hinter

end ProofsInTheBook.ZinanCh35Coverage

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35Coverage.reflTransGen_removeEdge
#print axioms ProofsInTheBook.ZinanCh35Coverage.face_pair_of_chordEdge
#print axioms ProofsInTheBook.ZinanCh35Coverage.chordSplitAdj_of_removeEdge_innerAdj
#print axioms ProofsInTheBook.ZinanCh35Coverage.boundedFacePartition_of_innerConnected
#print axioms ProofsInTheBook.ZinanCh35Coverage.edge_core_field_of_innerConnected
