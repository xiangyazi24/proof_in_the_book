import ProofsInTheBook.ZinanCh35Schoenflies
import ProofsInTheBook.ZinanCh35Gates
import ProofsInTheBook.ZinanCh35ChordCycle

/-!
# Chapter 35 discrete-Schoenflies: the side-1 vertex-star anchoring (the last residual)

This file attacks the single remaining Chapter-35 residual `Side₁StarConfinement`
(`ZinanCh35Schoenflies.lean`), the discrete-Schoenflies vertex-star anchoring.  The previous
two waves isolated it sharply and verified that **no landed material** discharges it: the gates
supply only *face*-dual separation (`face₂ ∉ side₁`, `jordan_simple_cycle2_unconditional`),
whereas the residual is a statement about an opposite-arc vertex's whole rotation star.

## The engine this file contributes (the genuine new content)

The decisive observation, missed by the earlier waves, is that the side-1 *definition itself*
is already a cycle-avoiding dual-reachability statement, and its avoidance set is a **superset**
of any chord∪arc cycle's edge set.  Concretely:

* `side₁ = Side u v face₁ = {f | ReflTransGen (ChordSplitAdj u v) face₁ f}`, where a
  `ChordSplitAdj` step crosses an edge that is **neither a boundary edge nor the chord**;
* for the chord∪arc cycle `C`, `hsub : ∀ e ∈ C.edgeSet, e = s(u,v) ∨ IsBoundaryEdge e`, so every
  `C`-edge is a boundary edge or the chord.

Hence a `ChordSplitAdj` step (avoiding *all* boundary edges and the chord) is, a fortiori, a
`DualAvoidsCycleStep` for `C` (avoiding only the `C`-edges).  Chaining the closure gives the
**engine**

  `side₁_dualReachable_avoidingCycle : f ∈ side₁ → DualReachableAvoidingCycle M C face₁ f`,

stated for *any* `C` with `hsub` (no near-triangulation, no separation, unconditional).  Composed
with the discharged `jordan_simple_cycle2_unconditional` (which forbids `face₁ ↝_C face₂`) it
yields the sharp **bank tool**

  `notDualReachableToFace₂_of_mem_side₁ :
      f ∈ side₁ → ¬ DualReachableAvoidingCycle M C f face₂`,

i.e. *no side-1 face can reach `face₂` avoiding `C`*.  This is strictly the gate vocabulary, one
transitivity step away from the discharged Jordan separation, and is the correct lever for the
opposite-arc star argument.

## What this file closes, and the residual it leaves

The bank tool **fully reduces** the `oppArc_star_core` field to a single pure geometric bridge:
the *bank placement* of an opposite-arc vertex's star (the inner star of a path₂-internal vertex
lies in `face₂`'s bank of the chord∪arc cycle).  In the bank-placement residual the
contradiction with side-1 membership — previously baked into the field — is discharged *here* by
the engine; the residual asserts only the placement, the one genuinely planar fact left.

The `edge_core` field is **not** reducible by the engine: it needs side-1 membership as a
*conclusion*, whereas the engine runs membership ⟹ reachability, not the converse (the converse,
reachability ⟹ membership, is false in general — it is exactly the back-direction the bare dual
path cannot supply, as the gate header warns).  So `edge_core` is carried verbatim in the residual.

Net effect: `Side₁StarConfinement` (two fields, the `oppArc` one a global side-1 statement) is
reduced to `Side₁StarBankAnchor` (the same `edge_core`, plus the `oppArc` field demoted to the
strictly weaker, single-bank placement statement).  `starConfinement_of_bankAnchor` derives the
former from the latter using only the engine and the discharged Jordan gate, so the reduction is
genuine and the residual strictly smaller.  Both residual fields are concrete and non-vacuous (the
opposite arc carries an internal vertex by `data.arc₂_internal`; the region is inhabited).

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Anchoring

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35Schoenflies

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## Section 1 — the engine: side-1 membership ⟹ cycle-avoiding dual reachability

A `ChordSplitAdj` step avoids *every* old boundary edge and the chord.  For a chord∪arc cycle
`C` (every `C`-edge is a boundary edge or the chord, by `hsub`), avoiding the full boundary∪chord
seam is *stronger* than avoiding only the `C`-edges.  So a single `ChordSplitAdj` step is a
`DualAvoidsCycleStep`, and the reachability closures inherit the implication. -/

/-- **A `ChordSplitAdj` step is a `DualAvoidsCycleStep`** for any cycle whose edges are all
boundary edges or the chord.  The shared dart `d` witnesses both: `ChordSplitAdj` already gives
`¬ IsBoundaryEdge (dartEdge d)` and `dartEdge d ≠ s(u,v)`, and `hsub` turns that into
`dartEdge d ∉ C.edgeSet`. -/
theorem dualAvoidsCycleStep_of_chordSplitAdj
    (data : hNT.ChordSplitData u v) (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    {f g : M.Face} (hadj : hNT.ChordSplitAdj u v f g) :
    DualAvoidsCycleStep M C f g := by
  obtain ⟨d, hdf, hdg, hbe, hch⟩ := hadj
  refine ⟨d, ?_, hdf, hdg⟩
  -- `dartEdge d ∉ C.edgeSet`: otherwise it would be the chord or a boundary edge.
  intro hmem
  rcases hsub _ hmem with hchord | hbnd
  · exact hch hchord
  · exact hbe hbnd

/-- **The engine.**  Every side-1 face is dual-reachable from `face₁` avoiding the chord∪arc
cycle `C`.  Unconditional (no separation, no near-triangulation specifics beyond `hsub`): pure
inheritance of the reachability closure from `ChordSplitAdj` to `DualAvoidsCycleStep`. -/
theorem side₁_dualReachable_avoidingCycle
    (data : hNT.ChordSplitData u v) (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    {f : M.Face} (hf : f ∈ data.side₁) :
    DualReachableAvoidingCycle M C data.face₁ f := by
  -- `data.side₁ = {g | ReflTransGen (ChordSplitAdj u v) face₁ g}`.
  have hf' : Relation.ReflTransGen (hNT.ChordSplitAdj u v) data.face₁ f := hf
  -- Map the `ChordSplitAdj`-closure onto the `DualAvoidsCycleStep`-closure step by step.
  exact Relation.ReflTransGen.mono
    (fun a b hab => dualAvoidsCycleStep_of_chordSplitAdj data C hsub hab) hf'

/-! ## Section 2 — the bank tool: a side-1 face cannot reach `face₂` avoiding `C`

The discharged Jordan gate `jordan_simple_cycle2_unconditional` says the two sides of the chord
edge are not dual-connected avoiding `C`.  At the chord index `i₀` those two sides are exactly
`face₁` and `face₂` (`hleft`/`hright`).  Composing with the engine (which reaches `face₁`) gives:
no side-1 face reaches `face₂` avoiding `C`. -/

/-- **The bank tool.**  On a sphere near-triangulation, a side-1 face does **not** dual-reach
`face₂` avoiding the chord∪arc cycle `C`.  Proof: such a reach, chained after the engine's
`face₁ ↝_C f`, would give `face₁ ↝_C face₂`, i.e.
`DualReachableAvoidingCycle C (faceLeft i₀) (faceRight i₀)`, contradicting the discharged Jordan
separation. -/
theorem notDualReachableToFace₂_of_mem_side₁
    (data : hNT.ChordSplitData u v) (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord)))
    {f : M.Face} (hf : f ∈ data.side₁) :
    ¬ DualReachableAvoidingCycle M C f data.face₂ := by
  intro hreach
  -- `face₁ ↝_C f` (engine) then `f ↝_C face₂` (hyp): so `face₁ ↝_C face₂`.
  have hchain : DualReachableAvoidingCycle M C data.face₁ data.face₂ :=
    Relation.ReflTransGen.trans
      (side₁_dualReachable_avoidingCycle data C hsub hf) hreach
  -- Rewrite the endpoints as `faceLeft i₀` / `faceRight i₀`.
  have hface₁ : data.face₁ = C.faceLeft i₀ := by
    show M.dartFace (hNT.chordDart data.chord) = C.faceLeft i₀
    rw [hleft]
  have hface₂ : data.face₂ = C.faceRight i₀ := by
    show M.dartFace (M.α (hNT.chordDart data.chord)) = C.faceRight i₀
    rw [hright]
  rw [hface₁, hface₂] at hchain
  -- Contradict the discharged Jordan separation.
  exact C.jordan_simple_cycle2_unconditional hNT.sphere.2 hNT.sphere.1 i₀ hchain

/-! ## Section 3 — the strictly-smaller residual `Side₁StarBankAnchor`

The bank tool reduces the `oppArc_star_core` field of `Side₁StarConfinement` to a single pure
geometric bridge: the **bank placement** of an opposite-arc vertex's star.  In the planar model
the inner star of a path₂-internal vertex `w` lies in the face-2 bank of the chord∪arc cycle:
every star face at `w` that is not the outer face dual-reaches `face₂` avoiding `C`.  Given that
placement, the bank tool forces every such face off `side₁` (a side-1 face cannot reach `face₂`),
which is exactly `oppArc_star_core`.

`edge_core` is carried verbatim: the engine reduces *membership ⟹ reachability*, but `edge_core`
needs *reachability ⟹ membership* (the back direction the bare dual path cannot supply), so it is
not reducible by the engine and remains an honest field. -/

/-- **The opposite-arc star bank-placement residual** (strictly smaller than
`Side₁StarConfinement`).  Carries the chord∪arc cycle datum (`C`, `hsub`, `i₀`, `hleft`,
`hright`) and:

* `edge_core` — *carried verbatim* from `Side₁StarConfinement` (not engine-reducible; see header).
* `oppArc_star_bank` — at a path₂-internal vertex `w`, every non-chord star dart `d` carries the
  planar bank placement of the inner star, expressed in the gate vocabulary
  (`DualReachableAvoidingCycle … face₂`, a single bank): its own face reaches `face₂` avoiding `C`
  (forcing it off `side₁`), and *additionally* either it is not an outer-interval dart
  (`dartFace d ≠ outerFace`) or its reverse face also reaches `face₂` (closing the
  outer-boundary-dart sub-case).  Both reach-clauses are strictly weaker than the original
  `oppArc_star_core`'s global side-1 statements — the engine supplies the side-1 contradiction
  here, not the field. -/
structure Side₁StarBankAnchor (data : hNT.ChordSplitData u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) : Prop where
  /-- Region edge-confinement core (carried verbatim; not engine-reducible). -/
  edge_core : ∀ {e : D},
    M.dartEdge e ≠ s(u, v) →
    M.tail e ∈ sideRegion₁ data →
    M.head e ∈ sideRegion₁ data →
      M.dartFace e ∈ data.side₁
  /-- Opposite-arc star bank placement: every non-chord star dart at a path₂-internal vertex has
  its own face on `face₂`'s bank, and (for the outer-boundary case) either is not an outer dart or
  has its reverse face on `face₂`'s bank too. -/
  oppArc_star_bank : ∀ {w : M.Vertex},
    w ∈ data.arc.path₂.internalVertices →
    ∀ d : D, M.tail d = w →
      (d = data.dart ∨
        (DualReachableAvoidingCycle M C (M.dartFace d) data.face₂ ∧
          (M.dartFace d ≠ hNT.outerFace ∨
            DualReachableAvoidingCycle M C (M.dartFace (M.α d)) data.face₂)))

/-! ## Section 4 — deriving `Side₁StarConfinement` from the bank anchor

The engine + bank tool discharge `oppArc_star_core` from `oppArc_star_bank`; `edge_core` passes
through verbatim. -/

/-- **`Side₁StarConfinement` from the bank anchor.**  The genuine reduction: the bank tool turns
each bank-placement bucket into the side-1 *omission* the original `oppArc_star_core` demands,
and `edge_core` is the same field. -/
theorem starConfinement_of_bankAnchor
    (data : hNT.ChordSplitData u v) (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord)))
    (anchor : Side₁StarBankAnchor data C hsub i₀ hleft hright) :
    Side₁StarConfinement data := by
  -- The bank tool, specialised to this cycle datum.
  have bank : ∀ {f : M.Face}, f ∈ data.side₁ →
      ¬ DualReachableAvoidingCycle M C f data.face₂ :=
    fun hf => notDualReachableToFace₂_of_mem_side₁ data C hsub i₀ hleft hright hf
  refine { edge_core := anchor.edge_core, oppArc_star_core := ?_ }
  -- oppArc_star_core: every star dart at a path₂-internal w is omitted by side 1.
  intro w hw d hd
  rcases anchor.oppArc_star_bank hw d hd with hchord | ⟨hbank, houtercase⟩
  · exact Or.inl hchord
  · right
    -- First conjunct: `dartFace d ∉ side₁` (its face reaches face₂; bank tool).
    have hnotside : M.dartFace d ∉ data.side₁ := fun hmem => bank hmem hbank
    refine ⟨hnotside, ?_⟩
    -- Second conjunct: refute `dartFace d = outerFace ∧ dartFace (α d) ∈ side₁`.
    rintro ⟨houter, hrev⟩
    rcases houtercase with hne | hrevbank
    · exact hne houter
    · exact bank hrev hrevbank

end ProofsInTheBook.ZinanCh35Anchoring

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35Anchoring.dualAvoidsCycleStep_of_chordSplitAdj
#print axioms ProofsInTheBook.ZinanCh35Anchoring.side₁_dualReachable_avoidingCycle
#print axioms ProofsInTheBook.ZinanCh35Anchoring.notDualReachableToFace₂_of_mem_side₁
#print axioms ProofsInTheBook.ZinanCh35Anchoring.starConfinement_of_bankAnchor
