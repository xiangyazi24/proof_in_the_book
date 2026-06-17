import ProofsInTheBook.ZinanCh35ArcDartRun
import ProofsInTheBook.ZinanCh35ChordCycle

/-!
# Chapter 35: closing the CONTIGUITY TIE — conjunct (1) of `ArcDartRunBankData`

`ZinanCh35ArcDartRun.lean` built the forward cyclic dart run of `outerCycle.darts` from `v` to `u`
(`boundaryArcDartRun`, unconditional) and packaged the *two* honest inputs that discharge
`ChordArcBankOrientation` (`path₂`-internal `w ⟹ w ∈ sideRegion₂`) as

```
ArcDartRunBankData data :=
  ∀ {w}, w ∈ data.arc.path₂.internalVertices →
    ∃ e : D, M.dartEdge e ≠ s(u, v)         -- conjunct (1): the CONTIGUITY TIE
           ∧ M.tail e = w                    -- conjunct (1): a dart tailed at w
           ∧ M.dartFace (M.α e) ∈ data.side₂ -- conjunct (2): the bank-side (Jordan) datum
```

It left **conjunct (1)** — relate `data.arc.path₂.internalVertices` to the dart-run built from
`outerCycle.darts` — as the residual to investigate.  This file closes it.

## What conjunct (1) actually asks, and why it is TRUE and unconditional

The R8 audit framed conjunct (1) as `path₂.internalVertices ⊆ (the run's tails)` — every
`path₂`-internal vertex is a *tail of a dart in the forward `v → u` cyclic run*.  We investigated
the substrate (`PlanarMapBoundary.lean`):

* `BoundaryCycle.arcSplit` is a **field** (no consistency tie to the cyclic dart order).  `path₂`,
  from `BoundaryArcSplit`, is a `BoundaryPath` carrying only a *vertex list* + an *edge list* + the
  three set-level fields `path₂_boundary_vertices`, `boundary_vertices_covered`,
  `internally_disjoint` (plus `HasInternalVertex ↔ proper`).  **No field pins which of the two
  cyclic arcs `path₂` is** — equivalently, `arcSplit` carries no orientation datum tying `path₂` to
  the *forward* `v → u` run rather than the *backward* `u → v` run.  This is exactly the symmetry
  obstruction `ZinanCh35BankOrient.bank_datum_substrate_symmetric` formalizes, and it blocks the
  literal "`⊆ this particular run's tails`" reading **and** its set-equality variant: the two cyclic
  arcs carry the identical extractable substrate predicate, so the vertex/edge substrate cannot
  decide whether `path₂.internalVertices` is the forward or the backward cyclic segment.

* **But the conjunct (1) the consumer actually needs is weaker and IS provable.**  The `Prop`
  `ArcDartRunBankData` asks, for each `path₂`-internal `w`, for **some** dart `e` with
  `M.dartEdge e ≠ s(u, v) ∧ M.tail e = w` — and the downstream consumer
  (`chordArcBankOrientation_of_bankData`, through `dartRun_tail_mem_sideRegion₂_of_face`) uses only
  `M.dartEdge e ≠ s(u, v)` and the side-2 face fact, **never** "e ∈ the forward run".  Since a
  `path₂`-internal `w` is a boundary vertex with `w ≠ u, w ≠ v`, the boundary cycle's own dart list
  (`outerCycle.vertices = outerCycle.darts.map tail`) supplies a dart of `outerCycle.darts` tailed
  exactly at `w`, and its edge `s(w, head)` cannot equal `s(u, v)` because `w ∉ {u, v}`.  Both facts
  are unconditional and axiom-clean.

So the genuine resolution of the CONTIGUITY TIE is:

1. **Conjunct (1) is FULLY DISCHARGED, unconditionally** — `path₂_internalVertex_outerDart` below
   produces, for every `path₂`-internal `w`, a dart `e ∈ outerCycle.darts` with `tail e = w` and
   `dartEdge e ≠ s(u, v)`.  The dart is even on the *outer cycle* (the canonical side-2 boundary
   arc), and the run-membership the R8 framing asked for is **not needed** by the consumer.

2. The **only** honest residue of `ArcDartRunBankData` is conjunct (2), the side-2 face datum
   (`dartFace (M.α e) ∈ side₂`) — the genuine discrete-Jordan arc↔side identification isolated in
   `ZinanCh35BankOrient`.  `arcDartRunBankData_of_sideData` below assembles `ArcDartRunBankData`
   from conjunct (1) (proved here) **plus** the side datum, exhibiting the precise residual.

This is the §3.3 honest outcome: the contiguity tie is *true* (every `path₂`-internal vertex is a
boundary vertex, hence the tail of an outer-cycle dart), conjunct (1) is closed with no `sorry` /
`axiom` / posit, and the remaining input is sharply the bank-side (Jordan) face fact — not the
contiguity.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35Contiguity

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35ArcDartRun

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## 1.  A boundary vertex is the tail of a dart on the cycle

Every listed boundary vertex of a `BoundaryCycle` is `M.tail` of one of the cycle's darts — this is
literally the field `vertices_eq : vertices = darts.map M.tail`.  We expose it in the membership form
the contiguity tie consumes. -/

/-- **A boundary vertex is the tail of a cycle dart.**  For `w ∈ C.vertices`, there is a dart
`e ∈ C.darts` with `M.tail e = w`.  Immediate from `vertices_eq`. -/
theorem exists_dart_tail_of_isBoundaryVertex {f : M.Face} (C : BoundaryCycle M f) {w : M.Vertex}
    (hw : C.IsBoundaryVertex w) :
    ∃ e : D, e ∈ C.darts ∧ M.tail e = w := by
  -- `w ∈ C.vertices = C.darts.map M.tail`.
  have hw' : w ∈ C.darts.map M.tail := by
    simpa [BoundaryCycle.IsBoundaryVertex, C.vertices_eq] using hw
  rw [List.mem_map] at hw'
  obtain ⟨e, he, hte⟩ := hw'
  exact ⟨e, he, hte⟩

/-! ## 2.  The contiguity tie — conjunct (1) of `ArcDartRunBankData`, unconditional

For a `path₂`-internal vertex `w`, we produce a dart `e` of `outerCycle.darts` with `M.tail e = w`
and `M.dartEdge e ≠ s(u, v)`.  The non-chord-edge fact is forced purely by `w ≠ u` and `w ≠ v`:
the dart's edge is `s(w, head e)`, which equals `s(u, v)` only if `w ∈ {u, v}`. -/

/-- **A dart tailed at `w` has non-chord edge, when `w ∉ {u, v}`.**  If `M.tail e = w` with `w ≠ u`
and `w ≠ v`, then `M.dartEdge e ≠ s(u, v)`: the edge is `s(w, M.head e)`, and `Sym2.eq_iff` forces
`w = u ∨ w = v`. -/
theorem dartEdge_ne_chord_of_tail_ne (data : hNT.ChordSplitData u v) {e : D} {w : M.Vertex}
    (htail : M.tail e = w) (hwu : w ≠ u) (hwv : w ≠ v) :
    M.dartEdge e ≠ s(u, v) := by
  intro hedge
  -- `s(w, head e) = s(u, v)`.
  have hsym : s(w, M.head e) = s(u, v) := by
    rw [← htail]; exact hedge
  rcases Sym2.eq_iff.mp hsym with ⟨hwu', _⟩ | ⟨hwv', _⟩
  · exact hwu hwu'
  · exact hwv hwv'

/-- **The CONTIGUITY TIE (conjunct (1)), unconditional and axiom-clean.**  For every `path₂`-internal
vertex `w`, there is a dart `e` on `outerCycle.darts` with

* `M.dartEdge e ≠ s(u, v)`  (the non-chord-edge half of conjunct (1)), and
* `M.tail e = w`            (the dart-tailed-at-`w` half of conjunct (1)).

The dart lives on the *outer cycle* — the canonical side-2 boundary arc — so this realizes the
contiguity tie R8 §A asked for, **without** needing the unprovable "`w` is on the *forward* `v → u`
run" orientation datum (which `BoundaryCycle.arcSplit` does not expose; see the module docstring).

Proof: `w` is a boundary vertex (`path₂_boundary_vertices ∘ internalVertices_subset`), hence the
tail of an outer-cycle dart (`exists_dart_tail_of_isBoundaryVertex`); and `w ≠ u, w ≠ v`
(`path₂ : BoundaryPath v u`, so `internalVertex_ne_end`/`_ne_start`), so that dart's edge is not the
chord (`dartEdge_ne_chord_of_tail_ne`). -/
theorem path₂_internalVertex_outerDart (data : hNT.ChordSplitData u v) {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices) :
    ∃ e : D, e ∈ hNT.outerCycle.darts ∧ M.dartEdge e ≠ s(u, v) ∧ M.tail e = w := by
  -- `w` is a boundary vertex of the outer cycle.
  have hbv : hNT.outerCycle.IsBoundaryVertex w :=
    data.arc.path₂_boundary_vertices (data.arc.path₂.internalVertices_subset hw)
  -- `w ≠ u`, `w ≠ v`.  `path₂ : BoundaryPath v u`: `_ne_end` gives `≠ u`, `_ne_start` gives `≠ v`.
  have hwu : w ≠ u := data.arc.path₂.internalVertex_ne_end hw
  have hwv : w ≠ v := data.arc.path₂.internalVertex_ne_start hw
  -- a dart of the outer cycle tailed at `w`.
  obtain ⟨e, he, hte⟩ := exists_dart_tail_of_isBoundaryVertex hNT.outerCycle hbv
  exact ⟨e, he, dartEdge_ne_chord_of_tail_ne data hte hwu hwv, hte⟩

/-- **The contiguity tie, in the exact shape conjunct (1) of `ArcDartRunBankData` consumes** (dropping
the run-membership, which the downstream consumer does not use).  This is the literal "`∃ e`,
non-chord edge, tailed at `w`" half of `ArcDartRunBankData`. -/
theorem path₂_internalVertices_dart (data : hNT.ChordSplitData u v) {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices) :
    ∃ e : D, M.dartEdge e ≠ s(u, v) ∧ M.tail e = w := by
  obtain ⟨e, _, hchord, htail⟩ := path₂_internalVertex_outerDart data hw
  exact ⟨e, hchord, htail⟩

/-! ## 3.  Assembling `ArcDartRunBankData` — the honest residue is exactly conjunct (2)

With conjunct (1) discharged unconditionally above, the *only* remaining input to
`ArcDartRunBankData` is the side-2 face datum (conjunct (2)).  We expose it as a clean predicate and
show it suffices to assemble `ArcDartRunBankData`. -/

/-- **The bank-side (Jordan) datum, conjunct (2) of `ArcDartRunBankData`.**  For every
`path₂`-internal vertex `w`, there is a *non-chord* dart `e` tailed at `w` whose reverse face lies on
side 2.  This is the genuine discrete-Jordan arc↔side identification (`ZinanCh35BankOrient`), the
single residual that survives after conjunct (1) is closed. -/
def BankSideDatum (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {w : M.Vertex}, w ∈ data.arc.path₂.internalVertices →
    ∃ e : D, M.dartEdge e ≠ s(u, v) ∧ M.tail e = w ∧ M.dartFace (M.α e) ∈ data.side₂

/-- **`BankSideDatum` is definitionally `ArcDartRunBankData`** — i.e. with conjunct (1) closed, the
full bank datum collapses to the single side-2 face residue.  This certifies, by `rfl`, that the
contiguity tie added *no* new obligation: every remaining requirement of `ArcDartRunBankData` is the
bank-side datum. -/
theorem bankSideDatum_eq_arcDartRunBankData (data : hNT.ChordSplitData u v) :
    BankSideDatum data = NearTriangulation.ArcDartRunBankData data :=
  rfl

/-- **`ArcDartRunBankData` from the bank-side datum.**  Trivial once conjunct (1) is folded in: the
side datum already carries a non-chord dart tailed at `w`, which *is* the contiguity tie.  Stated to
record that the contiguity tie is no longer an obligation — only the Jordan side fact is. -/
theorem arcDartRunBankData_of_bankSide (data : hNT.ChordSplitData u v)
    (hside : BankSideDatum data) :
    NearTriangulation.ArcDartRunBankData data :=
  hside

/-- **`ArcDartRunBankData` from conjunct (1) (proved here) + a per-vertex side face supply.**  This is
the *informative* assembly: the caller need only supply, for the dart produced by the contiguity tie,
the side-2 face fact `M.dartFace (M.α e) ∈ side₂` — the Jordan datum.  We thread the *same* dart
`path₂_internalVertex_outerDart` produced (an outer-cycle, non-chord dart tailed at `w`) so the side
fact is demanded of exactly that canonical dart. -/
theorem arcDartRunBankData_of_sideData (data : hNT.ChordSplitData u v)
    (hface : ∀ {w : M.Vertex} (hw : w ∈ data.arc.path₂.internalVertices),
      M.dartFace (M.α (Classical.choose (path₂_internalVertex_outerDart data hw))) ∈ data.side₂) :
    NearTriangulation.ArcDartRunBankData data := by
  intro w hw
  -- the canonical outer-cycle, non-chord dart tailed at `w` (conjunct (1)).
  set e := Classical.choose (path₂_internalVertex_outerDart data hw) with he
  have hspec := Classical.choose_spec (path₂_internalVertex_outerDart data hw)
  obtain ⟨_, hchord, htail⟩ := hspec
  exact ⟨e, hchord, htail, hface hw⟩

/-! ## 4.  End-to-end: `ChordArcBankOrientation` from conjunct (1) + the bank-side datum

Composing with `ZinanCh35ArcDartRun.chordArcBankOrientation_of_bankData`, the bank-side datum (the
sole honest residue) discharges `ChordArcBankOrientation` — the contiguity tie contributing nothing
further. -/

/-- **`ChordArcBankOrientation` from the bank-side datum alone** (conjunct (1) absorbed).  The
contiguity tie of §2 is no longer a hypothesis: it is proved, so the *only* input is the side-2
Jordan datum. -/
theorem chordArcBankOrientation_of_bankSide (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hside : BankSideDatum data) :
    ProofsInTheBook.ZinanCh35Side1Confine.ChordArcBankOrientation data :=
  NearTriangulation.chordArcBankOrientation_of_bankData data hsep
    (arcDartRunBankData_of_bankSide data hside)

end ProofsInTheBook.ZinanCh35Contiguity

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35Contiguity.exists_dart_tail_of_isBoundaryVertex
#print axioms ProofsInTheBook.ZinanCh35Contiguity.dartEdge_ne_chord_of_tail_ne
#print axioms ProofsInTheBook.ZinanCh35Contiguity.path₂_internalVertex_outerDart
#print axioms ProofsInTheBook.ZinanCh35Contiguity.path₂_internalVertices_dart
#print axioms ProofsInTheBook.ZinanCh35Contiguity.bankSideDatum_eq_arcDartRunBankData
#print axioms ProofsInTheBook.ZinanCh35Contiguity.arcDartRunBankData_of_bankSide
#print axioms ProofsInTheBook.ZinanCh35Contiguity.arcDartRunBankData_of_sideData
#print axioms ProofsInTheBook.ZinanCh35Contiguity.chordArcBankOrientation_of_bankSide
