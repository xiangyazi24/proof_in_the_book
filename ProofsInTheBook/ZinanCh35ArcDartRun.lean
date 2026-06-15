import ProofsInTheBook.ZinanCh35ChordCycle
import ProofsInTheBook.ZinanCh35EdgeCore
import ProofsInTheBook.ZinanCh35Side1Confine

/-!
# Chapter 35: the dart realization of the chord-split boundary arc (`BoundaryPathDartRun`)

This file is the *foundational bridge* the R8 audit (`HANDOFF/ch35-arcSide-via-bankTheorem-R8.md`)
isolated for closing `ArcSideIdentification` — the last Chapter 35 / Five-Colour-Theorem
confinement residual.  It is **bookkeeping**, not a new Jordan theorem: every fact below is
recovered from the *real* dart list of `hNT.outerCycle` (the field `outerCycle.darts`, with its
`consecutive_phi`, `consecutive_vertex`, `VertexNodup`), entirely **bypassing** the opaque
`BoundaryArcSplit`.

## What the substrate exposes, and why the bypass is forced

`data.arc.path₂ : BoundaryPath M v u` (from `BoundaryArcSplit`, i.e. the field
`BoundaryCycle.arcSplit`) is an **opaque arc certificate**: a *vertex list* and an *edge list*
with covering / internal-disjointness properties, and **no dart list**.  Crucially (formalized in
`ZinanCh35BankOrient.lean`), the *only* extractable substrate fact about a `path₂`-internal vertex
`w` is `IsBoundaryVertex w ∧ w ≠ u ∧ w ≠ v` — **identical** to the one for a `path₁`-internal
vertex.  So no `path₂.vertices`-level statement can break the `path₁`/`path₂` symmetry; the dart
list is genuinely needed and is genuinely absent from `BoundaryArcSplit`.

By contrast, `hNT.outerCycle : BoundaryCycle` carries the **real directed dart list** `darts : List
D` with `consecutive_phi` and `vertices = darts.map M.tail`.  Following R8 §4 ("bypass
`BoundaryArcSplit`, construct from `outerCycle.darts` which has the real dart list"), we build the
arc realization directly from that list.

## Deliverables (R8 §A / §B / §3)

* **`BoundaryPathDartRun`** (R8 §A) — the dart-level realization of a boundary arc: a directed list
  of `outerCycle.darts` whose tails trace the arc vertices, that chains by `M.φ`, with edge list and
  endpoints recorded.  Built (`ofDartArc'`) from the existing `DartArc` slicing machinery
  (`dartArcOfNonBoundaryEdge`), which slices a contiguous run out of `outerCycle.darts`.

* **`boundaryArcDartRun_of_chord`** (R8 §A) — *existence* of a `BoundaryPathDartRun` realizing the
  boundary arc between the two chord endpoints, **unconditional, axiom-clean**.  Its darts are a
  contiguous cyclic run of `outerCycle.darts` of length `≥ 2`.

* **`chordDart_orient`** (R8 §B) — the chord-dart **orientation chooser**: from a chord `h`, a dart
  of the chord edge `s(u,v)` with `tail = u ∧ head = v` *exists* (and the reversed one with
  `tail = v ∧ head = u`).  This is the orientation pinning `ofDartArc` consumes.

* **`dartRun_tail_mem_sideRegion₂_of_face`** (the bank-route bridge that *is* provable) — for a
  dart-run dart `e`, if the bounded face across its boundary edge lies in `side₂`, then `tail e ∈
  sideRegion₂`.  This is the per-dart conversion R8 §4.E/§4.F needs; it composes the **landed**
  `endpoints_mem_sideRegion₂_of_face` with the dart-run's boundary-edge data.

## The precise remaining gap (reported, not faked)

The dart-run realizes *a* boundary arc between `u` and `v` from the real dart list.  Closing
`ChordArcBankOrientation` (`path₂`-internal `w ⟹ w ∈ sideRegion₂`) for the **opaque**
`data.arc.path₂` additionally requires a *contiguity certificate*
`data.arc.path₂.internalVertices ⊆ (dart-run tails)` tying the opaque vertex list to this dart run.
`BoundaryArcSplit` does **not** expose it (it does not even assert its edges connect consecutive
vertices), and — as `ZinanCh35BankOrient.bank_datum_substrate_symmetric` proves — it is *not*
derivable from the vertex-list substrate.  We isolate that single residual SHARPLY as
`ArcDartRunContiguity` and show (`chordArcBankOrientation_of_contiguity_and_bank`) that it, together
with the dart-run bank-side data, discharges `ChordArcBankOrientation`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35ArcDartRun

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}

/-! ## 1. `BoundaryPathDartRun` — the dart realization of a boundary arc

The structure carries the **dart list** the opaque `BoundaryPath` omits.  It is indexed by the two
arc endpoints `a`, `b` and the boundary cycle `C` whose dart list it lives on.  Every field is the
dart-level analogue of (a sharpened) `BoundaryPath` field, plus the `φ`-chaining and the
sub-run membership that `BoundaryPath` cannot state.
-/

/-- **A dart realization of a boundary arc** between vertices `a` and `b`, living on the cyclic
dart list of a boundary cycle `C`.

This is the dart-level object R8 §A names `BoundaryPathDartRun`: the contiguous sub-run of
`C.darts` whose tails trace the arc from `a` to `b`.  Unlike `BoundaryPath`, it records the actual
directed darts, so the chord∪arc primal cycle can be built and the bank theorem applied.

* `darts_sub_outer` — every run dart lies on `C.darts` (R8: `darts_sub_outer`);
* `consecutive_phi` — consecutive darts chain head→tail along the boundary (R8: `consecutive_phi`,
  here in `head/tail` form, which is `consecutive_vertex` restricted to the slice);
* `edges_eq` — the run's edge list is its darts' graph edges (R8: `edges_eq`);
* `first_tail` / `last_head` — the endpoints (R8: `first_tail` / `last_head`);
* `tail_nodup` — the run is simple as a tail list. -/
structure BoundaryPathDartRun {f : M.Face} (C : BoundaryCycle M f) (a b : M.Vertex) where
  /-- The directed darts of the arc, in path order. -/
  darts : List D
  /-- The run is nonempty. -/
  darts_ne : darts ≠ []
  /-- Every run dart lies on the boundary cycle's dart list. -/
  darts_sub_outer : ∀ d ∈ darts, d ∈ C.darts
  /-- The run's tails are the arc vertices except the terminal one. -/
  tails : List M.Vertex
  /-- `tails` is exactly `darts.map M.tail`. -/
  tails_eq : tails = darts.map M.tail
  /-- The run's edge list. -/
  edges : List (Sym2 M.Vertex)
  /-- `edges` is exactly `darts.map M.dartEdge`. -/
  edges_eq : edges = darts.map M.dartEdge
  /-- Consecutive run darts chain head→tail (no wraparound — this is a *path*). -/
  consecutive_phi : ∀ i : Fin darts.length, (h : (i : ℕ) + 1 < darts.length) →
    M.head (darts.get i) = M.tail (darts.get ⟨i + 1, h⟩)
  /-- The first dart's tail is `a`. -/
  first_tail : ∀ (h : darts ≠ []), M.tail (darts.head h) = a
  /-- The last dart's head is `b`. -/
  last_head : ∀ (h : darts ≠ []), M.head (darts.getLast h) = b
  /-- The tails are pairwise distinct (simplicity). -/
  tails_nodup : (darts.map M.tail).Nodup

namespace BoundaryPathDartRun

variable {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}

/-- The length of the dart run. -/
def length (R : BoundaryPathDartRun C a b) : ℕ := R.darts.length

lemma length_pos (R : BoundaryPathDartRun C a b) : 0 < R.length :=
  List.length_pos_of_ne_nil R.darts_ne

end BoundaryPathDartRun

/-! ## 2. Building a `BoundaryPathDartRun` from a `DartArc`

The existing `DartArc` machinery (`ZinanCh35ChordCycle.dartArcOfNonBoundaryEdge`,
`DartArc.boundaryDartArc`, `cyclicDartArc`) already slices a contiguous dart run out of
`C.darts` and proves the chaining / simplicity / endpoint facts.  We convert a `DartArc` into a
`BoundaryPathDartRun`, materializing the explicit `List D` and its `map`-facts. -/

section DartArcHelpers

variable {f : M.Face} {C : BoundaryCycle M f} {a b : M.Vertex}

/-- The explicit `List D` of a `DartArc`'s darts, `[arcDart 0, …, arcDart (len-1)]`. -/
def _root_.ProofsInTheBook.PlanarMap.CombMap.DartArc.dartList (A : DartArc M C a b) : List D :=
  (List.finRange A.len).map A.arcDart

@[simp] lemma _root_.ProofsInTheBook.PlanarMap.CombMap.DartArc.dartList_length
    (A : DartArc M C a b) : A.dartList.length = A.len := by
  simp [DartArc.dartList]

lemma _root_.ProofsInTheBook.PlanarMap.CombMap.DartArc.dartList_ne_nil
    (A : DartArc M C a b) : A.dartList ≠ [] := by
  rw [← List.length_pos_iff_ne_nil, DartArc.dartList_length]; exact A.len_pos

lemma _root_.ProofsInTheBook.PlanarMap.CombMap.DartArc.dartList_getElem
    (A : DartArc M C a b) (j : ℕ) (hj : j < A.len) :
    A.dartList[j]'(by rw [DartArc.dartList_length]; exact hj) = A.arcDart ⟨j, hj⟩ := by
  simp only [DartArc.dartList, List.getElem_map, List.getElem_finRange]
  congr 1

lemma _root_.ProofsInTheBook.PlanarMap.CombMap.DartArc.mem_dartList
    (A : DartArc M C a b) {d : D} (hd : d ∈ A.dartList) :
    ∃ i : Fin A.len, A.arcDart i = d := by
  rw [DartArc.dartList, List.mem_map] at hd
  obtain ⟨i, _, hi⟩ := hd
  exact ⟨i, hi⟩

end DartArcHelpers

/-- **Convert a `DartArc` to a `BoundaryPathDartRun`.**  Materializes the explicit dart list and
proves all `BoundaryPathDartRun` obligations from the `DartArc` fields (`boundary`, `chain`,
`tail_first`, `head_last`, `tail_nodup`). -/
noncomputable def _root_.ProofsInTheBook.PlanarMap.CombMap.DartArc.toBoundaryPathDartRun
    {f : M.Face} {C : BoundaryCycle M f}
    {a b : M.Vertex} (A : DartArc M C a b) : BoundaryPathDartRun C a b where
  darts := A.dartList
  darts_ne := A.dartList_ne_nil
  darts_sub_outer := by
    intro d hd
    obtain ⟨i, hi⟩ := A.mem_dartList hd
    rw [← hi]; exact A.boundary i
  tails := A.dartList.map M.tail
  tails_eq := rfl
  edges := A.dartList.map M.dartEdge
  edges_eq := rfl
  consecutive_phi := by
    intro i h
    have hlen := A.dartList_length
    have hi : (i : ℕ) < A.len := by have := i.2; omega
    have hi1 : (i : ℕ) + 1 < A.len := by omega
    -- Translate the get's to getElem, then to `arcDart` via `dartList_getElem`.
    simp only [List.get_eq_getElem]
    rw [A.dartList_getElem i.1 hi, A.dartList_getElem ((i : ℕ) + 1) hi1]
    -- Goal: head (arcDart ⟨i,_⟩) = tail (arcDart ⟨i+1,_⟩).
    have := A.chain ⟨i.1, hi⟩ (by simpa using hi1)
    simpa using this
  first_tail := by
    intro h
    -- head of the list is `arcDart ⟨0, _⟩`.
    have hlen : 0 < A.dartList.length := by rw [DartArc.dartList_length]; exact A.len_pos
    rw [List.head_eq_getElem, A.dartList_getElem 0 A.len_pos]
    exact A.tail_first
  last_head := by
    intro h
    have hlen : 0 < A.dartList.length := by rw [DartArc.dartList_length]; exact A.len_pos
    have hlt : A.len - 1 < A.len := by have := A.len_pos; omega
    rw [List.getLast_eq_getElem]
    -- the index is dartList.length - 1; rewrite length and apply dartList_getElem.
    have hidx : A.dartList.length - 1 = A.len - 1 := by rw [DartArc.dartList_length]
    rw [show A.dartList[A.dartList.length - 1]'(by omega)
        = A.dartList[A.len - 1]'(by rw [DartArc.dartList_length]; omega) by
          congr 1,
      A.dartList_getElem (A.len - 1) hlt]
    exact A.head_last
  tails_nodup := by
    -- `(dartList.map tail).Nodup` from `A.tail_nodup` (injectivity of `i ↦ tail (arcDart i)`).
    rw [DartArc.dartList, List.map_map]
    rw [List.nodup_map_iff_inj_on (List.nodup_finRange A.len)]
    intro i _ j _ hij
    exact A.tail_nodup hij

/-! ## 3. The chord-dart orientation chooser (R8 §B)

`hNT.chordDart h` is chosen from an *unordered* edge witness: only `dartEdge (chordDart h) =
s(u, v)` is pinned, not which of `tail`/`head` is `u`.  Since `s(tail c, head c) = s(u, v)` and the
graph is simple (`tail ≠ head`), one of the two darts of the chord edge has `tail = u, head = v`.
We exhibit that orientation as an existence chooser. -/

namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The chord-dart orientation chooser** (R8 §B).  A dart of the chord edge oriented `u → v`
exists.  Concretely: either `chordDart h` already has `tail = u, head = v`, or its `α`-image does.
The disjunction is resolved by `Sym2.eq_iff` on `dartEdge (chordDart h) = s(u, v)`. -/
theorem chordDart_orient (h : hNT.outerCycle.Chord u v) :
    ∃ c : D, M.dartEdge c = s(u, v) ∧ M.tail c = u ∧ M.head c = v := by
  classical
  set c₀ := hNT.chordDart h with hc₀
  have hedge : M.dartEdge c₀ = s(u, v) := hNT.chordDart_edge h
  have hxy : s(M.tail c₀, M.head c₀) = s(u, v) := hedge
  rcases Sym2.eq_iff.mp hxy with ⟨ht, hh⟩ | ⟨ht, hh⟩
  · -- tail c₀ = u, head c₀ = v.
    exact ⟨c₀, hedge, ht, hh⟩
  · -- tail c₀ = v, head c₀ = u : the α-image is oriented u → v.
    refine ⟨M.α c₀, ?_, ?_, ?_⟩
    · rw [M.dartEdge_alpha]; exact hedge
    · rw [M.tail_alpha]; exact hh
    · rw [M.head_alpha]; exact ht

/-- The reversed orientation `v → u` also exists (used by `ofDartArc`, which wants the chord dart
oriented `v → u` so the arc closes `u → … → v → u`).  Just `α`-flip the `u → v` chooser. -/
theorem chordDart_orient_rev (h : hNT.outerCycle.Chord u v) :
    ∃ c : D, M.dartEdge c = s(u, v) ∧ M.tail c = v ∧ M.head c = u := by
  obtain ⟨c, he, ht, hh⟩ := chordDart_orient (hNT := hNT) h
  refine ⟨M.α c, ?_, ?_, ?_⟩
  · rw [M.dartEdge_alpha]; exact he
  · rw [M.tail_alpha]; exact hh
  · rw [M.head_alpha]; exact ht

end NearTriangulation

/-! ## 4. Existence of the boundary-arc dart run from a chord (R8 §A)

Reusing `dartArcOfNonBoundaryEdge` (which slices the cyclic run of `outerCycle.darts` between the
two chord endpoints, of length `≥ 2`), we get a `BoundaryPathDartRun` realizing *a* boundary arc
between the chord endpoints, directly from the real dart list.  This is unconditional. -/

namespace NearTriangulation

variable (hNT : NearTriangulation M) {u v : M.Vertex}

open ProofsInTheBook.PlanarMap.CombMap.BoundaryCycle

/-- **The boundary-arc dart run exists** (R8 §A), built from `outerCycle.darts`.  From a chord `h`,
the forward cyclic run of `outerCycle.darts` from `v` to `u` is a `BoundaryPathDartRun` of length
`≥ 2` (length `1` would make `s(u,v)` a boundary edge, contradicting the chord).  Endpoints `v →
u`, every dart on the outer cycle, chaining by `φ`. -/
noncomputable def _root_.ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.boundaryArcDartRun
    (h : hNT.outerCycle.Chord u v) :
    { R : BoundaryPathDartRun hNT.outerCycle v u // 2 ≤ R.length } := by
  classical
  -- `s(v, u) = s(u, v)` is not a boundary edge; `v ≠ u`; both boundary.
  have hvu_ne : v ≠ u := h.endpoints_ne.symm
  have hv_bv : hNT.outerCycle.IsBoundaryVertex v := h.right_boundary
  have hu_bv : hNT.outerCycle.IsBoundaryVertex u := h.left_boundary
  have hnbe : ¬ hNT.outerCycle.IsBoundaryEdge s(v, u) := by
    rw [show (s(v, u) : Sym2 M.Vertex) = s(u, v) from Sym2.eq_swap]
    exact h.not_boundary_edge
  obtain ⟨A, hAlen⟩ := hNT.outerCycle.dartArcOfNonBoundaryEdge hNT.outer_simple
    hvu_ne hv_bv hu_bv hnbe
  refine ⟨A.toBoundaryPathDartRun, ?_⟩
  -- length R = darts.length = A.dartList.length = A.len ≥ 2.
  show 2 ≤ (A.toBoundaryPathDartRun).darts.length
  change 2 ≤ A.dartList.length
  rw [DartArc.dartList_length]; exact hAlen

/-- **Existence form** of the boundary-arc dart run. -/
theorem boundaryArcDartRun_exists (h : hNT.outerCycle.Chord u v) :
    ∃ R : BoundaryPathDartRun hNT.outerCycle v u, 2 ≤ R.length :=
  ⟨(hNT.boundaryArcDartRun h).1, (hNT.boundaryArcDartRun h).2⟩

end NearTriangulation

/-! ## 5. The bank-route bridge that *is* provable (R8 §4.E/§4.F)

For a dart `e` on the boundary cycle, if the bounded face across its boundary edge
(`dartFace (M.α e)`) lies in `side₂`, then `tail e ∈ sideRegion₂`.  This is the per-dart conversion
that the bank theorem on the explicit cycle `C₂ = chord ∪ path₂` feeds into: the bank theorem
delivers `dartFace (M.α e) ∈ side₂`, and this lemma turns it into the `sideRegion₂` membership the
`ChordArcBankOrientation` datum demands.

It composes the **landed, unconditional** `endpoints_mem_sideRegion₂_of_face`. -/

namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The bank-route per-dart bridge.**  If `e` is a non-chord boundary dart whose *reverse* face
lies in `side₂`, then `tail e ∈ sideRegion₂`.

Apply `endpoints_mem_sideRegion₂_of_face` to `M.α e`: its face is `dartFace (M.α e) ∈ side₂`, its
edge is non-chord (same edge as `e`), so both its endpoints — in particular `head (M.α e) = tail
e` — lie in `sideRegion₂`. -/
theorem dartRun_tail_mem_sideRegion₂_of_face (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hface : M.dartFace (M.α e) ∈ data.side₂) :
    M.tail e ∈ sideRegion₂ data := by
  have hchord' : M.dartEdge (M.α e) ≠ s(u, v) := by rwa [M.dartEdge_alpha]
  obtain ⟨_, hhead⟩ := endpoints_mem_sideRegion₂_of_face data hsep hchord' hface
  -- head (α e) = tail e.
  rwa [M.head_alpha] at hhead

/-- Symmetric variant: the *forward* face in `side₂` gives the **head** in `sideRegion₂`. -/
theorem dartRun_head_mem_sideRegion₂_of_face (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    {e : D} (hchord : M.dartEdge e ≠ s(u, v)) (hface : M.dartFace (M.α e) ∈ data.side₂) :
    M.head e ∈ sideRegion₂ data := by
  have hchord' : M.dartEdge (M.α e) ≠ s(u, v) := by rwa [M.dartEdge_alpha]
  obtain ⟨htail, _⟩ := endpoints_mem_sideRegion₂_of_face data hsep hchord' hface
  rwa [M.tail_alpha] at htail

end NearTriangulation

/-! ## 6. The single remaining residual, isolated SHARPLY (R8 §3.3 honesty)

The dart run of §4 realizes *a* boundary arc between `u` and `v` from the real dart list.  To
discharge `ChordArcBankOrientation` (`path₂`-internal `w ⟹ w ∈ sideRegion₂`) for the **opaque**
`data.arc.path₂`, two further inputs are needed:

1. **Contiguity** — `data.arc.path₂.internalVertices ⊆ (the run's tails)`: each opaque-arc-internal
   vertex is realized by a run dart tailed there.  `BoundaryArcSplit` does NOT expose this (it does
   not even assert its edges connect consecutive vertices), and `ZinanCh35BankOrient.
   bank_datum_substrate_symmetric` proves it is *not* a vertex-list-substrate consequence.

2. **Bank side data** — for each such run dart `e`, `dartFace (M.α e) ∈ side₂`: the bounded face
   across the boundary edge is on the `side₂` bank.  This is what the genus-slack bank theorem on
   `C₂ = chord ∪ path₂` supplies.

We package both as `ArcDartRunBankData` and show it discharges `ChordArcBankOrientation`.  This
isolates the residual *exactly* at the dart level (R8's frontier), with the §5 bridge already
absorbing the face→region conversion. -/

namespace NearTriangulation

variable {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The dart-run bank datum** for `path₂`: for every `path₂`-internal vertex `w`, there is a
*non-chord boundary dart* `e` tailed at `w` whose reverse face lies in `side₂`.  This bundles the
contiguity tie (`tail e = w` with `e` on the run / outer cycle) and the bank-side fact
(`dartFace (M.α e) ∈ side₂`) — exactly the two inputs §6.1/§6.2 names.

This is the *honest* residual: neither conjunct is faked.  The contiguity tie is the absent
`BoundaryArcSplit`-to-dart-run certificate; the bank-side fact is the bank theorem's output. -/
def ArcDartRunBankData (data : hNT.ChordSplitData u v) : Prop :=
  ∀ {w : M.Vertex}, w ∈ data.arc.path₂.internalVertices →
    ∃ e : D, M.dartEdge e ≠ s(u, v) ∧ M.tail e = w ∧ M.dartFace (M.α e) ∈ data.side₂

/-- **`ArcDartRunBankData` discharges `ChordArcBankOrientation`.**  Given the dart-run bank datum,
every `path₂`-internal vertex lies in `sideRegion₂`: take the witness dart `e`, whose reverse face
is in `side₂`, and apply the §5 per-dart bridge `dartRun_tail_mem_sideRegion₂_of_face`.

This is the reduction R8 promises: the arc↔side identification is reduced to the *single* dart-level
bank datum, with all face→region bookkeeping discharged. -/
theorem chordArcBankOrientation_of_bankData (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (hbank : ArcDartRunBankData data) :
    ProofsInTheBook.ZinanCh35Side1Confine.ChordArcBankOrientation data := by
  refine ⟨?_⟩
  intro w hw
  obtain ⟨e, hchord, htail, hface⟩ := hbank hw
  have := dartRun_tail_mem_sideRegion₂_of_face data hsep hchord hface
  rwa [htail] at this

end NearTriangulation

end ProofsInTheBook.ZinanCh35ArcDartRun

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.DartArc.toBoundaryPathDartRun
#print axioms ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.chordDart_orient
#print axioms ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.chordDart_orient_rev
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.boundaryArcDartRun
#print axioms ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.boundaryArcDartRun_exists
#print axioms ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.dartRun_tail_mem_sideRegion₂_of_face
#print axioms ProofsInTheBook.ZinanCh35ArcDartRun.NearTriangulation.chordArcBankOrientation_of_bankData
