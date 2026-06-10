# ch35chordcycle — reply (DONE, clean-3)

## Status: COMPLETE — all targets proven, no sorry/axiom/admit/native_decide.

File: `ProofsInTheBook/ZinanCh35ChordCycle.lean` (444 lines, new file, only file touched).
Builds clean with `lake env lean`; dependency `ProofsInTheBook.ZinanCh35Gates` is clean-3.

### Delivered (all clean-3 `[propext, Classical.choice, Quot.sound]`)

* `NearTriangulation.ChordCycleData h` — structure with fields `C, hsub, i₀, hleft,
  hright` matching `separates_closed`'s consumed signature **verbatim**.
* `NearTriangulation.chordCycleData h : hNT.ChordCycleData h` — the constructor (existence).
* `NearTriangulation.chordCycleData_exists : Nonempty (hNT.ChordCycleData h)`.
* `NearTriangulation.separates_of_chord (data) (cc : ChordCycleData data.chord) :
  data.Separates` — composition via `separates_closed`.
* `NearTriangulation.separates_of_chordSplitData (data) : data.Separates` — the chord
  separates with the cycle datum built internally (no external datum hypothesis).

### Correction to the design brief

The brief said this was "mostly assembling ofDartArc's output." In fact the genuine
missing content was **building the dart-level boundary arc from a bare `Chord`** —
nobody had done this. `ofDartArc` and `DartArc.boundaryDartArc` existed, but
`boundaryDartArc` only handles the *non-wrapping* slice `p + k < L`; the forward arc
between two chord endpoints generally wraps past index 0. I therefore added:

* `BoundaryCycle.cyclicDartArc` — a **cyclic** dart-level arc `darts[(p+j)%L]`,
  `1 ≤ k < L`, handling wrap uniformly (chaining is `consecutive_vertex` at `(p+j)%L`;
  nodup via `Nat.ModEq.add_left_cancel'`). Note `k < L` is **strict** — `k = L` would
  make the head endpoint equal the first tail, falsifying `head_last_ne_tail`.
* `BoundaryCycle.dartArcOfNonBoundaryEdge` — from two distinct boundary vertices `a,b`
  with `s(a,b)` not a boundary edge, the forward cyclic run is a `DartArc … a b` with
  `len ≥ 2`. The `≥ 2` is the crux: a length-1 run would make `s(a,b)` a boundary edge
  (via `consecutive_vertex`), contradicting the chord hypothesis.

### No orientation case-split needed

Key simplification: build the arc between `M.head c₀` and `M.tail c₀` *as they are*
(`c₀ := chordDart h`), giving `A : DartArc … (head c₀) (tail c₀)`. Then
`ofDartArc A c₀` always has `dart 0 = c₀` (hc_tail/hc_head are `rfl`), so `i₀ = 0`
makes `hleft`/`hright` hold by `rw [hdart0]` — no swap, no orientation branch.

### Faithfulness (§3.3)

* `ChordCycleData` fields are the *exact* hypotheses of `separates_closed`
  (`ZinanCh35Gates.lean` line 286–293) — not weakened.
* The constructor is non-vacuous: every premise of `dartArcOfNonBoundaryEdge`
  (distinct endpoints, both boundary, non-boundary edge) is discharged from the
  `Chord` structure, so `chordCycleData_exists` is unconditionally inhabited.
* `separates_of_chordSplitData` has **no** hypothesis beyond `ChordSplitData`, so the
  separation is now closed for every chord of a near-triangulation modulo the
  already-clean-3 `separates_closed`.
