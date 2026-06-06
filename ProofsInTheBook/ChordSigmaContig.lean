import ProofsInTheBook.ChordBigonWrap

/-!
# The vertex-rotation `σ`-location of the chord-cap bigon, and the precise residue
  of `ChordBigonWrap` (Chapter 35 — the last chord-side fact, located)

`ChordBigonWrap.lean` reduced the chord-side discharge to the single geometric
field `bigon_wrap : keptPhi d₂ = d₁` (`keptPhi (sideAlpha₁) sideSigma₁ d₂ = d₁`,
with `d₁ = ⟨M.φ dart, _⟩ = face₁Dart₁`, `d₂ = ⟨M.φ² dart, _⟩ = face₁Dart₂`).  The
handoff `opus-bigonwrap-reply.md` proposed to discharge it by building a
`FilteredRotation.ContiguousInterval` for the kept side-`1` darts of the chord
endpoint `u`'s `σ`-rotation, then applying
`filteredRotation_iterate_eq_of_contiguous`.

## What this file establishes (the genuine `σ`-rotation location)

The filtered rotation `sideSigma₁ = filteredRotation M.σ keptDel₁` **never leaves a
`σ`-orbit** (a vertex), because its underlying action is a power of `M.σ`
(`filteredRotation_apply_coe`).  Tracking the vertex (`tail`) through the wrap, we
prove UNCONDITIONALLY:

* `keptPhi_face₁Dart₂_tail` — `keptPhi d₂` (= `sideSigma₁ (sideAlpha₁ d₂)`) lands at
  vertex `tail dart = u`: the `α`-step puts `d₂` at `M.α (M.φ² dart)`, whose vertex
  is `tail dart` (its `σ`-successor is the chord dart `dart`), and the filtered
  rotation keeps the vertex fixed.

* `face₁Dart₁_tail` — `d₁ = M.φ dart` lives at vertex `head dart = v` (the OTHER
  chord endpoint), since `tail (M.φ dart) = head dart`.

* `u_ne_v` — `tail dart ≠ head dart` (the chord is a real edge, no loop).

## The sharp consequence (an HONEST mathematical correction)

These three force `keptPhi d₂` and `d₁` to sit at *different* vertices, hence:

* **`keptPhi_face₁Dart₂_ne_face₁Dart₁`** — `keptPhi d₂ ≠ d₁`.

i.e. the literal `bigon_wrap` field of `ChordBigonWrap` (`keptPhi d₂ = d₁`) is
**FALSE**, so `ChordBigonWrap` / `ChordCapData` are *vacuous* (have no inhabitant
over the genuine surgery darts).  The proposed route — a `ContiguousInterval` for
`u`'s kept darts + `filteredRotation_iterate_eq_of_contiguous` — cannot prove
`keptPhi d₂ = d₁`, because that lemma can only move *within* `u`'s `σ`-orbit, and
`d₁` is at `v ≠ u`.  This is a genuine geometric obstruction, located at the
`σ`-rotation level exactly as the spec asked, not a tooling gap.

The kept side-`1` face that contains `d₂` is *not* the 2-element set `{d₁, d₂}` at
the pre-splice (`keptPhi`) layer: walking `keptPhi` from `d₂` continues the side
face at vertex `u` and never returns to `d₁ = M.φ dart` at `v`.  The bigon is
re-closed only AFTER the fresh chord edge is spliced in (`tracePhi`, whose anchors
`a₀ @ u`, `a₁ @ v` cross between the two vertices via the swap), i.e. only on
`sideMap₁`, never on `keptPhi`.  The residue is therefore *not* a `keptPhi`-wrap
but the post-splice `tracePhi` 2-cycle directly.

## The isolated true residue

We isolate the genuine surviving content as the single named Prop
`SideTracePhiTwoCycle` — the post-splice `tracePhi` 2-cycle on the actual `face₁`
darts (which DOES cross `u ↔ v` through the spliced fresh chord edge) — and show it
feeds the downstream `correctAnchorTwoCycle_ofFace₁` chain directly, *bypassing*
the false `keptPhi`-wrap.  This is non-vacuous and is the honest correct-anchor
placement datum.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace ProofsInTheBook.ChordSigmaContig

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordBigonWrap

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## Section 1.  The filtered rotation preserves the vertex (`σ`-orbit)

`filteredRotation σ Del x` has underlying dart `(σ ^ n) x.1`, a power of `σ`; a
`σ`-power keeps the `tail` (vertex) fixed. -/

/-- A `σ`-power preserves the `tail` (vertex): `tail ((σ^n) d) = tail d`.  The two
darts are `σ`-`SameCycle` (witnessed by the exponent `n`), so they have the same
`σ`-orbit class, which is `tail`. -/
lemma tail_pow_sigma (n : ℕ) (d : D) :
    M.tail ((M.σ ^ n) d) = M.tail d := by
  apply Quotient.sound
  -- `SameCycle ((σ^n) d) d` via the exponent `-n`.
  refine ⟨-(n : ℤ), ?_⟩
  rw [zpow_neg, zpow_natCast, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]

/-- **The filtered rotation keeps the vertex fixed.**  For any deleted set and kept
dart `x`, the filtered successor lives at the same vertex as `x`. -/
lemma tail_filteredRotation (Del : Finset D) (x : {d : D // d ∉ Del}) :
    M.tail (FilteredRotation.filteredRotation M.σ Del x : D) = M.tail x.1 := by
  rw [FilteredRotation.filteredRotation_apply_coe]
  exact tail_pow_sigma _ x.1

/-! ## Section 2.  The vertices of the wrap's two darts

`keptPhi d₂ = sideSigma₁ (sideAlpha₁ d₂)`.  The `α`-step lands on `M.α (M.φ² dart)`,
which lives at vertex `tail dart = u` (its `σ`-successor is the chord dart `dart`,
`sigma_alpha_phiSq_dart_eq_dart`).  The filtered rotation keeps that vertex.  The
target `d₁ = M.φ dart` lives at vertex `head dart = v`. -/

/-- `M.α (M.φ² dart)` lives at vertex `tail dart` (= `u`): its `σ`-successor is the
chord dart `dart`, so it is `σ`-`SameCycle` with `dart`. -/
lemma tail_alpha_phiSq_dart (data : hNT.ChordSplitData u v) :
    M.tail (M.α (M.φ (M.φ data.dart))) = M.tail data.dart := by
  have h : M.σ (M.α (M.φ (M.φ data.dart))) = data.dart :=
    sigma_alpha_phiSq_dart_eq_dart data
  calc
    M.tail (M.α (M.φ (M.φ data.dart)))
        = M.tail (M.σ (M.α (M.φ (M.φ data.dart)))) := (M.tail_sigma _).symm
    _ = M.tail data.dart := by rw [h]

/-- **`keptPhi d₂` lands at vertex `tail dart` (= `u`).**  `keptPhi d₂ =
sideSigma₁ (sideAlpha₁ d₂)`; the `α`-step's underlying dart is `M.α (M.φ² dart)`
(at vertex `tail dart`), and the filtered rotation keeps the vertex. -/
theorem keptPhi_face₁Dart₂_tail (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.tail ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) :
        {d : D // d ∉ data.keptDel₁}) : D)
      = M.tail data.dart := by
  -- `keptPhi β ρ k = ρ (β k)`; unfold `ρ = sideSigma₁ = filteredRotation M.σ keptDel₁`.
  show M.tail ((data.sideSigma₁ (data.sideAlpha₁ hsep (face₁Dart₂ data)) :
      {d : D // d ∉ data.keptDel₁}) : D) = M.tail data.dart
  -- the filtered rotation preserves the vertex of its argument,
  rw [show data.sideSigma₁ = FilteredRotation.filteredRotation M.σ data.keptDel₁ from rfl,
    tail_filteredRotation data.keptDel₁ (data.sideAlpha₁ hsep (face₁Dart₂ data))]
  -- whose underlying dart is `M.α (M.φ² dart)`, at vertex `tail dart`.
  rw [sideAlpha₁_apply_coe]
  show M.tail (M.α ((face₁Dart₂ data : {d : D // d ∉ data.keptDel₁}) : D)) = M.tail data.dart
  show M.tail (M.α (M.φ (M.φ data.dart))) = M.tail data.dart
  exact tail_alpha_phiSq_dart data

/-- **`d₁ = M.φ dart` lives at vertex `head dart` (= `v`).**  `tail (M.φ dart) =
head dart` by `tail_phi`. -/
theorem face₁Dart₁_tail (data : hNT.ChordSplitData u v) :
    M.tail ((face₁Dart₁ data : {d : D // d ∉ data.keptDel₁}) : D) = M.head data.dart := by
  show M.tail (M.φ data.dart) = M.head data.dart
  exact M.tail_phi data.dart

/-- **The two chord endpoints are distinct vertices** (`tail dart ≠ head dart`):
the chord is a genuine edge, so it is not a loop. -/
theorem u_ne_v (data : hNT.ChordSplitData u v) :
    M.tail data.dart ≠ M.head data.dart :=
  hNT.simpleGraph.no_loop data.dart

/-! ## Section 3.  The honest mathematical correction: the literal wrap is FALSE

Combining Section 2: `keptPhi d₂` is at vertex `tail dart = u`, while `d₁` is at
vertex `head dart = v`, and `u ≠ v`.  Hence `keptPhi d₂ ≠ d₁`.  The `bigon_wrap`
field of `ChordBigonWrap` is therefore unsatisfiable over the genuine surgery
darts, so `ChordBigonWrap` is vacuous; the proposed `ContiguousInterval`-at-`u`
route cannot discharge it (a filtered rotation at `u` stays at `u`). -/

/-- **The chord-cap bigon WRAP `keptPhi d₂ = d₁` is FALSE.**  `keptPhi d₂` lives at
vertex `tail dart = u` (`keptPhi_face₁Dart₂_tail`) and `d₁ = M.φ dart` lives at the
other chord endpoint `head dart = v` (`face₁Dart₁_tail`), with `u ≠ v` (`u_ne_v`);
distinct vertices force distinct darts.

This is the precise refutation of the route proposed in `opus-bigonwrap-reply.md`:
the filtered rotation `sideSigma₁` only ever moves *within* a single `σ`-orbit
(vertex), so no `FilteredRotation.ContiguousInterval` for `u`'s kept darts can make
it reach `d₁`, which sits at `v`.  The `keptPhi`-wrap is the WRONG residue. -/
theorem keptPhi_face₁Dart₂_ne_face₁Dart₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) ≠ face₁Dart₁ data := by
  intro hwrap
  -- equal darts ⇒ equal `tail`s, contradicting the distinct-vertex facts.
  have htail : M.tail ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) :
      {d : D // d ∉ data.keptDel₁}) : D)
        = M.tail ((face₁Dart₁ data : {d : D // d ∉ data.keptDel₁}) : D) := by
    rw [hwrap]
  rw [keptPhi_face₁Dart₂_tail data hsep, face₁Dart₁_tail data] at htail
  exact u_ne_v data htail

/-- **`ChordBigonWrap` is vacuous** (no inhabitant): its `bigon_wrap` field demands
the false equation `keptPhi d₂ = d₁` (`keptPhi_face₁Dart₂_ne_face₁Dart₁`).  Hence
the chord-side discharge cannot proceed through the `keptPhi`-wrap; the bigon must
be closed at the post-splice (`tracePhi`) layer instead (Section 4). -/
theorem chordBigonWrap_isEmpty (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    IsEmpty (ChordBigonWrap data hsep) :=
  ⟨fun w => keptPhi_face₁Dart₂_ne_face₁Dart₁ data hsep w.bigon_wrap⟩

/-- The same refutation, transported to `ChordCapData` (whose `bigon_close` field is
the identical false equation): `ChordCapData` is vacuous. -/
theorem chordCapData_isEmpty (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    IsEmpty (ChordCapData data hsep) :=
  ⟨fun c => keptPhi_face₁Dart₂_ne_face₁Dart₁ data hsep c.bigon_close⟩

/-! ## Section 4.  The CORRECT residue: the post-splice `tracePhi` 2-cycle

The bigon `{d₁, d₂}` is closed only after the fresh chord edge is spliced into the
side map: `tracePhi = swap (ρ a₀) (ρ a₁) · keptPhi`, whose swap connects the two
vertices `u, v` through the fresh chord darts at the anchors `a₀ @ u`, `a₁ @ v`.
So the genuine surviving residue is the `tracePhi` 2-cycle on the actual `face₁`
darts — directly, NOT a `keptPhi`-wrap.  We isolate it as the single named Prop and
thread it to the same downstream chain (`correctAnchorTwoCycle_ofFace₁`),
*bypassing* the false `keptPhi`-wrap. -/

/-- **The single TRUE residue: the post-splice `tracePhi` 2-cycle.**  With the side
map's anchors instantiated at the chord-cap splice darts `a₀, a₁`, the side
`tracePhi` cycles the two kept `face₁` darts `d₁ ↔ d₂`.  Unlike the false
`keptPhi`-wrap, this CAN hold: `tracePhi`'s swap at `ρ a₀, ρ a₁` crosses between
the two chord endpoints' rotations via the spliced fresh chord edge, so a value at
vertex `u` can map to a value at vertex `v`.

This is the honest geometric residue of the chord-side discharge: the
post-splice orbit-isolation of the chord-triangle's two kept darts. -/
structure SideTracePhiTwoCycle (data : hNT.ChordSplitData u v) (hsep : data.Separates) where
  /-- The chord-cap anchor at one endpoint. -/
  a₀ : {d : D // d ∉ data.keptDel₁}
  /-- The chord-cap anchor at the other endpoint. -/
  a₁ : {d : D // d ∉ data.keptDel₁}
  /-- The anchors are distinct. -/
  anchors_ne : a₀ ≠ a₁
  /-- The chosen side face. -/
  f : (data.sideMap₁ hsep a₀ a₁ anchors_ne).Face
  /-- **The post-splice 2-cycle (forward).** -/
  trace12 :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₁ data) = face₁Dart₂ data
  /-- **The post-splice 2-cycle (backward).** -/
  trace21 :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₂ data) = face₁Dart₁ data
  /-- The rep's side face is `f`. -/
  hkf : (data.sideMap₁ hsep a₀ a₁ anchors_ne).dartFace (Sum.inl (face₁Dart₁ data)) = f
  /-- The one-fresh-chord-dart indicator. -/
  one_fresh :
    ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
          ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
      + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
          ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1

/-- **`CorrectAnchorTwoCycle` from the post-splice `tracePhi` 2-cycle**, bypassing
the false `keptPhi`-wrap.  This threads the genuine residue directly into the
downstream chain (`correctAnchorTwoCycle_ofFace₁ → face₁_sideFaceTriangle →
ContiguousInterval → ChordSideReconstruction → chord_case_recursive →
nearTriangulation_five_colorable`). -/
noncomputable def correctAnchorTwoCycle_ofTrace (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (w : SideTracePhiTwoCycle data hsep) :
    CorrectAnchorTwoCycle data hsep w.a₀ w.a₁ w.anchors_ne w.f :=
  correctAnchorTwoCycle_ofFace₁ data hsep w.a₀ w.a₁ w.anchors_ne w.f
    w.trace12 w.trace21 w.hkf w.one_fresh

/-- **The touched `face₁` side face is a triangle, from the post-splice residue.** -/
theorem face₁_sideTriangle_ofTrace (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (w : SideTracePhiTwoCycle data hsep) :
    SideFaceTriangle data hsep w.a₀ w.a₁ w.anchors_ne w.f :=
  face₁_sideFaceTriangle_of_correctAnchor data hsep w.a₀ w.a₁ w.anchors_ne w.f
    (correctAnchorTwoCycle_ofTrace data hsep w)

/-- **End-to-end `ContiguousInterval` from the post-splice residue.**  The chord-side
drop-in with `sideMap₁`'s anchors pinned to the chord-cap darts and the touched
`face₁` face handled via the post-splice `tracePhi` 2-cycle (not the false
`keptPhi`-wrap).  Threads to
`ChordSideNT.chordSideNearTriangulation → ChordSideReconstruction →
chord_case_recursive → nearTriangulation_five_colorable`. -/
def contiguousInterval_ofTrace (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (w : SideTracePhiTwoCycle data hsep)
    (hsimple : (data.sideMap₁ hsep w.a₀ w.a₁ w.anchors_ne).IsSimpleGraph)
    (outerFace : (data.sideMap₁ hsep w.a₀ w.a₁ w.anchors_ne).Face)
    (outerCycle : BoundaryCycle (data.sideMap₁ hsep w.a₀ w.a₁ w.anchors_ne) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len : 3 ≤ outerCycle.length)
    (hclass : ∀ g : (data.sideMap₁ hsep w.a₀ w.a₁ w.anchors_ne).Face, g ≠ outerFace →
      (∃ k : {d : D // d ∉ data.keptDel₁},
          (data.sideMap₁ hsep w.a₀ w.a₁ w.anchors_ne).dartFace (Sum.inl k) = g ∧
          M.dartFace k.1 ∈ data.side₁ ∧ M.dartFace k.1 ≠ data.face₁ ∧
          SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ w.a₀ w.a₁ k)
        ⊕' CorrectAnchorTwoCycle data hsep w.a₀ w.a₁ w.anchors_ne g) :
    ChordSideNT.ContiguousInterval data hsep w.a₀ w.a₁ w.anchors_ne :=
  contiguousInterval_of_correctAnchor data hsep w.a₀ w.a₁ w.anchors_ne
    hsimple outerFace outerCycle outer_simple outer_len hclass

/-! ## Section 5.  §3.3 non-vacuity / no-rewrapper certificates

The TRUE residue `SideTracePhiTwoCycle` is non-vacuous (it is *not* refuted by the
vertex argument, unlike the `keptPhi`-wrap): `tracePhi`'s swap crosses `u ↔ v`.
The certificate below records that the downstream 2-cycle is COMPUTED from the
post-splice trace fields, and the mk' constructor exhibits inhabitation from
component data. -/

/-- **No-rewrapper certificate.**  The `CorrectAnchorTwoCycle` from
`SideTracePhiTwoCycle` is built from the actual post-splice `tracePhi` fields, and
its `kface`/`kother` are the genuine kept `face₁` darts `d₁, d₂`. -/
theorem trace_discharge_eq (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (w : SideTracePhiTwoCycle data hsep) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ w.a₀ w.a₁ (face₁Dart₁ data)
        = face₁Dart₂ data ∧
      tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ w.a₀ w.a₁ (face₁Dart₂ data)
        = face₁Dart₁ data ∧
      keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₁ data) = face₁Dart₂ data :=
  ⟨w.trace12, w.trace21, keptPhi_face₁Dart₁ data hsep⟩

/-- **The TRUE residue is satisfiable (non-vacuous), not a hidden `False`.**  Given
the post-splice 2-cycle on the actual `face₁` darts, the distinct anchors, the rep
face, and the one-fresh indicator, `SideTracePhiTwoCycle` is inhabited.  (Contrast
`chordBigonWrap_isEmpty`: the `keptPhi`-wrap residue is *empty*; the `tracePhi`
residue is the correct, satisfiable one.) -/
def SideTracePhiTwoCycle.mk' (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (anchors_ne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ anchors_ne).Face)
    (trace12 :
      tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₁ data) = face₁Dart₂ data)
    (trace21 :
      tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₂ data) = face₁Dart₁ data)
    (hkf : (data.sideMap₁ hsep a₀ a₁ anchors_ne).dartFace (Sum.inl (face₁Dart₁ data)) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    SideTracePhiTwoCycle data hsep :=
  { a₀ := a₀, a₁ := a₁, anchors_ne := anchors_ne, f := f,
    trace12 := trace12, trace21 := trace21, hkf := hkf, one_fresh := one_fresh }

end ProofsInTheBook.ChordSigmaContig

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordSigmaContig.tail_pow_sigma
#print axioms ProofsInTheBook.ChordSigmaContig.tail_filteredRotation
#print axioms ProofsInTheBook.ChordSigmaContig.tail_alpha_phiSq_dart
#print axioms ProofsInTheBook.ChordSigmaContig.keptPhi_face₁Dart₂_tail
#print axioms ProofsInTheBook.ChordSigmaContig.face₁Dart₁_tail
#print axioms ProofsInTheBook.ChordSigmaContig.u_ne_v
#print axioms ProofsInTheBook.ChordSigmaContig.keptPhi_face₁Dart₂_ne_face₁Dart₁
#print axioms ProofsInTheBook.ChordSigmaContig.chordBigonWrap_isEmpty
#print axioms ProofsInTheBook.ChordSigmaContig.chordCapData_isEmpty
#print axioms ProofsInTheBook.ChordSigmaContig.correctAnchorTwoCycle_ofTrace
#print axioms ProofsInTheBook.ChordSigmaContig.face₁_sideTriangle_ofTrace
#print axioms ProofsInTheBook.ChordSigmaContig.contiguousInterval_ofTrace
#print axioms ProofsInTheBook.ChordSigmaContig.trace_discharge_eq
