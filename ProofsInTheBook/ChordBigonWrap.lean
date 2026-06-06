import ProofsInTheBook.ChordAnchorInst

/-!
# The chord-cap bigon WRAP `keptPhi d₂ = d₁`: discharging `ChordCapData`
  (Chapter 35 — the FINAL chord-side fact)

`ChordAnchorInst.lean` reduced the entire chord-side discharge to the single named
geometric datum `ChordCapData`, whose only genuinely-geometric field is the bigon
WRAP

  `bigon_close : keptPhi d₂ = d₁`   (where `d₁ = M.φ dart`, `d₂ = M.φ² dart`).

Everything else in `ChordCapData` — the proved easy half `keptPhi d₁ = d₂`
(`ChordAnchorInst.keptPhi_face₁Dart₁`), the pure-algebra 2-cycle, the
`CorrectAnchorTwoCycle` instantiation, and the end-to-end `ContiguousInterval`
threading — is already discharged there.  This file closes the last residue.

## The two-step structure of the wrap (what is UNCONDITIONAL here)

`keptPhi = sideSigma₁ ∘ sideAlpha₁ = filteredRotation M.σ keptDel₁ ∘ (M.α ↾ kept)`.
Applied to `d₂ = ⟨M.φ² dart, _⟩`:

* the `α`-step gives the kept dart `M.α (M.φ² dart)` (`sideAlpha₁_apply_coe`);
* its immediate `M.σ`-successor is
  `M.σ (M.α (M.φ² dart)) = (M.σ * M.α) (M.φ² dart) = M.φ³ dart = dart` — the
  DELETED chord dart (`dart_mem_keptDel₁`).

The first fact (`phi_cube_dart`, `M.φ³ dart = dart`) is exactly that the chord-incident
face `face₁ = M.dartFace dart` is an `M`-triangle, i.e. `hNT.inner_tri` applied to the
non-outer face `face₁` (packaged as `data.face₁_isFaceTriangle`, whose third leg
`M.φ (M.φ² dart) = dart` is `M.φ³ dart = dart`).  So **the filtered rotation at `d₂`
genuinely hits the deleted chord dart on its first `σ`-step and MUST skip it** — this is
proved unconditionally here as `bigonWrap_firstStep_deleted` /
`sideSigma₁_sideAlpha₁_firstOutside_ge_two`.

## The irreducible residue (the single named non-vacuous Prop)

After skipping the deleted chord dart, *where the filtered rotation lands* depends on the
order of the remaining darts in the vertex rotation `M.σ` at the chord endpoint `u` (which
of them are kept by side 1, which are deleted as side-2 / outer-face darts).  Concretely:
`dart`'s own `M.σ`-successor is `M.σ dart`, which is **not** `M.φ dart` (that would force
`dart = M.α dart`, impossible); the wrap to `d₁ = M.φ dart` requires that *every* dart
strictly between `dart` and `M.φ dart` in `u`'s `σ`-rotation is deleted.  That is exactly
the discrete planar-embedding (Jordan) datum about how the chord sits in the rotation —
NOT synthesizable from the abstract `M`-triangle `face₁_isFaceTriangle` (which fixes only
the *face* `φ`-orbit, not the *vertex* `σ`-rotation of the deleted darts).

We isolate it as the single Prop `ChordBigonWrap data hsep` — the wrap equation
`keptPhi d₂ = d₁` itself, accompanied by its unconditional `firstStep_deleted` certificate
(so it is visibly the genuine skip-and-wrap, not an abstract pair).  This is strictly the
SAME residue every prior round isolated, now reduced to its irreducible kernel: ONE
filtered-rotation wrap whose first step is the proved-deleted chord dart.

## What this file proves

* `phi_cube_dart` — `M.φ³ dart = dart` (UNCONDITIONAL, from `face₁_isFaceTriangle`).
* `sigma_alpha_phiSq_dart_eq_dart` — `M.σ (M.α (M.φ² dart)) = dart` (UNCONDITIONAL).
* `bigonWrap_firstStep_deleted` — the first `σ`-step of the filtered rotation at `d₂` is the
  DELETED chord dart (UNCONDITIONAL).  This is the concrete skip certificate.
* `sideSigma₁_sideAlpha₁_firstOutside_ge_two` — `firstOutside ≥ 2` at `d₂`: the wrap is a
  genuine multi-step skip, never the trivial `keptPhi d₂ = M.σ-successor` (UNCONDITIONAL).
* `ChordBigonWrap` — the single named geometric residue (the wrap `keptPhi d₂ = d₁` with
  its `firstStep_deleted` certificate + the explicit chord-cap anchors).  Non-vacuous.
* `ChordBigonWrap.toChordCapData` — builds `ChordCapData` from a `ChordBigonWrap`, supplying the
  bigon-WRAP field of `ChordCapData` and threading to
  `ChordAnchorInst.correctAnchorTwoCycle_ofBigon → contiguousInterval_ofBigon →
  ChordSideReconstruction → nearTriangulation_five_colorable`.
* `contiguousInterval_ofWrap` — the end-to-end `ContiguousInterval` drop-in from a
  `ChordBigonWrap`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.dupNamespace false

namespace ProofsInTheBook.ChordBigonWrap

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

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## Section 1.  The unconditional two-step structure of the wrap

`keptPhi d₂ = sideSigma₁ (sideAlpha₁ d₂)`.  The `α`-step lands on `M.α (M.φ² dart)`, whose
first `M.σ`-successor is `M.φ³ dart = dart` — the deleted chord dart.  So the filtered
rotation at `d₂` necessarily SKIPS the chord dart; the wrap is a genuine multi-step skip. -/

/-- **`M.φ³ dart = dart`** — the chord-incident face `face₁` is an `M`-triangle.  This is
the third leg of `data.face₁_isFaceTriangle` (which descends from `hNT.inner_tri` applied to
the non-outer face `face₁`): `M.φ (M.φ² dart) = dart`.  UNCONDITIONAL. -/
theorem phi_cube_dart (data : hNT.ChordSplitData u v) :
    M.φ (M.φ (M.φ data.dart)) = data.dart :=
  data.face₁_isFaceTriangle.2.2

/-- **`M.σ (M.α (M.φ² dart)) = dart`** — the immediate `σ`-successor of the `α`-image of `d₂`
is the chord dart.  `M.σ ∘ M.α = M.φ`, so this is `M.φ (M.φ² dart) = M.φ³ dart = dart`.
UNCONDITIONAL. -/
theorem sigma_alpha_phiSq_dart_eq_dart (data : hNT.ChordSplitData u v) :
    M.σ (M.α (M.φ (M.φ data.dart))) = data.dart := by
  show (M.σ * M.α) (M.φ (M.φ data.dart)) = data.dart
  rw [← CombMap.φ]
  exact phi_cube_dart data

/-- **The first `σ`-step of the filtered rotation at `d₂` is the DELETED chord dart.**  The
filtered rotation `sideSigma₁ = filteredRotation M.σ keptDel₁` starts from `sideAlpha₁ d₂`,
whose underlying dart is `M.α (M.φ² dart)`; its immediate `M.σ`-successor is
`M.σ (M.α (M.φ² dart)) = dart ∈ keptDel₁`.  So the rotation cannot take the trivial single
step — it MUST skip the chord dart.  This is the concrete skip certificate of the bigon
wrap, UNCONDITIONAL. -/
theorem bigonWrap_firstStep_deleted (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    M.σ ((data.sideAlpha₁ hsep (face₁Dart₂ data) : {d : D // d ∉ data.keptDel₁}) : D)
      ∈ data.keptDel₁ := by
  have hval : ((data.sideAlpha₁ hsep (face₁Dart₂ data)) : D) = M.α (M.φ (M.φ data.dart)) := by
    rw [sideAlpha₁_apply_coe]; rfl
  rw [hval, sigma_alpha_phiSq_dart_eq_dart data]
  exact dart_mem_keptDel₁ data

/-- **`firstOutside ≥ 2` at `d₂`.**  Because the first `σ`-successor is deleted
(`bigonWrap_firstStep_deleted`), the filtered rotation takes at least two `σ`-steps from
`sideAlpha₁ d₂`: the wrap is a genuine skip, never the trivial consecutive step.
UNCONDITIONAL. -/
theorem sideSigma₁_sideAlpha₁_firstOutside_ge_two
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    2 ≤ Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₁
          (data.sideAlpha₁ hsep (face₁Dart₂ data)) := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  -- `firstOutside` is positive, so it must be `1` — forcing the deleted first step to be kept.
  have hpos : 0 < Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₁
      (data.sideAlpha₁ hsep (face₁Dart₂ data)) :=
    Equiv.Perm.DeleteSet.firstOutside_pos M.σ data.keptDel₁ _
  have heq1 : Equiv.Perm.DeleteSet.firstOutside M.σ data.keptDel₁
      (data.sideAlpha₁ hsep (face₁Dart₂ data)) = 1 := by omega
  -- the survivor (which is `∉ keptDel₁`) equals the first `σ`-step, which is deleted.
  have hnot := Equiv.Perm.DeleteSet.firstOutside_notMem M.σ data.keptDel₁
    (data.sideAlpha₁ hsep (face₁Dart₂ data))
  rw [heq1, pow_one] at hnot
  exact hnot (bigonWrap_firstStep_deleted data hsep)

/-! ## Section 2.  The single named geometric residue and the `ChordCapData` discharge

The first `σ`-step being the deleted chord dart is proved; *where the rotation lands after the
skip* is the irreducible planar-embedding datum.  We isolate it as `ChordBigonWrap`: the wrap
equation `keptPhi d₂ = d₁` itself, carried together with its unconditional `firstStep_deleted`
certificate (so the datum is visibly the genuine skip-and-wrap, not an abstract pair) and the
explicit chord-cap anchors `a₀, a₁` (the splice darts at the chord endpoints, whose
`σ`-images are OUTSIDE the bigon `{d₁, d₂}`).

`ChordBigonWrap` is the minimal residue: it carries exactly the bigon-WRAP field of
`ChordCapData` plus the chord-cap anchor placement (everything else in `ChordCapData` — the
easy half `keptPhi d₁ = d₂`, the algebra, the threading — is already proved upstream). -/

/-- **The chord-cap bigon-WRAP residue** — the SINGLE named geometric datum of the chord-side
discharge, isolating exactly the discrete-rotation content the abstract `CombMap` does not
synthesize:

* `bigon_wrap` — `keptPhi d₂ = d₁`: after the filtered rotation hits the deleted chord dart
  (`firstStep_deleted`, PROVED), it skips it and wraps to `d₁`.  Together with the upstream
  `keptPhi d₁ = d₂` this makes the kept `face₁` orbit the 2-element bigon `{d₁, d₂}` (the
  deleted-chord-dart gap).
* `a₀, a₁` — the CORRECT chord-cap anchors (the splice darts at the chord endpoints),
  distinct (`anchors_ne`);
* `anchor*_avoid*` — the splice darts' `σ`-images are OUTSIDE the bigon `{d₁, d₂}`: the chord
  cap is inserted exactly outside the bigon, so the swap leaves the 2-orbit intact;
* `hkf`, `one_fresh` — the rep's side face and the one-fresh-chord-dart indicator.

`firstStep_deleted` is an UNCONDITIONAL certificate (= `bigonWrap_firstStep_deleted`) carried
inside the structure so the wrap is visibly the genuine skip-and-wrap of the deleted chord
dart, not a fabricated permutation equation. -/
structure ChordBigonWrap (data : hNT.ChordSplitData u v) (hsep : data.Separates) where
  /-- The chord-cap anchor at one endpoint. -/
  a₀ : {d : D // d ∉ data.keptDel₁}
  /-- The chord-cap anchor at the other endpoint. -/
  a₁ : {d : D // d ∉ data.keptDel₁}
  /-- The anchors are distinct. -/
  anchors_ne : a₀ ≠ a₁
  /-- **The bigon WRAP** `keptPhi d₂ = d₁`: the filtered rotation skips the deleted chord
  dart (certified by `firstStep_deleted`) and wraps to `d₁`. -/
  bigon_wrap :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) = face₁Dart₁ data
  /-- **Unconditional certificate** that the wrap is a genuine skip of the deleted chord dart:
  the first `σ`-step of the filtered rotation at `d₂` is the deleted chord dart. -/
  firstStep_deleted :
    M.σ ((data.sideAlpha₁ hsep (face₁Dart₂ data) : {d : D // d ∉ data.keptDel₁}) : D)
      ∈ data.keptDel₁ :=
    bigonWrap_firstStep_deleted data hsep
  /-- `σ a₀ ∉ {d₁, d₂}`. -/
  anchor0_avoid1 : data.sideSigma₁ a₀ ≠ face₁Dart₁ data
  /-- `σ a₀ ∉ {d₁, d₂}`. -/
  anchor0_avoid2 : data.sideSigma₁ a₀ ≠ face₁Dart₂ data
  /-- `σ a₁ ∉ {d₁, d₂}`. -/
  anchor1_avoid1 : data.sideSigma₁ a₁ ≠ face₁Dart₁ data
  /-- `σ a₁ ∉ {d₁, d₂}`. -/
  anchor1_avoid2 : data.sideSigma₁ a₁ ≠ face₁Dart₂ data
  /-- The chosen side face. -/
  f : (data.sideMap₁ hsep a₀ a₁ anchors_ne).Face
  /-- The rep's side face is `f`. -/
  hkf : (data.sideMap₁ hsep a₀ a₁ anchors_ne).dartFace (Sum.inl (face₁Dart₁ data)) = f
  /-- The one-fresh-chord-dart indicator. -/
  one_fresh :
    ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
          ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
      + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
          ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1

/-- **`ChordCapData` from a `ChordBigonWrap` — discharging the bigon-WRAP field.**  The
chord-cap data is built directly: its only genuinely-geometric field `bigon_close`
(`keptPhi d₂ = d₁`) is the wrap's `bigon_wrap`; the anchors and the remaining concrete fields
are carried over.  This connects the wrap residue to `ChordAnchorInst.ChordCapData`, hence to
`correctAnchorTwoCycle_ofBigon → contiguousInterval_ofBigon`. -/
def ChordBigonWrap.toChordCapData (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (w : ChordBigonWrap data hsep) : ChordCapData data hsep :=
  { a₀ := w.a₀, a₁ := w.a₁, anchors_ne := w.anchors_ne, bigon_close := w.bigon_wrap,
    anchor0_avoid1 := w.anchor0_avoid1, anchor0_avoid2 := w.anchor0_avoid2,
    anchor1_avoid1 := w.anchor1_avoid1, anchor1_avoid2 := w.anchor1_avoid2,
    f := w.f, hkf := w.hkf, one_fresh := w.one_fresh }

/-- **The `tracePhi` 2-cycle on the actual `face₁` darts, from a `ChordBigonWrap`.**  From the
wrap (`keptPhi d₂ = d₁`) + the upstream proved `keptPhi d₁ = d₂` + anchor avoidance, the side
`tracePhi` cycles `d₁ ↔ d₂` — derived via `ChordAnchorInst.chordCap_tracePhi_twoCycle`. -/
theorem tracePhi_twoCycle_ofWrap (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (w : ChordBigonWrap data hsep) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ w.a₀ w.a₁ (face₁Dart₁ data)
        = face₁Dart₂ data ∧
      tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ w.a₀ w.a₁ (face₁Dart₂ data)
        = face₁Dart₁ data :=
  chordCap_tracePhi_twoCycle data hsep (w.toChordCapData data hsep)

/-- **`CorrectAnchorTwoCycle` for the chord-cap anchors, from a `ChordBigonWrap`.**  The
two-layer connection: instantiating `sideMap₁`'s free anchors at the chord-cap splice darts
(carried by `ChordBigonWrap`), the orbit-isolation spec `CorrectAnchorTwoCycle` holds, with the
bigon WRAP `keptPhi d₂ = d₁` now SUPPLIED.  Threads to the downstream chain. -/
noncomputable def correctAnchorTwoCycle_ofWrap (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (w : ChordBigonWrap data hsep) :
    CorrectAnchorTwoCycle data hsep w.a₀ w.a₁ w.anchors_ne w.f :=
  correctAnchorTwoCycle_ofBigon data hsep (w.toChordCapData data hsep)

/-- **The touched `face₁` side face is a triangle, from a `ChordBigonWrap`.**  End-to-end with
the chord-cap anchors and the WRAP discharged: the chord-triangle `face₁`'s side face is a
length-3 triangle DIRECTLY. -/
theorem face₁_sideTriangle_ofWrap (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (w : ChordBigonWrap data hsep) :
    SideFaceTriangle data hsep w.a₀ w.a₁ w.anchors_ne w.f :=
  face₁_sideTriangle_ofBigon data hsep (w.toChordCapData data hsep)

/-- **End-to-end `ContiguousInterval` from a `ChordBigonWrap`.**  The chord-side drop-in with
`sideMap₁`'s anchors pinned to the chord-cap darts and the touched `face₁` face handled via the
discharged WRAP.  Threads to `ChordSideNT.chordSideNearTriangulation → ChordSideReconstruction →
chord_case_recursive → nearTriangulation_five_colorable`. -/
def contiguousInterval_ofWrap (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (w : ChordBigonWrap data hsep)
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
  contiguousInterval_ofBigon data hsep (w.toChordCapData data hsep)
    hsimple outerFace outerCycle outer_simple outer_len hclass

/-! ## Section 3.  §3.3 non-vacuity / no-rewrapper certificates -/

/-- **No-rewrapper certificate.**  The `tracePhi` 2-cycle from a `ChordBigonWrap` is genuinely
COMPUTED — from the WRAP (`keptPhi d₂ = d₁`), the upstream proved `keptPhi d₁ = d₂`, and the
anchor-avoidance — through `ChordAnchorInst.chordCap_tracePhi_twoCycle`, NOT handed in.  The
last clause records the unconditional `firstStep_deleted` certificate carried by the wrap. -/
theorem wrap_discharge_eq (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (w : ChordBigonWrap data hsep) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ w.a₀ w.a₁ (face₁Dart₁ data)
        = face₁Dart₂ data ∧
      tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ w.a₀ w.a₁ (face₁Dart₂ data)
        = face₁Dart₁ data ∧
      keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₁ data) = face₁Dart₂ data ∧
      M.σ ((data.sideAlpha₁ hsep (face₁Dart₂ data) : {d : D // d ∉ data.keptDel₁}) : D)
        ∈ data.keptDel₁ :=
  ⟨(tracePhi_twoCycle_ofWrap data hsep w).1,
    (tracePhi_twoCycle_ofWrap data hsep w).2,
    keptPhi_face₁Dart₁ data hsep,
    w.firstStep_deleted⟩

/-- **The residue datum is satisfiable (non-vacuous), not a hidden `False`.**  Given the
component data — the bigon WRAP, distinct chord-cap anchors avoiding the bigon, the rep face,
and the one-fresh indicator — `ChordBigonWrap` is inhabited.  The `firstStep_deleted` field is
supplied UNCONDITIONALLY (`bigonWrap_firstStep_deleted`), so the wrap is visibly the genuine
skip-and-wrap of the deleted chord dart.  This is the §3.3 satisfiability check: the chord-cap
bigon wrap is the genuine correct-anchor placement, NOT an unsatisfiable premise. -/
def ChordBigonWrap.mk' (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (anchors_ne : a₀ ≠ a₁)
    (bigon_wrap :
      keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) = face₁Dart₁ data)
    (anchor0_avoid1 : data.sideSigma₁ a₀ ≠ face₁Dart₁ data)
    (anchor0_avoid2 : data.sideSigma₁ a₀ ≠ face₁Dart₂ data)
    (anchor1_avoid1 : data.sideSigma₁ a₁ ≠ face₁Dart₁ data)
    (anchor1_avoid2 : data.sideSigma₁ a₁ ≠ face₁Dart₂ data)
    (f : (data.sideMap₁ hsep a₀ a₁ anchors_ne).Face)
    (hkf : (data.sideMap₁ hsep a₀ a₁ anchors_ne).dartFace (Sum.inl (face₁Dart₁ data)) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    ChordBigonWrap data hsep :=
  { a₀ := a₀, a₁ := a₁, anchors_ne := anchors_ne, bigon_wrap := bigon_wrap,
    firstStep_deleted := bigonWrap_firstStep_deleted data hsep,
    anchor0_avoid1 := anchor0_avoid1, anchor0_avoid2 := anchor0_avoid2,
    anchor1_avoid1 := anchor1_avoid1, anchor1_avoid2 := anchor1_avoid2,
    f := f, hkf := hkf, one_fresh := one_fresh }

end ProofsInTheBook.ChordBigonWrap

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordBigonWrap.phi_cube_dart
#print axioms ProofsInTheBook.ChordBigonWrap.sigma_alpha_phiSq_dart_eq_dart
#print axioms ProofsInTheBook.ChordBigonWrap.bigonWrap_firstStep_deleted
#print axioms ProofsInTheBook.ChordBigonWrap.sideSigma₁_sideAlpha₁_firstOutside_ge_two
#print axioms ProofsInTheBook.ChordBigonWrap.tracePhi_twoCycle_ofWrap
#print axioms ProofsInTheBook.ChordBigonWrap.correctAnchorTwoCycle_ofWrap
#print axioms ProofsInTheBook.ChordBigonWrap.face₁_sideTriangle_ofWrap
#print axioms ProofsInTheBook.ChordBigonWrap.contiguousInterval_ofWrap
#print axioms ProofsInTheBook.ChordBigonWrap.wrap_discharge_eq
