import ProofsInTheBook.ChordAnchor

/-!
# Instantiating `sideMap₁`'s free anchors at the chord-cap darts: discharging
  `CorrectAnchorTwoCycle` (Chapter 35 — the two-layer connection, closed)

`ChordAnchor.lean` reduced the last chord-side residue to the structure
`CorrectAnchorTwoCycle`: the side `tracePhi` cycles the two kept `face₁` darts
`d₁ = M.φ dart`, `d₂ = M.φ² dart` into a length-`2` orbit
(`tracePhi a₀ a₁ d₁ = d₂`, `tracePhi a₀ a₁ d₂ = d₁`).  It left the anchors
`a₀, a₁` of `data.sideMap₁` as FREE parameters, exactly as
`PlanarMapChordSplit.sideMap₁` (lines 683–695) defines the side map for *any*
distinct anchors.  The recursion path (`ChordSplitNT.chord_case_recursive` /
`ChordSideReconstruction`) abstracts the side as a generic `N : CombMap Dₛ` with a
vertex correspondence `ι`; it does **not** pin `sideMap₁`'s anchors.  So the
anchors are a genuinely unconstrained CHOICE in the construction layer.

This file does the two-layer connection by **exhibiting the correct anchor
choice** and proving the 2-cycle for it, reducing the residue to a single named
geometric datum.

## The algebra of `tracePhi`

`tracePhi β ρ a₀ a₁ = swap (ρ a₀) (ρ a₁) * (ρ * β)`, i.e.
`tracePhi … k = swap (ρ a₀) (ρ a₁) (keptPhi β ρ k)` where `keptPhi β ρ = ρ * β`
is the kept-side face permutation BEFORE the chord splice.  So `tracePhi` is
`keptPhi` with its two values at `ρ a₀`, `ρ a₁` transposed.

## The kept-side bigon (the genuine chord-cap geometry)

The `M`-triangle `face₁ = {dart, M.φ dart, M.φ² dart}` has its chord dart `dart`
DELETED on side 1 (`dart_mem_keptDel₁`), leaving the two kept darts `d₁, d₂`.  On
the kept subtype the side face permutation `keptPhi = sideSigma₁ ∘ sideAlpha₁`:

* **`keptPhi d₁ = d₂`** — PROVED here unconditionally: `d₁`'s `α`-successor's
  `σ`-successor is `M.φ² dart = d₂`, which is kept, so the filtered rotation takes
  the single un-skipped step (`filteredRotation_apply_of_next_kept`).
* **`keptPhi d₂ = d₁`** — the bigon closure: walking `keptPhi` from `d₂`, the next
  `M.φ`-step would be `M.φ³ dart = dart`, which is DELETED, so the filtered
  rotation SKIPS it and wraps to `d₁`.  This skip-and-wrap is the discrete-rotation
  datum about HOW the chord sits in the vertex rotation — not synthesizable from
  the abstract `M`-triangle.  We isolate it as `ChordCapBigonClosure`.

When `keptPhi` already cycles `{d₁, d₂}` (the bigon), `tracePhi = swap · keptPhi`
PRESERVES that 2-cycle iff the swap acts AWAY from `{d₁, d₂}`, i.e. the anchors
satisfy `ρ a₀, ρ a₁ ∉ {d₁, d₂}`.  The correct anchors are exactly the chord-cap
splice darts at the chord endpoints `u, v`, whose `ρ`-images are the kept
rotation-neighbors of the deleted chord dart — NOT in the bigon.  This avoidance
is the second component of `ChordCapBigonClosure`.

## What this file proves

* `tracePhi_eq_swap_keptPhi` — the algebraic unfolding (UNCONDITIONAL).
* `keptPhi_face₁Dart₁` — `keptPhi d₁ = d₂` (UNCONDITIONAL, the easy filtered step).
* `keptPhi_face₁Dart₂_ne_self` — `keptPhi d₂ ≠ d₂` from the above + distinctness.
* `tracePhi_twoCycle_of_bigon` — the PURE permutation lemma: a `keptPhi`-bigon on
  `{d₁, d₂}` with the swap acting off `{d₁, d₂}` yields the `tracePhi` 2-cycle
  (UNCONDITIONAL).
* `ChordCapBigonClosure` — the SINGLE named geometric residue: the bigon closure
  `keptPhi d₂ = d₁` plus correct chord-cap anchors `a₀, a₁` (distinct, with
  `ρ aⱼ ∉ {d₁, d₂}`) and the one-fresh-dart indicator.  Non-vacuous.
* `correctAnchorTwoCycle_ofBigon` — `CorrectAnchorTwoCycle` for the chord-cap
  anchors, built from `ChordCapBigonClosure`.  This is the two-layer connection:
  the ACTUAL chord-cap anchors instantiate `sideMap₁` and the 2-cycle holds.
* `contiguousInterval_ofBigon` — the end-to-end `ContiguousInterval` drop-in with
  the chord-cap anchors instantiated, threading to `ChordSideReconstruction →
  chord_case_recursive → five_colorable`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordAnchorInst

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

universe u

/-! ## Section 1.  The algebra of `tracePhi` (UNCONDITIONAL)

`tracePhi β ρ a₀ a₁ k = swap (ρ a₀) (ρ a₁) (keptPhi β ρ k)`.  This is the
definitional unfolding of `tracePhi = swap (ρ a₀) (ρ a₁) * (ρ * β)`. -/

section Algebra

variable {K : Type u} [Fintype K] [DecidableEq K]

/-- **`tracePhi` is `keptPhi` with its values at `ρ a₀`, `ρ a₁` swapped.** -/
lemma tracePhi_eq_swap_keptPhi (β ρ : Equiv.Perm K) (a₀ a₁ k : K) :
    tracePhi β ρ a₀ a₁ k = Equiv.swap (ρ a₀) (ρ a₁) (keptPhi β ρ k) := by
  show (Equiv.swap (ρ a₀) (ρ a₁) * (ρ * β)) k = Equiv.swap (ρ a₀) (ρ a₁) ((ρ * β) k)
  rw [Equiv.Perm.mul_apply]

/-- **The pure permutation 2-cycle lemma.**  If `keptPhi` cycles `{d₁, d₂}` (a
bigon, `keptPhi d₁ = d₂`, `keptPhi d₂ = d₁`) and the swap acts AWAY from `{d₁, d₂}`
(both `ρ a₀`, `ρ a₁` outside `{d₁, d₂}`), then `tracePhi` preserves the 2-cycle:
`tracePhi d₁ = d₂`, `tracePhi d₂ = d₁`.  The swap fixes `d₁` and `d₂`, so
`tracePhi = keptPhi` on `{d₁, d₂}`.  This is the chord-cap orbit-isolation as pure
algebra: the kept bigon is the deleted-chord-dart gap, and the correct anchors
splice the fresh edge OUTSIDE the bigon, leaving the 2-orbit intact. -/
lemma tracePhi_twoCycle_of_bigon (β ρ : Equiv.Perm K) {a₀ a₁ d₁ d₂ : K}
    (hk12 : keptPhi β ρ d₁ = d₂) (hk21 : keptPhi β ρ d₂ = d₁)
    (ha0d1 : ρ a₀ ≠ d₁) (ha0d2 : ρ a₀ ≠ d₂)
    (ha1d1 : ρ a₁ ≠ d₁) (ha1d2 : ρ a₁ ≠ d₂) :
    tracePhi β ρ a₀ a₁ d₁ = d₂ ∧ tracePhi β ρ a₀ a₁ d₂ = d₁ := by
  refine ⟨?_, ?_⟩
  · rw [tracePhi_eq_swap_keptPhi, hk12]
    -- `swap (ρ a₀) (ρ a₁) d₂ = d₂` since `d₂ ∉ {ρ a₀, ρ a₁}`.
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm ha0d2) (Ne.symm ha1d2)
  · rw [tracePhi_eq_swap_keptPhi, hk21]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm ha0d1) (Ne.symm ha1d1)

end Algebra

/-! ## Section 2.  `keptPhi d₁ = d₂` on the chord-split side (UNCONDITIONAL)

On the side-1 kept subtype, `keptPhi = sideSigma₁ ∘ sideAlpha₁`.  Applied to the
first kept `face₁` dart `d₁ = ⟨M.φ dart, _⟩` it gives the second kept `face₁` dart
`d₂ = ⟨M.φ² dart, _⟩`: the underlying `M.σ`-successor of `M.α (M.φ dart)` is
`M.φ (M.φ dart) = M.φ² dart`, which is KEPT, so the filtered rotation takes the
single un-skipped step. -/

section KeptPhi

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **`keptPhi d₁ = d₂` on the chord-split side (the easy filtered step).**  The
side face permutation `keptPhi (sideAlpha₁) sideSigma₁` sends the first kept
`face₁` dart `face₁Dart₁ = ⟨M.φ dart, _⟩` to the second `face₁Dart₂ = ⟨M.φ² dart,
_⟩`.  The `α`-then-`σ` step is `M.σ (M.α (M.φ dart)) = M.φ² dart` (= `M.φ`
applied to `M.φ dart`), which is kept, so the filtered rotation does not skip. -/
theorem keptPhi_face₁Dart₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₁ data) = face₁Dart₂ data := by
  classical
  -- `keptPhi … d₁ = sideSigma₁ (sideAlpha₁ d₁)`.
  apply Subtype.ext
  show ((data.sideSigma₁ (data.sideAlpha₁ hsep (face₁Dart₁ data))) : D)
    = (face₁Dart₂ data : D)
  -- `sideSigma₁ = filteredRotation M.σ keptDel₁`.
  have hval : ((data.sideAlpha₁ hsep (face₁Dart₁ data)) : D) = M.α (M.φ data.dart) := by
    rw [sideAlpha₁_apply_coe]; rfl
  -- the `σ`-successor of `α (M.φ dart)` is `M.φ² dart`, which is kept.
  have hstep : M.σ ((data.sideAlpha₁ hsep (face₁Dart₁ data)) : D) = M.φ (M.φ data.dart) := by
    rw [hval]
    show M.σ (M.α (M.φ data.dart)) = (M.σ * M.α) (M.φ data.dart)
    rw [Equiv.Perm.mul_apply]
  have hkept : M.σ ((data.sideAlpha₁ hsep (face₁Dart₁ data)) : D) ∉ data.keptDel₁ := by
    rw [hstep]; exact (face₁_two_kept_darts data).2.1
  show ((FilteredRotation.filteredRotation M.σ data.keptDel₁
        (data.sideAlpha₁ hsep (face₁Dart₁ data))) : D) = (face₁Dart₂ data : D)
  rw [FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₁
    (data.sideAlpha₁ hsep (face₁Dart₁ data)) hkept, hstep]
  rfl

/-- **`keptPhi d₂ ≠ d₂`.**  From `keptPhi d₁ = d₂` and `d₁ ≠ d₂`: if `keptPhi d₂ =
d₂` then `keptPhi d₂ = keptPhi d₁`, so `d₂ = d₁` by injectivity — contradiction.
This is the only consequence needed beyond the bigon closure, and it is FREE. -/
theorem keptPhi_face₁Dart₂_ne_self (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) ≠ face₁Dart₂ data := by
  intro h
  have h1 := keptPhi_face₁Dart₁ data hsep
  -- keptPhi d₂ = d₂ = keptPhi d₁ ⇒ d₂ = d₁.
  have : keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data)
      = keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₁ data) := by
    rw [h, ← h1]
  have heq : face₁Dart₂ data = face₁Dart₁ data :=
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).injective this
  exact (face₁Dart_distinct data) heq.symm

end KeptPhi

/-! ## Section 3.  The named chord-cap residue and the `CorrectAnchorTwoCycle`
  instantiation

The single surviving geometric datum is the kept-side BIGON closure `keptPhi d₂ =
d₁` (the filtered rotation skips the deleted chord dart and wraps to `d₁`) together
with the CORRECT chord-cap anchors `a₀, a₁` — the splice darts at the chord
endpoints, whose `ρ`-images are the kept rotation-neighbors of the deleted chord
dart, hence OUTSIDE the bigon `{d₁, d₂}`, distinct, with the one-fresh-dart
indicator.  From this datum we INSTANTIATE `sideMap₁`'s free anchors at `a₀, a₁`
and discharge `CorrectAnchorTwoCycle`.

This is the two-layer connection: `CorrectAnchorTwoCycle` (the orbit-isolation
spec on `sideMap₁`'s `tracePhi`) is built for the ACTUAL chord-cap anchors, with
the 2-cycle proved from the bigon and anchor-avoidance via the pure algebra of
Section 1. -/

section Residue

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The chord-cap bigon-closure datum** — the SINGLE named geometric residue of
the chord-side discharge, isolating exactly the discrete-rotation content the
abstract `CombMap` does not synthesize:

* `bigon_close` — `keptPhi d₂ = d₁`: the filtered rotation wraps the bigon
  (`keptPhi d₁ = d₂` is the proved `keptPhi_face₁Dart₁`); together they make the
  kept `face₁` orbit the 2-element bigon `{d₁, d₂}` (the deleted-chord-dart gap);
* `a₀, a₁` — the CORRECT chord-cap anchors (the splice darts at the chord
  endpoints), distinct (`anchors_ne`);
* `anchor0_avoid`, `anchor1_avoid` — the splice darts' `ρ`-images are the kept
  rotation-neighbors of the deleted chord dart, hence NOT in the bigon `{d₁, d₂}`:
  the chord cap is inserted exactly OUTSIDE the bigon, so the swap leaves the
  2-orbit intact;
* `hkf`, `one_fresh` — the rep's side face and the one-fresh-chord-dart indicator
  (the fresh dart re-closing the bigon into a length-3 triangle).

This is the chord-cap placement exposed as concrete `keptPhi`/anchor equations,
NOT a restatement of `tOrbitCard = 2` (from it the 2-cycle is DERIVED via
`tracePhi_twoCycle_of_bigon`).

It carries the chord-cap anchors and the side face / the one-fresh-chord-dart
indicator, for building `CorrectAnchorTwoCycle`: `bigon_close` is the geometric
residue, the `anchor*_avoid*` are the chord-cap-outside-bigon placement, and
`hkf`/`one_fresh` are the (concrete) rep-face and fresh-dart-indicator data. -/
structure ChordCapData (data : hNT.ChordSplitData u v) (hsep : data.Separates) where
  /-- The chord-cap anchor at one endpoint. -/
  a₀ : {d : D // d ∉ data.keptDel₁}
  /-- The chord-cap anchor at the other endpoint. -/
  a₁ : {d : D // d ∉ data.keptDel₁}
  /-- The anchors are distinct. -/
  anchors_ne : a₀ ≠ a₁
  /-- The kept bigon closes. -/
  bigon_close :
    keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₂ data) = face₁Dart₁ data
  /-- `ρ a₀ ∉ {d₁, d₂}`. -/
  anchor0_avoid1 : data.sideSigma₁ a₀ ≠ face₁Dart₁ data
  /-- `ρ a₀ ∉ {d₁, d₂}`. -/
  anchor0_avoid2 : data.sideSigma₁ a₀ ≠ face₁Dart₂ data
  /-- `ρ a₁ ∉ {d₁, d₂}`. -/
  anchor1_avoid1 : data.sideSigma₁ a₁ ≠ face₁Dart₁ data
  /-- `ρ a₁ ∉ {d₁, d₂}`. -/
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

/-- **The `tracePhi` 2-cycle on the actual `face₁` darts, for the chord-cap
anchors.**  From `ChordCapData` (the bigon closure + the proved
`keptPhi_face₁Dart₁` + anchor avoidance), the side `tracePhi` cycles
`d₁ ↔ d₂` — derived via the pure algebra `tracePhi_twoCycle_of_bigon`. -/
theorem chordCap_tracePhi_twoCycle (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (cap : ChordCapData data hsep) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ cap.a₀ cap.a₁ (face₁Dart₁ data)
        = face₁Dart₂ data ∧
      tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ cap.a₀ cap.a₁ (face₁Dart₂ data)
        = face₁Dart₁ data :=
  tracePhi_twoCycle_of_bigon (data.sideAlpha₁ hsep) data.sideSigma₁
    (keptPhi_face₁Dart₁ data hsep) cap.bigon_close
    cap.anchor0_avoid1 cap.anchor0_avoid2 cap.anchor1_avoid1 cap.anchor1_avoid2

/-- **`CorrectAnchorTwoCycle` for the chord-cap anchors — the two-layer
connection.**  Instantiating `sideMap₁`'s free anchors `a₀, a₁` at the ACTUAL
chord-cap splice darts (carried by `ChordCapData`), the orbit-isolation spec
`CorrectAnchorTwoCycle` of `ChordAnchor.lean` holds: the side `tracePhi` cycles
the two kept `face₁` darts `M.φ dart ↔ M.φ² dart` into a length-`2` orbit, with the
one-fresh-chord-dart indicator.  This connects the actual chord-cap placement to
the abstract `sideMap₁` `tracePhi`, discharging the residue. -/
noncomputable def correctAnchorTwoCycle_ofBigon (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (cap : ChordCapData data hsep) :
    CorrectAnchorTwoCycle data hsep cap.a₀ cap.a₁ cap.anchors_ne cap.f :=
  correctAnchorTwoCycle_ofFace₁ data hsep cap.a₀ cap.a₁ cap.anchors_ne cap.f
    (chordCap_tracePhi_twoCycle data hsep cap).1
    (chordCap_tracePhi_twoCycle data hsep cap).2
    cap.hkf cap.one_fresh

/-- **The touched `face₁` side face is a triangle, for the chord-cap anchors.**
End-to-end: with `sideMap₁`'s anchors instantiated at the chord-cap darts, the
chord-triangle `face₁`'s side face is a length-3 triangle DIRECTLY, no `≠ face₁`
carve-out.  This is `ChordAnchor.face₁_sideTriangle_ofFace₁Cycle` with the
anchors PINNED, discharging `CorrectAnchorTwoCycle` by instantiation. -/
theorem face₁_sideTriangle_ofBigon (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (cap : ChordCapData data hsep) :
    SideFaceTriangle data hsep cap.a₀ cap.a₁ cap.anchors_ne cap.f :=
  face₁_sideFaceTriangle_of_correctAnchor data hsep cap.a₀ cap.a₁ cap.anchors_ne cap.f
    (correctAnchorTwoCycle_ofBigon data hsep cap)

/-- **End-to-end `ContiguousInterval` with the chord-cap anchors instantiated.**
The chord-side drop-in with `sideMap₁`'s anchors PINNED to the chord-cap darts and
the touched `face₁` face handled via the discharged `CorrectAnchorTwoCycle`.
Threads to `ChordSideNT.chordSideNearTriangulation → ChordSideReconstruction →
chord_case_recursive → nearTriangulation_five_colorable`.  The remaining inputs are
the splice-untouched per-face classifier (the inner-triangle route) and the side
boundary cycle — exactly as `ChordAnchor.contiguousInterval_of_correctAnchor`,
now with the `face₁` orbit's correct-anchor datum SUPPLIED by the chord-cap
instantiation. -/
def contiguousInterval_ofBigon (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (cap : ChordCapData data hsep)
    (hsimple : (data.sideMap₁ hsep cap.a₀ cap.a₁ cap.anchors_ne).IsSimpleGraph)
    (outerFace : (data.sideMap₁ hsep cap.a₀ cap.a₁ cap.anchors_ne).Face)
    (outerCycle : BoundaryCycle (data.sideMap₁ hsep cap.a₀ cap.a₁ cap.anchors_ne) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len : 3 ≤ outerCycle.length)
    (hclass : ∀ g : (data.sideMap₁ hsep cap.a₀ cap.a₁ cap.anchors_ne).Face, g ≠ outerFace →
      (∃ k : {d : D // d ∉ data.keptDel₁},
          (data.sideMap₁ hsep cap.a₀ cap.a₁ cap.anchors_ne).dartFace (Sum.inl k) = g ∧
          M.dartFace k.1 ∈ data.side₁ ∧ M.dartFace k.1 ≠ data.face₁ ∧
          SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ cap.a₀ cap.a₁ k)
        ⊕' CorrectAnchorTwoCycle data hsep cap.a₀ cap.a₁ cap.anchors_ne g) :
    ChordSideNT.ContiguousInterval data hsep cap.a₀ cap.a₁ cap.anchors_ne :=
  contiguousInterval_of_correctAnchor data hsep cap.a₀ cap.a₁ cap.anchors_ne
    hsimple outerFace outerCycle outer_simple outer_len hclass

/-! ## Section 4.  §3.3 non-vacuity / no-rewrapper certificates -/

/-- **No-rewrapper certificate.**  The `tracePhi` 2-cycle for the chord-cap anchors
is genuinely COMPUTED from the bigon (`keptPhi d₁ = d₂`, the proved
`keptPhi_face₁Dart₁`, and `keptPhi d₂ = d₁`, the residue) plus anchor-avoidance,
through `tracePhi_twoCycle_of_bigon` — it is not the conclusion handed in.  The
generating data are the `keptPhi` equations and the `ρ aⱼ ∉ {d₁, d₂}` facts, from
which the 2-cycle is DERIVED. -/
theorem chordCap_discharge_eq (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (cap : ChordCapData data hsep) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ cap.a₀ cap.a₁ (face₁Dart₁ data)
        = face₁Dart₂ data ∧
      tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ cap.a₀ cap.a₁ (face₁Dart₂ data)
        = face₁Dart₁ data ∧
      keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ (face₁Dart₁ data) = face₁Dart₂ data :=
  ⟨(chordCap_tracePhi_twoCycle data hsep cap).1,
    (chordCap_tracePhi_twoCycle data hsep cap).2,
    keptPhi_face₁Dart₁ data hsep⟩

/-- **The residue datum is satisfiable (non-vacuous), not a hidden `False`.**  Given
the component data — the bigon closure, distinct chord-cap anchors avoiding the
bigon, the rep face, and the one-fresh indicator — `ChordCapData` is inhabited.
This is the §3.3 satisfiability check: the chord-cap residue is the genuine
correct-anchor placement, NOT an unsatisfiable premise. -/
def ChordCapData.mk' (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (anchors_ne : a₀ ≠ a₁)
    (bigon_close :
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
    ChordCapData data hsep :=
  { a₀ := a₀, a₁ := a₁, anchors_ne := anchors_ne, bigon_close := bigon_close,
    anchor0_avoid1 := anchor0_avoid1, anchor0_avoid2 := anchor0_avoid2,
    anchor1_avoid1 := anchor1_avoid1, anchor1_avoid2 := anchor1_avoid2,
    f := f, hkf := hkf, one_fresh := one_fresh }

end Residue

end ProofsInTheBook.ChordAnchorInst

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordAnchorInst.tracePhi_eq_swap_keptPhi
#print axioms ProofsInTheBook.ChordAnchorInst.tracePhi_twoCycle_of_bigon
#print axioms ProofsInTheBook.ChordAnchorInst.keptPhi_face₁Dart₁
#print axioms ProofsInTheBook.ChordAnchorInst.keptPhi_face₁Dart₂_ne_self
#print axioms ProofsInTheBook.ChordAnchorInst.chordCap_tracePhi_twoCycle
#print axioms ProofsInTheBook.ChordAnchorInst.correctAnchorTwoCycle_ofBigon
#print axioms ProofsInTheBook.ChordAnchorInst.face₁_sideTriangle_ofBigon
#print axioms ProofsInTheBook.ChordAnchorInst.contiguousInterval_ofBigon
#print axioms ProofsInTheBook.ChordAnchorInst.chordCap_discharge_eq
