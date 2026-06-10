import ProofsInTheBook.ZinanCh35SideAnchors

/-!
# The Chapter 35 chord-side `hclass` gluing bricks (the `ContiguousInterval` master glue)

`ZinanCh35SideAnchors.lean` pinned the **canonical** chord-cap anchors `a₀, a₁` of side 1 and
proved, UNCONDITIONALLY, the post-splice `tracePhi` 2-cycle on the two kept `face₁` darts
(`side₁Anchors_trace12`/`trace21`).  This file assembles those anchor facts, together with the
explicit-trace orbit machinery of `ChordBoundaryOrbit` and the correct-anchor structure of
`ChordAnchor`, into the master **per-face classifier** consumed by
`ChordAnchor.contiguousInterval_of_correctAnchor`:

> for every non-outer side face `g`, EITHER `g` has a splice-untouched, side-`₁`,
> non-`face₁` kept-`inl` representative, OR `g` carries a `CorrectAnchorTwoCycle` datum.

and then feeds it into the final `ContiguousInterval` assembler.

## Bricks (design §8 order)

1.  Notation block (`β ρ a₀ a₁ hne S τ`).
2.  `side₁_trace_beta_a0_to_face₁Dart₁` — `τ (β a₀) = face₁Dart₁ data`
    (`tracePhi_b0` + `sideSigma₁_side₁Anchor₁`).
3.  `side₁_chord0_face_eq_face₁_canonical` — `S.dartFace (inr 0) = S.dartFace (inl face₁Dart₁)`
    (`chordDart_face_eq_b0` + `sideFace_inl_eq_iff_tracePhi` via brick 2).
4.  `Side₁OuterTraceData` — the INPUT bundle (outer face + its boundary cycle, the two chord/face
    incidence facts, and the inner-rep avoidance residue).
5.  `side₁Anchors_oneFresh_canonical` — the one-fresh indicator `= 1`.
6.  `side₁_correctAnchor_face₁_canonical` — the `CorrectAnchorTwoCycle` datum for the touched
    `face₁` side face (`correctAnchorTwoCycle_ofFace₁` + bricks 5 & landed trace12/trace21).
7.  `side1_hclass_canonical` — the MASTER per-face classifier (face₁ branch transports brick 6
    across the face equality; no-hit branch uses `spliceUntouched_of_face_ne_chordOrbits`).
8.  `contiguousInterval_canonical` — feed brick 7 into `contiguousInterval_of_correctAnchor`.

**Input-bundle addition (reported per the design's license).**  The design's
`Side₁OuterTraceData` lists `outerFace, outerCycle, outer_simple, outer_len, chord1_is_outer,
face₁_not_outer`.  The no-hit branch's `M.dartFace k.1 ∈ side₁` (`hside`) obligation is the
genuine geometric residue "the side outer face is exactly the `M`-outer-arc orbit, so every other
face's rep avoids the `M`-outer face" — NOT derivable from the abstract `CombMap`.  Rather than
weaken, we carry it as the repo-native field `inner_reps :
ChordBoundaryOrbit.InnerRepsAvoidBoundary …` (which packages exactly "each non-outer side face has
a kept-`inl` rep with `M`-face `≠ M`-outer and `≠ face₁`"), as the design explicitly permits.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35Hclass

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordFaceClass
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal
open ProofsInTheBook.ChordAnchor
open ProofsInTheBook.ChordAnchorInst
open ProofsInTheBook.ChordSigmaContig
open ProofsInTheBook.ZinanCh35SideAnchors

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## Brick 1.  Notation / abbreviations for the canonical side-1 chord cap

`β = sideAlpha₁ hsep`, `ρ = sideSigma₁`, `a₀ = side₁Anchor₀`, `a₁ = side₁Anchor₁`,
`hne : a₀ ≠ a₁`, `S = sideMap₁ hsep a₀ a₁ hne`, `τ = tracePhi β ρ a₀ a₁`.

To keep `simp`/`rw` against the landed lemmas (whose statements are phrased in the unfolded
`data.…` names) friction-free, we use the explicit `data.…` spellings throughout rather than
global abbreviation defs; the abbreviation dictionary below is for reading only.

* `β  := data.sideAlpha₁ hsep`
* `ρ  := data.sideSigma₁`
* `a₀ := side₁Anchor₀ data hsep`,  `a₁ := side₁Anchor₁ data hsep`
* `hne := side₁Anchors_ne data hsep`
* `S  := data.sideMap₁ hsep a₀ a₁ hne`
* `τ  := tracePhi β ρ a₀ a₁`
-/

/-! ## Brick 2.  `τ (β a₀) = face₁Dart₁ data`

`tracePhi (β a₀) = ρ a₁` (`tracePhi_b0`, using `β * β = 1`); and `ρ a₁ = sideSigma₁ a₁
= face₁Dart₁ data` (`sideSigma₁_side₁Anchor₁`).  So `β a₀` lies one `τ`-step before
`face₁Dart₁`, hence in the `face₁` `tracePhi`-orbit. -/

/-- **`τ (β a₀) = face₁Dart₁`** for the canonical anchors. -/
theorem side₁_trace_beta_a0_to_face₁Dart₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep))
      = face₁Dart₁ data := by
  rw [tracePhi_b0 (data.sideAlpha₁ hsep) data.sideSigma₁ (data.sideAlpha₁_involutive hsep),
    sideSigma₁_side₁Anchor₁]

/-- **`β a₀` is `τ`-SameCycle to `face₁Dart₁`** (one `τ`-step), the orbit form of brick 2. -/
theorem side₁_betaA0_sameCycle_face₁Dart₁
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
      ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) (face₁Dart₁ data) := by
  refine ⟨1, ?_⟩
  rw [zpow_one]
  exact side₁_trace_beta_a0_to_face₁Dart₁ data hsep

/-! ## Brick 3.  `S.dartFace (inr 0) = S.dartFace (inl face₁Dart₁)`

`S.dartFace (inr 0) = S.dartFace (inl (β a₀))` (`chordDart_face_eq_b0`, since `sideMap₁ = freshMap
…`), and `S.dartFace (inl (β a₀)) = S.dartFace (inl face₁Dart₁)` iff `β a₀ ~τ face₁Dart₁`
(`sideFace_inl_eq_iff_tracePhi`), which holds by brick 2. -/

/-- **The fresh dart `inr 0` joins the `face₁` side face**: `S.dartFace (inr 0) = S.dartFace
(inl face₁Dart₁)`. -/
theorem side₁_chord0_face_eq_face₁_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inr 0)
      = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data)) := by
  -- `inr 0 ↦ inl (β a₀)` (wrapper, in `sideMap₁` form), then `inl (β a₀) ↦ inl face₁Dart₁`.
  rw [sideMap₁_chordDart_face_eq_b0 data hsep (side₁Anchor₀ data hsep)
        (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)]
  -- `S.dartFace (inl (β a₀)) = S.dartFace (inl face₁Dart₁)` iff `β a₀ ~τ face₁Dart₁` (brick 2).
  exact (sideFace_inl_eq_iff_tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
    (side₁Anchors_ne data hsep)
    ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) (face₁Dart₁ data)).2
    (side₁_betaA0_sameCycle_face₁Dart₁ data hsep)

/-! ## Brick 4.  The input bundle `Side₁OuterTraceData`

The outer-boundary construction itself is NOT in scope; this is the INPUT structure threading the
chosen side outer face, its boundary cycle (simple, length `≥ 3`), the two chord/face incidence
facts pinned by the design (`chord1_is_outer`, `face₁_not_outer`), and the inner-rep avoidance
residue `inner_reps` (the reported addition; see file header). -/

/-- **The side-1 outer-trace input bundle.** -/
structure Side₁OuterTraceData (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    Type u where
  /-- The chosen side outer face. -/
  outerFace :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).Face
  /-- Its boundary cycle. -/
  outerCycle :
    BoundaryCycle
      (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep))
      outerFace
  /-- The outer boundary cycle is vertex-simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- The outer boundary cycle has length `≥ 3`. -/
  outer_len : 3 ≤ outerCycle.length
  /-- The fresh chord dart `inr 1` closes the outer boundary. -/
  chord1_is_outer :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) = outerFace
  /-- The touched `face₁` side face is NOT the outer face. -/
  face₁_not_outer :
    (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data)) ≠ outerFace
  /-- **(Reported addition.)** Every non-outer side face has a kept-`inl` rep whose `M`-face
  avoids the `M`-outer face and the chord face `face₁` — the side-outer = `M`-outer-arc orbit
  residue. -/
  inner_reps :
    InnerRepsAvoidBoundary data hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
      (side₁Anchors_ne data hsep) outerFace

/-! ## Brick 5.  The one-fresh indicator `= 1`

The first indicator is `1`: `face₁Dart₁ ~τ β a₀` (brick 2, by `SameCycle.symm`).  The second is
`0`: `face₁Dart₁ ~τ β a₁` would force `S.dartFace (inl face₁Dart₁) = S.dartFace (inl (β a₁))
= S.dartFace (inr 1) = outerFace` (`sideFace_inl_eq_iff_tracePhi`, `chordDart_face_eq_b1`,
`chord1_is_outer`), contradicting `face₁_not_outer`. -/

/-- **The canonical one-fresh indicator equals `1`.** -/
theorem side₁Anchors_oneFresh_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (out : Side₁OuterTraceData data hsep) :
    ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
          (face₁Dart₁ data)
          ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) then 1 else 0)
      + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
            (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
          (face₁Dart₁ data)
          ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) then 1 else 0)) = 1 := by
  classical
  -- First indicator true.
  have hfirst : (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        (face₁Dart₁ data) ((data.sideAlpha₁ hsep) (side₁Anchor₀ data hsep)) :=
    (side₁_betaA0_sameCycle_face₁Dart₁ data hsep).symm
  -- Second indicator false.
  have hsecond : ¬ (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
        (face₁Dart₁ data) ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)) := by
    intro hsc
    -- `face₁Dart₁ ~τ β a₁` ⇒ side faces of `inl face₁Dart₁` and `inl (β a₁)` agree.
    have hface : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data))
        = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).dartFace
            (Sum.inl ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep))) :=
      (sideFace_inl_eq_iff_tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
        (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
        (side₁Anchors_ne data hsep) _ _).2 hsc
    -- `inl (β a₁)` shares its face with `inr 1` (`chordDart_face_eq_b1`).
    have hb1 : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
          (side₁Anchors_ne data hsep)).dartFace
            (Sum.inl ((data.sideAlpha₁ hsep) (side₁Anchor₁ data hsep)))
        = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) :=
      (chordDart_face_eq_b1 (data.sideAlpha₁ hsep) data.sideSigma₁
        (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
        (side₁Anchors_ne data hsep)).symm
    -- Chain to `outerFace`, contradicting `face₁_not_outer`.
    apply out.face₁_not_outer
    rw [hface, hb1, out.chord1_is_outer]
  rw [if_pos hfirst, if_neg hsecond]

/-! ## Brick 6.  The correct-anchor datum for the touched `face₁` side face

Direct application of `correctAnchorTwoCycle_ofFace₁` with the landed `tracePhi` 2-cycle
(`side₁Anchors_trace12`/`trace21`), `hkf = rfl`, and brick 5. -/

/-- **The `CorrectAnchorTwoCycle` datum for the `face₁` side face**, anchored to the actual
`face₁` darts. -/
noncomputable def side₁_correctAnchor_face₁_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (out : Side₁OuterTraceData data hsep) :
    CorrectAnchorTwoCycle data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)
      ((data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data))) :=
  correctAnchorTwoCycle_ofFace₁ data hsep
    (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)
    _
    (side₁Anchors_trace12 data hsep)
    (side₁Anchors_trace21 data hsep)
    rfl
    (side₁Anchors_oneFresh_canonical data hsep out)

/-! ## Brick 7.  The master per-face classifier `side1_hclass_canonical`

For each non-outer side face `g`, classify it as splice-untouched-with-side-rep OR carrying a
`CorrectAnchorTwoCycle`.  Pick a non-`M`-outer, non-`face₁` rep `k` of `g` from `out.inner_reps`,
then split on `τ.SameCycle k (face₁Dart₁ data)`:

* `face₁` branch: `g = S.dartFace (inl face₁Dart₁)`, transport brick 6.
* no-hit branch: `k` is splice-untouched (`spliceUntouched_of_face_ne_chordOrbits`), with `g`
  distinct from both chord-dart faces (from `hg` + `chord1_is_outer`, and from the no-hit
  hypothesis + brick 3). -/

/-- **The master chord-side `hclass` classifier** for canonical side-1 anchors.

This is a `noncomputable def` (not a `theorem`): the codomain `… ⊕' CorrectAnchorTwoCycle …` is
`PSum` of a `Prop` and a `Type u`, hence lives in `Type u`.  The representative `k` is extracted
from the `Prop`-valued `out.inner_reps` via `Classical.choice` (`Exists.choose`), so it may be
named/used in the data-valued branches without eliminating a `Prop` into a `Type`. -/
noncomputable def side1_hclass_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (out : Side₁OuterTraceData data hsep) :
    ∀ g : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).Face,
      g ≠ out.outerFace →
        (∃ k : {d : D // d ∉ data.keptDel₁},
            (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).dartFace (Sum.inl k) = g ∧
            M.dartFace k.1 ∈ data.side₁ ∧
            M.dartFace k.1 ≠ data.face₁ ∧
            SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁
              (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) k)
          ⊕'
        CorrectAnchorTwoCycle data hsep
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) g :=
  fun g hg => by
    classical
    -- A non-`M`-outer, non-`face₁` representative `k` of `g`, extracted as DATA via `choose`.
    set hrep := out.inner_reps g hg with hrep_def
    set k := hrep.choose with hk_def
    have hkspec := hrep.choose_spec
    obtain ⟨hkf, houter, hfaceM⟩ := hkspec
    by_cases hface₁ :
        (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)).SameCycle
            k (face₁Dart₁ data)
    · -- face₁ branch: `g = S.dartFace (inl face₁Dart₁)`; transport brick 6.
      refine PSum.inr ?_
      have hgeq : g
          = (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).dartFace (Sum.inl (face₁Dart₁ data)) := by
        rw [← hkf]
        exact (sideFace_inl_eq_iff_tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
          (side₁Anchors_ne data hsep) k (face₁Dart₁ data)).2 hface₁
      rw [hgeq]
      exact side₁_correctAnchor_face₁_canonical data hsep out
    · -- no-hit branch: `k` is splice-untouched.
      refine PSum.inl ⟨k, hkf, keptDart_face_mem_side₁ data k houter, hfaceM, ?_⟩
      -- splice-untouched: `S.dartFace (inl k)` differs from both chord-dart faces.
      have h0 : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).dartFace (Sum.inl k)
          ≠ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).dartFace (Sum.inr 0) := by
        rw [side₁_chord0_face_eq_face₁_canonical data hsep]
        -- faces of `inl k`, `inl face₁Dart₁` differ, since `¬ k ~τ face₁Dart₁`.
        intro hcontra
        exact hface₁ ((sideFace_inl_eq_iff_tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁
          (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
          (side₁Anchors_ne data hsep) k (face₁Dart₁ data)).1 hcontra)
      have h1 : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
            (side₁Anchors_ne data hsep)).dartFace (Sum.inl k)
          ≠ (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
              (side₁Anchors_ne data hsep)).dartFace (Sum.inr 1) := by
        rw [out.chord1_is_outer, hkf]
        exact hg
      exact spliceUntouched_of_face_ne_chordOrbits (data.sideAlpha₁ hsep) data.sideSigma₁
        (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
        (side₁Anchors_ne data hsep) h0 h1

/-! ## Brick 8.  The final assembler `contiguousInterval_canonical`

Feed brick 7 into `ChordAnchor.contiguousInterval_of_correctAnchor`, with the outer boundary
cycle data drawn from `Side₁OuterTraceData` and `hsimple` supplied as a parameter (matching every
other `ContiguousInterval` assembler in the repo; the side map's simple-graph structure is an
input, not derived). -/

/-- **The full `ContiguousInterval` for canonical side-1 anchors.** -/
noncomputable def contiguousInterval_canonical
    (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (out : Side₁OuterTraceData data hsep)
    (hsimple : (data.sideMap₁ hsep (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep)
        (side₁Anchors_ne data hsep)).IsSimpleGraph) :
    ChordSideNT.ContiguousInterval data hsep
      (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep) :=
  contiguousInterval_of_correctAnchor data hsep
    (side₁Anchor₀ data hsep) (side₁Anchor₁ data hsep) (side₁Anchors_ne data hsep)
    hsimple out.outerFace out.outerCycle out.outer_simple out.outer_len
    (side1_hclass_canonical data hsep out)

end ProofsInTheBook.ZinanCh35Hclass

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35Hclass.side₁_trace_beta_a0_to_face₁Dart₁
#print axioms ProofsInTheBook.ZinanCh35Hclass.side₁_chord0_face_eq_face₁_canonical
#print axioms ProofsInTheBook.ZinanCh35Hclass.side₁Anchors_oneFresh_canonical
#print axioms ProofsInTheBook.ZinanCh35Hclass.side₁_correctAnchor_face₁_canonical
#print axioms ProofsInTheBook.ZinanCh35Hclass.side1_hclass_canonical
#print axioms ProofsInTheBook.ZinanCh35Hclass.contiguousInterval_canonical
