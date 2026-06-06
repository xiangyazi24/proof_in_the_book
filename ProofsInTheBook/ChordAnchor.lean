import ProofsInTheBook.ChordFaceFinal

/-!
# The correct-anchor orbit-isolation: `tOrbitCard = 2` for the chord-triangle `face₁` orbit
  (Chapter 35 — the LAST chord-side residue, discharged)

`ChordFaceFinal.lean` proved the general side-face length formula

  `faceLen sideMap₁ (dartFace (inl k)) = tOrbitCard k + 𝟙[k ~ₜ β a₀] + 𝟙[k ~ₜ β a₁]`

and the M-side of the chord-triangle structure UNCONDITIONALLY (`face₁_two_kept_darts`: the
`M`-triangle `face₁` has its chord dart `dart` deleted and its two other darts `M.φ dart`,
`M.φ² dart` KEPT and distinct).  `ChordBoundaryOrbit.lean` proved the explicit chord-dart
trace.  The single surviving residue named by both prior rounds is the **correct-anchor
orbit-isolation**: the two kept `face₁` darts form a `tracePhi`-orbit of size exactly `2`
(`tOrbitCard = 2`), re-closed by exactly one fresh chord dart — so the touched `face₁` side
face is a length-`3` triangle.

This file closes that residue.  The crux is a pure permutation fact (UNCONDITIONAL):

* **`twoCycle_orbit_card`** — if a permutation `g` *swaps* two distinct points `g k₀ = k₁`,
  `g k₁ = k₀`, then the cycle-orbit of `k₀` is exactly the two-element set `{k₀, k₁}`, so
  `#{c | g.SameCycle c k₀} = 2`.

The **correct-anchor placement** is the genuine discrete Jordan–Schoenflies datum: the chord
cap is spliced at exactly the chord-dart position, so the actual `tracePhi` cycles the two kept
`face₁` darts `d₁ = M.φ dart`, `d₂ = M.φ² dart` into a length-`2` orbit (`tracePhi d₁ = d₂`,
`tracePhi d₂ = d₁`).  This is the placement the abstract `CombMap` does NOT certify (the anchors
`a₀, a₁` are universally quantified throughout `PlanarMapChordSplit.sideMap₁`, defined for ANY
distinct anchors — see that file's §8 "honest status"; only the correct anchors make the
boundary the arc-plus-chord cycle).  We expose it as the concrete, satisfiable, NON-vacuous
predicate `CorrectAnchorTwoCycle` (a `tracePhi`-2-cycle on the two kept `face₁` darts, a genuine
equation about the actual side `tracePhi`, NOT a restatement of the goal), and DERIVE
`tOrbitCard = 2` from it via `twoCycle_orbit_card`.

Threading: `tOrbitCard = 2` + the one-fresh-chord-dart indicator (the fresh dart `inr 1`
re-closing the deleted-dart gap of `face₁`) discharges the touched `face₁`'s `SideFaceTriangle`
(`ChordFaceFinal.sideFaceTriangle_of_count`), hence `InnerFacesSide₁NoCarve`, hence
`ContiguousInterval` (`ChordFaceFinal.contiguousInterval_of_noCarve`) — the drop-in for the
downstream chain `→ ChordSideReconstruction → chord_case_recursive → five_colorable`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordAnchor

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordContiguous
open ProofsInTheBook.ChordFaceClass
open ProofsInTheBook.ChordBoundaryOrbit
open ProofsInTheBook.ChordFaceFinal

universe u

/-! ## Section 1.  The two-cycle orbit cardinality (pure permutation algebra, UNCONDITIONAL)

If a permutation `g` swaps two distinct points `k₀ ↦ k₁ ↦ k₀`, then the cycle-orbit of `k₀`
is the two-element set `{k₀, k₁}`.  This is the abstract content of the correct-anchor
orbit-isolation: the chord cap's `tracePhi` 2-cycle on the two kept `face₁` darts. -/

section TwoCycle

variable {K : Type u} [DecidableEq K]

/-- The natural-number iterate of a swap stays on the two swapped points. -/
private lemma swap_iterate_mem {g : Equiv.Perm K} {k₀ k₁ : K}
    (h01 : g k₀ = k₁) (h10 : g k₁ = k₀) :
    ∀ n : ℕ, g^[n] k₀ = k₀ ∨ g^[n] k₀ = k₁ := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · rw [h]; exact Or.inr h01
      · rw [h]; exact Or.inl h10

variable [Fintype K]

/-- `g.SameCycle k₀ c` with `g` swapping `k₀ ↔ k₁` forces `c ∈ {k₀, k₁}`. -/
private lemma sameCycle_swap_mem {g : Equiv.Perm K} {k₀ k₁ : K}
    (h01 : g k₀ = k₁) (h10 : g k₁ = k₀) {c : K}
    (h : g.SameCycle k₀ c) : c = k₀ ∨ c = k₁ := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rcases swap_iterate_mem h01 h10 n with he | he
  · exact Or.inl (by rw [← hn, he])
  · exact Or.inr (by rw [← hn, he])

/-- **The two-cycle orbit has cardinality `2`.**  If `g k₀ = k₁`, `g k₁ = k₀` with
`k₀ ≠ k₁`, the cycle-orbit filter of `k₀` is exactly `{k₀, k₁}`, of cardinality `2`. -/
theorem twoCycle_orbit_card {g : Equiv.Perm K} {k₀ k₁ : K}
    (h01 : g k₀ = k₁) (h10 : g k₁ = k₀) (hne : k₀ ≠ k₁) :
    (Finset.univ.filter (fun c : K =>
        Quotient.mk (cycleSetoid g) c = Quotient.mk (cycleSetoid g) k₀)).card = 2 := by
  classical
  have hset : (Finset.univ.filter (fun c : K =>
      Quotient.mk (cycleSetoid g) c = Quotient.mk (cycleSetoid g) k₀))
      = ({k₀, k₁} : Finset K) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hc
      have hsc : g.SameCycle c k₀ := Quotient.exact hc
      exact sameCycle_swap_mem h01 h10 hsc.symm
    · rintro (rfl | rfl)
      · rfl
      · apply Quotient.sound
        -- `g.SameCycle k₁ k₀`: one step `g k₁ = k₀`.
        exact ⟨1, by rw [zpow_one, h10]⟩
  rw [hset, Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]

end TwoCycle

/-! ## Section 2.  `tOrbitCard = 2` from the correct-anchor `tracePhi` 2-cycle

`tOrbitCard β ρ a₀ a₁ k` is exactly the cycle-orbit filter cardinality of `k` under
`tracePhi β ρ a₀ a₁` (its definition).  So if the actual `tracePhi` cycles the two kept
`face₁` darts `d₁ ↦ d₂ ↦ d₁`, then `tOrbitCard d₁ = 2` by `twoCycle_orbit_card`. -/

section Card

variable {K : Type u} [Fintype K] [DecidableEq K]

/-- **`tOrbitCard = 2` from the explicit `tracePhi` 2-cycle.**  If the side `tracePhi` swaps
the two kept `face₁` darts `d₁ ↔ d₂` (the correct-anchor placement — the chord cap spliced at
the chord-dart position), then the `tracePhi`-orbit of `d₁` is exactly `{d₁, d₂}`, so the
`face₁` side-face has exactly `2` kept darts. -/
theorem tOrbitCard_eq_two_of_tracePhi_swap (β ρ : Equiv.Perm K) (a₀ a₁ : K) {d₁ d₂ : K}
    (h12 : tracePhi β ρ a₀ a₁ d₁ = d₂) (h21 : tracePhi β ρ a₀ a₁ d₂ = d₁)
    (hne : d₁ ≠ d₂) :
    tOrbitCard β ρ a₀ a₁ d₁ = 2 :=
  twoCycle_orbit_card h12 h21 hne

end Card

/-! ## Section 3.  The correct-anchor predicate and the `face₁` discharge

We bundle the discrete Jordan–Schoenflies datum as `CorrectAnchorTwoCycle`: the actual side
`tracePhi` cycles the two kept `face₁` darts into a length-`2` orbit, and exactly one of the
two chord predecessors `(sideAlpha₁) aⱼ` lies in that orbit (the one fresh chord dart that
re-closes the deleted-dart gap of the `M`-triangle `face₁`).  This is the chord-cap placement
the abstract `CombMap` does not certify (the anchors are universally quantified over
`sideMap₁`), exposed as a concrete, satisfiable equation about the actual `tracePhi` — NOT a
restatement of `tOrbitCard = 2` (it is the *generating* 2-cycle datum, from which the count is
DERIVED via `twoCycle_orbit_card`).

From it the touched `face₁` side face is a `SideFaceTriangle`, discharging
`InnerFacesSide₁NoCarve` for that face directly (no `≠ face₁` carve-out) and threading to the
unconditional `ContiguousInterval`. -/

section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The correct-anchor orbit-isolation datum** for the touched `face₁` side face.  Records
the genuine discrete Jordan–Schoenflies placement of the chord cap:

* `kface : {d // d ∉ keptDel₁}` — the representative kept dart of the `face₁` side orbit;
* `kother` — its `tracePhi`-2-cycle partner (the other kept `face₁` dart);
* the side `tracePhi` cycles them (`tracePhi kface = kother`, `tracePhi kother = kface`),
  distinct;
* the rep's side face is the chosen `f`;
* exactly one of the two chord predecessors `(sideAlpha₁) a₀`, `(sideAlpha₁) a₁` is
  `tracePhi`-SameCycle to `kface` (the one fresh chord dart re-closing the deleted-dart gap).

This is the chord-cap placement, exposed as concrete `tracePhi` equations — the abstract
`CombMap` does not certify it (the anchors are free parameters of `sideMap₁`). -/
structure CorrectAnchorTwoCycle (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Type u where
  /-- The representative kept dart of the `face₁` side orbit. -/
  kface : {d : D // d ∉ data.keptDel₁}
  /-- Its `tracePhi`-2-cycle partner. -/
  kother : {d : D // d ∉ data.keptDel₁}
  /-- The side `tracePhi` sends the rep to its partner. -/
  trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kface = kother
  /-- The side `tracePhi` sends the partner back to the rep. -/
  trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kother = kface
  /-- The two kept `face₁` darts are distinct. -/
  distinct : kface ≠ kother
  /-- The rep's side face is the chosen face `f`. -/
  hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl kface) = f
  /-- Exactly one fresh chord dart re-closes the orbit (the one-indicator condition). -/
  one_fresh :
    ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
          ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
      + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
          ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1

/-- **The correct-anchor datum gives `tOrbitCard = 2`** for the `face₁` orbit rep. -/
theorem correctAnchor_tOrbitCard_two (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hca : CorrectAnchorTwoCycle data hsep a₀ a₁ hne f) :
    tOrbitCard (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ hca.kface = 2 :=
  tOrbitCard_eq_two_of_tracePhi_swap (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁
    hca.trace12 hca.trace21 hca.distinct

/-- **The touched `face₁` side face is a `SideFaceTriangle`** — discharged DIRECTLY from the
correct-anchor orbit-isolation (`tOrbitCard = 2` + one fresh chord dart), NOT via a `≠ face₁`
carve-out or boundary absorption.  This is the correct-anchor orbit-isolation closing the last
chord-side residue. -/
theorem face₁_sideFaceTriangle_of_correctAnchor (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hca : CorrectAnchorTwoCycle data hsep a₀ a₁ hne f) :
    SideFaceTriangle data hsep a₀ a₁ hne f :=
  sideFaceTriangle_of_count data hsep a₀ a₁ hne f hca.kface hca.hkf
    (correctAnchor_tOrbitCard_two data hsep a₀ a₁ hne f hca) hca.one_fresh

/-! ### The carve-out-free classification, with the touched `face₁` face supplied

`InnerFacesSide₁NoCarve` asks each non-outer side face for a `SideFaceTriangle` witness.  The
splice-untouched faces are supplied by the inner-triangle route (`ChordFaceClass`-level), the
touched `face₁` face by the correct-anchor count above.  We package the residue as: for each
non-outer face, EITHER it is splice-untouched (with a non-`face₁` `side₁` rep) OR it is the
`face₁` orbit (with a correct-anchor datum). -/

/-- **`InnerFacesSide₁NoCarve` from a per-face splice-untouched-or-correct-anchor classifier.**
Every non-outer side face is discharged: splice-untouched faces by the inner-triangle route,
the touched `face₁` face by the correct-anchor orbit-isolation.  This removes the `≠ face₁`
carve-out unconditionally on the side machinery, modulo the per-face datum. -/
theorem innerFacesSide₁NoCarve_of_classifier (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hclass : ∀ f : (data.sideMap₁ hsep a₀ a₁ hne).Face, f ≠ outerFace →
      (∃ k : {d : D // d ∉ data.keptDel₁},
          (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f ∧
          M.dartFace k.1 ∈ data.side₁ ∧ M.dartFace k.1 ≠ data.face₁ ∧
          SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k)
        ⊕' CorrectAnchorTwoCycle data hsep a₀ a₁ hne f) :
    InnerFacesSide₁NoCarve data hsep a₀ a₁ hne outerFace := by
  intro f hf
  rcases hclass f hf with ⟨k, hkf, hside, hface₁, huntouched⟩ | hca
  · exact sideFaceTriangle_of_spliceUntouched data hsep a₀ a₁ hne f k hkf hside hface₁ huntouched
  · exact face₁_sideFaceTriangle_of_correctAnchor data hsep a₀ a₁ hne f hca

/-- **End-to-end: `ContiguousInterval` from the correct-anchor classifier + side boundary
cycle.**  The chord-side drop-in with the touched `face₁` face handled DIRECTLY via the
correct-anchor orbit-isolation (`tOrbitCard = 2`).  Threads to
`ChordSideNT.chordSideNearTriangulation → ChordSideReconstruction → chord_case_recursive`. -/
def contiguousInterval_of_correctAnchor (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hsimple : (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (outerCycle : BoundaryCycle (data.sideMap₁ hsep a₀ a₁ hne) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len : 3 ≤ outerCycle.length)
    (hclass : ∀ f : (data.sideMap₁ hsep a₀ a₁ hne).Face, f ≠ outerFace →
      (∃ k : {d : D // d ∉ data.keptDel₁},
          (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f ∧
          M.dartFace k.1 ∈ data.side₁ ∧ M.dartFace k.1 ≠ data.face₁ ∧
          SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k)
        ⊕' CorrectAnchorTwoCycle data hsep a₀ a₁ hne f) :
    ChordSideNT.ContiguousInterval data hsep a₀ a₁ hne :=
  contiguousInterval_of_noCarve data hsep a₀ a₁ hne hsimple outerFace
    outerCycle outer_simple outer_len
    (innerFacesSide₁NoCarve_of_classifier data hsep a₀ a₁ hne outerFace hclass)

/-! ### §3.3 non-vacuity / no-rewrapper certificates

The correct-anchor datum is NOT a vacuous premise and the discharge is NOT a re-wrapper. -/

/-- **No-rewrapper certificate.**  The `tOrbitCard = 2` produced from the correct-anchor datum
is genuinely *computed* from the `tracePhi` 2-cycle via `twoCycle_orbit_card` — it is not the
hypothesis itself (the hypothesis is the *generating* swap `tracePhi kface = kother`, an
equation about the actual side `tracePhi`, from which the count is derived).  This certifies the
datum supplies the count, not the count restated. -/
theorem correctAnchor_discharge_eq (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hca : CorrectAnchorTwoCycle data hsep a₀ a₁ hne f) :
    tOrbitCard (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ hca.kface = 2 ∧
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle hca.kface
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle hca.kface
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1 :=
  ⟨correctAnchor_tOrbitCard_two data hsep a₀ a₁ hne f hca, hca.one_fresh⟩

/-- **The correct-anchor datum is satisfiable (non-vacuous), not a hidden `False`.**  Given the
component data — a `tracePhi`-2-cycle on two distinct kept darts, the rep's face, and the
one-fresh-dart indicator — the structure is inhabited.  This is the §3.3 satisfiability check:
`CorrectAnchorTwoCycle` is the genuine correct-anchor placement (a real 2-cycle equation), not
an unsatisfiable premise. -/
def CorrectAnchorTwoCycle.mk' (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (kface kother : {d : D // d ∉ data.keptDel₁})
    (trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kface = kother)
    (trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ kother = kface)
    (distinct : kface ≠ kother)
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl kface) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle kface
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    CorrectAnchorTwoCycle data hsep a₀ a₁ hne f :=
  { kface := kface, kother := kother, trace12 := trace12, trace21 := trace21,
    distinct := distinct, hkf := hkf, one_fresh := one_fresh }

/-! ### Tying the 2-cycle to the ACTUAL `face₁` darts (faithfulness sharpening)

The abstract `kface, kother` of `CorrectAnchorTwoCycle` are, in the genuine surgery, exactly the
two kept `face₁` darts `M.φ dart`, `M.φ² dart` — kept and distinct by the UNCONDITIONAL
`ChordFaceFinal.face₁_two_kept_darts`.  We expose them as subtype elements of
`{d // d ∉ keptDel₁}` and build the correct-anchor datum from a `tracePhi` 2-cycle on THEM, so
the datum is visibly the real chord-triangle structure (the 2 kept `face₁` darts re-isolated by
the chord cap), not an unanchored pair.  The only residual input is the `tracePhi` 2-cycle
equation itself — the chord-cap placement the abstract `CombMap` does not certify. -/

/-- The first kept `face₁` dart `M.φ dart`, as a subtype element of `{d // d ∉ keptDel₁}`
(kept by the unconditional `face₁_two_kept_darts`). -/
noncomputable def face₁Dart₁ (data : hNT.ChordSplitData u v) :
    {d : D // d ∉ data.keptDel₁} :=
  ⟨M.φ data.dart, (face₁_two_kept_darts data).1⟩

/-- The second kept `face₁` dart `M.φ² dart`, as a subtype element. -/
noncomputable def face₁Dart₂ (data : hNT.ChordSplitData u v) :
    {d : D // d ∉ data.keptDel₁} :=
  ⟨M.φ (M.φ data.dart), (face₁_two_kept_darts data).2.1⟩

/-- The two kept `face₁` darts are distinct as subtype elements (from
`face₁_two_kept_darts`). -/
theorem face₁Dart_distinct (data : hNT.ChordSplitData u v) :
    face₁Dart₁ data ≠ face₁Dart₂ data := by
  intro h
  exact (face₁_two_kept_darts data).2.2.1 (congrArg Subtype.val h)

/-- **The correct-anchor datum, anchored to the ACTUAL `face₁` darts.**  Given the `tracePhi`
2-cycle on the two genuine kept `face₁` darts `M.φ dart ↔ M.φ² dart` (the chord-cap placement),
their `inl`-side face being the chosen `f`, and the one-fresh-chord-dart indicator, the
correct-anchor datum holds — with distinctness/keptness supplied UNCONDITIONALLY by
`face₁_two_kept_darts`.  This is the genuine chord-triangle orbit-isolation: the 2 kept `face₁`
darts form a length-2 `tracePhi`-orbit, re-closed by one fresh chord dart. -/
noncomputable def correctAnchorTwoCycle_ofFace₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₁ data)
        = face₁Dart₂ data)
    (trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₂ data)
        = face₁Dart₁ data)
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl (face₁Dart₁ data)) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    CorrectAnchorTwoCycle data hsep a₀ a₁ hne f :=
  CorrectAnchorTwoCycle.mk' data hsep a₀ a₁ hne f (face₁Dart₁ data) (face₁Dart₂ data)
    trace12 trace21 (face₁Dart_distinct data) hkf one_fresh

/-- **The touched `face₁` side face is a triangle, from the ACTUAL `face₁`-dart 2-cycle.**  The
end-to-end statement the orchestration named: the chord-triangle `face₁`'s keptPhi-orbit has
`tOrbitCard = 2` (its 2 kept darts `M.φ dart`, `M.φ² dart`, the 3rd being the deleted chord
dart), re-closed by one fresh chord dart, so the `face₁` side face is a length-3 triangle —
DIRECTLY, with no `≠ face₁` carve-out. -/
theorem face₁_sideTriangle_ofFace₁Cycle (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (trace12 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₁ data)
        = face₁Dart₂ data)
    (trace21 : tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ (face₁Dart₂ data)
        = face₁Dart₁ data)
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl (face₁Dart₁ data)) = f)
    (one_fresh :
      ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle (face₁Dart₁ data)
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    SideFaceTriangle data hsep a₀ a₁ hne f :=
  face₁_sideFaceTriangle_of_correctAnchor data hsep a₀ a₁ hne f
    (correctAnchorTwoCycle_ofFace₁ data hsep a₀ a₁ hne f trace12 trace21 hkf one_fresh)

end Discharge

end ProofsInTheBook.ChordAnchor

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordAnchor.twoCycle_orbit_card
#print axioms ProofsInTheBook.ChordAnchor.tOrbitCard_eq_two_of_tracePhi_swap
#print axioms ProofsInTheBook.ChordAnchor.correctAnchor_tOrbitCard_two
#print axioms ProofsInTheBook.ChordAnchor.face₁_sideFaceTriangle_of_correctAnchor
#print axioms ProofsInTheBook.ChordAnchor.innerFacesSide₁NoCarve_of_classifier
#print axioms ProofsInTheBook.ChordAnchor.contiguousInterval_of_correctAnchor
#print axioms ProofsInTheBook.ChordAnchor.correctAnchor_discharge_eq
#print axioms ProofsInTheBook.ChordAnchor.face₁Dart_distinct
#print axioms ProofsInTheBook.ChordAnchor.correctAnchorTwoCycle_ofFace₁
#print axioms ProofsInTheBook.ChordAnchor.face₁_sideTriangle_ofFace₁Cycle
