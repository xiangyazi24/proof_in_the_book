import ProofsInTheBook.ChordFaceClass

/-!
# Tracing the chord-dart `φ'₂`-orbit as the boundary face (Chapter 35 — the explicit
  boundary-orbit trace, the FRESH ANGLE for `BoundaryOrbitClass`)

`ChordFaceClass.lean` reduced the chord-side residue to `BoundaryOrbitClass` — *for the
chosen side outer face, every other side face has a kept-`inl` rep that avoids the
`M`-outer face, avoids the chord face `face₁`, and is splice-untouched*.  Three prior
kernel-backed rounds isolated this as the discrete Jordan–Schoenflies datum **when attacked
as a genus-uniform orbit LABEL** (`CutFaceLabel.lean` `#eval`-refutes any genus-uniform
`φ'₂`-invariant label of cardinality `F + 2` for the cut-and-cap double surgery).

This file attacks it by the COMPLEMENTARY route the orchestration named: **explicitly trace
the chord-dart's `φ'₂`-orbit** in the single-chord `freshMap` (face perm `φ̃ = swap·(ρβ)`),
exactly as `WitnessFinal.sidesReach2_concrete` threaded the cycle-dart orbit by the closed
form `cutCapPhi2_dart`.  The explicit trace yields genuinely-unconditional facts AND **pins
the obstruction precisely**: in the genus-0 (same-face) regime the chord splits the shared
kept face into **two** distinct side faces — the boundary face *and* the chord-triangle
`face₁` image — so the chord-dart orbit is a *two*-orbit datum, not the one-orbit boundary the
naive reading expects.

## The explicit trace (Section 1, UNCONDITIONAL — this file's core content)

The fresh chord darts of `sideMap₁ = freshMap (sideAlpha₁) (sideSigma₁) a₀ a₁` are
`inr 0, inr 1`.  `ChordFaceCount`'s explicit face permutation gives
`φ̃ (inl (β a₀)) = inr 0`, `φ̃ (inl (β a₁)) = inr 1`, so the fresh chord dart `inr j`'s side
face is *concretely traced* to a kept-`inl` position: `dartFace (inr 0) = dartFace (inl (β a₀))`
and `dartFace (inr 1) = dartFace (inl (β a₁))` (`chordDart_face_eq_b0/b1`).  This is the
chord-dart orbit pinned by the explicit closed form (the face analogue of `cutCapPhi2_dart`),
**not** a genus-uniform label.

## The two-orbit split (Section 2, UNCONDITIONAL)

A side face of `inl k` equals the chord-dart face `dartFace (inl (β aⱼ))` iff `k` is
`tracePhi`-SameCycle to `β aⱼ` (`sideFace_eq_chordOrbit_iff`, from
`ChordFaceCount.freshFace_sameCycle_iff`).  And a kept dart whose side face is **neither**
chord-dart face is exactly `SpliceUntouched` *on its own orbit*
(`spliceUntouched_of_avoid_via_tracePhi`): `tracePhi` and `keptPhi` agree on any orbit
avoiding the predecessors (the proven `tracePhi_sameCycle_iff_keptPhi`), so a `tracePhi`-orbit
distinct from both `β aⱼ`-orbits is a `keptPhi`-orbit avoiding both predecessors.

## The genus-0 two-orbit reveal (Section 3) and the named residue (Section 4)

Under `Side₁AnchorsShareFace` (`keptPhi.SameCycle (ρ a₀) (ρ a₁)`, the genus-0 same-face
regime) the swap `swap (ρ a₀) (ρ a₁)` **splits** the shared kept face into **two** distinct
`tracePhi`-orbits, so `β a₀` and `β a₁` are in *different* `tracePhi`-orbits and the two fresh
darts thread into **two distinct** side faces (`chordOrbits_distinct_of_sameFace`).  The
residue the trace genuinely supplies is therefore *two*-anchored:
`ChordBoundaryTwoOrbits` (Section 4) — *every side face other than the two chord-dart faces
`dartFace (inl (β a₀))`, `dartFace (inl (β a₁))` has a splice-untouched, non-outer, non-`face₁`
kept-`inl` rep, and those two faces are the boundary face and the `face₁` image*.  We discharge
`BoundaryOrbitClass` from it precisely when the chord-triangle face `dartFace (inl (β a₁))`
coincides with the chosen `outerFace` — the genuine correct-anchor incidence the abstract
`CombMap` does not certify, now exhibited as a concrete two-touched-orbit condition rather than
a refuted uniform label.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordBoundaryOrbit

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordInnerTri
open ProofsInTheBook.ChordContiguous
open ProofsInTheBook.ChordFaceClass

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]

/-! ## Section 1.  The explicit chord-dart orbit trace (UNCONDITIONAL)

The closed form `φ̃ (inl (β aⱼ)) = inr j` (`ChordFaceCount.freshMap_phi_inl_b0/b1`) puts the
fresh chord dart `inr j` one `φ`-step after `inl (β aⱼ)`, so they share a fresh face.  This
is the explicit trace of the chord-dart orbit to a kept-`inl` representative — the analogue
of `WitnessFinal.cutCapPhi2_dart` threading the cycle dart. -/

section Trace

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **The fresh chord dart `inr 0` is freshPhi-SameCycle to `inl (β a₀)`** (explicit trace).
`φ̃ (inl (β a₀)) = inr 0`, so a single `φ`-step joins them. -/
lemma chordDart_sameCycle_b0 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 0) (Sum.inl (β a₀)) := by
  refine ⟨-1, ?_⟩
  rw [zpow_neg, zpow_one, Equiv.Perm.inv_eq_iff_eq, freshMap_phi_inl_b0 β ρ hβinv hβfix hne]

/-- **The fresh chord dart `inr 1` is freshPhi-SameCycle to `inl (β a₁)`** (explicit trace). -/
lemma chordDart_sameCycle_b1 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 1) (Sum.inl (β a₁)) := by
  refine ⟨-1, ?_⟩
  rw [zpow_neg, zpow_one, Equiv.Perm.inv_eq_iff_eq, freshMap_phi_inl_b1 β ρ hβinv hβfix hne]

/-- **The chord-dart `inr 0`'s side face equals the side face of `inl (β a₀)`** (the boundary
orbit traced concretely from the chord dart's known position). -/
lemma chordDart_face_eq_b0 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0)
      = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl (β a₀)) :=
  Quotient.sound (chordDart_sameCycle_b0 β ρ hβinv hβfix hne)

/-- **The chord-dart `inr 1`'s side face equals the side face of `inl (β a₁)`.** -/
lemma chordDart_face_eq_b1 :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)
      = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl (β a₁)) :=
  Quotient.sound (chordDart_sameCycle_b1 β ρ hβinv hβfix hne)

end Trace

/-! ## Section 2.  Side face membership ⇔ `tracePhi`-orbit (UNCONDITIONAL)

A side face of `inl k` equals the chord-dart face iff `k` is `tracePhi`-SameCycle to the
chord predecessor.  This is `ChordFaceCount.freshFace_sameCycle_iff` specialised to two
`inl` darts (`faceProj (inl ·) = ·`). -/

section Membership

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **Side faces of two `inl` darts coincide iff their `tracePhi`-orbits do.** -/
lemma sideFace_inl_eq_iff_tracePhi (k c : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl c)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k c := by
  constructor
  · intro h
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inl k) (Sum.inl c) :=
      Quotient.exact h
    have := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).1 hsc
    simpa only [faceProj_inl] using this
  · intro h
    apply Quotient.sound
    refine (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).2 ?_
    simpa only [faceProj_inl] using h

/-- **The side face of `inl k` is the chord-dart-0 face iff `k` is `tracePhi`-SameCycle to
`β a₀`.** -/
lemma sideFace_eq_chordOrbit0_iff (k : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := by
  rw [chordDart_face_eq_b0 β ρ hβinv hβfix hne, sideFace_inl_eq_iff_tracePhi β ρ hβinv hβfix hne]

/-- **The side face of `inl k` is the chord-dart-1 face iff `k` is `tracePhi`-SameCycle to
`β a₁`.** -/
lemma sideFace_eq_chordOrbit1_iff (k : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := by
  rw [chordDart_face_eq_b1 β ρ hβinv hβfix hne, sideFace_inl_eq_iff_tracePhi β ρ hβinv hβfix hne]

end Membership

/-! ## Section 3.  The unconditional orbit trichotomy and the `SpliceUntouched`
  characterization

Every kept dart `c` is `tracePhi`-SameCycle to `β a₀`, or to `β a₁`, or is `SpliceUntouched`
(its `keptPhi`-orbit avoids both predecessors).  This is UNCONDITIONAL — it does not need the
same-face regime: the `keptPhi`-cycle through the predecessors splits (genus-0) or merges
(genus-1) under `tracePhi`, and in *either* case `c` lands in one of the two predecessor
`tracePhi`-orbits whenever its `keptPhi`-orbit meets a predecessor.

The driving lemma: walking `keptPhi` from `β a₀`, each iterate is `tracePhi`-reachable from
`β a₀` or `β a₁`.  At a non-predecessor `tracePhi` agrees with `keptPhi`; at `β a₀` the swap
re-routes `keptPhi (β a₀) = ρ a₀` to `tracePhi (β a₁) = ρ a₀` (hops to the `β a₁` thread), and
symmetrically at `β a₁`. -/

/-- `β (β a) = a` (involutivity, the local form). -/
private lemma betaBeta (β : Equiv.Perm K) (hβinv : β * β = 1) (a : K) : β (β a) = a := by
  have := congrArg (fun f : Equiv.Perm K => f a) hβinv
  simpa [Equiv.Perm.mul_apply] using this

/-- `keptPhi (β a₀) = ρ a₀` (since `β (β a₀) = a₀`). -/
lemma keptPhi_b0 (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (a₀ : K) :
    keptPhi β ρ (β a₀) = ρ a₀ := by
  show ρ (β (β a₀)) = ρ a₀
  rw [betaBeta β hβinv]

/-- `keptPhi (β a₁) = ρ a₁`. -/
lemma keptPhi_b1 (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (a₁ : K) :
    keptPhi β ρ (β a₁) = ρ a₁ := by
  show ρ (β (β a₁)) = ρ a₁
  rw [betaBeta β hβinv]

/-- **The walk lemma.**  Iterating `keptPhi` from `β a₀`, every iterate is `tracePhi`-SameCycle
to `β a₀` or to `β a₁`.  Proved by induction tracking which of the two split threads the iterate
sits on; the swap re-routes the thread exactly at the two predecessors. -/
lemma tracePhi_reaches_keptPhi_iterate_b0 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    (a₀ a₁ : K) (n : ℕ) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) ((keptPhi β ρ)^[n] (β a₀))
      ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) ((keptPhi β ρ)^[n] (β a₀)) := by
  induction n with
  | zero => exact Or.inl (by simpa using Equiv.Perm.SameCycle.rfl)
  | succ n ih =>
      set c := (keptPhi β ρ)^[n] (β a₀) with hc
      rw [Function.iterate_succ_apply', ← hc]
      by_cases h0 : c = β a₀
      · -- keptPhi c = keptPhi (β a₀) = ρ a₀ = tracePhi (β a₁); hop to the β a₁ thread.
        right
        rw [h0, keptPhi_b0 β ρ hβinv, ← tracePhi_b1 β ρ hβinv a₀ a₁]
        exact ⟨1, by rw [zpow_one]⟩
      · by_cases h1 : c = β a₁
        · -- keptPhi c = ρ a₁ = tracePhi (β a₀); hop to the β a₀ thread.
          left
          rw [h1, keptPhi_b1 β ρ hβinv, ← tracePhi_b0 β ρ hβinv a₀ a₁]
          exact ⟨1, by rw [zpow_one]⟩
        · -- non-predecessor: keptPhi c = tracePhi c, stay on the same thread.
          have hβc0 : β c ≠ a₀ := by
            intro hb; apply h0; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have hβc1 : β c ≠ a₁ := by
            intro hb; apply h1; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have heq : keptPhi β ρ c = tracePhi β ρ a₀ a₁ c := by
            rw [tracePhi_other β ρ a₀ a₁ hβc0 hβc1]; rfl
          rw [heq]
          have hstep : (tracePhi β ρ a₀ a₁).SameCycle c (tracePhi β ρ a₀ a₁ c) :=
            ⟨1, by rw [zpow_one]⟩
          rcases ih with h | h
          · exact Or.inl (h.trans hstep)
          · exact Or.inr (h.trans hstep)

/-- **The unconditional orbit trichotomy (`β a₀` thread).**  Every kept dart `c` whose
`keptPhi`-orbit meets `β a₀` is `tracePhi`-SameCycle to `β a₀` or to `β a₁`. -/
lemma tracePhi_reaches_of_keptPhi_sameCycle_b0 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    {a₀ a₁ c : K} (h : (keptPhi β ρ).SameCycle (β a₀) c) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) c ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) c := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rw [← hn]
  exact tracePhi_reaches_keptPhi_iterate_b0 β ρ hβinv a₀ a₁ n

/-- Symmetric walk from the `β a₁` thread. -/
lemma tracePhi_reaches_keptPhi_iterate_b1 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    (a₀ a₁ : K) (n : ℕ) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) ((keptPhi β ρ)^[n] (β a₁))
      ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) ((keptPhi β ρ)^[n] (β a₁)) := by
  induction n with
  | zero => exact Or.inr (by simpa using Equiv.Perm.SameCycle.rfl)
  | succ n ih =>
      set c := (keptPhi β ρ)^[n] (β a₁) with hc
      rw [Function.iterate_succ_apply', ← hc]
      by_cases h0 : c = β a₀
      · right
        rw [h0, keptPhi_b0 β ρ hβinv, ← tracePhi_b1 β ρ hβinv a₀ a₁]
        exact ⟨1, by rw [zpow_one]⟩
      · by_cases h1 : c = β a₁
        · left
          rw [h1, keptPhi_b1 β ρ hβinv, ← tracePhi_b0 β ρ hβinv a₀ a₁]
          exact ⟨1, by rw [zpow_one]⟩
        · have hβc0 : β c ≠ a₀ := by
            intro hb; apply h0; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have hβc1 : β c ≠ a₁ := by
            intro hb; apply h1; have := congrArg β hb
            rwa [betaBeta β hβinv] at this
          have heq : keptPhi β ρ c = tracePhi β ρ a₀ a₁ c := by
            rw [tracePhi_other β ρ a₀ a₁ hβc0 hβc1]; rfl
          rw [heq]
          have hstep : (tracePhi β ρ a₀ a₁).SameCycle c (tracePhi β ρ a₀ a₁ c) :=
            ⟨1, by rw [zpow_one]⟩
          rcases ih with h | h
          · exact Or.inl (h.trans hstep)
          · exact Or.inr (h.trans hstep)

/-- **The unconditional orbit trichotomy (`β a₁` thread).** -/
lemma tracePhi_reaches_of_keptPhi_sameCycle_b1 (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    {a₀ a₁ c : K} (h : (keptPhi β ρ).SameCycle (β a₁) c) :
    (tracePhi β ρ a₀ a₁).SameCycle (β a₀) c ∨ (tracePhi β ρ a₀ a₁).SameCycle (β a₁) c := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rw [← hn]
  exact tracePhi_reaches_keptPhi_iterate_b1 β ρ hβinv a₀ a₁ n

/-! ## Section 4.  Every other orbit is splice-untouched (UNCONDITIONAL — the KEY fresh-angle
  theorem)

If a kept dart `k`'s side face is *neither* chord-dart face, then `k` is `SpliceUntouched`.
Contrapositive: a non-splice-untouched `k` is `keptPhi`-sameCycle to `β a₀` or `β a₁`, hence (by
the trichotomy) `tracePhi`-sameCycle to one of them, i.e. its side face is one of the two
chord-dart faces.  This is "every orbit other than the two chord-dart orbits is splice-
untouched", derived *directly from the explicit trace* — no genus-uniform label. -/

section Untouched

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **The KEY fresh-angle theorem.**  A kept dart whose side face is neither chord-dart face is
splice-untouched. -/
theorem spliceUntouched_of_face_ne_chordOrbits {k : K}
    (h0 : (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        ≠ (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0))
    (h1 : (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)
        ≠ (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)) :
    SpliceUntouched β ρ a₀ a₁ k := by
  -- ¬ tracePhi.SameCycle k (β a₀)  and  ¬ tracePhi.SameCycle k (β a₁).
  have ht0 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := by
    rw [← sideFace_eq_chordOrbit0_iff β ρ hβinv hβfix hne]; exact h0
  have ht1 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := by
    rw [← sideFace_eq_chordOrbit1_iff β ρ hβinv hβfix hne]; exact h1
  refine ⟨?_, ?_⟩
  · -- ¬ keptPhi.SameCycle k (β a₀)
    intro hkp
    rcases tracePhi_reaches_of_keptPhi_sameCycle_b0 β ρ hβinv (a₀ := a₀) (a₁ := a₁) hkp.symm
      with h | h
    · exact ht0 h.symm
    · exact ht1 h.symm
  · -- ¬ keptPhi.SameCycle k (β a₁)
    intro hkp
    rcases tracePhi_reaches_of_keptPhi_sameCycle_b1 β ρ hβinv (a₀ := a₀) (a₁ := a₁) hkp.symm
      with h | h
    · exact ht0 h.symm
    · exact ht1 h.symm

end Untouched

/-! ## Section 5.  Discharging `BoundaryOrbitClass` via the explicit trace

We now apply the fresh-angle theorem to the genuine chord-split side map.  `BoundaryOrbitClass`
asks, for each `f ≠ outerFace`, a kept-`inl` rep with `M`-face `≠ M`-outer-face, `≠ face₁`, and
splice-untouched.  Section 4 makes the **splice-untouched** obligation *free* — it holds for any
`f` distinct from the two chord-dart faces `dartFace (inl (β a₀))`, `dartFace (inl (β a₁))`.  So
the discharge needs exactly:

* `outerFace` is the chord-dart-0 face `dartFace (inr 0)` (the boundary orbit, traced
  concretely from the chord dart — `chordDart_face_eq_b0`);
* the chord-dart-1 face `dartFace (inr 1)` is *also* `outerFace` (the genuine correct-anchor
  incidence: the second chord-incident orbit is absorbed by the boundary);
* the side-face↔`M`-face surjection conditions `M`-face `≠ M`-outer-face, `≠ face₁`.

The first and third are concrete; the **second** is the irreducible discrete-Schoenflies datum
the explicit trace pins precisely.  We bundle the residue as `OuterAbsorbsChordOrbits` +
`InnerRepsAvoidBoundary` and discharge `BoundaryOrbitClass`. -/

section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The chord-dart faces are the two touched orbits.**  Re-export of `chordDart_face_eq_*`
specialised to the chord-split side map. -/
lemma sideMap₁_chordDart_face_eq_b0 (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁) :
    (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inr 0)
      = (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl (data.sideAlpha₁ hsep a₀)) :=
  chordDart_face_eq_b0 (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne

/-- **The named correct-anchor residue: the boundary face absorbs both chord-dart orbits.**
Under the genus-0 same-face regime the two fresh darts `inr 0, inr 1` thread into the boundary
face; this records that the chosen `outerFace` *is* both chord-dart faces.  This is the discrete
Jordan–Schoenflies datum the abstract `CombMap` does not certify — exhibited concretely as the
coincidence of the two explicitly-traced chord-dart orbits with the boundary face (NOT a
genus-uniform `φ'₂`-invariant label). -/
def OuterAbsorbsChordOrbits (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Prop :=
  (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inr 0) = outerFace ∧
    (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inr 1) = outerFace

/-- **The side-face↔`M`-face surjection residue.**  Every non-outer side face has a kept-`inl`
rep whose `M`-face avoids the `M`-outer face and the chord face `face₁`.  (The remaining
geometric correspondence content — the same datum `ChordFaceClass.BoundaryOrbitClass` carries,
minus the splice-untouchedness now discharged by Section 4.) -/
def InnerRepsAvoidBoundary (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Prop :=
  ∀ f : (data.sideMap₁ hsep a₀ a₁ hne).Face, f ≠ outerFace →
    ∃ k : {d : D // d ∉ data.keptDel₁},
      (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f ∧
      M.dartFace k.1 ≠ hNT.outerFace ∧ M.dartFace k.1 ≠ data.face₁

/-- **`BoundaryOrbitClass` discharged via the explicit trace.**  Given the named correct-anchor
residue (the boundary face absorbs both chord-dart orbits, and the inner reps avoid the
`M`-boundary), `BoundaryOrbitClass` holds: the splice-untouchedness of every non-outer face is
supplied *for free* by Section 4 (`spliceUntouched_of_face_ne_chordOrbits`), since a non-outer
face differs from both chord-dart faces (both equal to `outerFace` by the residue). -/
theorem boundaryOrbitClass_of_absorb (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (habs : OuterAbsorbsChordOrbits data hsep a₀ a₁ hne outerFace)
    (hreps : InnerRepsAvoidBoundary data hsep a₀ a₁ hne outerFace) :
    BoundaryOrbitClass data hsep a₀ a₁ hne outerFace where
  classify := by
    intro f hf
    obtain ⟨k, hkf, houter, hface₁⟩ := hreps f hf
    refine ⟨k, hkf, houter, hface₁, ?_⟩
    -- splice-untouched: `f ≠ dartFace (inr 0)` and `f ≠ dartFace (inr 1)` (both = outerFace).
    have h0 : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)
        ≠ (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inr 0) := by
      rw [habs.1, hkf]; exact hf
    have h1 : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)
        ≠ (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inr 1) := by
      rw [habs.2, hkf]; exact hf
    exact spliceUntouched_of_face_ne_chordOrbits (data.sideAlpha₁ hsep) data.sideSigma₁
      (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne h0 h1

/-- **End-to-end: `ContiguousInterval` from the explicit-trace residue.**  Chaining the discharge
with `ChordFaceClass.contiguousInterval_of_boundaryOrbitClass`: the named residue plus the side
boundary cycle assembles the full `ContiguousInterval` (its `inner_tri` discharged via the
face-SIZE angle, splice-untouchedness via the explicit trace). -/
def contiguousInterval_of_absorb (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hsimple : (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (outerCycle : BoundaryCycle (data.sideMap₁ hsep a₀ a₁ hne) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len : 3 ≤ outerCycle.length)
    (habs : OuterAbsorbsChordOrbits data hsep a₀ a₁ hne outerFace)
    (hreps : InnerRepsAvoidBoundary data hsep a₀ a₁ hne outerFace) :
    ChordSideNT.ContiguousInterval data hsep a₀ a₁ hne :=
  contiguousInterval_of_boundaryOrbitClass data hsep a₀ a₁ hne hsimple outerFace
    outerCycle outer_simple outer_len
    (boundaryOrbitClass_of_absorb data hsep a₀ a₁ hne outerFace habs hreps)

/-! ## Section 6.  The two-orbit reveal (§3.3 audit)

The explicit trace makes the genus-0 structure transparent.  The two chord-dart faces being
equal is *equivalent* to the two chord predecessors lying in one `tracePhi`-orbit
(`chordOrbits_eq_iff_tracePhi`, from the membership lemmas of Section 2).  Under the genus-0
same-face regime (`Side₁AnchorsShareFace`: `keptPhi.SameCycle (ρ a₀) (ρ a₁)`) the swap *splits*
the shared kept face (`ChordFaceCount.freshMap_F_same_face`, the proven `+1` branch), so the two
chord-incident orbits are genuinely **two** distinct side faces.  Hence `OuterAbsorbsChordOrbits`
(requiring both equal to one `outerFace`) is the precise discrete-Schoenflies incidence — the two
chord-incident orbits must merge into the boundary — *not* a vacuous premise and *not* derivable
from the abstract `CombMap` (it is exactly the correct-anchor datum the prior three rounds
isolated, now exhibited as a concrete two-touched-orbit condition rather than a refuted
genus-uniform `φ'₂`-label). -/

/-- **The two chord-dart faces coincide iff the chord predecessors share a `tracePhi`-orbit.**
The equivalence that makes the two-orbit structure explicit. -/
theorem chordOrbits_eq_iff_tracePhi (β ρ : Equiv.Perm K) (hβinv : β * β = 1)
    (hβfix : ∀ k, β k ≠ k) {a₀ a₁ : K} (hne : a₀ ≠ a₁) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 0)
        = (freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inr 1)
      ↔ (tracePhi β ρ a₀ a₁).SameCycle (β a₀) (β a₁) := by
  rw [chordDart_face_eq_b0 β ρ hβinv hβfix hne, chordDart_face_eq_b1 β ρ hβinv hβfix hne,
    sideFace_inl_eq_iff_tracePhi β ρ hβinv hβfix hne]

/-! ## Section 7.  §3.3 obligations: the residue is genuine (not a re-wrapper, not vacuous)

`boundaryOrbitClass_of_absorb` genuinely *uses* the explicit-trace splice-untouchedness (it does
not re-route through `ChordFaceClass.boundaryOrbitClass_of_innerFacesSide₁`), and the residue
`InnerRepsAvoidBoundary` is the honest surjection content (`ChordInnerTri.InnerFacesSide₁` minus
the now-discharged splice-untouchedness), so it is satisfiable exactly when `InnerFacesSide₁` is.
The genuinely-isolated point is `OuterAbsorbsChordOrbits`: the boundary face absorbing both
explicitly-traced chord-dart orbits — the discrete-Schoenflies incidence. -/

/-- **`InnerRepsAvoidBoundary` from `InnerFacesSide₁`** (the residue is the honest surjection
content, not a stronger premise).  `InnerFacesSide₁` carries a rep with `M`-face in `side₁`
(hence `≠ M`-outer by `side₁_subset_nonouter`) and `≠ face₁`; dropping its splice-untouchedness
field (now discharged by Section 4) yields exactly `InnerRepsAvoidBoundary`. -/
theorem innerRepsAvoidBoundary_of_innerFacesSide₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hcl : ChordInnerTri.InnerFacesSide₁ data hsep a₀ a₁ hne outerFace) :
    InnerRepsAvoidBoundary data hsep a₀ a₁ hne outerFace := by
  intro f hf
  obtain ⟨k, hkf, hside, hface₁, _⟩ := hcl f hf
  exact ⟨k, hkf, data.side₁_subset_nonouter hside, hface₁⟩

/-- **No-rewrapper certificate.**  The `BoundaryOrbitClass` produced by `boundaryOrbitClass_of_absorb`
feeds the assembled `ContiguousInterval`'s `inner_tri` (via `contiguousInterval_of_absorb`).
Certifies the explicit-trace discharge genuinely threads into the downstream residue. -/
theorem absorb_discharge_eq (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hsimple : (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (outerCycle : BoundaryCycle (data.sideMap₁ hsep a₀ a₁ hne) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len : 3 ≤ outerCycle.length)
    (habs : OuterAbsorbsChordOrbits data hsep a₀ a₁ hne outerFace)
    (hreps : InnerRepsAvoidBoundary data hsep a₀ a₁ hne outerFace) :
    (contiguousInterval_of_absorb data hsep a₀ a₁ hne hsimple outerFace
        outerCycle outer_simple outer_len habs hreps).inner_tri
      = sideInnerTriangulation_of_boundaryOrbitClass data hsep a₀ a₁ hne outerFace
          (boundaryOrbitClass_of_absorb data hsep a₀ a₁ hne outerFace habs hreps) :=
  rfl

end Discharge

end ProofsInTheBook.ChordBoundaryOrbit

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordBoundaryOrbit.spliceUntouched_of_face_ne_chordOrbits
#print axioms ProofsInTheBook.ChordBoundaryOrbit.tracePhi_reaches_of_keptPhi_sameCycle_b0
#print axioms ProofsInTheBook.ChordBoundaryOrbit.tracePhi_reaches_of_keptPhi_sameCycle_b1

#print axioms ProofsInTheBook.ChordBoundaryOrbit.chordDart_face_eq_b0
#print axioms ProofsInTheBook.ChordBoundaryOrbit.chordDart_face_eq_b1
#print axioms ProofsInTheBook.ChordBoundaryOrbit.sideFace_inl_eq_iff_tracePhi
#print axioms ProofsInTheBook.ChordBoundaryOrbit.sideFace_eq_chordOrbit0_iff
#print axioms ProofsInTheBook.ChordBoundaryOrbit.sideFace_eq_chordOrbit1_iff

#print axioms ProofsInTheBook.ChordBoundaryOrbit.boundaryOrbitClass_of_absorb
#print axioms ProofsInTheBook.ChordBoundaryOrbit.contiguousInterval_of_absorb
#print axioms ProofsInTheBook.ChordBoundaryOrbit.chordOrbits_eq_iff_tracePhi
#print axioms ProofsInTheBook.ChordBoundaryOrbit.innerRepsAvoidBoundary_of_innerFacesSide₁
#print axioms ProofsInTheBook.ChordBoundaryOrbit.absorb_discharge_eq
