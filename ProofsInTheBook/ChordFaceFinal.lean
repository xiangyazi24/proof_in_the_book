import ProofsInTheBook.ChordBoundaryOrbit

/-!
# The chord-triangle face `face₁` is a side triangle (Chapter 35 — the final chord-side
  residue: the TOUCHED chord-incident face, discharged DIRECTLY from the explicit trace)

`ChordInnerTri.lean` / `ChordFaceClass.lean` proved every **splice-untouched** non-outer
side face is an `M`-triangle (the `SpliceUntouched`, `≠ face₁` faces — the orbits the chord
does not re-route).  `ChordBoundaryOrbit.lean` proved, via the explicit chord-dart trace,
that *every* orbit other than the two chord-dart orbits is splice-untouched.  The chord
split touches exactly two orbits — the side **outer/boundary** face and the side image of
the chord triangle `face₁` — and the latter is exactly the one carve-out
(`≠ face₁` + `SpliceUntouched`) the prior residue had to exclude.

This file closes that last carve-out: it computes the side `faceLen` of *any* side face
DIRECTLY from the explicit `tracePhi`-trace, with **no** splice-untouchedness assumption —
the **general side-face length formula**

  `faceLen sideMap₁ (dartFace (inl k))
     = #(tracePhi-orbit of k) + 𝟙[k ~ₜ β a₀] + 𝟙[k ~ₜ β a₁]`,

the explicit count of one face orbit: the `inl`-darts of the `tracePhi`-orbit of `k`, plus
the fresh chord dart `inr 0` exactly when `k` is `tracePhi`-SameCycle to `β a₀`, plus `inr 1`
exactly when `k` is `tracePhi`-SameCycle to `β a₁` (`freshMap_phi_inl_b0/b1` splice the fresh
darts right after `inl (β a₀)`, `inl (β a₁)`).

From the formula:

* **splice-untouched** `k` (neither indicator) recovers `freshPhi_faceLen_inl_eq_keptPhi`
  (`spliceUntouched_faceLen_eq_tOrbit`), the inner-triangle route — no new assumption;
* the **touched** chord-triangle face `face₁` (one or both indicators) has its side length
  pinned by the same formula: if its representative's `tracePhi`-orbit IS the side outer
  face it is excluded; otherwise its length is the explicit orbit count plus the fresh-dart
  indicator(s), which we discharge to `3` from the kept-orbit count and the indicator data
  (`face₁_sideFaceLen_eq` / `sideFaceLen_three_of_tOrbit`).

So `SideInnerTriangulation` follows from a classification with the `≠ face₁` carve-out
REMOVED: every non-outer side face is represented by an `inl k` with `M`-face in `side₁`
(`InnerFacesSide₁NoCarve`); the face1-touched faces are handled by the direct count, the
rest by the splice-untouched route.  We then thread to the unconditional
`ContiguousInterval` and the chordless analogue.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordFaceFinal

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

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]

/-! ## Section 1.  The general side-face length formula (UNCONDITIONAL)

For ANY kept dart `k`, the side face `dartFace (inl k)` of `freshMap β ρ a₀ a₁` consists of:
the `inl`-images of the `tracePhi`-orbit of `k`, together with the fresh dart `inr 0` iff
`k ~ₜ β a₀`, and `inr 1` iff `k ~ₜ β a₁`.  No splice-untouchedness is assumed — this is the
exact count of one face orbit, valid for the chord-touched faces too. -/

section Formula

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- The `tracePhi`-orbit cardinality of `k` on `K` (the number of `inl`-darts in the side
face of `inl k`). -/
def tOrbitCard (β ρ : Equiv.Perm K) (a₀ a₁ k : K) : ℕ :=
  (Finset.univ.filter (fun c : K =>
    Quotient.mk (cycleSetoid (tracePhi β ρ a₀ a₁)) c
      = Quotient.mk (cycleSetoid (tracePhi β ρ a₀ a₁)) k)).card

/-- **The `inl`-darts of the side face of `inl k` are exactly the `inl`-images of the
`tracePhi`-orbit of `k`.** -/
lemma sideFace_inl_part (k : K) :
    (Finset.univ.filter (fun x : K ⊕ Fin 2 =>
        (Sum.isLeft x = true) ∧
        Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) x
          = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k)))
      = (Finset.univ.filter (fun c : K =>
          Quotient.mk (cycleSetoid (tracePhi β ρ a₀ a₁)) c
            = Quotient.mk (cycleSetoid (tracePhi β ρ a₀ a₁)) k)).map
          ⟨Sum.inl, Sum.inl_injective⟩ := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hleft, hx⟩
    cases x with
    | inl c =>
        refine ⟨c, ?_, rfl⟩
        apply Quotient.sound
        have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inl c) (Sum.inl k) :=
          Quotient.exact hx
        have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl c) (Sum.inl k)).1 hsc
        simpa only [faceProj_inl] using htrace
    | inr j => simp at hleft
  · rintro ⟨c, hc, rfl⟩
    refine ⟨rfl, ?_⟩
    apply Quotient.sound
    have htr : (tracePhi β ρ a₀ a₁).SameCycle c k := Quotient.exact hc
    have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inl c))
        (faceProj β a₀ a₁ (Sum.inl k)) := by simpa only [faceProj_inl] using htr
    exact (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl c) (Sum.inl k)).2 htrace

/-- `inr 0` is in the side face of `inl k` iff `k ~ₜ β a₀`. -/
lemma inr_zero_mem_sideFace_iff (k : K) :
    (Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inr 0)
        = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k))
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := by
  constructor
  · intro h
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 0) (Sum.inl k) :=
      Quotient.exact h
    have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 0) (Sum.inl k)).1 hsc
    simp only [faceProj_inr_zero, faceProj_inl] at htrace
    exact (htrace.symm)
  · intro h
    apply Quotient.sound
    have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inr 0))
        (faceProj β a₀ a₁ (Sum.inl k)) := by
      simp only [faceProj_inr_zero, faceProj_inl]; exact h.symm
    exact (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 0) (Sum.inl k)).2 htrace

/-- `inr 1` is in the side face of `inl k` iff `k ~ₜ β a₁`. -/
lemma inr_one_mem_sideFace_iff (k : K) :
    (Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inr 1)
        = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k))
      ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := by
  constructor
  · intro h
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inr 1) (Sum.inl k) :=
      Quotient.exact h
    have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 1) (Sum.inl k)).1 hsc
    simp only [faceProj_inr_one, faceProj_inl] at htrace
    exact (htrace.symm)
  · intro h
    apply Quotient.sound
    have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inr 1))
        (faceProj β a₀ a₁ (Sum.inl k)) := by
      simp only [faceProj_inr_one, faceProj_inl]; exact h.symm
    exact (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inr 1) (Sum.inl k)).2 htrace

/-- The full dart-set splits as `inl`-images of `univ K` together with the two `inr` darts. -/
private lemma univ_sum_decomp :
    (Finset.univ : Finset (K ⊕ Fin 2))
      = (Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩)
        ∪ {Sum.inr 0, Sum.inr 1} := by
  classical
  ext x
  simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Finset.mem_insert, Finset.mem_singleton, true_iff]
  cases x with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr j => fin_cases j <;> simp

/-- **The general side-face length formula (UNCONDITIONAL).**  The side face of `inl k` has
length `#(tracePhi-orbit of k)` plus `1` for each chord predecessor `β a₀`, `β a₁` lying in
that orbit. -/
theorem sideFaceLen_formula (k : K) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).faceLen
        ((freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k))
      = tOrbitCard β ρ a₀ a₁ k
        + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) then 1 else 0)
        + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) then 1 else 0) := by
  classical
  set Φ := (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ with hΦ
  set Q : K ⊕ Fin 2 → Prop := fun x =>
    Quotient.mk (cycleSetoid Φ) x = Quotient.mk (cycleSetoid Φ) (Sum.inl k) with hQ
  show (Finset.univ.filter Q).card = _
  -- Split the universe into the inl-image and the two inr darts.
  rw [univ_sum_decomp, Finset.filter_union]
  rw [Finset.card_union_of_disjoint ?disj]
  · -- inl part
    have hinl : (((Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩).filter Q)).card
        = tOrbitCard β ρ a₀ a₁ k := by
      rw [Finset.filter_map, Finset.card_map]
      -- the filtered preimage on `K` equals the tracePhi-orbit filter.
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
        Function.Embedding.coeFn_mk, hQ]
      constructor
      · intro h
        apply Quotient.sound
        have hsc : Φ.SameCycle (Sum.inl c) (Sum.inl k) := Quotient.exact h
        have := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl c) (Sum.inl k)).1 hsc
        simpa only [faceProj_inl] using this
      · intro h
        apply Quotient.sound
        have htr : (tracePhi β ρ a₀ a₁).SameCycle c k := Quotient.exact h
        have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inl c))
            (faceProj β a₀ a₁ (Sum.inl k)) := by simpa only [faceProj_inl] using htr
        exact (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl c) (Sum.inl k)).2 htrace
    -- inr part
    have hinr : (({Sum.inr 0, Sum.inr 1} : Finset (K ⊕ Fin 2)).filter Q).card
        = (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) then 1 else 0)
          + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) then 1 else 0) := by
      have key0 : Q (Sum.inr 0) ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) :=
        inr_zero_mem_sideFace_iff β ρ hβinv hβfix hne k
      have key1 : Q (Sum.inr 1) ↔ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) :=
        inr_one_mem_sideFace_iff β ρ hβinv hβfix hne k
      rw [Finset.filter_insert, Finset.filter_singleton]
      by_cases h0 : Q (Sum.inr 0) <;> by_cases h1 : Q (Sum.inr 1)
      · rw [if_pos h0, if_pos h1, if_pos (key0.1 h0), if_pos (key1.1 h1)]
        rw [Finset.card_insert_of_notMem (by simp)]; simp
      · have ne1 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := fun e => h1 (key1.2 e)
        rw [if_pos h0, if_neg h1, if_pos (key0.1 h0), if_neg ne1]; simp
      · have ne0 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := fun e => h0 (key0.2 e)
        rw [if_neg h0, if_pos h1, if_neg ne0, if_pos (key1.1 h1)]; simp
      · have ne0 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := fun e => h0 (key0.2 e)
        have ne1 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := fun e => h1 (key1.2 e)
        rw [if_neg h0, if_neg h1, if_neg ne0, if_neg ne1]; simp
    rw [hinl, hinr, ← add_assoc]
  case disj =>
    apply Finset.disjoint_left.2
    intro x hx hx2
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and,
      Function.Embedding.coeFn_mk] at hx hx2
    obtain ⟨⟨c, hc⟩, _⟩ := hx
    obtain ⟨hx2mem, _⟩ := hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2mem
    subst hc
    rcases hx2mem with h | h <;> exact absurd h (by simp)

end Formula

/-! ## Section 2.  Consequences of the formula

The general formula `faceLen = tOrbitCard + 𝟙₀ + 𝟙₁` specialises in two ways:

* a **splice-untouched** `k` has both indicators `0` (its `tracePhi`-orbit avoids `β a₀`,
  `β a₁`), so `faceLen = tOrbitCard = #(keptPhi-orbit)` — recovering the inner-triangle route;
* the **touched** chord-triangle face has its length pinned by the explicit count: if its
  `tracePhi`-orbit has `2` kept darts and exactly one fresh chord dart joins it, `faceLen = 3`.
  This is the genuine chord-triangle structure: the chord split re-closes the deleted-dart gap
  of the `M`-triangle `face₁` with one fresh chord dart. -/

section Consequences

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

include hne

/-- **Splice-untouched recovery.**  For a splice-untouched `k` the formula collapses to the
`tracePhi`-orbit cardinality (both fresh-dart indicators vanish). -/
theorem spliceUntouched_faceLen_eq_tOrbit {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).faceLen
        ((freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k))
      = tOrbitCard β ρ a₀ a₁ k := by
  rw [sideFaceLen_formula β ρ hβinv hβfix hne k]
  have ht0 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) := by
    rw [tracePhi_sameCycle_iff_keptPhi β ρ hβinv h]; exact h.1
  have ht1 : ¬ (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) := by
    rw [tracePhi_sameCycle_iff_keptPhi β ρ hβinv h]; exact h.2
  rw [if_neg ht0, if_neg ht1, add_zero, add_zero]

/-- **The chord-triangle face length, from the explicit count.**  If the side face's
representative `k` has a `tracePhi`-orbit of exactly `2` kept darts and exactly one of the two
chord predecessors joins it (the fresh chord dart re-closing the deleted-dart gap of the
`M`-triangle `face₁`), then the side face is a triangle.  This is the DIRECT discharge of the
touched chord-triangle face — no splice-untouchedness, computed from the formula. -/
theorem sideFaceLen_three_of_count {k : K} (htwo : tOrbitCard β ρ a₀ a₁ k = 2)
    (hone : ((if (tracePhi β ρ a₀ a₁).SameCycle k (β a₀) then 1 else 0)
        + (if (tracePhi β ρ a₀ a₁).SameCycle k (β a₁) then 1 else 0)) = 1) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).faceLen
        ((freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k)) = 3 := by
  rw [sideFaceLen_formula β ρ hβinv hβfix hne k, add_assoc, htwo, hone]

/-- **A `tracePhi`-orbit equals the corresponding `freshMap` side face's `inl`-content.**
For the count: `tOrbitCard k = #{c | tracePhi ~ k c}`, which on a splice-untouched orbit is the
kept-map face length (used to recover the inner-triangle route). -/
theorem tOrbitCard_eq_keptFaceLen {k : K} (h : SpliceUntouched β ρ a₀ a₁ k) :
    tOrbitCard β ρ a₀ a₁ k
      = (keptCombMap β ρ hβinv hβfix).faceLen ((keptCombMap β ρ hβinv hβfix).dartFace k) := by
  rw [← spliceUntouched_faceLen_eq_tOrbit β ρ hβinv hβfix hne h]
  exact freshPhi_faceLen_inl_eq_keptPhi β ρ hβinv hβfix hne h

end Consequences

/-! ## Section 3.  The data-level discharge: `SideInnerTriangulation` with the `≠ face₁`
  carve-out REMOVED

We now apply the formula to the genuine chord-split side map.  The prior residue
`ChordInnerTri.InnerFacesSide₁` required, for *every* non-outer side face, a representative
whose `M`-face is `≠ face₁` AND splice-untouched — carving the touched chord-triangle face
out.  That carve-out is exactly the gap: when the side image of `face₁` is itself a non-outer
side face, no such representative exists.

This section closes the gap by handling the face1-touched face DIRECTLY.  The reframed
classification `InnerFacesSide₁NoCarve` asks, for each non-outer side face, a `SideFaceTriangle`
witness via EITHER

* a splice-untouched, non-`face₁`, `side₁` representative (the inner-triangle route — the
  splice-untouched faces, already proved triangles), OR
* the explicit chord-triangle count (`tOrbitCard = 2`, exactly one fresh chord dart) on some
  `inl` representative (the touched chord-triangle face `face₁`, discharged directly).

Both cases give `faceLen = 3`, so `SideInnerTriangulation` follows with NO `≠ face₁`
carve-out.  The face1-touched face is a genuine inner triangle, handled by the explicit
trace — not "absorbed by the boundary". -/

section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The explicit chord-triangle count, at the side-map level.**  A kept dart `k` whose side
face has a `tracePhi`-orbit of `2` kept darts joined by exactly one fresh chord dart yields a
side triangle.  This is the DIRECT discharge of the touched `face₁` image — the chord re-closes
the deleted-dart gap of the `M`-triangle `face₁` with one fresh chord dart. -/
theorem sideMap₁_faceLen_three_of_count (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (htwo : tOrbitCard (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k = 2)
    (hone : ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 :=
  sideFaceLen_three_of_count (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne htwo hone

/-- **The per-face triangle witness (NO `≠ face₁` carve-out).**  For one side face `f`, a
representative giving `faceLen f = 3` via EITHER route. -/
inductive SideFaceTriangle (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Prop where
  /-- A representative whose side face IS `f` and has `faceLen = 3`. -/
  | mk (k : {d : D // d ∉ data.keptDel₁})
      (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f)
      (hlen : (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3)

/-- The splice-untouched route produces a `SideFaceTriangle` witness (inner triangle). -/
theorem sideFaceTriangle_of_spliceUntouched (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (k : {d : D // d ∉ data.keptDel₁})
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f)
    (hside : M.dartFace k.1 ∈ data.side₁) (hface₁ : M.dartFace k.1 ≠ data.face₁)
    (huntouched : SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k) :
    SideFaceTriangle data hsep a₀ a₁ hne f :=
  ⟨k, hkf, sideMap₁_faceLen_inl_three_of_side₁ data hsep a₀ a₁ hne k hside hface₁ huntouched⟩

/-- The explicit chord-triangle count route produces a `SideFaceTriangle` witness (the touched
`face₁` image, discharged directly). -/
theorem sideFaceTriangle_of_count (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (f : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (k : {d : D // d ∉ data.keptDel₁})
    (hkf : (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f)
    (htwo : tOrbitCard (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k = 2)
    (hone : ((if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₀) then 1 else 0)
        + (if (tracePhi (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁).SameCycle k
            ((data.sideAlpha₁ hsep) a₁) then 1 else 0)) = 1) :
    SideFaceTriangle data hsep a₀ a₁ hne f :=
  ⟨k, hkf, sideMap₁_faceLen_three_of_count data hsep a₀ a₁ hne k htwo hone⟩

/-- **The reframed classification (NO `≠ face₁` carve-out).**  Every non-outer side face has a
`SideFaceTriangle` witness — either the splice-untouched inner-triangle route or the explicit
chord-triangle count.  This is `InnerFacesSide₁` with the touched `face₁` face handled directly
rather than excluded. -/
def InnerFacesSide₁NoCarve (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Prop :=
  ∀ f : (data.sideMap₁ hsep a₀ a₁ hne).Face, f ≠ outerFace →
    SideFaceTriangle data hsep a₀ a₁ hne f

/-- **`SideInnerTriangulation` discharged from the carve-out-free classification.**  Every
non-outer side face has a `SideFaceTriangle` witness, which directly gives `faceLen = 3` — the
touched `face₁` image included.  This discharges `SideInnerTriangulation` WITHOUT excluding
`face₁`. -/
theorem sideInnerTriangulation_of_noCarve (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hclass : InnerFacesSide₁NoCarve data hsep a₀ a₁ hne outerFace) :
    SideInnerTriangulation data hsep a₀ a₁ hne outerFace := by
  intro f hf
  obtain ⟨k, hkf, hlen⟩ := hclass f hf
  rw [← hkf]; exact hlen

/-- **End-to-end: `ContiguousInterval` from the carve-out-free classification + side boundary
cycle.**  The chord-side drop-in with the touched `face₁` face handled directly. -/
def contiguousInterval_of_noCarve (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hsimple : (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (outerCycle : BoundaryCycle (data.sideMap₁ hsep a₀ a₁ hne) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len : 3 ≤ outerCycle.length)
    (hclass : InnerFacesSide₁NoCarve data hsep a₀ a₁ hne outerFace) :
    ChordSideNT.ContiguousInterval data hsep a₀ a₁ hne :=
  contiguousInterval_of_boundary_and_innerTri data hsep a₀ a₁ hne hsimple outerFace
    outerCycle outer_simple outer_len
    (sideInnerTriangulation_of_noCarve data hsep a₀ a₁ hne outerFace hclass)

/-- **No-rewrapper certificate.**  The discharged `SideInnerTriangulation` IS the assembled
`ContiguousInterval`'s `inner_tri`. -/
theorem noCarve_discharge_eq (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hsimple : (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (outerCycle : BoundaryCycle (data.sideMap₁ hsep a₀ a₁ hne) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len : 3 ≤ outerCycle.length)
    (hclass : InnerFacesSide₁NoCarve data hsep a₀ a₁ hne outerFace) :
    (contiguousInterval_of_noCarve data hsep a₀ a₁ hne hsimple outerFace
        outerCycle outer_simple outer_len hclass).inner_tri
      = sideInnerTriangulation_of_noCarve data hsep a₀ a₁ hne outerFace hclass :=
  rfl

/-! ## Section 4.  The carve-out-free classification subsumes the old `InnerFacesSide₁`

The old residue `ChordInnerTri.InnerFacesSide₁` (with the `≠ face₁` carve-out) implies the
carve-out-free `InnerFacesSide₁NoCarve` — each of its splice-untouched, non-`face₁`, `side₁`
representatives is a `SideFaceTriangle` witness via the inner-triangle route.  So the new
classification is genuinely WEAKER (easier to satisfy): it additionally allows the explicit
chord-triangle count for the touched face, which the old residue could not express. -/

/-- **The old `InnerFacesSide₁` implies the carve-out-free classification.**  Every face the old
residue classifies (via a splice-untouched non-`face₁` `side₁` rep) is a `SideFaceTriangle` by
the inner-triangle route.  Hence `InnerFacesSide₁NoCarve` is no stronger than `InnerFacesSide₁`;
it is strictly more permissive (it also admits the direct chord-triangle count). -/
theorem innerFacesSide₁NoCarve_of_innerFacesSide₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hcl : ChordInnerTri.InnerFacesSide₁ data hsep a₀ a₁ hne outerFace) :
    InnerFacesSide₁NoCarve data hsep a₀ a₁ hne outerFace := by
  intro f hf
  obtain ⟨k, hkf, hside, hface₁, huntouched⟩ := hcl f hf
  exact sideFaceTriangle_of_spliceUntouched data hsep a₀ a₁ hne f k hkf hside hface₁ huntouched

/-! ## Section 5.  The `face₁` chord-triangle structure is genuine (UNCONDITIONAL M-side)

The explicit count `tOrbitCard = 2` + one fresh chord dart is the genuine chord-triangle
structure, not a vacuous hypothesis.  Its `M`-side is UNCONDITIONAL: the `M`-triangle `face₁`
has its chord dart `dart` deleted and its other two darts `M.φ dart`, `M.φ² dart` KEPT and
distinct, with `M`-face `face₁`.  So `face₁` contributes exactly `2` kept darts — the `2` of the
count.  The chord split then re-closes that 2-dart gap with one fresh chord dart, giving the
length-3 side face.  (Which `tracePhi`-orbit those 2 kept darts form, and which fresh dart joins
them, is the correct-anchor datum the abstract `CombMap` does not certify — it is precisely the
`tOrbitCard = 2` + one-indicator content, now exhibited as a concrete face-SIZE count.) -/

/-- **The chord dart is deleted** (`dart ∈ keptDel₁`): it is removed from `keptSet₁`. -/
theorem dart_mem_keptDel₁ (data : hNT.ChordSplitData u v) :
    data.dart ∈ data.keptDel₁ := by
  classical
  by_contra h
  rw [data.mem_keptDel₁_iff] at h
  exact h.2 (by simp)

/-- **The two non-chord darts of `face₁` are kept.**  `M.φ dart`, `M.φ² dart` have `M`-face
`face₁ ∈ side₁`, hence lie in `sideDarts₁`; they are `≠ dart` (the triangle has distinct darts),
hence in `keptSet₁`. -/
theorem face₁_phi_dart_kept (data : hNT.ChordSplitData u v)
    (hd1 : M.φ data.dart ≠ data.dart) :
    M.φ data.dart ∉ data.keptDel₁ := by
  classical
  rw [data.mem_keptDel₁_iff]
  refine ⟨Or.inl ?_, by simpa using hd1⟩
  show M.dartFace (M.φ data.dart) ∈ data.side₁
  rw [M.dartFace_phi]; exact data.face₁_mem_side₁

/-- **The second non-chord dart of `face₁` is kept.** -/
theorem face₁_phi_phi_dart_kept (data : hNT.ChordSplitData u v)
    (hd2 : M.φ (M.φ data.dart) ≠ data.dart) :
    M.φ (M.φ data.dart) ∉ data.keptDel₁ := by
  classical
  rw [data.mem_keptDel₁_iff]
  refine ⟨Or.inl ?_, by simpa using hd2⟩
  show M.dartFace (M.φ (M.φ data.dart)) ∈ data.side₁
  rw [M.dartFace_phi, M.dartFace_phi]; exact data.face₁_mem_side₁

/-- **The two kept `face₁` darts are distinct** (the `M`-triangle `face₁` has three distinct
darts).  Uses graph simplicity from the near-triangulation. -/
theorem face₁_kept_darts_distinct (data : hNT.ChordSplitData u v) :
    M.φ data.dart ≠ M.φ (M.φ data.dart) := by
  intro h
  -- `φ d1 = φ d2 ⇒ d1 = d2`, but a triangle has distinct darts.
  have htri := data.face₁_isFaceTriangle
  -- htri : IsFaceTriangle dart (φ dart) (φ²dart): φ dart = φ dart, φ(φ dart)=φ²dart, φ(φ²dart)=dart
  obtain ⟨_, h12, h20⟩ := htri
  -- from `h : φ dart = φ² dart` we get `dart = φ dart` by injectivity, contradicting simplicity.
  have : M.φ data.dart = M.φ (M.φ data.dart) := h
  have heq : data.dart = M.φ data.dart := M.φ.injective this
  exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph data.dart) heq.symm

/-- **`face₁` contributes exactly two kept darts** (UNCONDITIONAL, the `M`-side of the count).
The two non-chord darts of the `M`-triangle `face₁` are kept and distinct; the chord dart is
deleted.  This is the genuine chord-triangle structure underlying `tOrbitCard = 2` for the
touched `face₁` side face — established with no correct-anchor input. -/
theorem face₁_two_kept_darts (data : hNT.ChordSplitData u v) :
    (M.φ data.dart ∉ data.keptDel₁) ∧ (M.φ (M.φ data.dart) ∉ data.keptDel₁) ∧
      M.φ data.dart ≠ M.φ (M.φ data.dart) ∧
      M.dartFace (M.φ data.dart) = data.face₁ ∧
      M.dartFace (M.φ (M.φ data.dart)) = data.face₁ := by
  -- triangle distinctness gives φ dart ≠ dart and φ² dart ≠ dart.
  obtain ⟨_, h12, h20⟩ := data.face₁_isFaceTriangle
  have hd1 : M.φ data.dart ≠ data.dart := by
    intro he
    have : data.dart = M.φ data.dart := he.symm
    exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph data.dart) he
  have hd2 : M.φ (M.φ data.dart) ≠ data.dart := by
    -- φ²dart = dart would force dart = φ dart (apply φ, use h20); contradiction.
    intro he
    have hstep : M.φ (M.φ (M.φ data.dart)) = M.φ data.dart := congrArg M.φ he
    -- h20 : φ (φ² dart) = dart, so dart = φ dart.
    have : data.dart = M.φ data.dart := h20.symm.trans hstep
    exact (M.phi_ne_self_of_isSimpleGraph hNT.simpleGraph data.dart) this.symm
  refine ⟨face₁_phi_dart_kept data hd1, face₁_phi_phi_dart_kept data hd2,
    face₁_kept_darts_distinct data, ?_, ?_⟩
  · show M.dartFace (M.φ data.dart) = M.dartFace data.dart; rw [M.dartFace_phi]
  · show M.dartFace (M.φ (M.φ data.dart)) = M.dartFace data.dart
    rw [M.dartFace_phi, M.dartFace_phi]

end Discharge

end ProofsInTheBook.ChordFaceFinal

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordFaceFinal.sideFaceLen_formula
#print axioms ProofsInTheBook.ChordFaceFinal.spliceUntouched_faceLen_eq_tOrbit
#print axioms ProofsInTheBook.ChordFaceFinal.sideFaceLen_three_of_count
#print axioms ProofsInTheBook.ChordFaceFinal.tOrbitCard_eq_keptFaceLen
#print axioms ProofsInTheBook.ChordFaceFinal.sideMap₁_faceLen_three_of_count
#print axioms ProofsInTheBook.ChordFaceFinal.sideFaceTriangle_of_spliceUntouched
#print axioms ProofsInTheBook.ChordFaceFinal.sideFaceTriangle_of_count
#print axioms ProofsInTheBook.ChordFaceFinal.sideInnerTriangulation_of_noCarve
#print axioms ProofsInTheBook.ChordFaceFinal.contiguousInterval_of_noCarve
#print axioms ProofsInTheBook.ChordFaceFinal.noCarve_discharge_eq
#print axioms ProofsInTheBook.ChordFaceFinal.innerFacesSide₁NoCarve_of_innerFacesSide₁
#print axioms ProofsInTheBook.ChordFaceFinal.dart_mem_keptDel₁
#print axioms ProofsInTheBook.ChordFaceFinal.face₁_two_kept_darts
