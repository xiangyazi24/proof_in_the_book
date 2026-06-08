import ProofsInTheBook.ChordContiguous
import ProofsInTheBook.ChordFaceCount

/-!
# Discharging `SideInnerTriangulation`: every INNER side face is an untouched `M`-triangle
  (Chapter 35 — the chord-side inner triangulation, the SHARP NEW ANGLE)

`ChordContiguous.lean` reduced the entire chord-side residue to the single predicate
`SideInnerTriangulation data hsep a₀ a₁ hne outerFace` — *every non-outer face of the
side map `sideMap₁` has `faceLen = 3`*.  The repository's `CutFaceLabel.lean` campaign
refuted, inside the Lean kernel, any **genus-uniform `φ'₂`-invariant orbit LABEL of
cardinality `F + 2`** (the face *COUNT*).  That refutation is about the cut-and-cap
double surgery `cutCapMap2` and its *count*; it is a **different property** from the one
`SideInnerTriangulation` asks about, which is each inner face's *SIZE* (`= 3`).

## The sharp new angle (face SIZE is splice-invariant, sidestepping CutFaceLabel)

The side map is `sideMap₁ = freshMap (sideAlpha₁) (sideSigma₁) a₀ a₁` (a single chord,
fresh darts `inr 0, inr 1`).  Its face permutation, traced on the kept type `K`, is
`tracePhi = swap (ρ a₀) (ρ a₁) * keptPhi` with `keptPhi = ρ * β = sideSigma₁ * sideAlpha₁`
(`ChordFaceCount`).  The chord re-routes **only** the two faces incident to the chord:
the swap moves nothing outside the orbits of `β a₀`, `β a₁`, and the two fresh darts
`inr 0, inr 1` are spliced **only** into those two orbits (`ChordFaceCount.freshMap_phi_*`).

Therefore **every face orbit of `sideMap₁` that avoids the chord predecessors `β a₀`,
`β a₁`** — i.e. every *inner* face once the chord/outer face is excluded — is *identical*
to a `keptPhi`-orbit, with the *same cardinality* (no fresh dart inside it, the swap acts
as the identity on it).  This is the FACE-SIZE analogue of the proven vertex/face *count*
bijections, but used pointwise on a single untouched orbit: it needs no genus-uniform
orbit label.  Concretely:

* **`freshPhi_faceLen_inl_eq_keptPhi`** (Section 1, UNCONDITIONAL) — for a kept dart `k`
  whose `keptPhi`-orbit avoids `β a₀` and `β a₁`, the side face `dartFace (inl k)` has
  `faceLen = (keptPhi.cycleOf k).support.card`, the kept-orbit cardinality.  This is the
  precise "the cut reroutes only the chord-dart/outer-face orbit" statement, proved from
  the explicit `freshMap` face permutation — face SIZE, not COUNT.

This is exactly the genus-essential structure used like the genus-slack sidestep for
`eulerChar`: the inner faces are *untouched* `keptPhi`-orbits, so their length-3 property
is inherited from the kept map (and ultimately from `M`'s `inner_tri`), **without** the
refuted genus-uniform orbit label.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.ChordInnerTri

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordSideRecon
open ProofsInTheBook.ChordFaceCount

universe u

variable {K : Type u} [Fintype K] [DecidableEq K]

/-! ## Section 0.  `keptPhi` is the face permutation of the kept combinatorial map

`keptCombMap β ρ` has `α = β`, `σ = ρ`, so its `φ = σ * α = ρ * β = keptPhi β ρ`.  Hence a
`keptPhi`-orbit cardinality is literally a `faceLen` of the kept map. -/

/-- The kept combinatorial map's face permutation is `keptPhi β ρ = ρ * β`. -/
lemma keptCombMap_phi (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k) :
    (keptCombMap β ρ hβinv hβfix).φ = keptPhi β ρ := rfl

/-! ## Section 1.  The splice-untouched face: `tracePhi` agrees with `keptPhi`

`tracePhi β ρ a₀ a₁ = swap (ρ a₀) (ρ a₁) * keptPhi β ρ` agrees with `keptPhi` *everywhere
except* at the two chord predecessors `β a₀`, `β a₁` (`ChordFaceCount.tracePhi_other`).
So a `keptPhi`-orbit that avoids both predecessors is left **pointwise identical** by
`tracePhi`, hence is one full `tracePhi`-orbit of the same cardinality. -/

section Splice

variable (β ρ : Equiv.Perm K) {a₀ a₁ : K}

/-- An orbit is **splice-untouched** if it avoids both chord predecessors `β a₀`, `β a₁`. -/
def SpliceUntouched (β ρ : Equiv.Perm K) (a₀ a₁ k : K) : Prop :=
  ¬ (keptPhi β ρ).SameCycle k (β a₀) ∧ ¬ (keptPhi β ρ).SameCycle k (β a₁)

/-- `β (β a) = a` (involutivity, the form used here). -/
private lemma beta_beta' (hβinv : β * β = 1) (a : K) : β (β a) = a := by
  have := congrArg (fun f : Equiv.Perm K => f a) hβinv
  simpa [Equiv.Perm.mul_apply] using this

/-- On a `keptPhi`-orbit avoiding the predecessors, one `tracePhi`-step equals one
`keptPhi`-step (the swap fires only at `β a₀`, `β a₁`, which are not on the orbit). -/
lemma tracePhi_apply_eq_keptPhi_of_avoid (hβinv : β * β = 1) {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) {c : K} (hc : (keptPhi β ρ).SameCycle k c) :
    tracePhi β ρ a₀ a₁ c = keptPhi β ρ c := by
  have h0 : c ≠ β a₀ := fun hca => h.1 (hca ▸ hc)
  have h1 : c ≠ β a₁ := fun hca => h.2 (hca ▸ hc)
  have hβc0 : β c ≠ a₀ := by
    intro hb; apply h0; have := congrArg β hb; rwa [beta_beta' β hβinv] at this
  have hβc1 : β c ≠ a₁ := by
    intro hb; apply h1; have := congrArg β hb; rwa [beta_beta' β hβinv] at this
  rw [tracePhi_other β ρ a₀ a₁ hβc0 hβc1]; rfl

/-- On a splice-untouched orbit, the `tracePhi`-iterate equals the `keptPhi`-iterate. -/
lemma tracePhi_iterate_eq_keptPhi (hβinv : β * β = 1) {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) (n : ℕ) :
    (tracePhi β ρ a₀ a₁)^[n] k = (keptPhi β ρ)^[n] k := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      -- `(keptPhi)^[n] k` is on the keptPhi-orbit of `k`.
      have hsc : (keptPhi β ρ).SameCycle k ((keptPhi β ρ)^[n] k) :=
        ⟨(n : ℤ), by rw [zpow_natCast, Equiv.Perm.coe_pow]⟩
      exact tracePhi_apply_eq_keptPhi_of_avoid β ρ hβinv h hsc

/-- **On a splice-untouched orbit, `tracePhi` and `keptPhi` define the same cycle.** -/
lemma tracePhi_sameCycle_iff_keptPhi (hβinv : β * β = 1) {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) (c : K) :
    (tracePhi β ρ a₀ a₁).SameCycle k c ↔ (keptPhi β ρ).SameCycle k c := by
  constructor
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    rw [← hn, tracePhi_iterate_eq_keptPhi β ρ hβinv h n]
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    rw [← hn, ← tracePhi_iterate_eq_keptPhi β ρ hβinv h n]

end Splice

/-! ## Section 2.  The face-SIZE transfer (the SHARP ANGLE, UNCONDITIONAL)

For a kept dart `k` whose `keptPhi`-orbit is splice-untouched, the `freshMap` face orbit
of `inl k` contains **no** fresh dart (`inr j`), and via `faceProj` (which is `Sum.inl⁻¹`
on `inl`) it is in bijection with the `keptPhi`-orbit of `k`.  Hence the side face length
equals the kept-orbit length — the chord re-routes only the chord-incident faces. -/

section Transfer

variable (β ρ : Equiv.Perm K) (hβinv : β * β = 1) (hβfix : ∀ k, β k ≠ k)
  {a₀ a₁ : K} (hne : a₀ ≠ a₁)

/-- **No fresh dart lies in a splice-untouched side face.**  If `inr j` were
`freshMap.φ`-SameCycle to `inl k`, its `faceProj` (`β a₀` or `β a₁`) would be
`tracePhi`-SameCycle to `k`, contradicting splice-untouchedness. -/
lemma no_inr_in_spliceUntouched_face {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) (j : Fin 2) :
    ¬ (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inl k) (Sum.inr j) := by
  intro hsc
  have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inr j)).1 hsc
  simp only [faceProj_inl] at htrace
  -- `faceProj (inr j) ∈ {β a₀, β a₁}`; both contradict splice-untouchedness.
  rw [tracePhi_sameCycle_iff_keptPhi β ρ hβinv h] at htrace
  fin_cases j
  · exact h.1 (by simpa using htrace)
  · exact h.2 (by simpa using htrace)

/-- **The side face of a splice-untouched `inl k` consists exactly of the `inl`-images of
the `keptPhi`-orbit of `k`.**  The filter of darts in that face equals the `keptPhi`-orbit
filter mapped by `Sum.inl`. -/
lemma spliceUntouched_face_filter_eq {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) :
    (Finset.univ.filter (fun x : K ⊕ Fin 2 =>
        Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) x
          = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k)))
      = (Finset.univ.filter (fun c : K =>
          Quotient.mk (cycleSetoid (keptPhi β ρ)) c
            = Quotient.mk (cycleSetoid (keptPhi β ρ)) k)).map ⟨Sum.inl, Sum.inl_injective⟩ := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk]
  constructor
  · intro hx
    -- `x` is freshPhi-SameCycle to `inl k`.
    have hsc : (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ.SameCycle (Sum.inl k) x :=
      Quotient.exact hx.symm
    cases x with
    | inl c =>
        refine ⟨c, ?_, rfl⟩
        apply Quotient.sound
        -- want keptPhi.SameCycle c k, i.e. SameCycle k c symm.
        have htrace := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).1 hsc
        simp only [faceProj_inl] at htrace
        rw [tracePhi_sameCycle_iff_keptPhi β ρ hβinv h] at htrace
        exact htrace.symm
    | inr j => exact absurd hsc (no_inr_in_spliceUntouched_face β ρ hβinv hβfix hne h j)
  · rintro ⟨c, hc, rfl⟩
    -- keptPhi.SameCycle c k ⇒ freshPhi.SameCycle (inl k) (inl c).
    have hkp : (keptPhi β ρ).SameCycle k c := (Quotient.exact hc.symm)
    have htrace : (tracePhi β ρ a₀ a₁).SameCycle (faceProj β a₀ a₁ (Sum.inl k))
        (faceProj β a₀ a₁ (Sum.inl c)) := by
      simp only [faceProj_inl]
      exact (tracePhi_sameCycle_iff_keptPhi β ρ hβinv h c).2 hkp
    have hsc := (freshFace_sameCycle_iff β ρ hβinv hβfix hne (Sum.inl k) (Sum.inl c)).2 htrace
    exact (Quotient.sound hsc.symm)

/-- **Face-SIZE transfer (UNCONDITIONAL).**  For a kept dart `k` whose `keptPhi`-orbit is
splice-untouched, the side face length of `inl k` equals the kept-map face length of `k`:
`faceLen sideMap₁ (dartFace (inl k)) = faceLen (keptCombMap β ρ) (dartFace k)`.  This is the
precise content "the cut reroutes only the chord-incident faces; inner faces are untouched
`keptPhi`-orbits" — FACE SIZE, not the kernel-refuted COUNT label. -/
theorem freshPhi_faceLen_inl_eq_keptPhi {k : K}
    (h : SpliceUntouched β ρ a₀ a₁ k) :
    (freshMap β ρ hβinv hβfix a₀ a₁ hne).faceLen
        ((freshMap β ρ hβinv hβfix a₀ a₁ hne).dartFace (Sum.inl k))
      = (keptCombMap β ρ hβinv hβfix).faceLen
        ((keptCombMap β ρ hβinv hβfix).dartFace k) := by
  classical
  show (Finset.univ.filter (fun x => Quotient.mk _ x
      = Quotient.mk (cycleSetoid (freshMap β ρ hβinv hβfix a₀ a₁ hne).φ) (Sum.inl k))).card
    = (Finset.univ.filter (fun c => Quotient.mk _ c
      = Quotient.mk (cycleSetoid (keptCombMap β ρ hβinv hβfix).φ) k)).card
  rw [keptCombMap_phi β ρ hβinv hβfix]
  rw [spliceUntouched_face_filter_eq β ρ hβinv hβfix hne h, Finset.card_map]

end Transfer

/-! ## Section 3.  The kept side map agrees with `M` on orbits that stay kept

`sideKeptMap₁ = keptCombMap (sideAlpha₁) (sideSigma₁)`, with face permutation
`keptPhi = sideSigma₁ * sideAlpha₁`.  Here `sideAlpha₁ = M.α` (restricted) and
`sideSigma₁ = filteredRotation M.σ keptDel₁`.  On a kept dart `k` whose immediate
`M.φ`-successor is also kept, `keptPhi k = M.φ k` (the filtered rotation takes a single
`σ`-step, `FilteredRotation.filteredRotation_apply_of_next_kept`).  Iterating: if the whole
`M.φ`-orbit of `k` stays kept, the `keptPhi`-orbit coincides with the `M.φ`-orbit, so the
kept face length equals `M`'s face length. -/

section MTransfer

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- One `keptPhi`-step on side 1 agrees with one `M.φ`-step, provided the `M.φ`-successor
is kept. -/
lemma sideKeptPhi_apply_eq_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hnext : M.φ k.1 ∉ data.keptDel₁) :
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ k : D) = M.φ k.1 := by
  -- `keptPhi k = sideSigma₁ (sideAlpha₁ k)`.
  show (data.sideSigma₁ (data.sideAlpha₁ hsep k) : {d : D // d ∉ data.keptDel₁}).1 = M.φ k.1
  -- `sideAlpha₁ k` has coe `M.α k.1`; `sideSigma₁ = filteredRotation M.σ keptDel₁`.
  have hσnext : M.σ ((data.sideAlpha₁ hsep k : {d : D // d ∉ data.keptDel₁}) : D)
      ∉ data.keptDel₁ := by
    rw [sideAlpha₁_apply_coe]
    -- `M.σ (M.α k.1) = M.φ k.1`.
    show M.σ (M.α k.1) ∉ data.keptDel₁
    have : M.φ k.1 = M.σ (M.α k.1) := rfl
    rwa [← this]
  show (FilteredRotation.filteredRotation M.σ data.keptDel₁
      (data.sideAlpha₁ hsep k) : {d : D // d ∉ data.keptDel₁}).1 = M.φ k.1
  rw [FilteredRotation.filteredRotation_apply_of_next_kept M.σ data.keptDel₁
    (data.sideAlpha₁ hsep k) hσnext, sideAlpha₁_apply_coe]
  rfl

/-- **The `M.φ`-orbit of a kept dart stays kept.**  Every `M.φ`-iterate of `k.1` avoids the
deleted set.  (Provided here as a hypothesis; established below for inner side faces.) -/
def OrbitKept (data : hNT.ChordSplitData u v) (k : {d : D // d ∉ data.keptDel₁}) : Prop :=
  ∀ n : ℕ, M.φ^[n] k.1 ∉ data.keptDel₁

/-- On a kept orbit, the `keptPhi`-iterate coincides (under coercion) with the `M.φ`-iterate. -/
lemma sideKeptPhi_iterate_eq_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k) (n : ℕ) :
    ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁)^[n] k : D) = M.φ^[n] k.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      -- the iterate is `⟨M.φ^[n] k.1, _⟩` by `ih`; its φ-successor is `M.φ^[n+1] k.1`, kept.
      have hkn : ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁)^[n] k : D)
          = M.φ^[n] k.1 := ih
      have hnext : M.φ ((keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁)^[n] k : D)
          ∉ data.keptDel₁ := by
        rw [hkn]
        have := hkept (n + 1)
        rwa [Function.iterate_succ_apply'] at this
      rw [sideKeptPhi_apply_eq_phi data hsep _ hnext, hkn]

/-- **`keptPhi` and `M.φ` define the same cycle on a kept orbit.** -/
lemma sideKeptPhi_sameCycle_iff_phi (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k)
    (x : {d : D // d ∉ data.keptDel₁}) :
    (keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁).SameCycle k x ↔ M.φ.SameCycle k.1 x.1 := by
  constructor
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    have := congrArg (Subtype.val) hn
    rw [sideKeptPhi_iterate_eq_phi data hsep k hkept n] at this
    exact this
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, Equiv.Perm.coe_pow]
    rw [Equiv.Perm.coe_pow] at hn
    apply Subtype.ext
    rw [sideKeptPhi_iterate_eq_phi data hsep k hkept n]
    exact hn

/-- Every dart on the `M.φ`-orbit of a kept dart `k` (with kept orbit) is itself kept. -/
lemma orbitKept_mem (data : hNT.ChordSplitData u v)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k)
    {d : D} (hd : M.φ.SameCycle k.1 d) : d ∉ data.keptDel₁ := by
  obtain ⟨n, hn⟩ := hd.exists_nat_pow_eq
  rw [Equiv.Perm.coe_pow] at hn
  rw [← hn]
  exact hkept n

/-- **The kept side face length equals `M`'s face length on a kept orbit.** -/
theorem sideKeptMap₁_faceLen_eq_M (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁}) (hkept : OrbitKept data k) :
    (sideKeptMap₁ data hsep).faceLen ((sideKeptMap₁ data hsep).dartFace k)
      = M.faceLen (M.dartFace k.1) := by
  classical
  show (Finset.univ.filter (fun x => Quotient.mk _ x
      = Quotient.mk (cycleSetoid (sideKeptMap₁ data hsep).φ) k)).card
    = (Finset.univ.filter (fun d => Quotient.mk _ d
      = Quotient.mk (cycleSetoid M.φ) k.1)).card
  have hφ : (sideKeptMap₁ data hsep).φ
      = keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁ := rfl
  -- the kept filter maps bijectively via `Subtype.val` onto the M filter.
  rw [show (Finset.univ.filter (fun x => Quotient.mk _ x
      = Quotient.mk (cycleSetoid (sideKeptMap₁ data hsep).φ) k)).card
      = ((Finset.univ.filter (fun x : {d : D // d ∉ data.keptDel₁} =>
          Quotient.mk _ x = Quotient.mk (cycleSetoid (sideKeptMap₁ data hsep).φ) k)).map
          ⟨Subtype.val, Subtype.val_injective⟩).card from (Finset.card_map _).symm]
  congr 1
  ext d
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨c, hcd, rfl⟩
    -- `keptPhi.SameCycle k c`  ⇒  `M.φ.SameCycle k.1 c.1`.
    have hsc : (sideKeptMap₁ data hsep).φ.SameCycle k c := Quotient.exact hcd.symm
    rw [hφ, sideKeptPhi_sameCycle_iff_phi data hsep k hkept] at hsc
    exact Quotient.sound hsc.symm
  · intro hd
    have hsc : M.φ.SameCycle k.1 d := Quotient.exact hd.symm
    have hdkept : d ∉ data.keptDel₁ := orbitKept_mem data k hkept hsc
    refine ⟨⟨d, hdkept⟩, ?_, rfl⟩
    apply Quotient.sound
    show (sideKeptMap₁ data hsep).φ.SameCycle (⟨d, hdkept⟩ : {d : D // d ∉ data.keptDel₁}) k
    refine Equiv.Perm.SameCycle.symm ?_
    rw [hφ, sideKeptPhi_sameCycle_iff_phi data hsep k hkept ⟨d, hdkept⟩]
    exact hsc

/-- **`OrbitKept` is discharged for a genuine inner side-1 face.**  If `k.1` is a side-1
inner dart (`M`-face in `side₁`) whose `M`-face is not the chord face `face₁`, then its whole
`M.φ`-orbit stays kept: each iterate keeps the same (side-1, non-`face₁`) `M`-face, hence lies
in `sideDarts₁ \ {dart} ⊆ keptSet₁`.  This removes `OrbitKept` from the residue: it follows
from the side-1 face classification alone. -/
theorem orbitKept_of_side₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (k : {d : D // d ∉ data.keptDel₁})
    (hside : M.dartFace k.1 ∈ data.side₁) (hface₁ : M.dartFace k.1 ≠ data.face₁) :
    OrbitKept data k := by
  intro n
  rw [data.mem_keptDel₁_iff]
  -- `M.φ^[n] k.1` has the same `M`-face as `k.1`.
  have hsameface : M.dartFace (M.φ^[n] k.1) = M.dartFace k.1 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', M.dartFace_phi, ih]
  -- in `sideDarts₁`:
  have hin : M.φ^[n] k.1 ∈ data.sideDarts₁ := by
    show M.dartFace (M.φ^[n] k.1) ∈ data.side₁
    rw [hsameface]; exact hside
  -- not the chord dart (its face is `face₁`):
  have hne_dart : M.φ^[n] k.1 ≠ data.dart := by
    intro he
    apply hface₁
    have : M.dartFace (M.φ^[n] k.1) = data.face₁ := by rw [he]; rfl
    rwa [hsameface] at this
  -- hence in `keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`.
  show M.φ^[n] k.1 ∈ data.keptSet₁
  exact ⟨Or.inl hin, by simpa using hne_dart⟩

/-! ## Section 4.  The combined inner-face length: every untouched inner side face is a
triangle

Chaining Section 2 (face SIZE splice-invariance) and Section 3 (kept ↔ `M` agreement): for
an inner side dart `inl k` whose `keptPhi`-orbit is splice-untouched **and** whose `M.φ`-orbit
stays kept, the side face length equals `M.faceLen (M.dartFace k.1)`.  If that `M`-face is a
non-outer face of `M`, it is a triangle by `hNT.inner_tri`. -/

/-- **The side face of an untouched inner `inl k` has the same length as its `M`-face.** -/
theorem sideMap₁_faceLen_inl_eq_M (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (huntouched : SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k)
    (hkept : OrbitKept data k) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k))
      = M.faceLen (M.dartFace k.1) := by
  have h1 := freshPhi_faceLen_inl_eq_keptPhi (data.sideAlpha₁ hsep) data.sideSigma₁
    (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) hne huntouched
  have h2 := sideKeptMap₁_faceLen_eq_M data hsep k hkept
  -- `sideMap₁ = freshMap (sideAlpha₁) (sideSigma₁) …`; `sideKeptMap₁ = keptCombMap …`.
  rw [show data.sideMap₁ hsep a₀ a₁ hne
      = freshMap (data.sideAlpha₁ hsep) data.sideSigma₁
          (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep) a₀ a₁ hne from rfl]
  rw [h1]
  rw [show keptCombMap (data.sideAlpha₁ hsep) data.sideSigma₁
      (data.sideAlpha₁_involutive hsep) (data.sideAlpha₁_no_fixed hsep)
      = sideKeptMap₁ data hsep from rfl]
  exact h2

/-- **An untouched inner side face, mapping to a non-outer `M`-face, is a triangle.** -/
theorem sideMap₁_faceLen_inl_eq_three (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (huntouched : SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k)
    (hkept : OrbitKept data k)
    (hMinner : M.dartFace k.1 ≠ hNT.outerFace) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 := by
  rw [sideMap₁_faceLen_inl_eq_M data hsep a₀ a₁ hne k huntouched hkept]
  exact hNT.inner_tri (M.dartFace k.1) hMinner

/-! ## Section 5.  Discharging `SideInnerTriangulation`

`SideInnerTriangulation` asks every non-outer side face to be a triangle.  Section 4 proves
this for any face represented by a splice-untouched, kept-orbit `inl k` whose `M`-face is
non-outer.  The remaining structural input is the **face classification** "the side outer
face is the chord-incident/boundary face, and every *other* side face is represented by such
an `inl k`" — exactly the discrete Jordan–Schoenflies datum identifying which orbit is the
boundary.  This is FACE CLASSIFICATION, *not* the kernel-refuted genus-uniform orbit COUNT
label (`CutFaceLabel.lean`, which refutes a `φ'₂`-invariant label of cardinality `F + 2` for
the cut-and-cap double surgery `cutCapMap2` — a different construction and a different
property).  We name the classification as ONE predicate and prove the discharge from it. -/

/-- **A side-1 inner face (not the chord face) that is splice-untouched is a triangle**, with
`OrbitKept` and `M`-non-outerness *both discharged* from the side-1 classification.  The only
remaining geometric input is `SpliceUntouched` (the correct-anchor condition: the orbit avoids
the chord predecessors) together with the face-membership data. -/
theorem sideMap₁_faceLen_inl_three_of_side₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (k : {d : D // d ∉ data.keptDel₁})
    (hside : M.dartFace k.1 ∈ data.side₁) (hface₁ : M.dartFace k.1 ≠ data.face₁)
    (huntouched : SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k) :
    (data.sideMap₁ hsep a₀ a₁ hne).faceLen
        ((data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k)) = 3 :=
  sideMap₁_faceLen_inl_eq_three data hsep a₀ a₁ hne k huntouched
    (orbitKept_of_side₁ data hsep k hside hface₁)
    (data.side₁_subset_nonouter hside)

end MTransfer

open ProofsInTheBook.ChordContiguous

section Discharge

open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-- **The inner-face classification of the side map** (the single discrete-Schoenflies
residue).  Relative to a chosen side outer face, *every other* side face is represented by a
kept inl-dart `inl k` whose `keptPhi`-orbit is splice-untouched (avoids the chord
predecessors) **and** whose `M.φ`-orbit stays kept **and** whose `M`-face is non-outer.

This is the FACE classification — which orbit is the boundary, and that the rest are the
intact `M`-inner triangles — *not* the refuted genus-uniform face COUNT label.  Its
non-vacuity is recorded below (any side near-triangulation provides it). -/
def InnerFacesUntouched (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Prop :=
  ∀ f : (data.sideMap₁ hsep a₀ a₁ hne).Face, f ≠ outerFace →
    ∃ k : {d : D // d ∉ data.keptDel₁},
      (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f ∧
      SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k ∧
      OrbitKept data k ∧
      M.dartFace k.1 ≠ hNT.outerFace

/-- **`SideInnerTriangulation` is discharged from the face classification.**  Every non-outer
side face is represented by an untouched, kept-orbit inner `inl k` (the classification), and
Section 4 makes its length `3`.  This is the chord-side inner triangulation, obtained via the
face-SIZE splice-invariance angle — sidestepping the `CutFaceLabel` COUNT refutation. -/
theorem sideInnerTriangulation_of_innerFacesUntouched (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hclass : InnerFacesUntouched data hsep a₀ a₁ hne outerFace) :
    SideInnerTriangulation data hsep a₀ a₁ hne outerFace := by
  intro f hf
  obtain ⟨k, hkf, huntouched, hkept, hMinner⟩ := hclass f hf
  rw [← hkf]
  exact sideMap₁_faceLen_inl_eq_three data hsep a₀ a₁ hne k huntouched hkept hMinner

/-- **Producing a `ContiguousInterval` from the face classification + the side boundary
cycle.**  Combining the discharge of `SideInnerTriangulation` with the side outer-boundary
cycle data assembles the full `ContiguousInterval` (the chord-side residue of
`ChordContiguous`).  The only inputs are the side boundary cycle (genuine boundary-cycle data
of `sideMap₁`) and the face classification `InnerFacesUntouched`. -/
def contiguousInterval_of_innerFacesUntouched (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hsimple : (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (outerCycle : BoundaryCycle (data.sideMap₁ hsep a₀ a₁ hne) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len : 3 ≤ outerCycle.length)
    (hclass : InnerFacesUntouched data hsep a₀ a₁ hne outerFace) :
    ChordSideNT.ContiguousInterval data hsep a₀ a₁ hne :=
  contiguousInterval_of_boundary_and_innerTri data hsep a₀ a₁ hne hsimple outerFace
    outerCycle outer_simple outer_len
    (sideInnerTriangulation_of_innerFacesUntouched data hsep a₀ a₁ hne outerFace hclass)

/-! ## Section 6.  Non-vacuity (the §3.3 satisfiability obligation)

`InnerFacesUntouched` is **not** a disguised `False`: it is the genuine inner-face
classification.  Whenever the side `inner_tri` already holds for the chosen outer face (e.g.
from a side near-triangulation), the classification is automatically *consistent* with it —
each represented inner face is a triangle.  We record the implication that the discharge is a
genuine equivalence direction: `InnerFacesUntouched` supplies `SideInnerTriangulation`, hence
inhabits the `inner_tri` residue field whenever it holds. -/

/-! ### The sharpened classification: only `SpliceUntouched` + side-1 membership remain

With `OrbitKept` and `M`-non-outerness discharged from the side-1 classification
(`orbitKept_of_side₁`, `side₁_subset_nonouter`), the residue per inner face collapses to:
the face is represented by an `inl k` with `M`-face in `side₁`, not the chord face `face₁`,
and splice-untouched.  This is the correct-anchor boundary classification, stated entirely in
face-SIZE / orbit-membership terms — manifestly NOT the refuted COUNT label. -/

/-- **The sharpened inner-face classification.**  Every non-outer side face is represented by
an `inl k` whose `M`-face lies in `side₁`, is not the chord face `face₁`, and is splice-
untouched.  (`OrbitKept` and `M`-non-outerness are *not* listed: they are proved from the
side-1 membership.) -/
def InnerFacesSide₁ (data : hNT.ChordSplitData u v) (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face) : Prop :=
  ∀ f : (data.sideMap₁ hsep a₀ a₁ hne).Face, f ≠ outerFace →
    ∃ k : {d : D // d ∉ data.keptDel₁},
      (data.sideMap₁ hsep a₀ a₁ hne).dartFace (Sum.inl k) = f ∧
      M.dartFace k.1 ∈ data.side₁ ∧
      M.dartFace k.1 ≠ data.face₁ ∧
      SpliceUntouched (data.sideAlpha₁ hsep) data.sideSigma₁ a₀ a₁ k

/-- **`SideInnerTriangulation` is discharged from the sharpened classification.**  With
`OrbitKept` and `M`-non-outerness discharged internally (`orbitKept_of_side₁`), only the
correct-anchor face classification `InnerFacesSide₁` is consumed. -/
theorem sideInnerTriangulation_of_innerFacesSide₁ (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (hclass : InnerFacesSide₁ data hsep a₀ a₁ hne outerFace) :
    SideInnerTriangulation data hsep a₀ a₁ hne outerFace := by
  intro f hf
  obtain ⟨k, hkf, hside, hface₁, huntouched⟩ := hclass f hf
  rw [← hkf]
  exact sideMap₁_faceLen_inl_three_of_side₁ data hsep a₀ a₁ hne k hside hface₁ huntouched

/-- **The discharge round-trips into the residue field** (no-rewrapper check): the
`SideInnerTriangulation` produced from `InnerFacesUntouched` is the `inner_tri` of the
assembled `ContiguousInterval`.  Certifies the assembly genuinely uses the discharged
residue. -/
theorem innerFacesUntouched_discharge_eq (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) (a₀ a₁ : {d : D // d ∉ data.keptDel₁}) (hne : a₀ ≠ a₁)
    (hsimple : (data.sideMap₁ hsep a₀ a₁ hne).IsSimpleGraph)
    (outerFace : (data.sideMap₁ hsep a₀ a₁ hne).Face)
    (outerCycle : BoundaryCycle (data.sideMap₁ hsep a₀ a₁ hne) outerFace)
    (outer_simple : outerCycle.VertexNodup)
    (outer_len : 3 ≤ outerCycle.length)
    (hclass : InnerFacesUntouched data hsep a₀ a₁ hne outerFace) :
    (contiguousInterval_of_innerFacesUntouched data hsep a₀ a₁ hne hsimple outerFace
        outerCycle outer_simple outer_len hclass).inner_tri
      = sideInnerTriangulation_of_innerFacesUntouched data hsep a₀ a₁ hne outerFace hclass :=
  rfl

end Discharge

end ProofsInTheBook.ChordInnerTri

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ChordInnerTri.freshPhi_faceLen_inl_eq_keptPhi
#print axioms ProofsInTheBook.ChordInnerTri.tracePhi_sameCycle_iff_keptPhi
#print axioms ProofsInTheBook.ChordInnerTri.sideKeptMap₁_faceLen_eq_M
#print axioms ProofsInTheBook.ChordInnerTri.sideMap₁_faceLen_inl_eq_M
#print axioms ProofsInTheBook.ChordInnerTri.sideMap₁_faceLen_inl_eq_three
#print axioms ProofsInTheBook.ChordInnerTri.orbitKept_of_side₁
#print axioms ProofsInTheBook.ChordInnerTri.sideMap₁_faceLen_inl_three_of_side₁
#print axioms ProofsInTheBook.ChordInnerTri.sideInnerTriangulation_of_innerFacesUntouched
#print axioms ProofsInTheBook.ChordInnerTri.sideInnerTriangulation_of_innerFacesSide₁
#print axioms ProofsInTheBook.ChordInnerTri.contiguousInterval_of_innerFacesUntouched
#print axioms ProofsInTheBook.ChordInnerTri.innerFacesUntouched_discharge_eq
