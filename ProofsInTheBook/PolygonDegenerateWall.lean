import ProofsInTheBook.PolygonGenericRay

/-!
# Chapter 36 — degenerate-wall parity transport for TRIANGLES (`PolygonDegenerateWall`)

`PolygonWallGlobal` assembled the per-wall local-zero layer of `PolygonWall` into the
global parity-constancy `rcrossSum_parity_eventually_const`, but **gated behind the
generic-wall residual `GenericWallSeg`**: at a *wall* `t₀` (`dirDen i t₀ = 0`) the
assembly demanded both endpoint side values nonzero, which fails exactly on the
**degenerate wall** (`x` on edge `i`'s line, `ds0Of i t₀ = 0`).  `PolygonGenericRay`
showed this residual is *false in general* and discharged only the off-edge-line
stratum.

This module removes the gate **for triangles** (`n = 3`), unconditionally.  The
mechanism (numerically confirmed in the prior round): at a degenerate wall of edge `w`,
the wall edge contributes `0` (`PolygonWall.rfcount_eventually_zero_of_wall`, which is
already unconditional), and the **two non-wall edges flip together** — their combined
crossing count has *even* parity in a whole neighbourhood, so the total parity is
locally constant.  The two non-wall edges are `cyclicNext w` and `cyclicPrev w`; they
share the unique off-line vertex `P.q (cyclicNext (cyclicNext w))`, while their other
two vertices are the two endpoints of the wall edge `w`, which lie on the ray line and
whose side functions are **positively proportional** (`x` outside the segment, off the
boundary) — so the span of those two endpoints is always false and the pair count is
even.  The `span_mod_two_through_vertex` truth table absorbs the shared off-line vertex.

Since a non-degenerate triangle has three pairwise-non-parallel edge directions, at any
probe parameter the direction is parallel to **at most one** edge, so there is at most
one wall; case-splitting on whether that wall is degenerate (`x` on its line) gives a
clean, hypothesis-free per-`t₀` parity-constancy lemma.  Chaining through one
antiparallel-avoiding intermediate then discharges the full
`UnconditionalRayIndepInput Q` for every triangle, **unconditionally** — feeding
`PolygonSeparation.triangleExteriorEven_of_rayIndep` and the fully unconditional
`artGallery_strict`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonDegenerateWall

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonVertexSweep
open ProofsInTheBook.PolygonRayIndep
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonWall
open ProofsInTheBook.PolygonWallGlobal
open ProofsInTheBook.PolygonGenericRay
open ProofsInTheBook.PolygonLocalConstancy
open Filter Topology
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the local generic-wall hypothesis and the generic per-`t₀` assembly

`rcrossSum_parity_eventually_const` of `PolygonWallGlobal` uses its global
`GenericWallSeg` hypothesis **only at the single parameter `t₀`**.  We re-derive that
per-`t₀` statement under the strictly local hypothesis `LocalGenericWall … t₀` (every
wall at `t₀` is generic), so it can be discharged at a parameter even when the segment
has degenerate walls *elsewhere*.  The proof is the assembly of `PolygonWallGlobal`
with the global `hgen t₀ ht₀` call replaced by the local hypothesis. -/

/-- Local generic-wall condition at a single parameter `t₀`: every edge that is a wall
at `t₀` has both endpoint side values nonzero (the wall is *generic*, `x` off the
wall-edge's line). -/
def LocalGenericWall (P : StrictSimplePolygon n) (r₁ r₂ x : Pt) (t₀ : ℝ) : Prop :=
  ∀ i : Fin n, dirDen P r₁ r₂ i t₀ = 0 →
    ds0Of P r₁ r₂ x i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x i t₀ ≠ 0

/-- **Per-`t₀` eventual parity constancy under the local generic-wall hypothesis.**
A re-derivation of `PolygonWallGlobal.rcrossSum_parity_eventually_const` needing only
the local hypothesis at `t₀`. -/
lemma rcrossSum_parity_eventually_const_local {P : StrictSimplePolygon n} {r₁ r₂ : Pt}
    {x : Pt} (hoff : ¬ OnBoundary P x) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1)
    (hrne : dirAt r₁ r₂ t₀ ≠ 0)
    (hgen : LocalGenericWall P r₁ r₂ x t₀) :
    ∀ᶠ t in nhds t₀, rcrossSum P r₁ r₂ x t % 2 = rcrossSum P r₁ r₂ x t₀ % 2 := by
  classical
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  set W : Finset (Fin n) := Finset.univ.filter
    (fun i => dirDen P r₁ r₂ i t₀ = 0) with hW
  set R : Finset (Fin n) := Finset.univ.filter
    (fun i => dirDen P r₁ r₂ i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x i t₀ = 0) with hR
  set N : Finset (Fin n) := Finset.univ.filter
    (fun i => dirDen P r₁ r₂ i t₀ ≠ 0 ∧ ds0Of P r₁ r₂ x i t₀ = 0) with hN
  have hWmem : ∀ i, i ∈ W ↔ dirDen P r₁ r₂ i t₀ = 0 := by
    intro i; rw [hW, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hRmem : ∀ i, i ∈ R ↔ dirDen P r₁ r₂ i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x i t₀ = 0 := by
    intro i; rw [hR, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hNmem : ∀ i, i ∈ N ↔ dirDen P r₁ r₂ i t₀ ≠ 0 ∧ ds0Of P r₁ r₂ x i t₀ = 0 := by
    intro i; rw [hN, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hgen0 : ∀ i, dirDen P r₁ r₂ i t₀ = 0 →
      ds0Of P r₁ r₂ x i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x i t₀ ≠ 0 := hgen
  have hshare : ∀ i, ds0Of P r₁ r₂ x (cyclicNext i) t₀ = ds1Of P r₁ r₂ x i t₀ :=
    fun i => rfl
  have hRnextNW : ∀ i ∈ R, dirDen P r₁ r₂ (cyclicNext i) t₀ ≠ 0 := by
    intro i hi
    rw [hRmem] at hi
    intro hwk
    have := (hgen0 (cyclicNext i) hwk).1
    rw [hshare i, hi.2] at this; exact this rfl
  have hNimg : N = R.image cyclicNext := by
    apply Finset.ext; intro kk
    rw [hNmem, Finset.mem_image]
    constructor
    · rintro ⟨hDk, hk0⟩
      refine ⟨cyclicPrev kk, ?_, cyclicNext_cyclicPrev htwo kk⟩
      rw [hRmem]
      have hpe : ds1Of P r₁ r₂ x (cyclicPrev kk) t₀ = 0 := by
        have := hshare (cyclicPrev kk)
        rw [cyclicNext_cyclicPrev htwo kk] at this; rw [← this]; exact hk0
      refine ⟨?_, hpe⟩
      intro hwp
      exact (hgen0 (cyclicPrev kk) hwp).2 hpe
    · rintro ⟨i, hiR, rfl⟩
      rw [hRmem] at hiR
      exact ⟨hRnextNW i (by rw [hRmem]; exact hiR), by rw [hshare i]; exact hiR.2⟩
  have hdisjWR : Disjoint W R := by
    rw [Finset.disjoint_left]; intro i hiW hiR
    rw [hWmem] at hiW; rw [hRmem] at hiR; exact hiR.1 hiW
  have hdisjWN : Disjoint W N := by
    rw [Finset.disjoint_left]; intro i hiW hiN
    rw [hWmem] at hiW; rw [hNmem] at hiN; exact hiN.1 hiW
  have hdisjRN : Disjoint R N := by
    rw [Finset.disjoint_left]; intro i hiR hiN
    rw [hRmem] at hiR; rw [hNmem] at hiN
    exact noWall_not_both_zero hiR.1 ⟨hiN.2, hiR.2⟩
  set Rest : Finset (Fin n) := Finset.univ \ (W ∪ R ∪ N) with hRest
  have hpart : Finset.univ = ((W ∪ R) ∪ N) ∪ Rest := by
    rw [hRest]
    exact (Finset.union_sdiff_of_subset (Finset.subset_univ (W ∪ R ∪ N))).symm
  have hdisjRest : Disjoint ((W ∪ R) ∪ N) Rest := by
    rw [hRest]; exact Finset.disjoint_sdiff
  have hdisjWR_N : Disjoint (W ∪ R) N := by
    rw [Finset.disjoint_union_left]; exact ⟨hdisjWN, hdisjRN⟩
  have hsum : ∀ t, ∑ i : Fin n, rfcount P r₁ r₂ x i t =
      ((∑ i ∈ W, rfcount P r₁ r₂ x i t + ∑ i ∈ R, rfcount P r₁ r₂ x i t)
        + ∑ i ∈ N, rfcount P r₁ r₂ x i t) + ∑ i ∈ Rest, rfcount P r₁ r₂ x i t := by
    intro t
    conv_lhs => rw [show (Finset.univ : Finset (Fin n)) = ((W ∪ R) ∪ N) ∪ Rest from hpart]
    rw [Finset.sum_union hdisjRest, Finset.sum_union hdisjWR_N, Finset.sum_union hdisjWR]
  have hNsum : ∀ t, ∑ i ∈ N, rfcount P r₁ r₂ x i t =
      ∑ i ∈ R, rfcount P r₁ r₂ x (cyclicNext i) t := by
    intro t
    rw [hNimg, Finset.sum_image]
    intro a _ b _ hh; exact cyclicNext_injective hh
  have hwallEv : ∀ᶠ t in nhds t₀, ∀ i ∈ W, rfcount P r₁ r₂ x i t = 0 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [hWmem] at hi
    exact rfcount_eventually_zero_of_wall hoff hrne hi
  have hpairs : ∀ᶠ t in nhds t₀, ∀ i ∈ R,
      (rfcount P r₁ r₂ x i t + rfcount P r₁ r₂ x (cyclicNext i) t) % 2 =
        (rfcount P r₁ r₂ x i t₀ + rfcount P r₁ r₂ x (cyclicNext i) t₀) % 2 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hir := (hRmem i).mp hi
    exact rpair_count_eventually_const_noWall hoff hir.1 (hRnextNW i hi) hir.2
  have hrest : ∀ᶠ t in nhds t₀, ∀ i ∈ Rest, rfcount P r₁ r₂ x i t = rfcount P r₁ r₂ x i t₀ := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hi' : i ∉ W ∧ i ∉ R ∧ i ∉ N := by
      rw [hRest, Finset.mem_sdiff] at hi
      have := hi.2
      rw [Finset.mem_union, not_or, Finset.mem_union, not_or] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    have hDi : dirDen P r₁ r₂ i t₀ ≠ 0 := fun h => hi'.1 ((hWmem i).mpr h)
    have hs1 : ds1Of P r₁ r₂ x i t₀ ≠ 0 := fun h => hi'.2.1 ((hRmem i).mpr ⟨hDi, h⟩)
    have hs0 : ds0Of P r₁ r₂ x i t₀ ≠ 0 := fun h => hi'.2.2 ((hNmem i).mpr ⟨hDi, h⟩)
    exact rfcount_eventually_eq_of_noWall_noEvent hoff hDi hs0 hs1
  filter_upwards [hwallEv, hpairs, hrest] with t hw hp hr
  unfold rcrossSum
  rw [hsum t, hsum t₀, hNsum t, hNsum t₀]
  have hWt : ∑ i ∈ W, rfcount P r₁ r₂ x i t = 0 := Finset.sum_eq_zero (fun i hi => hw i hi)
  have hWt0 : ∑ i ∈ W, rfcount P r₁ r₂ x i t₀ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hWmem] at hi
    exact (rfcount_eventually_zero_of_wall hoff hrne hi).self_of_nhds
  rw [hWt, hWt0]
  set PR : ℝ → ℕ := fun s => ∑ i ∈ R, rfcount P r₁ r₂ x i s with hPR
  set PN : ℝ → ℕ := fun s => ∑ i ∈ R, rfcount P r₁ r₂ x (cyclicNext i) s with hPN
  set PE : ℝ → ℕ := fun s => ∑ i ∈ Rest, rfcount P r₁ r₂ x i s with hPE
  have hpairR : (PR t + PN t) % 2 = (PR t₀ + PN t₀) % 2 := by
    rw [hPR, hPN]
    have h1 : (∑ i ∈ R, rfcount P r₁ r₂ x i t) + (∑ i ∈ R, rfcount P r₁ r₂ x (cyclicNext i) t)
        = ∑ i ∈ R, (rfcount P r₁ r₂ x i t + rfcount P r₁ r₂ x (cyclicNext i) t) := by
      rw [Finset.sum_add_distrib]
    have h2 : (∑ i ∈ R, rfcount P r₁ r₂ x i t₀) + (∑ i ∈ R, rfcount P r₁ r₂ x (cyclicNext i) t₀)
        = ∑ i ∈ R, (rfcount P r₁ r₂ x i t₀ + rfcount P r₁ r₂ x (cyclicNext i) t₀) := by
      rw [Finset.sum_add_distrib]
    rw [h1, h2, Finset.sum_nat_mod, Finset.sum_nat_mod
      (s := R) (f := fun i => rfcount P r₁ r₂ x i t₀ + rfcount P r₁ r₂ x (cyclicNext i) t₀)]
    congr 1
    exact Finset.sum_congr rfl (fun i hi => hp i hi)
  have hrestEq : PE t = PE t₀ := by
    rw [hPE]; exact Finset.sum_congr rfl (fun i hi => hr i hi)
  show (0 + PR t + PN t + PE t) % 2 = (0 + PR t₀ + PN t₀ + PE t₀) % 2
  have e1 : 0 + PR t + PN t + PE t = (PR t + PN t) + PE t := by ring
  have e2 : 0 + PR t₀ + PN t₀ + PE t₀ = (PR t₀ + PN t₀) + PE t₀ := by ring
  rw [e1, e2, Nat.add_mod, hpairR, hrestEq, ← Nat.add_mod]

/-! ## Part 2: cyclic combinatorics for the triangle (`n = 3`)

A non-degenerate triangle has three edges forming a `3`-cycle.  We record the two
cyclic identities the degenerate-wall pairing needs:
`cyclicNext (cyclicNext w) = cyclicPrev w` and (its consequence)
`cyclicNext (cyclicNext (cyclicNext w)) = w`. -/

lemma cyclicNext_cyclicNext_eq_cyclicPrev (w : Fin 3) :
    cyclicNext (cyclicNext w) = cyclicPrev w := by
  apply Fin.ext
  rw [cyclicNext_val, cyclicNext_val, cyclicPrev_val]
  have hw : w.val < 3 := w.isLt
  interval_cases h : w.val <;> simp_all <;> omega

lemma cyclicNext_three_eq (w : Fin 3) :
    cyclicNext (cyclicNext (cyclicNext w)) = w := by
  apply Fin.ext
  rw [cyclicNext_val, cyclicNext_val, cyclicNext_val]
  have hw : w.val < 3 := w.isLt
  interval_cases h : w.val <;> simp_all

/-! ## Part 3: the degenerate-wall double-event pairing (the new math)

At a *degenerate* wall of edge `w` (`dirDen w t₀ = 0` and `ds0Of w t₀ = 0`, i.e. `x` on
edge `w`'s line) off the boundary, the wall edge contributes `0` near `t₀`
(`rfcount_eventually_zero_of_wall`), and the two adjacent edges `j = cyclicNext w` and
`p = cyclicNext j` carry **equal** crossing counts near `t₀`, hence an even pair sum.

The two key geometric facts, both flowing from the positive proportionality
`P.q w − x = μ • (P.q (cyclicNext w) − x)` (`μ > 0`, `x` outside the wall segment):

* **Span agreement** — `ds0Of j = ds1Of w = side (P.q (cyclicNext w))` and
  `ds1Of p = ds0Of w = side (P.q w)` are positively proportional, while the shared
  vertex `ds1Of j = ds0Of p = side (P.q (cyclicNext (cyclicNext w)))` is common; `Span`
  is symmetric and sign-only, so `Span (ds0Of j) (ds1Of j) ↔ Span (ds0Of p) (ds1Of p)`
  pointwise.
* **Forward agreement** — at `t₀` the ray reaches `P.q (cyclicNext w)` (edge `j`'s start)
  and `P.q w` (edge `p`'s end) at forward parameters in positive proportion
  `dirTau p t₀ = μ • dirTau j t₀`, both nonzero (off boundary), so the forward guards
  `0 ≤ dirTau j` and `0 ≤ dirTau p` agree in a neighbourhood. -/

/-- Two triangle edges with non-parallel edge vectors cannot both be walls at a
nonzero direction: the direction would be `det2`-orthogonal to both, forcing it to be
`0`. -/
lemma dirDen_ne_zero_of_wall_of_nonpar {P : StrictSimplePolygon 3} {r₁ r₂ : Pt}
    {w k : Fin 3} {t₀ : ℝ} (hrne : dirAt r₁ r₂ t₀ ≠ 0)
    (hwall : dirDen P r₁ r₂ w t₀ = 0)
    (hnpar : det2 (P.q (cyclicNext w) - P.q w) (P.q (cyclicNext k) - P.q k) ≠ 0) :
    dirDen P r₁ r₂ k t₀ ≠ 0 := by
  intro hwk
  have hew : det2 (dirAt r₁ r₂ t₀) (P.q (cyclicNext w) - P.q w) = 0 := hwall
  have hek : det2 (dirAt r₁ r₂ t₀) (P.q (cyclicNext k) - P.q k) = 0 := hwk
  have hz : dirAt r₁ r₂ t₀ = 0 :=
    eq_zero_of_det2_eq_zero
      (u := P.q (cyclicNext w) - P.q w) (v := P.q (cyclicNext k) - P.q k)
      (w := dirAt r₁ r₂ t₀) hnpar
      (by rw [det2_antisymm]; rw [hew]; ring)
      (by rw [det2_antisymm]; rw [hek]; ring)
  exact hrne hz

/-- Consecutive edge vectors of a triangle are non-parallel:
`det2 (edgeVec w) (edgeVec (cyclicNext w)) ≠ 0` (the consecutive noncollinearity). -/
lemma det2_edgeVec_next_ne_zero (P : StrictSimplePolygon 3) (w : Fin 3) :
    det2 (P.q (cyclicNext w) - P.q w) (P.q (cyclicNext (cyclicNext w)) - P.q (cyclicNext w)) ≠ 0 := by
  set j := cyclicNext w with hj
  have hnc := P.noncollinear_consecutive j
  have hpj : cyclicPrev j = w := by
    apply Fin.ext
    rw [hj, cyclicPrev_val, cyclicNext_val]
    have hw : w.val < 3 := w.isLt
    interval_cases h : w.val <;> simp_all
  rw [hpj] at hnc
  have hsplit : P.q (cyclicNext j) - P.q w
      = (P.q (cyclicNext j) - P.q j) + (P.q (cyclicNext w) - P.q w) := by
    rw [hj]; abel
  have horient : orient (P.q w) (P.q j) (P.q (cyclicNext j))
      = det2 (P.q (cyclicNext w) - P.q w) (P.q (cyclicNext j) - P.q j) := by
    unfold orient
    rw [show P.q j - P.q w = P.q (cyclicNext w) - P.q w from by rw [hj], hsplit,
      det2_add_right, PolygonLocalConstancy.det2_self, add_zero]
  rw [horient] at hnc
  exact hnc

/-- The wall edge `w` and the previous edge `cyclicNext (cyclicNext w) = cyclicPrev w`
have non-parallel edge vectors: `det2 (edgeVec w) (edgeVec (cyclicPrev w)) ≠ 0`. -/
lemma det2_edgeVec_prev_ne_zero (P : StrictSimplePolygon 3) (w : Fin 3) :
    det2 (P.q (cyclicNext w) - P.q w)
        (P.q (cyclicNext (cyclicNext (cyclicNext w))) - P.q (cyclicNext (cyclicNext w))) ≠ 0 := by
  -- p := cyclicNext (cyclicNext w) = cyclicPrev w ; edgeVec p ends at cyclicNext p = w.
  set p := cyclicNext (cyclicNext w) with hp
  have hpw : cyclicNext p = w := by rw [hp]; exact cyclicNext_three_eq w
  have hnc := P.noncollinear_consecutive w
  -- prev w = p.
  have hpwp : cyclicPrev w = p := by
    apply Fin.ext
    rw [hp, cyclicPrev_val, cyclicNext_val, cyclicNext_val]
    have hw : w.val < 3 := w.isLt
    interval_cases h : w.val <;> simp_all
  rw [hpwp] at hnc
  -- orient (q p) (q w) (q (next w)) = det2 (q w - q p) (q (next w) - q p)
  --  = det2 (edgeVec p) (edgeVec p + edgeVec w) = det2 (edgeVec p) (edgeVec w).
  have e1 : P.q w - P.q p = P.q (cyclicNext p) - P.q p := by rw [hpw]
  have e2 : P.q (cyclicNext w) - P.q p
      = (P.q (cyclicNext p) - P.q p) + (P.q (cyclicNext w) - P.q w) := by
    rw [hpw]; abel
  have horient : orient (P.q p) (P.q w) (P.q (cyclicNext w))
      = det2 (P.q (cyclicNext p) - P.q p) (P.q (cyclicNext w) - P.q w) := by
    unfold orient
    rw [e1, e2, det2_add_right, PolygonLocalConstancy.det2_self, zero_add]
  rw [horient] at hnc
  -- want det2 (edgeVec w) (edgeVec p) ≠ 0 = - det2 (edgeVec p) (edgeVec w).
  rw [det2_antisymm]
  rw [hp]
  exact fun h => hnc (by linarith [h])

/-- **The degenerate-wall pair lemma.**  At a degenerate wall of edge `w` (`n = 3`,
`x` off the boundary), the two adjacent edges `cyclicNext w` and `cyclicNext (cyclicNext w)`
carry equal crossing counts in a neighbourhood of `t₀`. -/
lemma rfcount_pair_eventually_eq_of_degenerateWall_tri {P : StrictSimplePolygon 3}
    {r₁ r₂ : Pt} {x : Pt} (hoff : ¬ OnBoundary P x) {w : Fin 3} {t₀ : ℝ}
    (hrne : dirAt r₁ r₂ t₀ ≠ 0)
    (hwall : dirDen P r₁ r₂ w t₀ = 0)
    (h0 : ds0Of P r₁ r₂ x w t₀ = 0) :
    ∀ᶠ t in nhds t₀,
      rfcount P r₁ r₂ x (cyclicNext w) t
        = rfcount P r₁ r₂ x (cyclicNext (cyclicNext w)) t := by
  classical
  set j := cyclicNext w with hj
  set p := cyclicNext j with hp
  have hpw : cyclicNext p = w := by rw [hp, hj]; exact cyclicNext_three_eq w
  -- ds1Of w t₀ = 0.
  have h1 : ds1Of P r₁ r₂ x w t₀ = 0 := by rw [← ds_eq_at_wall hwall]; exact h0
  -- adjacent denominators nonzero.
  have hDj : dirDen P r₁ r₂ j t₀ ≠ 0 := by
    rw [hj]
    exact dirDen_ne_zero_of_wall_of_nonpar hrne hwall (det2_edgeVec_next_ne_zero P w)
  have hDp : dirDen P r₁ r₂ p t₀ ≠ 0 := by
    rw [hp, hj]
    exact dirDen_ne_zero_of_wall_of_nonpar hrne hwall (det2_edgeVec_prev_ne_zero P w)
  -- side identifications.
  -- ds0Of j = ds1Of w  (shared vertex P.q (cyclicNext w) = P.q j).
  have hds0j : ds0Of P r₁ r₂ x j = ds1Of P r₁ r₂ x w := by
    rw [hj]; exact (ds1Of_eq_ds0Of_next P r₁ r₂ x w).symm
  -- ds1Of p = ds0Of w  (P.q (cyclicNext p) = P.q w).
  have hds1p : ds1Of P r₁ r₂ x p = ds0Of P r₁ r₂ x w := by
    have : ds1Of P r₁ r₂ x p = ds0Of P r₁ r₂ x (cyclicNext p) :=
      ds1Of_eq_ds0Of_next P r₁ r₂ x p
    rw [this, hpw]
  -- shared off-line vertex: ds1Of j = ds0Of p = side (P.q (cyclicNext j)).
  have hshared : ds1Of P r₁ r₂ x j = ds0Of P r₁ r₂ x p := by
    rw [hp]; exact ds1Of_eq_ds0Of_next P r₁ r₂ x j
  -- positive proportionality of the two wall-edge endpoints.
  -- a - x = μ • (b - x), μ > 0, a = P.q w, b = P.q (cyclicNext w) = P.q j.
  set a := P.q w with ha
  set b := P.q j with hb'
  have hbx : b - x ≠ 0 := by
    intro hz
    apply hoff
    refine ⟨w, ?_⟩
    rw [show x = b from by rw [sub_eq_zero] at hz; exact hz.symm, hb', hj, Edge]
    exact right_mem_segment ℝ _ _
  have hda : det2 (dirAt r₁ r₂ t₀) (a - x) = 0 := h0
  have hdb : det2 (dirAt r₁ r₂ t₀) (b - x) = 0 := by rw [hb', hj]; exact h1
  obtain ⟨μ, hμeq⟩ :=
    exists_smul_of_det2_zero hrne hda hdb hbx
  -- μ > 0 (else x in the wall segment, on boundary).
  have hμpos : 0 < μ := by
    by_contra hle
    push_neg at hle
    apply hoff
    refine ⟨w, ?_⟩
    set lam := -μ / (1 - μ) with hlam
    have hedge : b - a = (1 - μ) • (b - x) := by
      have : b - a = (b - x) - (a - x) := by abel
      rw [this, hμeq, sub_smul, one_smul]
    have h1μ : (1 : ℝ) - μ ≠ 0 := by
      intro hz
      apply edgeVec_ne_zero P w
      rw [edgeVec, ← hj, ← hb', ← ha, hedge, hz, zero_smul]
    have hxa : x - a = lam • (b - a) := by
      rw [hlam, hedge, smul_smul, div_mul_cancel₀ _ h1μ]
      have : x - a = -(a - x) := by abel
      rw [this, hμeq, neg_smul]
    have hxeq : x = AffineMap.lineMap a b lam := by
      rw [AffineMap.lineMap_apply_module]
      have : (1 - lam) • a + lam • b = a + lam • (b - a) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [this, ← hxa]; abel
    have hden : 0 < 1 - μ := by linarith
    have hlam0 : 0 ≤ lam := by
      rw [hlam]; exact div_nonneg (by linarith) (le_of_lt hden)
    have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one hden]; linarith
    have hxeq' : AffineMap.lineMap (P.q w) (P.q (cyclicNext w)) lam = x := by
      have hab : AffineMap.lineMap a b lam = AffineMap.lineMap (P.q w) (P.q (cyclicNext w)) lam := by
        rw [ha, hb', hj]
      rw [← hab, ← hxeq]
    rw [Edge, seg, segment_eq_image_lineMap]
    exact ⟨lam, ⟨hlam0, hlam1⟩, hxeq'⟩
  -- pointwise proportionality of the two outer side functions:
  -- ds0Of w t = μ * ds1Of w t  (a-side = μ * b-side).
  have hprop : ∀ t, ds0Of P r₁ r₂ x w t = μ * ds1Of P r₁ r₂ x w t := by
    intro t
    have e0 : ds0Of P r₁ r₂ x w t = det2 (dirAt r₁ r₂ t) (a - x) := rfl
    have e1 : ds1Of P r₁ r₂ x w t = det2 (dirAt r₁ r₂ t) (b - x) := by
      rw [hb', hj]; rfl
    rw [e0, e1, hμeq, det2_smul_right]
  -- ===== Span agreement pointwise =====
  -- Span (ds0Of j t) (ds1Of j t) ↔ Span (ds0Of p t) (ds1Of p t).
  have hspan_iff : ∀ t, Span (ds0Of P r₁ r₂ x j t) (ds1Of P r₁ r₂ x j t)
      ↔ Span (ds0Of P r₁ r₂ x p t) (ds1Of P r₁ r₂ x p t) := by
    intro t
    -- ds0Of j t = ds1Of w t =: s_b ; ds1Of j t = ds0Of p t =: c ; ds1Of p t = ds0Of w t = μ s_b.
    have ej0 : ds0Of P r₁ r₂ x j t = ds1Of P r₁ r₂ x w t := by rw [hds0j]
    have ejs : ds1Of P r₁ r₂ x j t = ds0Of P r₁ r₂ x p t := by rw [hshared]
    have ep1 : ds1Of P r₁ r₂ x p t = ds0Of P r₁ r₂ x w t := by rw [hds1p]
    rw [ej0, ejs, ep1, hprop t]
    -- goal: Span (ds1Of w t) (ds0Of p t) ↔ Span (ds0Of p t) (μ * ds1Of w t)
    set sb := ds1Of P r₁ r₂ x w t with hsb
    set c := ds0Of P r₁ r₂ x p t with hc
    -- Span symmetric + positive scaling invariance: with μ > 0,
    -- 0 < μ*sb ↔ 0 < sb and μ*sb ≤ 0 ↔ sb ≤ 0.
    have hpos : 0 < μ * sb ↔ 0 < sb := by
      constructor
      · intro h; nlinarith [hμpos, h]
      · intro h; positivity
    have hnonpos : μ * sb ≤ 0 ↔ sb ≤ 0 := by
      constructor
      · intro h; nlinarith [hμpos, h]
      · intro h; nlinarith [hμpos, h]
    unfold Span
    rw [hpos, hnonpos]
    tauto
  -- ===== Forward (tau) agreement near t₀ =====
  -- at t₀, ray reaches P.q j = b at dirTau j t₀, and P.q w = a at dirTau p t₀,
  -- with dirTau p t₀ = μ • dirTau j t₀ ; both nonzero.
  -- edge j start event: ds0Of j t₀ = 0 ⟹ rU j t₀ = 0 ⟹ x + dirTau j t₀ • dir = P.q j.
  have hcek : x + dirTau P r₁ r₂ x j t₀ • dirAt r₁ r₂ t₀ = P.q j := by
    have hDj' : det2 (dirAt r₁ r₂ t₀) (P.q (cyclicNext j) - P.q j) ≠ 0 := hDj
    have hce := r_cross_eq P (dirAt r₁ r₂ t₀) x j hDj'
    have hrU0 : rU P (dirAt r₁ r₂ t₀) x j = 0 := by
      rw [rU, div_eq_zero_iff]; left
      have : ds0Of P r₁ r₂ x j t₀ = 0 := by rw [hds0j]; exact h1
      have hsj : det2 (dirAt r₁ r₂ t₀) (P.q j - x) = 0 := this
      have hneg : det2 (dirAt r₁ r₂ t₀) (x - P.q j)
          = - det2 (dirAt r₁ r₂ t₀) (P.q j - x) := by
        unfold det2; simp only [PiLp.sub_apply]; ring
      rw [hneg, hsj, neg_zero]
    rw [hrU0, AffineMap.lineMap_apply_zero] at hce
    rw [dirTau_eq_rTau]; exact hce
  -- edge p end event: ds1Of p t₀ = 0 ⟹ rU p t₀ = 1 ⟹ x + dirTau p t₀ • dir = P.q (cyclicNext p) = a.
  have hcep : x + dirTau P r₁ r₂ x p t₀ • dirAt r₁ r₂ t₀ = P.q w := by
    have hsp : ds1Of P r₁ r₂ x p t₀ = 0 := by rw [hds1p]; exact h0
    have hce := r_cross_eq P (dirAt r₁ r₂ t₀) x p
      (show det2 (dirAt r₁ r₂ t₀) (P.q (cyclicNext p) - P.q p) ≠ 0 from hDp)
    rw [rU_eq_one_of_event hDp hsp, AffineMap.lineMap_apply_one] at hce
    rw [dirTau_eq_rTau, hce, hpw]
  -- dirTau p t₀ = μ * dirTau j t₀.
  have hτprop : dirTau P r₁ r₂ x p t₀ = μ * dirTau P r₁ r₂ x j t₀ := by
    -- (P.q w - x) = dirTau p • dir ; (P.q j - x) = dirTau j • dir ; a - x = μ (b - x).
    have ep : dirTau P r₁ r₂ x p t₀ • dirAt r₁ r₂ t₀ = a - x := by
      rw [show a = P.q w from rfl, ← hcep]; abel
    have ej : dirTau P r₁ r₂ x j t₀ • dirAt r₁ r₂ t₀ = b - x := by
      rw [hb', ← hcek]; abel
    have : dirTau P r₁ r₂ x p t₀ • dirAt r₁ r₂ t₀
        = (μ * dirTau P r₁ r₂ x j t₀) • dirAt r₁ r₂ t₀ := by
      rw [ep, hμeq, ← ej, ← mul_smul]
    have hsub : (dirTau P r₁ r₂ x p t₀ - μ * dirTau P r₁ r₂ x j t₀) • dirAt r₁ r₂ t₀ = 0 := by
      rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.mp hsub with hc | hc
    · linarith [hc]
    · exact absurd hc hrne
  -- dirTau j t₀ ≠ 0 (off boundary).
  have hτjne : dirTau P r₁ r₂ x j t₀ ≠ 0 := by
    intro hz
    rw [hz, zero_smul, add_zero] at hcek
    apply hoff
    exact ⟨j, by rw [hcek, hj, Edge]; exact left_mem_segment ℝ _ _⟩
  -- so dirTau j t₀ and dirTau p t₀ have the same strict sign.
  have hctau_j := continuousAt_dirTau_of_noWall (P := P) (x := x) hDj
  have hctau_p := continuousAt_dirTau_of_noWall (P := P) (x := x) hDp
  have htausign : ∀ᶠ t in nhds t₀,
      (0 ≤ dirTau P r₁ r₂ x j t ↔ 0 ≤ dirTau P r₁ r₂ x p t) := by
    rcases lt_or_gt_of_ne hτjne with hjneg | hjpos
    · -- both negative at t₀: dirTau p t₀ = μ * (neg) < 0.
      have hpneg : dirTau P r₁ r₂ x p t₀ < 0 := by rw [hτprop]; exact mul_neg_of_pos_of_neg hμpos hjneg
      have evj : ∀ᶠ t in nhds t₀, dirTau P r₁ r₂ x j t < 0 := by
        filter_upwards [hctau_j.tendsto.eventually_lt_const hjneg] with t ht using ht
      have evp : ∀ᶠ t in nhds t₀, dirTau P r₁ r₂ x p t < 0 := by
        filter_upwards [hctau_p.tendsto.eventually_lt_const hpneg] with t ht using ht
      filter_upwards [evj, evp] with t htj htp
      constructor
      · intro h; linarith
      · intro h; linarith
    · -- both positive at t₀.
      have hppos : 0 < dirTau P r₁ r₂ x p t₀ := by rw [hτprop]; positivity
      have evj : ∀ᶠ t in nhds t₀, 0 < dirTau P r₁ r₂ x j t := by
        filter_upwards [hctau_j.tendsto.eventually_const_lt hjpos] with t ht using ht
      have evp : ∀ᶠ t in nhds t₀, 0 < dirTau P r₁ r₂ x p t := by
        filter_upwards [hctau_p.tendsto.eventually_const_lt hppos] with t ht using ht
      filter_upwards [evj, evp] with t htj htp
      constructor
      · intro _; linarith
      · intro _; linarith
  -- assemble: rfcount j t = rfcount p t.
  filter_upwards [htausign] with t htau
  rw [rfcount_eq, rfcount_eq]
  congr 1
  rw [eq_iff_iff, rstatusOf_iff, rstatusOf_iff, hspan_iff t]
  constructor
  · rintro ⟨hsp, hτ⟩; exact ⟨hsp, htau.mp hτ⟩
  · rintro ⟨hsp, hτ⟩; exact ⟨hsp, htau.mpr hτ⟩

/-! ## Part 4: hypothesis-free per-`t₀` parity constancy for the triangle

For `n = 3`, at any probe parameter `t₀` with `dirAt r₁ r₂ t₀ ≠ 0`, the direction is
parallel to **at most one** edge (the three edge directions are pairwise non-parallel),
so there is at most one wall.  Case-splitting on whether a *degenerate* wall (`x` on its
line) exists at `t₀`:

* **No degenerate wall** — `LocalGenericWall` holds, so `rcrossSum_parity_eventually_const_local`
  gives parity constancy.
* **A degenerate wall** of edge `w` — the wall edge contributes `0` and the two adjacent
  edges carry equal counts (`rfcount_pair_eventually_eq_of_degenerateWall_tri`), so
  `rcrossSum % 2 = 0` in a whole neighbourhood, hence constant. -/

/-- The three edges of a triangle, as a finset, cover `Fin 3`. -/
lemma univ_eq_triple (w : Fin 3) :
    (Finset.univ : Finset (Fin 3)) =
      {w, cyclicNext w, cyclicNext (cyclicNext w)} := by
  have hw : w.val < 3 := w.isLt
  have hjw : cyclicNext w ≠ w := cyclicNext_ne_self (by decide) w
  have hpw : cyclicNext (cyclicNext w) ≠ w := by
    apply Fin.val_ne_iff.mp
    rw [cyclicNext_val, cyclicNext_val]
    interval_cases h : w.val <;> simp_all
  have hpj : cyclicNext (cyclicNext w) ≠ cyclicNext w := cyclicNext_ne_self (by decide) _
  have hcard : ({w, cyclicNext w, cyclicNext (cyclicNext w)} : Finset (Fin 3)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hjw.symm, hpw.symm]),
        Finset.card_insert_of_notMem (by simp [hpj.symm]), Finset.card_singleton]
  refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
  rw [Finset.card_univ, Fintype.card_fin, hcard]

/-- **Degenerate-wall total parity is zero near `t₀` (`n = 3`).**  At a degenerate wall
of edge `w` off the boundary, `rcrossSum % 2 = 0` in a neighbourhood of `t₀`. -/
lemma rcrossSum_eventually_zero_of_degenerateWall_tri {P : StrictSimplePolygon 3}
    {r₁ r₂ : Pt} {x : Pt} (hoff : ¬ OnBoundary P x) {w : Fin 3} {t₀ : ℝ}
    (hrne : dirAt r₁ r₂ t₀ ≠ 0)
    (hwall : dirDen P r₁ r₂ w t₀ = 0)
    (h0 : ds0Of P r₁ r₂ x w t₀ = 0) :
    ∀ᶠ t in nhds t₀, rcrossSum P r₁ r₂ x t % 2 = 0 := by
  classical
  set j := cyclicNext w with hj
  set p := cyclicNext (cyclicNext w) with hp
  have hwallEv : ∀ᶠ t in nhds t₀, rfcount P r₁ r₂ x w t = 0 :=
    rfcount_eventually_zero_of_wall hoff hrne hwall
  have hpairEv : ∀ᶠ t in nhds t₀, rfcount P r₁ r₂ x j t = rfcount P r₁ r₂ x p t := by
    have := rfcount_pair_eventually_eq_of_degenerateWall_tri hoff hrne hwall h0
    rw [hj, hp]; exact this
  filter_upwards [hwallEv, hpairEv] with t hw hpair
  unfold rcrossSum
  rw [univ_eq_triple w]
  -- distinctness for the sum-over-insert.
  have hjw : j ≠ w := cyclicNext_ne_self (by decide) w
  have hpw : p ≠ w := by
    apply Fin.val_ne_iff.mp
    rw [hp, cyclicNext_val, cyclicNext_val]
    have hwv : w.val < 3 := w.isLt
    interval_cases h : w.val <;> simp_all
  have hpj : p ≠ j := by rw [hp, hj]; exact cyclicNext_ne_self (by decide) _
  rw [show ({w, cyclicNext w, cyclicNext (cyclicNext w)} : Finset (Fin 3))
        = {w, j, p} from rfl,
      Finset.sum_insert (by simp [hjw.symm, hpw.symm]),
      Finset.sum_insert (by simp [hpj.symm]),
      Finset.sum_singleton]
  rw [hw, hpair]
  -- 0 + (rfcount p + rfcount p) ≡ 0 mod 2.
  omega

/-- **Hypothesis-free per-`t₀` parity constancy (`n = 3`).**  Off the boundary, with
`dirAt r₁ r₂ t₀ ≠ 0`, the raw crossing parity is eventually constant at every
`t₀ ∈ [0,1]` — no generic-wall hypothesis. -/
lemma rcrossSum_parity_eventually_const_tri {P : StrictSimplePolygon 3} {r₁ r₂ : Pt}
    {x : Pt} (hoff : ¬ OnBoundary P x) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1)
    (hrne : dirAt r₁ r₂ t₀ ≠ 0) :
    ∀ᶠ t in nhds t₀, rcrossSum P r₁ r₂ x t % 2 = rcrossSum P r₁ r₂ x t₀ % 2 := by
  classical
  by_cases hdeg : ∃ w : Fin 3, dirDen P r₁ r₂ w t₀ = 0 ∧ ds0Of P r₁ r₂ x w t₀ = 0
  · obtain ⟨w, hwall, h0⟩ := hdeg
    have hev := rcrossSum_eventually_zero_of_degenerateWall_tri hoff hrne hwall h0
    have hself : rcrossSum P r₁ r₂ x t₀ % 2 = 0 := hev.self_of_nhds
    filter_upwards [hev] with t ht
    rw [ht, hself]
  · -- no degenerate wall at t₀: LocalGenericWall holds.
    push_neg at hdeg
    have hloc : LocalGenericWall P r₁ r₂ x t₀ := by
      intro i hwall
      have hs0 : ds0Of P r₁ r₂ x i t₀ ≠ 0 := hdeg i hwall
      have hs1 : ds1Of P r₁ r₂ x i t₀ ≠ 0 := by
        rw [← ds_eq_at_wall hwall]; exact hs0
      exact ⟨hs0, hs1⟩
    exact rcrossSum_parity_eventually_const_local hoff ht₀ hrne hloc

/-! ## Part 5: global parity constancy on `[0,1]` and the wall-global ray independence

The `Icc 0 1` engine of `PolygonWallGlobal` (preconnectedness + local constancy), now
fed by the *hypothesis-free* per-`t₀` lemma, gives equal endpoint parities for any
segment that avoids the zero direction — **no `GenericWallSeg`**. -/

/-- The raw parity along the segment is locally constant on `Icc 0 1` (`n = 3`,
hypothesis-free at each wall). -/
lemma rParity_locallyConstant_tri {P : StrictSimplePolygon 3} {r₁ r₂ : Pt} {x : Pt}
    (hoff : ¬ OnBoundary P x) (hz : SegAvoidsZero r₁ r₂) :
    IsLocallyConstant (rParity P r₁ r₂ x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t₀
  have hev := rcrossSum_parity_eventually_const_tri hoff t₀.2 (hz t₀.val t₀.2)
  exact (continuous_subtype_val.continuousAt (x := t₀)).tendsto.eventually hev

/-- **Global parity constancy on the segment (`n = 3`).**  Under avoid-zero, the raw
crossing parities at the two endpoint directions agree — no generic-wall hypothesis. -/
lemma rcrossSum_parity_endpoints_tri {P : StrictSimplePolygon 3} {r₁ r₂ : Pt} {x : Pt}
    (hoff : ¬ OnBoundary P x) (hz : SegAvoidsZero r₁ r₂) :
    rcrossSum P r₁ r₂ x 0 % 2 = rcrossSum P r₁ r₂ x 1 % 2 := by
  have hLC := rParity_locallyConstant_tri hoff hz
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have := hLC.apply_eq_of_preconnectedSpace (⟨0, h0⟩ : ↥(Set.Icc (0:ℝ) 1)) ⟨1, h1⟩
  unfold rParity at this
  exact this

/-- **Wall-global crossing-number parity independence (`n = 3`, no `GenericWallSeg`).**
For two ray directions whose connecting segment avoids the zero direction, the crossing
parities agree off the boundary — unconditional in the walls (generic *and* degenerate). -/
theorem crossingNumber'_wallGlobal_tri {P : StrictSimplePolygon 3} (ρ σ : RayDirection P)
    {x : Pt} (hoff : ¬ OnBoundary P x) (hz : SegAvoidsZero ρ.r σ.r) :
    CrossingNumber' P ρ x % 2 = CrossingNumber' P σ x % 2 := by
  have hcr0 : CrossingNumber' P ρ x = rcrossSum P ρ.r σ.r x 0 :=
    crossingNumber'_eq_rcrossSum P ρ.r σ.r x 0 ρ (dirAt_zero ρ.r σ.r).symm
  have hcr1 : CrossingNumber' P σ x = rcrossSum P ρ.r σ.r x 1 :=
    crossingNumber'_eq_rcrossSum P ρ.r σ.r x 1 σ (dirAt_one ρ.r σ.r).symm
  rw [hcr0, hcr1]
  exact rcrossSum_parity_endpoints_tri hoff hz

/-- **Wall-global region-indicator ray independence (`n = 3`).**  Off the boundary, the
corrected closed region is the same for two ray directions whose connecting segment
avoids the zero direction — no generic-wall hypothesis. -/
theorem closedRegion'_wallGlobal_tri {P : StrictSimplePolygon 3} (ρ σ : RayDirection P)
    {x : Pt} (hoff : ¬ OnBoundary P x) (hz : SegAvoidsZero ρ.r σ.r) :
    ClosedRegion' P ρ x ↔ ClosedRegion' P σ x := by
  unfold ClosedRegion'
  have hpar := crossingNumber'_wallGlobal_tri ρ σ hoff hz
  constructor
  · rintro (hb | ho)
    · exact Or.inl hb
    · exact Or.inr ((odd_iff_of_mod_two_eq hpar).mp ho)
  · rintro (hb | ho)
    · exact Or.inl hb
    · exact Or.inr ((odd_iff_of_mod_two_eq hpar).mpr ho)

/-! ## Part 6: the avoid-zero chain and the unconditional triangle ray-independence

Two arbitrary ray directions are connected through a single intermediate `μ = mkPt 1 s`
whose slope avoids the (finite) edge slopes (so `μ` is a genuine `RayDirection`) and the
at-most-two antiparallel slopes of `ρ.r`, `σ.r` (so both connecting segments avoid the
zero direction).  No genericity at the walls is required — `closedRegion'_wallGlobal_tri`
handles every wall.  Composing the two region transports discharges the full
`UnconditionalRayIndepInput Q`, **unconditionally**. -/

/-- **Avoid-zero chain.**  Any two ray directions of a triangle admit a connecting
intermediate `μ` whose two segments both avoid the zero direction. -/
theorem closedRegion'_chain_tri {P : StrictSimplePolygon 3} (ρ σ : RayDirection P)
    {x : Pt} (hoff : ¬ OnBoundary P x) :
    ClosedRegion' P ρ x ↔ ClosedRegion' P σ x := by
  classical
  let bad : Finset ℝ :=
    (Finset.univ.image fun i : Fin 3 => badSlope (edgeVec P i)) ∪
      {antiSlope ρ.r, antiSlope σ.r}
  obtain ⟨s, hsbad⟩ := bad.exists_notMem
  have hsedge : ∀ i : Fin 3, s ≠ badSlope (edgeVec P i) := by
    intro i hi
    apply hsbad; apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩
  have hsρ : s ≠ antiSlope ρ.r := by
    intro h; apply hsbad; apply Finset.mem_union_right; rw [h]; simp
  have hsσ : s ≠ antiSlope σ.r := by
    intro h; apply hsbad; apply Finset.mem_union_right; rw [h]; simp
  let μ : RayDirection P :=
    { r := mkPt 1 s
      r_ne_zero := mkPt_one_ne_zero s
      no_edge_parallel := by
        intro i hdet
        exact hsedge i (slope_eq_badSlope_of_det2_mkPt_one_eq_zero
          (edgeVec_ne_zero P i) hdet) }
  have hμr : μ.r = mkPt 1 s := rfl
  have hzρ : SegAvoidsZero ρ.r μ.r := by rw [hμr]; exact segAvoidsZero_to_mkPt ρ hsρ
  have hzσ : SegAvoidsZero μ.r σ.r := by
    intro t ht hzero
    have hrev : dirAt μ.r σ.r t = dirAt σ.r μ.r (1 - t) := by
      unfold dirAt; rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
      have : (1 : ℝ) - (1 - t) = t := by ring
      rw [this]; abel
    rw [hrev] at hzero
    have ht' : (1 - t) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [hμr] at hzero
    exact (segAvoidsZero_to_mkPt σ hsσ) (1 - t) ht' hzero
  exact (closedRegion'_wallGlobal_tri ρ μ hoff hzρ).trans
    (closedRegion'_wallGlobal_tri μ σ hoff hzσ)

/-- **The unconditional triangle ray-independence input.**  For every triangle, the
off-boundary region indicator is independent of the ray direction —
`PolygonFinish.UnconditionalRayIndepInput`, proved **unconditionally** (every wall,
generic or degenerate, is handled). -/
theorem unconditionalRayIndepInput_triangle :
    ∀ Q : StrictSimplePolygon 3, UnconditionalRayIndepInput Q :=
  fun Q ρ σ _ hoff => closedRegion'_chain_tri ρ σ hoff

/-! ## Part 7: the fully unconditional Chapter-36 art-gallery headline

Feeding `unconditionalRayIndepInput_triangle` into
`PolygonSeparation.triangleExteriorEven_of_rayIndep` discharges the triangle leaf's
exterior-even atom **with no ray/genericity hypothesis**, hence the
`PolygonSeparation.chapter36_headline_separation` art-gallery bound is unconditional in
the ray choice (the remaining inputs being the genuinely-planar residuals the design
already isolates: the uniform residual geometry `D`, the convex-vertex leaf primitive
`hconv`, and the diagonal-attach peel `M`). -/

/-- **`TriangleExteriorEven`, unconditional.**  The triangle leaf's exterior-even atom,
with the ray-choice oracle fully discharged by the degenerate-wall parity transport. -/
theorem triangleExteriorEven_unconditional :
    ProofsInTheBook.PolygonLeaf.TriangleExteriorEven :=
  ProofsInTheBook.PolygonSeparation.triangleExteriorEven_of_rayIndep
    unconditionalRayIndepInput_triangle

/-- **Chapter-36 art-gallery headline, unconditional in the ray choice.**  The kept
ray-choice oracle of `PolygonSeparation.chapter36_headline_separation`
(`∀ Q : StrictSimplePolygon 3, UnconditionalRayIndepInput Q`) is now *produced*
unconditionally by `unconditionalRayIndepInput_triangle`, so the `⌊n/3⌋` guard bound
holds for *any* ray direction `ρ` with no ray/genericity hypothesis. -/
theorem artGallery_strict_unconditional {n : ℕ}
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ProofsInTheBook.PolygonOracleClose.ResidualGeometryData P ρ)
    (hconv : ProofsInTheBook.PolygonLeaf.TriangleConvexLeaf)
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms hconv
          triangleExteriorEven_unconditional)))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonSeparation.chapter36_headline_separation D hconv
    unconditionalRayIndepInput_triangle M P ρ

end

end ProofsInTheBook.PolygonDegenerateWall
