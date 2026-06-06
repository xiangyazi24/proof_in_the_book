import ProofsInTheBook.PolygonDegenerateWall

/-!
# Chapter 36 — degenerate-wall parity transport for GENERAL `n` (`PolygonGeneralWall`)

`PolygonDegenerateWall` removed the generic-wall gate (`GenericWallSeg`) for triangles
(`n = 3`), giving the hypothesis-free per-`t₀` parity constancy
`rcrossSum_parity_eventually_const_tri` and hence the fully unconditional triangle
ray-independence `unconditionalRayIndepInput_triangle`.  The any-`n` local-constancy
`rcrossSum_parity_eventually_const_local` (under the *local* generic-wall hypothesis at
`t₀`) was already proved there; the only `n = 3`-specific ingredient was the
degenerate-wall pairing.

This module GENERALISES the degenerate-wall pairing to arbitrary `n`, removing the
`GenericWallSeg` gate **for every polygon**, and hence produces
`∀ P, UnconditionalRayIndepInput P` unconditionally — the exact analytic core the
diagonal region-split `CutGeometry` consumes (`PolygonCutGeometry.rayIndep_of_genericity`
needed `RegionSplitGenericity = ∀ P, GenericChainInput P`, which is *provably false* on
the straddle stratum; we instead supply `UnconditionalRayIndepInput` directly, which is
all the consumer needs).

## The mechanism (the genuine new content for `n ≥ 4`)

At a probe parameter `t₀` (off boundary, `dir(t₀) ≠ 0`) partition `Fin n`:

* **W** (wall, `dirDen i t₀ = 0`): contributes `0` near `t₀`
  (`PolygonWall.rfcount_eventually_zero_of_wall`, already unconditional, any `n`).
* **R** (non-wall, end vertex on line, `ds1Of i t₀ = 0`).
* **N** (non-wall, start vertex on line, `ds0Of i t₀ = 0`).
* **Rest** (non-wall, both side functions nonzero): locally count-constant.

The local lemma paired each R-edge `i` with `cyclicNext i ∈ N`, requiring `cyclicNext i`
non-wall — which FAILS at a degenerate wall (`cyclicNext i = w` a wall with both
endpoints on the line).  No two *consecutive* edges are walls (consecutive
non-collinearity), so each wall is isolated; at a **degenerate** wall `w`, the R-orphan
`cyclicPrev w` and the N-orphan `cyclicNext w` pair *across* `w` (the wall contributing
`0`).  The pairing partner map

  `pairNext i = if cyclicNext i is a wall then cyclicNext (cyclicNext i) else cyclicNext i`

is a bijection `R → N`, and each pair `(i, pairNext i)` has locally-constant parity:

* the **standard** pair `(i, cyclicNext i)` by `rpair_count_eventually_const_noWall`;
* the **skip** pair `(i, cyclicNext (cyclicNext i))` across the degenerate wall `w` by
  the new `rpair_count_eventually_const_degenWall`: the wall edge's two endpoints are
  positively proportional from `x` (`μ > 0`), so the two on-line side values
  `s₁ = ds0Of w`, `s₂ = ds1Of w` collapse (`s₁ = μ s₂`, `μ > 0`), and
  `span_mod_two_through_vertex` (applied at the collapsed shared value) gives the pair
  parity as the span of the two FAR off-line endpoints `P.q(cyclicPrev w)`,
  `P.q(cyclicNext(cyclicNext w))` — locally constant.  (For `n = 3` these two far
  endpoints coincide, recovering the triangle's *equal counts*; for `n ≥ 4` they differ,
  and only the parity, not the counts, is paired.)

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonGeneralWall

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
open ProofsInTheBook.PolygonDegenerateWall
open ProofsInTheBook.PolygonLocalConstancy
open Filter Topology
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: no two consecutive walls (general `n`)

`dirDen_ne_zero_of_wall_of_nonpar` of `PolygonDegenerateWall` was stated for
`StrictSimplePolygon 3` but its proof only uses `eq_zero_of_det2_eq_zero`; we restate it
for general `n`, then derive the consecutive edge non-parallelism from
`noncollinear_consecutive`. -/

/-- Two edges with non-parallel edge vectors cannot both be walls at a nonzero
direction (general `n`). -/
lemma dirDen_ne_zero_of_wall_of_nonpar {P : StrictSimplePolygon n} {r₁ r₂ : Pt}
    {w k : Fin n} {t₀ : ℝ} (hrne : dirAt r₁ r₂ t₀ ≠ 0)
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

/-- `cyclicPrev (cyclicNext k) = k` (general `n`, the right inverse). -/
lemma cyclicPrev_cyclicNext (hn : 2 ≤ n) (k : Fin n) :
    cyclicPrev (cyclicNext k) = k := by
  apply Fin.ext
  rw [cyclicPrev_val, cyclicNext_val]
  have hk : k.val < n := k.isLt
  by_cases h1 : k.val + 1 < n
  · rw [if_pos h1]
    rw [if_neg (by omega : ¬ (k.val + 1 = 0))]; omega
  · rw [if_neg h1]
    rw [if_pos rfl]; omega

/-- Consecutive edge vectors are non-parallel:
`det2 (edgeVec w) (edgeVec (cyclicNext w)) ≠ 0` (any `n`). -/
lemma det2_edgeVec_next_ne_zero (P : StrictSimplePolygon n) (w : Fin n) :
    det2 (P.q (cyclicNext w) - P.q w)
        (P.q (cyclicNext (cyclicNext w)) - P.q (cyclicNext w)) ≠ 0 := by
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  set j := cyclicNext w with hj
  have hnc := P.noncollinear_consecutive j
  have hpj : cyclicPrev j = w := by rw [hj]; exact cyclicPrev_cyclicNext htwo w
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

/-- The wall edge `w` and the previous edge `cyclicPrev w` have non-parallel edge
vectors (any `n`).  Written, like the triangle version, on the forward index form. -/
lemma det2_edgeVec_prev_ne_zero (P : StrictSimplePolygon n) (w : Fin n) :
    det2 (P.q (cyclicNext w) - P.q w)
        (P.q (cyclicNext (cyclicPrev w)) - P.q (cyclicPrev w)) ≠ 0 := by
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  set p := cyclicPrev w with hp
  have hpw : cyclicNext p = w := by rw [hp]; exact cyclicNext_cyclicPrev htwo w
  have hnc := P.noncollinear_consecutive w
  have hpwp : cyclicPrev w = p := hp
  rw [hpwp] at hnc
  have e1 : P.q w - P.q p = P.q (cyclicNext p) - P.q p := by rw [hpw]
  have e2 : P.q (cyclicNext w) - P.q p
      = (P.q (cyclicNext p) - P.q p) + (P.q (cyclicNext w) - P.q w) := by
    rw [hpw]; abel
  have horient : orient (P.q p) (P.q w) (P.q (cyclicNext w))
      = det2 (P.q (cyclicNext p) - P.q p) (P.q (cyclicNext w) - P.q w) := by
    unfold orient
    rw [e1, e2, det2_add_right, PolygonLocalConstancy.det2_self, zero_add]
  rw [horient] at hnc
  rw [det2_antisymm]
  exact fun h => hnc (by linarith [h])

/-- **No two consecutive walls.**  At a nonzero direction, a wall edge's successor is
not a wall (any `n`). -/
lemma not_wall_cyclicNext_of_wall {P : StrictSimplePolygon n} {r₁ r₂ : Pt}
    {w : Fin n} {t₀ : ℝ} (hrne : dirAt r₁ r₂ t₀ ≠ 0)
    (hwall : dirDen P r₁ r₂ w t₀ = 0) :
    dirDen P r₁ r₂ (cyclicNext w) t₀ ≠ 0 :=
  dirDen_ne_zero_of_wall_of_nonpar hrne hwall (det2_edgeVec_next_ne_zero P w)

/-- **No two consecutive walls (predecessor form).** -/
lemma not_wall_cyclicPrev_of_wall {P : StrictSimplePolygon n} {r₁ r₂ : Pt}
    {w : Fin n} {t₀ : ℝ} (hrne : dirAt r₁ r₂ t₀ ≠ 0)
    (hwall : dirDen P r₁ r₂ w t₀ = 0) :
    dirDen P r₁ r₂ (cyclicPrev w) t₀ ≠ 0 :=
  dirDen_ne_zero_of_wall_of_nonpar hrne hwall (det2_edgeVec_prev_ne_zero P w)

/-! ## Part 2: the general-`n` degenerate-wall double-event pairing (the new math)

At a *degenerate* wall of edge `w` off the boundary, with `p = cyclicPrev w` and
`j = cyclicNext w` (both non-wall, by Part 1), the pair `(p, j)` carries
**locally-constant parity** — *not* equal counts (only `n = 3` gives equality).  The wall
edge contributes `0`; the two on-line side values `ds0Of w = side(P.q w)` and
`ds1Of w = side(P.q (cyclicNext w))` are positively proportional (`μ > 0`); the
`span_mod_two_through_vertex` truth table, applied at the collapsed shared on-line value,
reduces the pair parity to the span of the two far off-line endpoints `P.q(cyclicPrev w)`
and `P.q(cyclicNext (cyclicNext w))`, both locally nonzero (else `p` resp. `j` would be a
wall). -/

/-- **The general-`n` degenerate-wall pair-parity lemma.**  At a degenerate wall of edge
`w` (`n` arbitrary, `x` off the boundary), the raw pair count
`rfcount (cyclicPrev w) + rfcount (cyclicNext w)` has eventually-constant parity at
`t₀`. -/
lemma rpair_count_eventually_const_degenWall {P : StrictSimplePolygon n}
    {r₁ r₂ : Pt} {x : Pt} (hoff : ¬ OnBoundary P x) {w : Fin n} {t₀ : ℝ}
    (hrne : dirAt r₁ r₂ t₀ ≠ 0)
    (hwall : dirDen P r₁ r₂ w t₀ = 0)
    (h0 : ds0Of P r₁ r₂ x w t₀ = 0) :
    ∀ᶠ t in nhds t₀,
      (rfcount P r₁ r₂ x (cyclicPrev w) t + rfcount P r₁ r₂ x (cyclicNext w) t) % 2 =
        (rfcount P r₁ r₂ x (cyclicPrev w) t₀ + rfcount P r₁ r₂ x (cyclicNext w) t₀) % 2 := by
  classical
  set p := cyclicPrev w with hp
  set j := cyclicNext w with hj
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  have hpw : cyclicNext p = w := by rw [hp]; exact cyclicNext_cyclicPrev htwo w
  -- ds1Of w t₀ = 0.
  have h1 : ds1Of P r₁ r₂ x w t₀ = 0 := by rw [← ds_eq_at_wall hwall]; exact h0
  -- p, j non-wall.
  have hDp : dirDen P r₁ r₂ p t₀ ≠ 0 := not_wall_cyclicPrev_of_wall hrne hwall
  have hDj : dirDen P r₁ r₂ j t₀ ≠ 0 := not_wall_cyclicNext_of_wall hrne hwall
  -- side identifications.
  -- ds1Of p = ds0Of w  (end of p = P.q (cyclicNext p) = P.q w = start of w).
  have hds1p : ds1Of P r₁ r₂ x p = ds0Of P r₁ r₂ x w := by
    have : ds1Of P r₁ r₂ x p = ds0Of P r₁ r₂ x (cyclicNext p) :=
      ds1Of_eq_ds0Of_next P r₁ r₂ x p
    rw [this, hpw]
  -- ds0Of j = ds1Of w  (start of j = P.q (cyclicNext w) = end of w).
  have hds0j : ds0Of P r₁ r₂ x j = ds1Of P r₁ r₂ x w := by
    rw [hj]; exact (ds1Of_eq_ds0Of_next P r₁ r₂ x w).symm
  -- the far off-line endpoints A = ds0Of p, B = ds1Of j, nonzero at t₀ (else wall).
  have hAne : ds0Of P r₁ r₂ x p t₀ ≠ 0 := by
    intro hA
    apply hDp
    -- ds0Of p = 0 and ds1Of p = ds0Of w = 0 ⟹ dirDen p = 0.
    have hpend : ds1Of P r₁ r₂ x p t₀ = 0 := by rw [hds1p]; exact h0
    have := ds1Of_sub_ds0Of P r₁ r₂ x p t₀
    rw [hpend, hA] at this; linarith
  have hBne : ds1Of P r₁ r₂ x j t₀ ≠ 0 := by
    intro hB
    apply hDj
    have hjstart : ds0Of P r₁ r₂ x j t₀ = 0 := by rw [hds0j]; exact h1
    have := ds1Of_sub_ds0Of P r₁ r₂ x j t₀
    rw [hB, hjstart] at this; linarith
  -- positive proportionality of the wall-edge endpoints.
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
  obtain ⟨μ, hμeq⟩ := exists_smul_of_det2_zero hrne hda hdb hbx
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
      have hab : AffineMap.lineMap a b lam
          = AffineMap.lineMap (P.q w) (P.q (cyclicNext w)) lam := by
        rw [ha, hb', hj]
      rw [← hab, ← hxeq]
    rw [Edge, seg, segment_eq_image_lineMap]
    exact ⟨lam, ⟨hlam0, hlam1⟩, hxeq'⟩
  -- pointwise: ds0Of w t = μ * ds1Of w t.
  have hprop : ∀ t, ds0Of P r₁ r₂ x w t = μ * ds1Of P r₁ r₂ x w t := by
    intro t
    have e0 : ds0Of P r₁ r₂ x w t = det2 (dirAt r₁ r₂ t) (a - x) := rfl
    have e1 : ds1Of P r₁ r₂ x w t = det2 (dirAt r₁ r₂ t) (b - x) := by
      rw [hb', hj]; rfl
    rw [e0, e1, hμeq, det2_smul_right]
  -- ===== forward (tau) facts =====
  -- ray reaches P.q w = a (end of p) at dirTau p t₀, and P.q (cyclicNext w) = b
  -- (start of j) at dirTau j t₀, with dirTau p t₀ = μ dirTau j t₀, μ>0, both nonzero.
  -- event for p: ds1Of p t₀ = 0 ⟹ rU p t₀ = 1 ⟹ x + dirTau p t₀ • dir = P.q (cyclicNext p) = a.
  have hcep : x + dirTau P r₁ r₂ x p t₀ • dirAt r₁ r₂ t₀ = a := by
    have hsp : ds1Of P r₁ r₂ x p t₀ = 0 := by rw [hds1p]; exact h0
    have hce := r_cross_eq P (dirAt r₁ r₂ t₀) x p
      (show det2 (dirAt r₁ r₂ t₀) (P.q (cyclicNext p) - P.q p) ≠ 0 from hDp)
    rw [rU_eq_one_of_event hDp hsp, AffineMap.lineMap_apply_one] at hce
    rw [dirTau_eq_rTau, hce, hpw, ha]
  -- event for j: ds0Of j t₀ = 0 ⟹ rU j t₀ = 0 ⟹ x + dirTau j t₀ • dir = P.q j = b.
  have hcej : x + dirTau P r₁ r₂ x j t₀ • dirAt r₁ r₂ t₀ = b := by
    have hDj' : det2 (dirAt r₁ r₂ t₀) (P.q (cyclicNext j) - P.q j) ≠ 0 := hDj
    have hce := r_cross_eq P (dirAt r₁ r₂ t₀) x j hDj'
    have hrU0 : rU P (dirAt r₁ r₂ t₀) x j = 0 := by
      rw [rU, div_eq_zero_iff]; left
      have hjz : ds0Of P r₁ r₂ x j t₀ = 0 := by rw [hds0j]; exact h1
      have hsj : det2 (dirAt r₁ r₂ t₀) (P.q j - x) = 0 := hjz
      have hneg : det2 (dirAt r₁ r₂ t₀) (x - P.q j)
          = - det2 (dirAt r₁ r₂ t₀) (P.q j - x) := by
        unfold det2; simp only [PiLp.sub_apply]; ring
      rw [hneg, hsj, neg_zero]
    rw [hrU0, AffineMap.lineMap_apply_zero] at hce
    rw [dirTau_eq_rTau, hce, hb']
  -- dirTau p t₀ = μ * dirTau j t₀.
  have hτprop : dirTau P r₁ r₂ x p t₀ = μ * dirTau P r₁ r₂ x j t₀ := by
    have ep : dirTau P r₁ r₂ x p t₀ • dirAt r₁ r₂ t₀ = a - x := by
      rw [← hcep]; abel
    have ej : dirTau P r₁ r₂ x j t₀ • dirAt r₁ r₂ t₀ = b - x := by
      rw [← hcej]; abel
    have : dirTau P r₁ r₂ x p t₀ • dirAt r₁ r₂ t₀
        = (μ * dirTau P r₁ r₂ x j t₀) • dirAt r₁ r₂ t₀ := by
      rw [ep, hμeq, ← ej, ← mul_smul]
    have hsub : (dirTau P r₁ r₂ x p t₀ - μ * dirTau P r₁ r₂ x j t₀) • dirAt r₁ r₂ t₀ = 0 := by
      rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.mp hsub with hc | hc
    · linarith [hc]
    · exact absurd hc hrne
  -- dirTau j t₀ ≠ 0 (off boundary; else ray reaches b = P.q j at τ=0, i.e. x = P.q j).
  have hτjne : dirTau P r₁ r₂ x j t₀ ≠ 0 := by
    intro hz
    rw [hz, zero_smul, add_zero] at hcej
    apply hoff
    exact ⟨j, by rw [hcej, hb', hj, Edge]; exact left_mem_segment ℝ _ _⟩
  have hctau_p := continuousAt_dirTau_of_noWall (P := P) (x := x) hDp
  have hctau_j := continuousAt_dirTau_of_noWall (P := P) (x := x) hDj
  -- the two forward guards agree in sign near t₀.
  rcases lt_or_gt_of_ne hτjne with hjneg | hjpos
  · -- both negative: both counts are 0 near t₀, pair sum ≡ 0.
    have hpneg : dirTau P r₁ r₂ x p t₀ < 0 := by
      rw [hτprop]; exact mul_neg_of_pos_of_neg hμpos hjneg
    have evj : ∀ᶠ t in nhds t₀, dirTau P r₁ r₂ x j t < 0 := by
      filter_upwards [hctau_j.tendsto.eventually_lt_const hjneg] with t ht using ht
    have evp : ∀ᶠ t in nhds t₀, dirTau P r₁ r₂ x p t < 0 := by
      filter_upwards [hctau_p.tendsto.eventually_lt_const hpneg] with t ht using ht
    have hpc0 : ∀ t, dirTau P r₁ r₂ x p t < 0 → rfcount P r₁ r₂ x p t = 0 := by
      intro t ht; rw [rfcount_eq, if_neg]; rw [rstatusOf_iff]; rintro ⟨_, hτ⟩; linarith
    have hjc0 : ∀ t, dirTau P r₁ r₂ x j t < 0 → rfcount P r₁ r₂ x j t = 0 := by
      intro t ht; rw [rfcount_eq, if_neg]; rw [rstatusOf_iff]; rintro ⟨_, hτ⟩; linarith
    filter_upwards [evj, evp] with t htj htp
    rw [hpc0 t htp, hjc0 t htj, hpc0 t₀ hpneg, hjc0 t₀ hjneg]
  · -- both positive: span_mod_two_through_vertex collapses the on-line pair.
    have hppos : 0 < dirTau P r₁ r₂ x p t₀ := by rw [hτprop]; positivity
    have evj : ∀ᶠ t in nhds t₀, 0 < dirTau P r₁ r₂ x j t := by
      filter_upwards [hctau_j.tendsto.eventually_const_lt hjpos] with t ht using ht
    have evp : ∀ᶠ t in nhds t₀, 0 < dirTau P r₁ r₂ x p t := by
      filter_upwards [hctau_p.tendsto.eventually_const_lt hppos] with t ht using ht
    -- A = ds0Of p, B = ds1Of j nonzero near t₀.
    have hcA := (continuous_ds0Of P r₁ r₂ x p).continuousAt (x := t₀)
    have hcB := (continuous_ds1Of P r₁ r₂ x j).continuousAt (x := t₀)
    have evA : ∀ᶠ t in nhds t₀, ds0Of P r₁ r₂ x p t ≠ 0 := by
      rcases lt_or_gt_of_ne hAne with hlt | hgt
      · filter_upwards [hcA.tendsto.eventually_lt_const hlt] with t ht using ne_of_lt ht
      · filter_upwards [hcA.tendsto.eventually_const_lt hgt] with t ht using ne_of_gt ht
    have evB : ∀ᶠ t in nhds t₀, ds1Of P r₁ r₂ x j t ≠ 0 := by
      rcases lt_or_gt_of_ne hBne with hlt | hgt
      · filter_upwards [hcB.tendsto.eventually_lt_const hlt] with t ht using ne_of_lt ht
      · filter_upwards [hcB.tendsto.eventually_const_lt hgt] with t ht using ne_of_gt ht
    -- the span of the far endpoints A, B is locally constant.
    have hABev : ∀ᶠ t in nhds t₀,
        (Span (ds0Of P r₁ r₂ x p t) (ds1Of P r₁ r₂ x j t) ↔
          Span (ds0Of P r₁ r₂ x p t₀) (ds1Of P r₁ r₂ x j t₀)) :=
      span_const_two_sides (continuous_ds0Of P r₁ r₂ x p)
        (continuous_ds1Of P r₁ r₂ x j) hAne hBne
    -- forward status = span (both edges non-wall, forward guard locally positive).
    have hstat_p : ∀ t, 0 < dirTau P r₁ r₂ x p t →
        (if rstatusOf P r₁ r₂ x p t then 1 else 0) =
          (if Span (ds0Of P r₁ r₂ x p t) (ds1Of P r₁ r₂ x p t) then 1 else 0) := by
      intro t hτ
      by_cases hsp : Span (ds0Of P r₁ r₂ x p t) (ds1Of P r₁ r₂ x p t)
      · rw [if_pos hsp, if_pos (by rw [rstatusOf_iff]; exact ⟨hsp, le_of_lt hτ⟩)]
      · rw [if_neg hsp, if_neg (by rw [rstatusOf_iff]; rintro ⟨hh, _⟩; exact hsp hh)]
    have hstat_j : ∀ t, 0 < dirTau P r₁ r₂ x j t →
        (if rstatusOf P r₁ r₂ x j t then 1 else 0) =
          (if Span (ds0Of P r₁ r₂ x j t) (ds1Of P r₁ r₂ x j t) then 1 else 0) := by
      intro t hτ
      by_cases hsp : Span (ds0Of P r₁ r₂ x j t) (ds1Of P r₁ r₂ x j t)
      · rw [if_pos hsp, if_pos (by rw [rstatusOf_iff]; exact ⟨hsp, le_of_lt hτ⟩)]
      · rw [if_neg hsp, if_neg (by rw [rstatusOf_iff]; rintro ⟨hh, _⟩; exact hsp hh)]
    -- the collapse: ds1Of p = μ * ds0Of j  (= μ * ds1Of w via ds0Of w = μ ds1Of w).
    -- ds1Of p t = ds0Of w t = μ * ds1Of w t = μ * ds0Of j t.
    have hcollapse : ∀ t, ds1Of P r₁ r₂ x p t = μ * ds0Of P r₁ r₂ x j t := by
      intro t
      have e1 : ds1Of P r₁ r₂ x p t = ds0Of P r₁ r₂ x w t := by rw [hds1p]
      have e2 : ds0Of P r₁ r₂ x j t = ds1Of P r₁ r₂ x w t := by rw [hds0j]
      rw [e1, e2, hprop t]
    -- the pair-span parity collapses to Span(A, B) via span_mod_two_through_vertex.
    have hpairspan : ∀ t, ds0Of P r₁ r₂ x p t ≠ 0 → ds1Of P r₁ r₂ x j t ≠ 0 →
        ((if Span (ds0Of P r₁ r₂ x p t) (ds1Of P r₁ r₂ x p t) then 1 else 0) +
          (if Span (ds0Of P r₁ r₂ x j t) (ds1Of P r₁ r₂ x j t) then 1 else 0)) % 2 =
          (if Span (ds0Of P r₁ r₂ x p t) (ds1Of P r₁ r₂ x j t) then 1 else 0) := by
      intro t hAt hBt
      -- ds1Of p t = μ * ds0Of j t, μ>0 ⟹ Span(A, ds1Of p) ↔ Span(A, ds0Of j).
      set A := ds0Of P r₁ r₂ x p t with hA
      set sj := ds0Of P r₁ r₂ x j t with hsj
      set B := ds1Of P r₁ r₂ x j t with hB
      have hsp1 : ds1Of P r₁ r₂ x p t = μ * sj := by rw [hsj]; exact hcollapse t
      -- Span(A, μ sj) ↔ Span(A, sj).
      have hspanA : Span A (μ * sj) ↔ Span A sj := by
        constructor
        · intro h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, by nlinarith [hμpos]⟩
          · exact Or.inr ⟨by nlinarith [hμpos], h2⟩
        · intro h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, by positivity⟩
          · exact Or.inr ⟨by nlinarith [hμpos], h2⟩
      rw [hsp1]
      rw [show (if Span A (μ * sj) then (1:ℕ) else 0)
          = (if Span A sj then 1 else 0) from by
        by_cases h : Span A sj
        · rw [if_pos (hspanA.mpr h), if_pos h]
        · rw [if_neg (fun hc => h (hspanA.mp hc)), if_neg h]]
      -- now span_mod_two_through_vertex with shared value sj.
      exact span_mod_two_through_vertex hAt hBt
    -- assemble.
    filter_upwards [evj, evp, evA, evB, hABev] with t htj htp hAt hBt hABt
    have key : (rfcount P r₁ r₂ x p t + rfcount P r₁ r₂ x j t) % 2 =
        (if Span (ds0Of P r₁ r₂ x p t₀) (ds1Of P r₁ r₂ x j t₀) then 1 else 0) := by
      rw [rfcount_eq, rfcount_eq, hstat_p t htp, hstat_j t htj, hpairspan t hAt hBt]
      by_cases hsp : Span (ds0Of P r₁ r₂ x p t) (ds1Of P r₁ r₂ x j t)
      · rw [if_pos hsp, if_pos (hABt.mp hsp)]
      · rw [if_neg hsp, if_neg (fun hc => hsp (hABt.mpr hc))]
    have key0 : (rfcount P r₁ r₂ x p t₀ + rfcount P r₁ r₂ x j t₀) % 2 =
        (if Span (ds0Of P r₁ r₂ x p t₀) (ds1Of P r₁ r₂ x j t₀) then 1 else 0) := by
      rw [rfcount_eq, rfcount_eq, hstat_p t₀ hppos, hstat_j t₀ hjpos, hpairspan t₀ hAne hBne]
    rw [key, key0]

/-! ## Part 3: the general-`n` hypothesis-free per-`t₀` parity constancy

We assemble the per-`t₀` parity constancy WITHOUT any generic-wall hypothesis, by the
wall-skipping pairing.  Partition `Fin n` into the walls `W`, the non-wall R-events
(`ds1Of = 0`), the non-wall N-events (`ds0Of = 0`), and the non-wall `Rest`.  The
partner map `pairNext` sends each R-edge `i` to `cyclicNext i` when that is non-wall, and
to `cyclicNext (cyclicNext i)` when `cyclicNext i` is a (degenerate) wall.  It is a
bijection `R → N`, and each pair `(i, pairNext i)` has locally-constant parity (standard
vertex event, or the degenerate-wall pair of Part 2). -/

/-- The wall-skipping pairing partner of an R-edge. -/
def pairNext (P : StrictSimplePolygon n) (r₁ r₂ : Pt) (t₀ : ℝ) (i : Fin n) : Fin n :=
  if dirDen P r₁ r₂ (cyclicNext i) t₀ = 0 then cyclicNext (cyclicNext i) else cyclicNext i

/-- **General-`n` hypothesis-free per-`t₀` eventual parity constancy.**  Off the
boundary, with `dirAt r₁ r₂ t₀ ≠ 0`, the raw crossing parity is eventually constant at
`t₀` — no generic-wall hypothesis (degenerate walls handled by the skip pairing). -/
lemma rcrossSum_parity_eventually_const_general {P : StrictSimplePolygon n} {r₁ r₂ : Pt}
    {x : Pt} (hoff : ¬ OnBoundary P x) {t₀ : ℝ} (_ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1)
    (hrne : dirAt r₁ r₂ t₀ ≠ 0) :
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
  have hshare : ∀ i, ds0Of P r₁ r₂ x (cyclicNext i) t₀ = ds1Of P r₁ r₂ x i t₀ :=
    fun i => rfl
  -- a wall whose start vertex is on the line (`ds0Of = 0`) is degenerate at both ends.
  -- the partner map sends R into N.
  have hpairMemN : ∀ i ∈ R, pairNext P r₁ r₂ t₀ i ∈ N := by
    intro i hi
    rw [hRmem] at hi
    unfold pairNext
    by_cases hwk : dirDen P r₁ r₂ (cyclicNext i) t₀ = 0
    · -- cyclicNext i = w is a degenerate wall; partner = cyclicNext w ∈ N.
      rw [if_pos hwk, hNmem]
      -- ds0Of (cyclicNext i) = ds1Of i = 0, so the wall cyclicNext i is degenerate.
      have hw0 : ds0Of P r₁ r₂ x (cyclicNext i) t₀ = 0 := by rw [hshare i]; exact hi.2
      have hw1 : ds1Of P r₁ r₂ x (cyclicNext i) t₀ = 0 := by
        rw [← ds_eq_at_wall hwk]; exact hw0
      constructor
      · exact not_wall_cyclicNext_of_wall hrne hwk
      · -- ds0Of (cyclicNext (cyclicNext i)) = ds1Of (cyclicNext i) = 0.
        rw [hshare (cyclicNext i)]; exact hw1
    · -- cyclicNext i non-wall; partner = cyclicNext i ∈ N.
      rw [if_neg hwk, hNmem]
      exact ⟨hwk, by rw [hshare i]; exact hi.2⟩
  -- pairNext is injective on R.
  have hpairInj : ∀ i ∈ R, ∀ i' ∈ R,
      pairNext P r₁ r₂ t₀ i = pairNext P r₁ r₂ t₀ i' → i = i' := by
    intro i hi i' hi' heq
    -- recover cyclicNext i from the partner: cyclicPrev (partner) is cyclicNext i
    -- (standard) or cyclicNext i (skip via the wall).  Use: cyclicNext i = cyclicNext i'.
    have hkey : cyclicNext i = cyclicNext i' := by
      -- from heq we get cyclicNext i = cyclicNext i' by applying cyclicPrev appropriately;
      -- branch on the two if-conditions for i and i'.
      unfold pairNext at heq
      by_cases hwi : dirDen P r₁ r₂ (cyclicNext i) t₀ = 0 <;>
        by_cases hwi' : dirDen P r₁ r₂ (cyclicNext i') t₀ = 0
      · rw [if_pos hwi, if_pos hwi'] at heq
        -- cyclicNext (cyclicNext i) = cyclicNext (cyclicNext i') ⟹ cyclicNext i = cyclicNext i'.
        exact cyclicNext_injective heq
      · rw [if_pos hwi, if_neg hwi'] at heq
        -- cyclicNext (cyclicNext i) = cyclicNext i'.  Then cyclicNext i = i'
        -- (apply cyclicNext_injective) ; but cyclicNext i is a wall (hwi), so i' would be a
        -- wall, contradicting i' ∈ R.
        exfalso
        have hci : cyclicNext i = i' := cyclicNext_injective heq
        have : dirDen P r₁ r₂ i' t₀ = 0 := by rw [← hci]; exact hwi
        exact ((hRmem i').mp hi').1 this
      · rw [if_neg hwi, if_pos hwi'] at heq
        exfalso
        have hci : i = cyclicNext i' := cyclicNext_injective heq
        have : dirDen P r₁ r₂ i t₀ = 0 := by rw [hci]; exact hwi'
        exact ((hRmem i).mp hi).1 this
      · rw [if_neg hwi, if_neg hwi'] at heq
        exact heq
    exact cyclicNext_injective hkey
  -- pairNext is surjective onto N.
  have hpairSurj : ∀ m ∈ N, ∃ i ∈ R, pairNext P r₁ r₂ t₀ i = m := by
    intro m hm
    rw [hNmem] at hm
    -- ds1Of (cyclicPrev m) = ds0Of m = 0.
    have hpe : ds1Of P r₁ r₂ x (cyclicPrev m) t₀ = 0 := by
      have := hshare (cyclicPrev m)
      rw [cyclicNext_cyclicPrev htwo m] at this; rw [← this]; exact hm.2
    by_cases hwp : dirDen P r₁ r₂ (cyclicPrev m) t₀ = 0
    · -- cyclicPrev m = w is a degenerate wall (end on line); partner of cyclicPrev w is m.
      -- cyclicPrev w non-wall, in R, ds1Of (cyclicPrev w) = ds0Of w = ds1Of w = 0.
      set w := cyclicPrev m with hwdef
      have hw1 : ds1Of P r₁ r₂ x w t₀ = 0 := hpe
      have hw0 : ds0Of P r₁ r₂ x w t₀ = 0 := by rw [ds_eq_at_wall hwp]; exact hw1
      refine ⟨cyclicPrev w, ?_, ?_⟩
      · rw [hRmem]
        refine ⟨not_wall_cyclicPrev_of_wall hrne hwp, ?_⟩
        -- ds1Of (cyclicPrev w) = ds0Of w = 0.
        have := hshare (cyclicPrev w)
        rw [cyclicNext_cyclicPrev htwo w] at this; rw [← this]; exact hw0
      · -- pairNext (cyclicPrev w): cyclicNext (cyclicPrev w) = w is a wall, so skip.
        unfold pairNext
        rw [if_pos (by rw [cyclicNext_cyclicPrev htwo w]; exact hwp)]
        rw [cyclicNext_cyclicPrev htwo w, hwdef, cyclicNext_cyclicPrev htwo m]
    · -- cyclicPrev m non-wall, in R; partner = cyclicNext (cyclicPrev m) = m.
      refine ⟨cyclicPrev m, ?_, ?_⟩
      · rw [hRmem]; exact ⟨hwp, hpe⟩
      · unfold pairNext
        rw [if_neg (by rw [cyclicNext_cyclicPrev htwo m]; exact hm.1)]
        exact cyclicNext_cyclicPrev htwo m
  -- N = R.image pairNext.
  have hNimg : N = R.image (pairNext P r₁ r₂ t₀) := by
    apply Finset.ext; intro m
    rw [Finset.mem_image]
    constructor
    · intro hmN; obtain ⟨i, hiR, hi⟩ := hpairSurj m hmN; exact ⟨i, hiR, hi⟩
    · rintro ⟨i, hiR, rfl⟩; exact hpairMemN i hiR
  -- disjointness.
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
      ∑ i ∈ R, rfcount P r₁ r₂ x (pairNext P r₁ r₂ t₀ i) t := by
    intro t
    rw [hNimg, Finset.sum_image]
    intro a ha b hb hh; exact hpairInj a ha b hb hh
  -- eventual: wall edges vanish.
  have hwallEv : ∀ᶠ t in nhds t₀, ∀ i ∈ W, rfcount P r₁ r₂ x i t = 0 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [hWmem] at hi
    exact rfcount_eventually_zero_of_wall hoff hrne hi
  -- eventual: each (R, pairNext) pair has constant parity.
  have hpairs : ∀ᶠ t in nhds t₀, ∀ i ∈ R,
      (rfcount P r₁ r₂ x i t + rfcount P r₁ r₂ x (pairNext P r₁ r₂ t₀ i) t) % 2 =
        (rfcount P r₁ r₂ x i t₀ + rfcount P r₁ r₂ x (pairNext P r₁ r₂ t₀ i) t₀) % 2 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hir := (hRmem i).mp hi
    unfold pairNext
    by_cases hwk : dirDen P r₁ r₂ (cyclicNext i) t₀ = 0
    · -- skip pair across the degenerate wall w = cyclicNext i.  i = cyclicPrev w.
      rw [if_pos hwk]
      set w := cyclicNext i with hwdef
      have hiw : cyclicPrev w = i := by rw [hwdef]; exact cyclicPrev_cyclicNext htwo i
      have hw0 : ds0Of P r₁ r₂ x w t₀ = 0 := by rw [hwdef, hshare i]; exact hir.2
      have := rpair_count_eventually_const_degenWall hoff hrne hwk hw0
      rw [hiw] at this
      -- `this` is about (cyclicPrev w, cyclicNext w) = (i, cyclicNext (cyclicNext i)).
      exact this
    · -- standard pair (i, cyclicNext i), both non-wall.
      rw [if_neg hwk]
      exact rpair_count_eventually_const_noWall hoff hir.1 hwk hir.2
  -- eventual: Rest edges count-constant.
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
  set PN : ℝ → ℕ := fun s => ∑ i ∈ R, rfcount P r₁ r₂ x (pairNext P r₁ r₂ t₀ i) s with hPN
  set PE : ℝ → ℕ := fun s => ∑ i ∈ Rest, rfcount P r₁ r₂ x i s with hPE
  have hpairR : (PR t + PN t) % 2 = (PR t₀ + PN t₀) % 2 := by
    rw [hPR, hPN]
    have h1 : (∑ i ∈ R, rfcount P r₁ r₂ x i t)
          + (∑ i ∈ R, rfcount P r₁ r₂ x (pairNext P r₁ r₂ t₀ i) t)
        = ∑ i ∈ R, (rfcount P r₁ r₂ x i t + rfcount P r₁ r₂ x (pairNext P r₁ r₂ t₀ i) t) := by
      rw [Finset.sum_add_distrib]
    have h2 : (∑ i ∈ R, rfcount P r₁ r₂ x i t₀)
          + (∑ i ∈ R, rfcount P r₁ r₂ x (pairNext P r₁ r₂ t₀ i) t₀)
        = ∑ i ∈ R, (rfcount P r₁ r₂ x i t₀
            + rfcount P r₁ r₂ x (pairNext P r₁ r₂ t₀ i) t₀) := by
      rw [Finset.sum_add_distrib]
    rw [h1, h2, Finset.sum_nat_mod, Finset.sum_nat_mod
      (s := R) (f := fun i => rfcount P r₁ r₂ x i t₀
        + rfcount P r₁ r₂ x (pairNext P r₁ r₂ t₀ i) t₀)]
    congr 1
    exact Finset.sum_congr rfl (fun i hi => hp i hi)
  have hrestEq : PE t = PE t₀ := by
    rw [hPE]; exact Finset.sum_congr rfl (fun i hi => hr i hi)
  show (0 + PR t + PN t + PE t) % 2 = (0 + PR t₀ + PN t₀ + PE t₀) % 2
  have e1 : 0 + PR t + PN t + PE t = (PR t + PN t) + PE t := by ring
  have e2 : 0 + PR t₀ + PN t₀ + PE t₀ = (PR t₀ + PN t₀) + PE t₀ := by ring
  rw [e1, e2, Nat.add_mod, hpairR, hrestEq, ← Nat.add_mod]

/-! ## Part 4: global parity constancy on `[0,1]` and the wall-global ray independence
(general `n`)

The `Icc 0 1` engine (preconnectedness + local constancy), fed by the *hypothesis-free*
per-`t₀` lemma of Part 3, gives equal endpoint parities for any segment that avoids the
zero direction — for ANY `n`, no `GenericWallSeg`. -/

/-- The raw parity along the segment is locally constant on `Icc 0 1` (general `n`,
hypothesis-free at each wall). -/
lemma rParity_locallyConstant_general {P : StrictSimplePolygon n} {r₁ r₂ : Pt} {x : Pt}
    (hoff : ¬ OnBoundary P x) (hz : SegAvoidsZero r₁ r₂) :
    IsLocallyConstant (rParity P r₁ r₂ x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t₀
  have hev := rcrossSum_parity_eventually_const_general hoff t₀.2 (hz t₀.val t₀.2)
  exact (continuous_subtype_val.continuousAt (x := t₀)).tendsto.eventually hev

/-- **Global parity constancy on the segment (general `n`).**  Under avoid-zero, the raw
crossing parities at the two endpoint directions agree — no generic-wall hypothesis. -/
lemma rcrossSum_parity_endpoints_general {P : StrictSimplePolygon n} {r₁ r₂ : Pt} {x : Pt}
    (hoff : ¬ OnBoundary P x) (hz : SegAvoidsZero r₁ r₂) :
    rcrossSum P r₁ r₂ x 0 % 2 = rcrossSum P r₁ r₂ x 1 % 2 := by
  have hLC := rParity_locallyConstant_general hoff hz
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have := hLC.apply_eq_of_preconnectedSpace (⟨0, h0⟩ : ↥(Set.Icc (0:ℝ) 1)) ⟨1, h1⟩
  unfold rParity at this
  exact this

/-- **Wall-global crossing-number parity independence (general `n`, no `GenericWallSeg`).** -/
theorem crossingNumber'_wallGlobal_general {P : StrictSimplePolygon n} (ρ σ : RayDirection P)
    {x : Pt} (hoff : ¬ OnBoundary P x) (hz : SegAvoidsZero ρ.r σ.r) :
    CrossingNumber' P ρ x % 2 = CrossingNumber' P σ x % 2 := by
  have hcr0 : CrossingNumber' P ρ x = rcrossSum P ρ.r σ.r x 0 :=
    crossingNumber'_eq_rcrossSum P ρ.r σ.r x 0 ρ (dirAt_zero ρ.r σ.r).symm
  have hcr1 : CrossingNumber' P σ x = rcrossSum P ρ.r σ.r x 1 :=
    crossingNumber'_eq_rcrossSum P ρ.r σ.r x 1 σ (dirAt_one ρ.r σ.r).symm
  rw [hcr0, hcr1]
  exact rcrossSum_parity_endpoints_general hoff hz

/-- **Wall-global region-indicator ray independence (general `n`).** -/
theorem closedRegion'_wallGlobal_general {P : StrictSimplePolygon n} (ρ σ : RayDirection P)
    {x : Pt} (hoff : ¬ OnBoundary P x) (hz : SegAvoidsZero ρ.r σ.r) :
    ClosedRegion' P ρ x ↔ ClosedRegion' P σ x := by
  unfold ClosedRegion'
  have hpar := crossingNumber'_wallGlobal_general ρ σ hoff hz
  constructor
  · rintro (hb | ho)
    · exact Or.inl hb
    · exact Or.inr ((odd_iff_of_mod_two_eq hpar).mp ho)
  · rintro (hb | ho)
    · exact Or.inl hb
    · exact Or.inr ((odd_iff_of_mod_two_eq hpar).mpr ho)

/-! ## Part 5: the avoid-zero chain and the unconditional general-`n` ray independence

Two arbitrary ray directions are connected through a single intermediate `μ = mkPt 1 s`
whose slope avoids the (finite) edge slopes and the two antiparallel slopes of `ρ.r`,
`σ.r` (so both connecting segments avoid the zero direction).  No genericity at the walls
is required — `closedRegion'_wallGlobal_general` handles every wall, generic or
degenerate.  Composing the two transports discharges `UnconditionalRayIndepInput P` for
EVERY polygon, unconditionally. -/

/-- **Avoid-zero chain (general `n`).**  Any two ray directions admit a connecting
intermediate `μ` whose two segments both avoid the zero direction; the region indicator
is direction-independent off the boundary. -/
theorem closedRegion'_chain_general {P : StrictSimplePolygon n} (ρ σ : RayDirection P)
    {x : Pt} (hoff : ¬ OnBoundary P x) :
    ClosedRegion' P ρ x ↔ ClosedRegion' P σ x := by
  classical
  let bad : Finset ℝ :=
    (Finset.univ.image fun i : Fin n => badSlope (edgeVec P i)) ∪
      {antiSlope ρ.r, antiSlope σ.r}
  obtain ⟨s, hsbad⟩ := bad.exists_notMem
  have hsedge : ∀ i : Fin n, s ≠ badSlope (edgeVec P i) := by
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
  exact (closedRegion'_wallGlobal_general ρ μ hoff hzρ).trans
    (closedRegion'_wallGlobal_general μ σ hoff hzσ)

/-- **The unconditional general-`n` ray-independence input.**  For EVERY polygon, the
off-boundary region indicator is independent of the ray direction —
`PolygonFinish.UnconditionalRayIndepInput`, proved **unconditionally** (every wall,
generic or degenerate, handled).  This is the analytic core the diagonal region-split
`CutGeometry` consumes, supplied directly (the `GenericChainInput` proxy being provably
false on the straddle stratum). -/
theorem unconditionalRayIndepInput_general (P : StrictSimplePolygon n) :
    UnconditionalRayIndepInput P :=
  fun ρ σ _ hoff => closedRegion'_chain_general ρ σ hoff

end

end ProofsInTheBook.PolygonGeneralWall
