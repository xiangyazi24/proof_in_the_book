import ProofsInTheBook.ZinanCh36LobeChain
import ProofsInTheBook.ZinanCh36LobeWiring
import ProofsInTheBook.PolygonWindingZero

/-!
# `ZinanCh36NonInterleave` — the same-side lobe noninterleaving theorem (Ch36).

This file assembles the last geometric piece of Chapter 36: two same-side boundary
lobes of a strict simple polygon cannot interleave along a generic line.  The proof is the
**fixed-direction parity sweep** of the committed design
(`HANDOFF/ch36-lobes-master-design.md`,
`HANDOFF/design-rounds/ch36-lobe-pairing-comb.md`), built on the banked substrate:

* `ZinanCh36ArcSweep` — the open-chain forward-ray crossing count `Chain.rayCount` and its
  moving-base parity invariance (`rayCountParity_constant_on_segment`,
  `rayCount_zero_of_coordMax`), the along-direction coordinate `lineCoord`, and the
  ray-side identity `side_ray_eta`.
* `ZinanCh36LobeChain` — the clipped chain `lobeChain` of an `UpperLobe`, its feet, and
  `carrier_side_zero_imp_foot` (the carrier meets the base line only at the two feet).
* `ZinanCh36Lobes` — the abstract 1-D sign telescope `sum_crossInd_emod_two`.

## Strategy (the fixed sweep)

Fix the reference direction `r = ρ.r`.  Pick a sweep direction `η = perpVec r + λ•r` with
`det2 r η = ‖r‖² > 0` and `λ` avoiding the finitely many chain-segment parallelisms, so `η` is
transverse to both lobe chains.  Pick `u₀ ∈ (τ(Y.start), τ(X.lastEdge))` avoiding `X`'s feet
coords.  Set `z₀ = x + u₀•r` (on the base line).

* `N(z₀) := (lobeChain X).rayCount η z₀` is ODD: along the base line `z₀` sits strictly between
  `X`'s two feet, the chain's far endpoint sides straddle, and (because `X` lives in the closed
  upper halfplane and the forward `η`-ray points up, `det2 r η > 0`) every span-crossing of the
  chain is forward — so `rayCount` is exactly the abstract straddle count, which is odd.
* The path `z₀ → footFirst Y → (Y's chain) → footLast Y → z_R` (with `z_R` far along `r` beyond
  every `X`-vertex coord) avoids `X`'s carrier and stays endpoint-safe, so the parity is
  transported unchanged; but `N(z_R) = 0` (far point), forcing `even = odd`, a contradiction.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36NonInterleave

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonWindingZero
open ProofsInTheBook.ZinanCh36Lobes
open ProofsInTheBook.ZinanCh36ArcSweep
open ProofsInTheBook.ZinanCh36LobeChain
open ProofsInTheBook.ZinanCh36LobeWiring
open Filter Topology
open scoped RealInnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ## §0. The sweep direction and the basic determinant identities -/

/-- The sweep direction `η = perpVec r + λ•r`.  Its determinant against `r` is `‖r‖² > 0`
(independent of `λ`), so the forward `η`-ray points to the `side r`-positive halfplane. -/
def sweepDir (r : Pt) (lam : ℝ) : Pt := perpVec r + lam • r

/-- `det2 r (sweepDir r lam) = det2 r (perpVec r) > 0`: the `r`-component drops out. -/
lemma det2_r_sweepDir (r : Pt) (lam : ℝ) :
    det2 r (sweepDir r lam) = det2 r (perpVec r) := by
  unfold sweepDir
  rw [det2_add_right, det2_smul_right, det2_self, mul_zero, add_zero]

lemma det2_r_sweepDir_pos {r : Pt} (hr : r ≠ 0) (lam : ℝ) :
    0 < det2 r (sweepDir r lam) := by
  rw [det2_r_sweepDir]; exact det2_perpVec_pos hr

/-- `det2 (sweepDir r lam) v = det2 (perpVec r) v + lam · det2 r v`: affine in `lam`. -/
lemma det2_sweepDir_left (r : Pt) (lam : ℝ) (v : Pt) :
    det2 (sweepDir r lam) v = det2 (perpVec r) v + lam * det2 r v := by
  unfold sweepDir
  rw [det2_add_left, det2_smul_left]

/-! ## §1. The along-line geometry: feet sides and the `crossTau` ↔ `lineCoord` bridge

All four feet and the base points live on the line `x + ℝ•r`.  Their `side η` against the
ray line through a base `x + u₀•r` and their `lineCoord` are simple affine functions of the
along-line coordinate `τ`. -/

variable {P : StrictSimplePolygon n} {ρ : RayDirection P} {x : Pt}

/-- **`side η` of a line point.**  For a base point `x + u₀•r` on the line and any line point
`x + τ•r`, the `side η` coordinate is `(u₀ − τ)·det2 r η`. -/
lemma side_eta_linePoint (r η : Pt) (x : Pt) (u₀ τ : ℝ) :
    side η (x + u₀ • r) (x + τ • r) = (u₀ - τ) * det2 r η := by
  unfold side
  have hsub : (x + τ • r) - (x + u₀ • r) = (τ - u₀) • r := by module
  rw [hsub, det2_smul_right]
  have hflip : det2 η r = - det2 r η := det2_antisymm η r
  rw [hflip]; ring

/-- **`lineCoord` of a line point.**  For base `x + u₀•r` (and `0 < det2 r η`), the along-`r`
coordinate of `x + τ•r` is `τ − u₀`. -/
lemma lineCoord_linePoint (r η : Pt) (x : Pt) (u₀ τ : ℝ) (hrη : det2 r η ≠ 0) :
    lineCoord r η (x + u₀ • r) (x + τ • r) = τ - u₀ := by
  unfold lineCoord
  have hsub : (x + τ • r) - (x + u₀ • r) = (τ - u₀) • r := by module
  rw [hsub, det2_smul_left]
  field_simp

/-! ## §2. The forward-only `rayCount` parity of a lobe chain

The forward `η`-ray from a base point `z₀ = x + u₀•r` on the base line, with `0 < det2 r η`,
points into the `side r`-positive halfplane (`side_ray_eta`).  Because every vertex of a lobe
chain has `side r ≥ 0` (`chainPt_side_nonneg`), every chain point has `side r ≥ 0`, so any
span-crossing of the chain by the (full) `η`-line is automatically on the *forward* ray.  Hence
`rayCount` is exactly the abstract span/straddle count, governed by the 1-D telescope. -/

/-- **Forward-only.**  For a base point `z₀ = x + u₀•r` on the base line with `0 < det2 r η`,
any span-crossing chain segment of a lobe is forward-crossed: the crossing point lies on a
chain segment (`side r ≥ 0`) and on the forward ray (`side r = segTau·det2 r η`). -/
lemma lobeChain_segCrossInd_forward (L : UpperLobe P ρ x) {η : Pt} (u₀ : ℝ)
    (hη : (lobeChain L).Transverse η)
    (hdet : 0 < det2 ρ.r η) (i : Fin L.len)
    (hspan : Span (side η (x + u₀ • ρ.r) ((lobeChain L).segA i))
                  (side η (x + u₀ • ρ.r) ((lobeChain L).segB i))) :
    0 ≤ segTau η (x + u₀ • ρ.r) ((lobeChain L).segA i) ((lobeChain L).segB i) := by
  set z₀ := x + u₀ • ρ.r with hz₀
  set a := (lobeChain L).segA i with hadef
  set b := (lobeChain L).segB i with hbdef
  have hden : det2 η (b - a) ≠ 0 := hη.2 i
  set τ := segTau η z₀ a b with hτdef
  -- the crossing point reconstructs as lineMap a b (segU).
  have hrec : z₀ + τ • η = AffineMap.lineMap a b (segU η z₀ a b) := seg_cross_eq hden
  -- side r of the crossing point read two ways.
  have hside_ray : side ρ.r x (z₀ + τ • η) = τ * det2 ρ.r η := by
    rw [side_ray_eta]
    have : side ρ.r x z₀ = 0 := by
      rw [hz₀]; exact side_ray_point u₀
    rw [this, zero_add]
  have hside_seg : side ρ.r x (AffineMap.lineMap a b (segU η z₀ a b))
      = (1 - segU η z₀ a b) * side ρ.r x a + segU η z₀ a b * side ρ.r x b :=
    side_lineMap_right ρ.r x a b _
  -- segU ∈ [0,1] (span).
  have hu := segU_mem_Icc_of_span hden hspan
  -- both endpoints of a chain segment have side r ≥ 0.
  have ha0 : 0 ≤ side ρ.r x a := by
    rw [hadef, lobeChain_segA]; exact chainPt_side_nonneg L _
  have hb0 : 0 ≤ side ρ.r x b := by
    rw [hbdef, lobeChain_segB]; exact chainPt_side_nonneg L _
  -- the crossing point has side r ≥ 0, hence τ · det2 r η ≥ 0, hence τ ≥ 0.
  have hcross_nonneg : 0 ≤ side ρ.r x (z₀ + τ • η) := by
    rw [hrec, hside_seg]
    have h1 : 0 ≤ 1 - segU η z₀ a b := by linarith [hu.2]
    have h2 : 0 ≤ segU η z₀ a b := hu.1
    positivity
  rw [hside_ray] at hcross_nonneg
  -- τ · det2 r η ≥ 0 with det2 r η > 0 ⟹ τ ≥ 0.
  nlinarith [hcross_nonneg, hdet]

/-! ### The chain-vertex side sequence and its straddle telescope -/

/-- The `side η z₀` sequence along the lobe chain's walk (a total `ℕ → ℝ` extension that agrees
with `chainPt` on `0 ≤ k ≤ len`). -/
def chainSide (L : UpperLobe P ρ x) (η : Pt) (u₀ : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then side η (x + u₀ • ρ.r) (footFirst L)
  else if L.len ≤ k then side η (x + u₀ • ρ.r) (footLast L)
  else side η (x + u₀ • ρ.r) (P.q (arcPos L.start k))

/-- `chainSide` agrees with the `side` of the chain vertex for `k ≤ len`. -/
lemma chainSide_eq_chainPt (L : UpperLobe P ρ x) (η : Pt) (u₀ : ℝ) {k : ℕ} (hk : k ≤ L.len) :
    chainSide L η u₀ k = side η (x + u₀ • ρ.r) (chainPt L ⟨k, by omega⟩) := by
  have hpos := L.len_pos
  unfold chainSide chainPt
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp
  · rw [if_neg (show ¬ k = 0 by omega)]
    by_cases hklen : k = L.len
    · subst hklen
      rw [if_pos (le_refl _), if_neg (show ¬ L.len = 0 by omega), if_pos rfl]
    · rw [if_neg (show ¬ L.len ≤ k by omega), if_neg (show ¬ k = 0 by omega),
        if_neg hklen]

/-- The first value of `chainSide` is the `side η` of the first foot. -/
lemma chainSide_zero (L : UpperLobe P ρ x) (η : Pt) (u₀ : ℝ) :
    chainSide L η u₀ 0 = side η (x + u₀ • ρ.r) (footFirst L) := by
  unfold chainSide; simp

/-- The `len`-value of `chainSide` is the `side η` of the last foot. -/
lemma chainSide_len (L : UpperLobe P ρ x) (η : Pt) (u₀ : ℝ) :
    chainSide L η u₀ L.len = side η (x + u₀ • ρ.r) (footLast L) := by
  unfold chainSide
  have hpos := L.len_pos
  rw [if_neg (by omega), if_pos (le_refl _)]

/-- **Per-segment indicator = abstract span indicator.**  Under forward-only and off-line
endpoints, each chain segment's `segCrossInd` is the abstract `crossInd` (threshold `0`) of the
two endpoint `side η` values. -/
lemma lobeChain_segCrossInd_eq_crossInd (L : UpperLobe P ρ x) {η : Pt} (u₀ : ℝ)
    (hη : (lobeChain L).Transverse η) (hdet : 0 < det2 ρ.r η) (i : Fin L.len)
    (ha : side η (x + u₀ • ρ.r) ((lobeChain L).segA i) ≠ 0)
    (hb : side η (x + u₀ • ρ.r) ((lobeChain L).segB i) ≠ 0) :
    segCrossInd η (x + u₀ • ρ.r) ((lobeChain L).segA i) ((lobeChain L).segB i)
      = crossInd 0 (side η (x + u₀ • ρ.r) ((lobeChain L).segA i))
                   (side η (x + u₀ • ρ.r) ((lobeChain L).segB i)) := by
  set z₀ := x + u₀ • ρ.r with hz₀
  set a := (lobeChain L).segA i
  set b := (lobeChain L).segB i
  set sa := side η z₀ a with hsadef
  set sb := side η z₀ b with hsbdef
  -- crossInd 0 sa sb = if sa*sb<0 then 1 else 0 = if Span sa sb then 1 else 0.
  have hcross : crossInd 0 sa sb = if Span sa sb then 1 else 0 := by
    unfold crossInd
    by_cases hsp : Span sa sb
    · rw [if_pos hsp, if_pos]
      have := (span_iff_opp_sign ha hb).mp hsp; simpa using this
    · rw [if_neg hsp, if_neg]
      intro h; exact hsp ((span_iff_opp_sign ha hb).mpr (by simpa using h))
  rw [hcross]
  unfold segCrossInd SegCrossesRay
  by_cases hsp : Span sa sb
  · rw [if_pos hsp, if_pos]
    exact ⟨hsp, lobeChain_segCrossInd_forward L u₀ hη hdet i hsp⟩
  · rw [if_neg hsp, if_neg]
    rintro ⟨h, _⟩; exact hsp h

/-- **The lobe-chain `rayCount` parity is the feet straddle.**  With `η` transverse, `0 < det2 r η`,
and every chain vertex off the `η`-line through `z₀ = x + u₀•r`, the forward-ray crossing count of
the lobe chain has the parity of the strict-above indicator difference of the two feet's `side η`
values.  In particular it is ODD iff `z₀` separates the two feet along the line. -/
lemma lobeChain_rayCount_parity (L : UpperLobe P ρ x) {η : Pt} (u₀ : ℝ)
    (hη : (lobeChain L).Transverse η) (hdet : 0 < det2 ρ.r η)
    (hgen : ∀ j : Fin (L.len + 1), side η (x + u₀ • ρ.r) (chainPt L j) ≠ 0) :
    (lobeChain L).rayCount η (x + u₀ • ρ.r) % 2
      = (aboveInd 0 (side η (x + u₀ • ρ.r) (footLast L))
          - aboveInd 0 (side η (x + u₀ • ρ.r) (footFirst L))) % 2 := by
  classical
  set z₀ := x + u₀ • ρ.r with hz₀
  set f : ℕ → ℤ := fun k => crossInd 0 (chainSide L η u₀ k) (chainSide L η u₀ (k + 1)) with hfdef
  -- per-segment: segCrossInd = f i.val.
  have hper : ∀ i : Fin L.len,
      segCrossInd η z₀ ((lobeChain L).segA i) ((lobeChain L).segB i) = f i.val := by
    intro i
    have hile : i.val ≤ L.len := le_of_lt i.isLt
    have hile1 : i.val + 1 ≤ L.len := i.isLt
    -- side η z₀ of segA/segB as chainSide.
    have hsA : side η z₀ ((lobeChain L).segA i) = chainSide L η u₀ i.val := by
      rw [lobeChain_segA, chainSide_eq_chainPt L η u₀ hile]
    have hsB : side η z₀ ((lobeChain L).segB i) = chainSide L η u₀ (i.val + 1) := by
      rw [lobeChain_segB, chainSide_eq_chainPt L η u₀ hile1]
    -- both off-line.
    have ha : side η z₀ ((lobeChain L).segA i) ≠ 0 := by
      rw [lobeChain_segA]; exact hgen ⟨i.val, by omega⟩
    have hb : side η z₀ ((lobeChain L).segB i) ≠ 0 := by
      rw [lobeChain_segB]; exact hgen ⟨i.val + 1, by omega⟩
    rw [lobeChain_segCrossInd_eq_crossInd L u₀ hη hdet i ha hb, hfdef]
    simp only []
    rw [hsA, hsB]
  -- rayCount as a range sum of f.
  have hsum : (lobeChain L).rayCount η z₀ = ∑ k ∈ Finset.range L.len, f k := by
    unfold Chain.rayCount
    rw [Finset.sum_congr rfl (fun i _ => hper i)]
    exact Fin.sum_univ_eq_sum_range f L.len
  rw [hsum]
  -- the chain-side sequence avoids the threshold 0 for k ≤ len.
  have hne : ∀ k, k ≤ L.len → chainSide L η u₀ k ≠ 0 := by
    intro k hk
    rw [chainSide_eq_chainPt L η u₀ hk]; exact hgen ⟨k, by omega⟩
  have htel := sum_crossInd_emod_two L.len 0 (fun k => chainSide L η u₀ k) hne
  simp only [hfdef] at htel ⊢
  rw [htel, chainSide_zero, chainSide_len]

/-! ### Feet `side η` values and the odd-count criterion -/

/-- The along-line coordinate of the first foot. -/
def tauFirst (L : UpperLobe P ρ x) : ℝ := crossTau P ρ x L.start

/-- The along-line coordinate of the last foot. -/
def tauLast (L : UpperLobe P ρ x) : ℝ := crossTau P ρ x (lobeLastEdge L)

/-- `side η z₀` of the first foot is `(u₀ − tauFirst)·det2 r η`. -/
lemma side_eta_footFirst (L : UpperLobe P ρ x) (η : Pt) (u₀ : ℝ) :
    side η (x + u₀ • ρ.r) (footFirst L) = (u₀ - tauFirst L) * det2 ρ.r η := by
  unfold footFirst tauFirst
  exact side_eta_linePoint ρ.r η x u₀ (crossTau P ρ x L.start)

/-- `side η z₀` of the last foot is `(u₀ − tauLast)·det2 r η`. -/
lemma side_eta_footLast (L : UpperLobe P ρ x) (η : Pt) (u₀ : ℝ) :
    side η (x + u₀ • ρ.r) (footLast L) = (u₀ - tauLast L) * det2 ρ.r η := by
  unfold footLast tauLast
  exact side_eta_linePoint ρ.r η x u₀ (crossTau P ρ x (lobeLastEdge L))

/-- **The odd-count criterion.**  When `z₀` strictly separates the two feet (`u₀` between
`tauFirst` and `tauLast`, either order) and `0 < det2 r η`, the feet straddle indicator
difference is `±1`, hence the `rayCount` parity is `1` (odd). -/
lemma aboveInd_feet_straddle (L : UpperLobe P ρ x) (η : Pt) (u₀ : ℝ)
    (hdet : 0 < det2 ρ.r η)
    (hbetween : (tauFirst L < u₀ ∧ u₀ < tauLast L) ∨ (tauLast L < u₀ ∧ u₀ < tauFirst L)) :
    (aboveInd 0 (side η (x + u₀ • ρ.r) (footLast L))
      - aboveInd 0 (side η (x + u₀ • ρ.r) (footFirst L))) % 2 = 1 := by
  rw [side_eta_footFirst, side_eta_footLast]
  unfold aboveInd
  rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- tauFirst < u₀ < tauLast: footFirst side > 0, footLast side < 0.
    rw [if_neg (by nlinarith), if_pos (by nlinarith)]; decide
  · -- tauLast < u₀ < tauFirst: footLast side > 0, footFirst side < 0.
    rw [if_pos (by nlinarith), if_neg (by nlinarith)]; decide

/-! ## §3. The far point: `rayCount = 0`

Sliding the base point along `r` shifts every `lineCoord` by the opposite amount.  Pushing the
base far enough along `r` puts every chain vertex strictly behind it, so no segment is
forward-crossed (`rayCount_zero_of_coordMax`). -/

/-- **`lineCoord` shifts by `−R` when the base slides `R•r` along `r`** (for `0 < det2 r η`). -/
lemma lineCoord_base_shift (r η : Pt) (x p : Pt) (R : ℝ) (hrη : det2 r η ≠ 0) :
    lineCoord r η (x + R • r) p = lineCoord r η x p - R := by
  unfold lineCoord
  have hsub : p - (x + R • r) = (p - x) - R • r := by module
  rw [hsub, det2_sub_left, det2_smul_left]
  field_simp

/-- **Far-point zero count.**  If `R` strictly exceeds every chain vertex's along-`r` coordinate
`lineCoord r η x`, then the lobe chain's forward-ray count from `x + R•r` is `0`. -/
lemma lobeChain_rayCount_far (L : UpperLobe P ρ x) {η : Pt} (R : ℝ)
    (hη : (lobeChain L).Transverse η) (hdet : 0 < det2 ρ.r η)
    (hR : ∀ j : Fin (L.len + 1), lineCoord ρ.r η x (chainPt L j) < R) :
    (lobeChain L).rayCount η (x + R • ρ.r) = 0 := by
  apply Chain.rayCount_zero_of_coordMax (r := ρ.r) (hrη := hdet) (hη := hη)
  intro i
  constructor
  · rw [lobeChain_segA, lineCoord_base_shift ρ.r η x _ R (ne_of_gt hdet)]
    have := hR ⟨i.val, by omega⟩; linarith
  · rw [lobeChain_segB, lineCoord_base_shift ρ.r η x _ R (ne_of_gt hdet)]
    have := hR ⟨i.val + 1, by omega⟩; linarith

/-! ## §4. Endpoint safety along an upper-halfplane path

The unpaired endpoints of the chain `X` are its two feet, which lie on the base line
(`side r = 0`).  At a path point `z` in the closed upper halfplane (`0 ≤ side r x z`) that is off
the carrier, each foot-event is either off the `η`-line (`side η z foot ≠ 0`) or *locally
backward*: if the foot is on the `η`-ray-line of `z`, then the forward-ray foot is at the chain
vertex itself, whose `side r = 0`; from `side_ray_eta` the ray parameter is
`−(side r x z)/det2 r η ≤ 0`, and equals `0` only when `z` is that foot — excluded by off-carrier. -/

/-- A chain segment whose start is on the `η`-line of `z` has its forward foot at the start
vertex: `z + segTau•η = a`. -/
lemma seg_foot_at_start {η z a b : Pt} (hden : det2 η (b - a) ≠ 0)
    (ha : side η z a = 0) : z + segTau η z a b • η = a := by
  have hrec := seg_cross_eq (η := η) (z := z) (a := a) (b := b) hden
  have hu0 : segU η z a b = 0 := by
    unfold segU
    have : det2 η (z - a) = 0 := by
      have he : side η z a = det2 η (a - z) := rfl
      have : det2 η (z - a) = - det2 η (a - z) := by
        unfold det2; simp only [PiLp.sub_apply]; ring
      rw [this, ← he, ha, neg_zero]
    rw [this, zero_div]
  rw [hu0, AffineMap.lineMap_apply_zero] at hrec; exact hrec

/-- A chain segment whose end is on the `η`-line of `z` has its forward foot at the end vertex:
`z + segTau•η = b`. -/
lemma seg_foot_at_end {η z a b : Pt} (hden : det2 η (b - a) ≠ 0)
    (hb : side η z b = 0) : z + segTau η z a b • η = b := by
  have hrec := seg_cross_eq (η := η) (z := z) (a := a) (b := b) hden
  have hu1 : segU η z a b = 1 := by
    unfold segU
    have hzb : det2 η (z - b) = 0 := by
      have he : side η z b = det2 η (b - z) := rfl
      have : det2 η (z - b) = - det2 η (b - z) := by
        unfold det2; simp only [PiLp.sub_apply]; ring
      rw [this, ← he, hb, neg_zero]
    have hnum : det2 η (z - a) = det2 η (b - a) := by
      have h1 : det2 η (z - a) = det2 η (z - b) + det2 η (b - a) := by
        rw [← det2_add_right]; congr 1; abel
      rw [h1, hzb, zero_add]
    rw [hnum, div_self hden]
  rw [hu1, AffineMap.lineMap_apply_one] at hrec; exact hrec

/-- The first chain vertex is `footFirst`. -/
lemma lobeChain_p_zero (L : UpperLobe P ρ x) : (lobeChain L).p 0 = footFirst L := by
  show chainPt L 0 = footFirst L
  unfold chainPt; simp

/-- The last chain vertex is `footLast`. -/
lemma lobeChain_p_last (L : UpperLobe P ρ x) :
    (lobeChain L).p (Fin.last L.len) = footLast L := by
  show chainPt L (Fin.last L.len) = footLast L
  have hpos := L.len_pos
  unfold chainPt
  rw [if_neg (show ¬ (Fin.last L.len).val = 0 by simp; omega),
    if_pos (show (Fin.last L.len).val = L.len from rfl)]

/-- **EndpointSafe along an upper-halfplane path point.**  For `z` with `0 ≤ side r x z` and
`z ∉ carrier`, the lobe chain is endpoint-safe for the ray direction `η` (`0 < det2 r η`). -/
lemma lobeChain_endpointSafe (L : UpperLobe P ρ x) {η z : Pt}
    (hη : (lobeChain L).Transverse η) (hdet : 0 < det2 ρ.r η)
    (hz : 0 ≤ side ρ.r x z) (hoff : z ∉ (lobeChain L).carrier) :
    (lobeChain L).EndpointSafe η z := by
  have hpos := L.len_pos
  constructor
  · -- first vertex (footFirst).
    rw [lobeChain_p_zero]
    by_cases hfoot : side η z (footFirst L) = 0
    · -- foot on the η-line: locally backward.
      right
      refine ⟨hpos, ?_⟩
      -- segA ⟨0⟩ = footFirst, segB ⟨0⟩ = chainPt 1.
      set a := (lobeChain L).segA ⟨0, hpos⟩ with hadef
      set b := (lobeChain L).segB ⟨0, hpos⟩ with hbdef
      have hafoot : a = footFirst L := by
        rw [hadef, lobeChain_segA]; show chainPt L ⟨0, by omega⟩ = footFirst L
        unfold chainPt; simp
      have hden : det2 η (b - a) ≠ 0 := hη.2 ⟨0, hpos⟩
      have haline : side η z a = 0 := by rw [hafoot]; exact hfoot
      have hfeq : z + segTau η z a b • η = a := seg_foot_at_start hden haline
      -- side r of a = footFirst is 0.
      have hra : side ρ.r x a = 0 := by rw [hafoot, side_footFirst]
      -- side r x (z + segTau η) = side r x z + segTau det2 r η = side r x a = 0.
      have hkey : side ρ.r x z + segTau η z a b * det2 ρ.r η = 0 := by
        have := side_ray_eta ρ.r x z η (segTau η z a b)
        rw [hfeq, hra] at this; linarith
      -- segTau = -side r x z / det2 r η ≤ 0; strict unless z = a (excluded).
      rcases eq_or_lt_of_le hz with hz0 | hz0
      · -- side r x z = 0 ⟹ segTau = 0 ⟹ z = a ∈ carrier.
        exfalso
        have hτ0 : segTau η z a b = 0 := by
          have : segTau η z a b * det2 ρ.r η = 0 := by rw [← hz0] at hkey; linarith
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd h (ne_of_gt hdet)
        apply hoff
        rw [show z = a from by rw [← hfeq, hτ0, zero_smul, add_zero]]
        exact ⟨⟨0, hpos⟩, by rw [hadef, seg]; exact left_mem_segment ℝ _ _⟩
      · -- side r x z > 0 ⟹ segTau < 0.
        show segTau η z a b < 0
        nlinarith [hkey, hz0, hdet]
    · left; exact hfoot
  · -- last vertex (footLast).
    rw [lobeChain_p_last]
    by_cases hfoot : side η z (footLast L) = 0
    · right
      refine ⟨hpos, ?_⟩
      set i : Fin L.len := ⟨L.len - 1, by omega⟩ with hidef
      set a := (lobeChain L).segA i with hadef
      set b := (lobeChain L).segB i with hbdef
      have hbfoot : b = footLast L := by
        rw [hbdef, lobeChain_segB]
        show chainPt L ⟨(L.len - 1) + 1, by omega⟩ = footLast L
        have : (⟨(L.len - 1) + 1, by omega⟩ : Fin (L.len + 1)) = ⟨L.len, by omega⟩ := by
          apply Fin.ext; show (L.len - 1) + 1 = L.len; omega
        rw [this]; exact chainPt_len L
      have hden : det2 η (b - a) ≠ 0 := hη.2 i
      have hbline : side η z b = 0 := by rw [hbfoot]; exact hfoot
      have hfeq : z + segTau η z a b • η = b := seg_foot_at_end hden hbline
      have hrb : side ρ.r x b = 0 := by rw [hbfoot, side_footLast]
      have hkey : side ρ.r x z + segTau η z a b * det2 ρ.r η = 0 := by
        have := side_ray_eta ρ.r x z η (segTau η z a b)
        rw [hfeq, hrb] at this; linarith
      rcases eq_or_lt_of_le hz with hz0 | hz0
      · exfalso
        have hτ0 : segTau η z a b = 0 := by
          have : segTau η z a b * det2 ρ.r η = 0 := by rw [← hz0] at hkey; linarith
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd h (ne_of_gt hdet)
        apply hoff
        rw [show z = b from by rw [← hfeq, hτ0, zero_smul, add_zero]]
        exact ⟨i, by rw [hbdef, seg]; exact right_mem_segment ℝ _ _⟩
      · show (lobeChain L).segTauOf η z ⟨L.len - 1, by omega⟩ < 0
        rw [Chain.segTauOf]
        show segTau η z a b < 0
        nlinarith [hkey, hz0, hdet]
    · left; exact hfoot

/-! ## §5. Parity transport along the sweep path

`rayCount` of `X` is parity-transported along any straight segment that avoids `X`'s carrier and
stays in the closed upper halfplane (`rayCountParity_constant_on_segment` +
`lobeChain_endpointSafe`). -/

/-- **Transport wrapper.**  `rayCount X` has the same parity at the two ends of a straight segment
whose points all avoid `X`'s carrier and lie in the closed upper halfplane. -/
lemma transport_X (X : UpperLobe P ρ x) {η z₀ z₁ : Pt}
    (hη : (lobeChain X).Transverse η) (hdet : 0 < det2 ρ.r η)
    (havoid : ∀ t ∈ Set.Icc (0:ℝ) 1, AffineMap.lineMap z₀ z₁ t ∉ (lobeChain X).carrier)
    (hup : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ side ρ.r x (AffineMap.lineMap z₀ z₁ t)) :
    (lobeChain X).rayCount η z₀ % 2 = (lobeChain X).rayCount η z₁ % 2 := by
  apply (lobeChain X).rayCountParity_constant_on_segment hη havoid
  intro t ht
  exact lobeChain_endpointSafe X hη hdet (hup t ht) (havoid t ht)

/-- A point on the closed segment between two `lobeChain Y` vertices lies in `Y`'s carrier. -/
lemma seg_chainPt_subset_carrier (Y : UpperLobe P ρ x) (i : Fin Y.len) :
    seg ((lobeChain Y).segA i) ((lobeChain Y).segB i) ⊆ (lobeChain Y).carrier := by
  intro z hz; exact ⟨i, hz⟩

/-- **Transport across one `Y`-segment.**  Disjoint carriers make every point of the `Y`-segment
avoid `X`'s carrier; `carrier_side_nonneg` keeps it in the closed upper halfplane. -/
lemma transport_X_across_Y_seg (X Y : UpperLobe P ρ x) {η : Pt}
    (hη : (lobeChain X).Transverse η) (hdet : 0 < det2 ρ.r η)
    (hdisj : Disjoint (lobeChain X).carrier (lobeChain Y).carrier) (i : Fin Y.len) :
    (lobeChain X).rayCount η ((lobeChain Y).segA i) % 2
      = (lobeChain X).rayCount η ((lobeChain Y).segB i) % 2 := by
  apply transport_X X hη hdet
  · intro t ht hmem
    -- the path point is on a Y-segment ⟹ in carrier Y ⟹ not in carrier X.
    have hY : AffineMap.lineMap ((lobeChain Y).segA i) ((lobeChain Y).segB i) t
        ∈ (lobeChain Y).carrier := by
      apply seg_chainPt_subset_carrier Y i
      rw [seg, segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩
    exact (Set.disjoint_left.mp hdisj hmem) hY
  · intro t ht
    have hY : AffineMap.lineMap ((lobeChain Y).segA i) ((lobeChain Y).segB i) t
        ∈ (lobeChain Y).carrier := by
      apply seg_chainPt_subset_carrier Y i
      rw [seg, segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩
    exact carrier_side_nonneg Y hY

/-- **Transport over the whole `Y` walk.**  Chaining `transport_X_across_Y_seg` across all of `Y`'s
chain segments: `rayCount X` has the same parity at `footFirst Y` and `footLast Y`. -/
lemma transport_X_over_Y (X Y : UpperLobe P ρ x) {η : Pt}
    (hη : (lobeChain X).Transverse η) (hdet : 0 < det2 ρ.r η)
    (hdisj : Disjoint (lobeChain X).carrier (lobeChain Y).carrier) :
    (lobeChain X).rayCount η (footFirst Y) % 2
      = (lobeChain X).rayCount η (footLast Y) % 2 := by
  -- induction over the prefix of Y's walk.
  have key : ∀ k, (hk : k < Y.len + 1) →
      (lobeChain X).rayCount η (footFirst Y) % 2
        = (lobeChain X).rayCount η (chainPt Y ⟨k, hk⟩) % 2 := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [show (⟨0, by omega⟩ : Fin (Y.len + 1)) = 0 from rfl, ← lobeChain_p_zero Y]; rfl
    | succ k ih =>
      intro hk
      have hklt : k < Y.len := by omega
      rw [ih (by omega)]
      -- transport across Y-segment k.
      have hstep := transport_X_across_Y_seg X Y hη hdet hdisj ⟨k, hklt⟩
      rw [lobeChain_segA, lobeChain_segB] at hstep
      rw [hstep]
  have h := key Y.len (by omega)
  rw [h, chainPt_len Y]

/-- **Transport along a base-line piece.**  A straight piece between two line points
`x + α•r` and `x + β•r` whose along-line span `[min α β, max α β]` excludes both feet of `X`
transports `rayCount X` parity (the piece stays on the line, `side r = 0`, and meets `X`'s
carrier only at a foot). -/
lemma transport_X_along_line (X : UpperLobe P ρ x) {η : Pt} (α β : ℝ)
    (hη : (lobeChain X).Transverse η) (hdet : 0 < det2 ρ.r η)
    (hfirst : tauFirst X < min α β ∨ max α β < tauFirst X)
    (hlast : tauLast X < min α β ∨ max α β < tauLast X) :
    (lobeChain X).rayCount η (x + α • ρ.r) % 2
      = (lobeChain X).rayCount η (x + β • ρ.r) % 2 := by
  apply transport_X X hη hdet
  · intro t ht hmem
    -- the path point is a line point x + c•r with c between α and β.
    set c := (1 - t) * α + t * β with hcdef
    have hpt : AffineMap.lineMap (x + α • ρ.r) (x + β • ρ.r) t = x + c • ρ.r := by
      rw [AffineMap.lineMap_apply_module]; rw [hcdef]; module
    rw [hpt] at hmem
    -- side r of a line point is 0.
    have hside0 : side ρ.r x (x + c • ρ.r) = 0 := side_ray_point c
    -- so it is footFirst X or footLast X.
    rcases carrier_side_zero_imp_foot X hmem hside0 with hf | hf
    · -- = footFirst X ⟹ c = tauFirst X.
      have hc : c = tauFirst X := by
        have := congrArg (fun p => uCoord ρ.r x p) hf
        simp only at this
        rw [show footFirst X = x + crossTau P ρ x X.start • ρ.r from rfl] at this
        rw [uCoord_ray, uCoord_ray] at this
        have hnz : (0:ℝ) < ‖ρ.r‖ ^ 2 := normSq_pos ρ.r ρ.r_ne_zero
        have := mul_right_cancel₀ (ne_of_gt hnz) this
        rw [tauFirst]; exact this
      -- c is between α and β, contradicting the exclusion.
      have hcb : min α β ≤ c ∧ c ≤ max α β := by
        constructor
        · rw [hcdef]; nlinarith [ht.1, ht.2, min_le_left α β, min_le_right α β]
        · rw [hcdef]; nlinarith [ht.1, ht.2, le_max_left α β, le_max_right α β]
      rcases hfirst with h | h <;> rw [hc] at hcb <;> [linarith [hcb.1]; linarith [hcb.2]]
    · have hc : c = tauLast X := by
        have := congrArg (fun p => uCoord ρ.r x p) hf
        simp only at this
        rw [show footLast X = x + crossTau P ρ x (lobeLastEdge X) • ρ.r from rfl] at this
        rw [uCoord_ray, uCoord_ray] at this
        have hnz : (0:ℝ) < ‖ρ.r‖ ^ 2 := normSq_pos ρ.r ρ.r_ne_zero
        have := mul_right_cancel₀ (ne_of_gt hnz) this
        rw [tauLast]; exact this
      have hcb : min α β ≤ c ∧ c ≤ max α β := by
        constructor
        · rw [hcdef]; nlinarith [ht.1, ht.2, min_le_left α β, min_le_right α β]
        · rw [hcdef]; nlinarith [ht.1, ht.2, le_max_left α β, le_max_right α β]
      rcases hlast with h | h <;> rw [hc] at hcb <;> [linarith [hcb.1]; linarith [hcb.2]]
  · intro t ht
    set c := (1 - t) * α + t * β with hcdef
    have hpt : AffineMap.lineMap (x + α • ρ.r) (x + β • ρ.r) t = x + c • ρ.r := by
      rw [AffineMap.lineMap_apply_module]; rw [hcdef]; module
    rw [hpt, side_ray_point]

/-! ## §6. Genericity: the transverse sweep direction

`η = sweepDir r λ` is transverse to a lobe chain whose feet are distinct as soon as `λ` avoids the
finitely many segment-parallelisms.  The crux is that every chain segment has a *nonzero* vector
(`chainPt_consecutive_ne`), so the affine-in-`λ` determinant `det2 η v` is a nonzero affine
function, vanishing at ≤ 1 value of `λ`. -/

/-- **Consecutive chain vertices are distinct** (feet distinct).  Feet have `side r = 0`, interior
walk vertices `side r > 0`; interior walk vertices are distinct by injectivity of `P.q` and the
cyclic-step. -/
lemma chainPt_consecutive_ne (L : UpperLobe P ρ x) (hfeet : footFirst L ≠ footLast L)
    {j : ℕ} (hj : j < L.len) :
    chainPt L ⟨j + 1, by omega⟩ ≠ chainPt L ⟨j, by omega⟩ := by
  have hpos := L.len_pos
  have hn : 2 ≤ n := by have := P.hthree; omega
  -- side r values: feet 0, interior > 0.
  by_cases hj0 : j = 0
  · subst hj0
    -- chainPt 0 = footFirst (sr 0), chainPt 1 = footLast (len=1) or interior (sr>0).
    have h0 : chainPt L ⟨0, by omega⟩ = footFirst L := by unfold chainPt; simp
    by_cases hlen1 : L.len = 1
    · -- chainPt 1 = footLast.
      have h1 : chainPt L ⟨1, by omega⟩ = footLast L := by
        rw [show (⟨1, by omega⟩ : Fin (L.len + 1)) = ⟨L.len, by omega⟩ from by
          apply Fin.ext; simp; omega]
        exact chainPt_len L
      rw [h0, h1]; exact fun h => hfeet h.symm
    · -- chainPt 1 interior: side r > 0 ≠ 0 = side r footFirst.
      have h1pos : 0 < side ρ.r x (chainPt L ⟨1, by omega⟩) :=
        chainPt_side_pos_interior L (by omega) (by omega) (by omega)
      rw [h0]
      intro h; rw [h, side_footFirst] at h1pos; exact lt_irrefl _ h1pos
  · -- j > 0.
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    by_cases hjlen : j + 1 = L.len
    · -- chainPt (j+1) = footLast (sr 0), chainPt j interior (sr > 0).
      have hL : chainPt L ⟨j + 1, by omega⟩ = footLast L := by
        rw [show (⟨j + 1, by omega⟩ : Fin (L.len + 1)) = ⟨L.len, by omega⟩ from by
          apply Fin.ext; simp; omega]
        exact chainPt_len L
      have hjpos2 : 0 < side ρ.r x (chainPt L ⟨j, by omega⟩) :=
        chainPt_side_pos_interior L hjpos (by omega) (by omega)
      rw [hL]
      intro h; rw [← h, side_footLast] at hjpos2; exact lt_irrefl _ hjpos2
    · -- both interior: P.q (arcPos start (j+1)) ≠ P.q (arcPos start j).
      have hjlt1 : j + 1 < L.len := by omega
      have hI1 : chainPt L ⟨j + 1, by omega⟩ = P.q (arcPos L.start (j + 1)) :=
        chainPt_interior L (by omega) hjlt1 (by omega)
      have hI0 : chainPt L ⟨j, by omega⟩ = P.q (arcPos L.start j) :=
        chainPt_interior L hjpos hj (by omega)
      rw [hI1, hI0]
      intro h
      have hinj := P.injective_q h
      -- arcPos start (j+1) = cyclicNext (arcPos start j) ≠ arcPos start j.
      have hstep : arcPos L.start (j + 1) = cyclicNext (arcPos L.start j) :=
        (ZinanCh36LobeChain.cyclicNext_arcPos L.start j).symm
      rw [hstep] at hinj
      exact cyclicNext_ne_self hn (arcPos L.start j) hinj

/-- A chain segment vector is nonzero (feet distinct). -/
lemma lobeChain_segVec_ne_zero (L : UpperLobe P ρ x) (hfeet : footFirst L ≠ footLast L)
    (i : Fin L.len) : (lobeChain L).segB i - (lobeChain L).segA i ≠ 0 := by
  rw [lobeChain_segA, lobeChain_segB]
  have hne := chainPt_consecutive_ne L hfeet i.isLt
  rw [sub_ne_zero]
  exact hne

/-- **`sweepDir` transverse off a finite `λ`-set.**  For a lobe chain with distinct feet there is a
finite set of `λ` outside of which `sweepDir r λ` is transverse to the chain.  Concretely the
bad set is the image of the per-segment parallelism roots. -/
lemma exists_transverse_lobeChain (L : UpperLobe P ρ x) (hfeet : footFirst L ≠ footLast L) :
    ∃ bad : Finset ℝ, ∀ lam : ℝ, lam ∉ bad → (lobeChain L).Transverse (sweepDir ρ.r lam) := by
  classical
  -- the per-segment root (only meaningful when det2 r v ≠ 0).
  let root : Fin L.len → ℝ := fun i =>
    - det2 (perpVec ρ.r) ((lobeChain L).segB i - (lobeChain L).segA i)
      / det2 ρ.r ((lobeChain L).segB i - (lobeChain L).segA i)
  refine ⟨Finset.univ.image root, fun lam hlam => ?_⟩
  refine ⟨?_, ?_⟩
  · -- sweepDir ≠ 0.
    intro h0
    have := det2_r_sweepDir_pos ρ.r_ne_zero lam
    rw [h0] at this; simp [det2] at this
  · intro i
    set v := (lobeChain L).segB i - (lobeChain L).segA i with hvdef
    have hv0 : v ≠ 0 := lobeChain_segVec_ne_zero L hfeet i
    rw [det2_sweepDir_left]
    by_cases hrv : det2 ρ.r v = 0
    · -- v ∥ r: det2 (perpVec r) v ≠ 0 (else v = 0).
      rw [hrv, mul_zero, add_zero]
      intro hp
      -- det2 (perpVec r) v = 0 and det2 r v = 0 ⟹ v = 0 (perpVec r, r independent).
      have hdet_pr : det2 (perpVec ρ.r) ρ.r ≠ 0 := by
        have : det2 (perpVec ρ.r) ρ.r = - det2 ρ.r (perpVec ρ.r) := det2_antisymm _ _
        rw [this]; exact neg_ne_zero.mpr (ne_of_gt (det2_perpVec_pos ρ.r_ne_zero))
      exact hv0 (eq_zero_of_det2_eq_zero hdet_pr hp hrv)
    · -- det2 r v ≠ 0: bad λ is the root; lam ≠ root.
      have hlamne : lam ≠ root i := by
        intro h; exact hlam (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h.symm⟩)
      intro hz
      apply hlamne
      show lam = - det2 (perpVec ρ.r) v / det2 ρ.r v
      field_simp
      linarith [hz]

/-! ## §7. Genericity of the base coordinate `u₀`

For a fixed transverse `η`, all chain `X` vertices are off the `η`-line through `z₀ = x + u₀•r`
provided `u₀` avoids the finitely many vertex projections. -/

/-- `side η z₀` of any point as an affine function of `u₀`:
`side η (x + u₀•r) p = det2 η (p − x) + u₀·det2 r η`. -/
lemma side_eta_base_affine (r η : Pt) (x p : Pt) (u₀ : ℝ) :
    side η (x + u₀ • r) p = det2 η (p - x) + u₀ * det2 r η := by
  unfold side
  have hsub : p - (x + u₀ • r) = (p - x) - u₀ • r := by module
  rw [hsub, det2_sub_right, det2_smul_right]
  have hflip : det2 η r = - det2 r η := det2_antisymm η r
  rw [hflip]; ring

/-- **`u₀`-genericity.**  For fixed transverse `η` (`0 < det2 r η`) there is a finite set of `u₀`
outside of which every chain `X` vertex is off the `η`-line through `x + u₀•r`. -/
lemma exists_generic_u0 (X : UpperLobe P ρ x) {η : Pt} (hdet : 0 < det2 ρ.r η) :
    ∃ bad : Finset ℝ, ∀ u₀ : ℝ, u₀ ∉ bad →
      ∀ j : Fin (X.len + 1), side η (x + u₀ • ρ.r) (chainPt X j) ≠ 0 := by
  classical
  let root : Fin (X.len + 1) → ℝ := fun j => - det2 η (chainPt X j - x) / det2 ρ.r η
  refine ⟨Finset.univ.image root, fun u₀ hu₀ j => ?_⟩
  rw [side_eta_base_affine]
  intro hz
  apply hu₀
  refine Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩
  show - det2 η (chainPt X j - x) / det2 ρ.r η = u₀
  field_simp
  linarith [hz]

/-! ## §8. The far coordinate and the assembly -/

/-- **Existence of a far coordinate.**  There is `R` strictly exceeding every `lineCoord`
of `X`'s chain vertices and a given threshold `t₀`. -/
lemma exists_far_R (X : UpperLobe P ρ x) (η : Pt) (t₀ : ℝ) :
    ∃ R : ℝ, (∀ j : Fin (X.len + 1), lineCoord ρ.r η x (chainPt X j) < R) ∧ t₀ < R := by
  classical
  set S : Finset ℝ := (Finset.univ.image fun j : Fin (X.len + 1) =>
    lineCoord ρ.r η x (chainPt X j)) ∪ {t₀} with hSdef
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ s ∈ S, s ≤ M := by
    rcases S.exists_le with ⟨M, hM⟩; exact ⟨M, hM⟩
  refine ⟨M + 1, ?_, ?_⟩
  · intro j
    have : lineCoord ρ.r η x (chainPt X j) ≤ M := by
      apply hM; rw [hSdef]; apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
    linarith
  · have : t₀ ≤ M := by
      apply hM; rw [hSdef]; apply Finset.mem_union_right; simp
    linarith

/-- **The upper-lobe noninterleaving theorem** (the fixed sweep path).  Two `UpperLobe`s with
disjoint clipped-chain carriers cannot interleave their feet along the line. -/
theorem upper_lobes_not_interleave
    (X Y : UpperLobe P ρ x)
    (hdisj : Disjoint (lobeChain X).carrier (lobeChain Y).carrier)
    (hinter : crossTau P ρ x X.start < crossTau P ρ x Y.start ∧
              crossTau P ρ x Y.start < crossTau P ρ x (lobeLastEdge X) ∧
              crossTau P ρ x (lobeLastEdge X) < crossTau P ρ x (lobeLastEdge Y)) :
    False := by
  classical
  obtain ⟨hXY, hYX, hXYlast⟩ := hinter
  -- restate via tauFirst/tauLast: tauFirst X < tauFirst Y < tauLast X < tauLast Y.
  have hi1 : tauFirst X < tauFirst Y := hXY
  have hi2 : tauFirst Y < tauLast X := hYX
  have hi3 : tauLast X < tauLast Y := hXYlast
  -- feet of X and Y are distinct.
  have hfeetX : footFirst X ≠ footLast X := by
    intro h
    have := congrArg (uCoord ρ.r x) h
    rw [show footFirst X = x + crossTau P ρ x X.start • ρ.r from rfl,
      show footLast X = x + crossTau P ρ x (lobeLastEdge X) • ρ.r from rfl,
      uCoord_ray, uCoord_ray] at this
    have hnz := normSq_pos ρ.r ρ.r_ne_zero
    have := mul_right_cancel₀ (ne_of_gt hnz) this
    rw [← tauFirst, ← tauLast] at this; linarith
  have hfeetY : footFirst Y ≠ footLast Y := by
    intro h
    have := congrArg (uCoord ρ.r x) h
    rw [show footFirst Y = x + crossTau P ρ x Y.start • ρ.r from rfl,
      show footLast Y = x + crossTau P ρ x (lobeLastEdge Y) • ρ.r from rfl,
      uCoord_ray, uCoord_ray] at this
    have hnz := normSq_pos ρ.r ρ.r_ne_zero
    have := mul_right_cancel₀ (ne_of_gt hnz) this
    rw [← tauFirst, ← tauLast] at this; linarith
  -- pick λ transverse to BOTH chains.
  obtain ⟨badX, hbadX⟩ := exists_transverse_lobeChain X hfeetX
  obtain ⟨badY, hbadY⟩ := exists_transverse_lobeChain Y hfeetY
  obtain ⟨lam, hlam⟩ := (badX ∪ badY).exists_notMem
  set η := sweepDir ρ.r lam with hηdef
  have hηX : (lobeChain X).Transverse η :=
    hbadX lam (fun h => hlam (Finset.mem_union_left _ h))
  have hηY : (lobeChain Y).Transverse η :=
    hbadY lam (fun h => hlam (Finset.mem_union_right _ h))
  have hdet : 0 < det2 ρ.r η := det2_r_sweepDir_pos ρ.r_ne_zero lam
  -- pick u₀ ∈ (tauFirst Y, tauLast X) avoiding the X-vertex projections.
  obtain ⟨badU, hbadU⟩ := exists_generic_u0 X (η := η) hdet
  obtain ⟨u₀, hu₀io, hu₀bad⟩ : ∃ u₀ : ℝ, u₀ ∈ Set.Ioo (tauFirst Y) (tauLast X) ∧ u₀ ∉ badU := by
    have hinf : (Set.Ioo (tauFirst Y) (tauLast X)).Infinite := Set.Ioo_infinite hi2
    have hns : ¬ (Set.Ioo (tauFirst Y) (tauLast X) ⊆ (badU : Set ℝ)) := by
      intro hsub; exact hinf (badU.finite_toSet.subset hsub)
    rw [Set.not_subset] at hns
    obtain ⟨u₀, hio, hnb⟩ := hns; exact ⟨u₀, hio, hnb⟩
  rw [Set.mem_Ioo] at hu₀io
  have hgenX : ∀ j : Fin (X.len + 1), side η (x + u₀ • ρ.r) (chainPt X j) ≠ 0 :=
    hbadU u₀ hu₀bad
  -- N(z₀) odd.
  have hodd : (lobeChain X).rayCount η (x + u₀ • ρ.r) % 2 = 1 := by
    rw [lobeChain_rayCount_parity X u₀ hηX hdet hgenX]
    apply aboveInd_feet_straddle X η u₀ hdet
    left; exact ⟨by linarith [hu₀io.1], hu₀io.2⟩
  -- pick R far.
  obtain ⟨R, hRmax, hRt⟩ := exists_far_R X η (tauLast Y)
  -- N(z_R) = 0.
  have hzero : (lobeChain X).rayCount η (x + R • ρ.r) = 0 :=
    lobeChain_rayCount_far X R hηX hdet hRmax
  -- transport: z₀ → footFirst Y → footLast Y → z_R.
  -- piece 1: z₀ = x + u₀•r → footFirst Y = x + tauFirst Y•r.
  have hp1 : (lobeChain X).rayCount η (x + u₀ • ρ.r) % 2
      = (lobeChain X).rayCount η (footFirst Y) % 2 := by
    have hT := transport_X_along_line X u₀ (tauFirst Y) hηX hdet
      (hfirst := by left; rw [lt_min_iff]; exact ⟨by linarith, hi1⟩)
      (hlast := by right; rw [max_lt_iff]; exact ⟨hu₀io.2, by linarith⟩)
    have heq : footFirst Y = x + tauFirst Y • ρ.r := rfl
    rw [heq]; exact hT
  -- piece 2: footFirst Y → footLast Y (over Y's walk).
  have hp2 : (lobeChain X).rayCount η (footFirst Y) % 2
      = (lobeChain X).rayCount η (footLast Y) % 2 :=
    transport_X_over_Y X Y hηX hdet hdisj
  -- piece 3: footLast Y = x + tauLast Y•r → z_R = x + R•r.
  have hp3 : (lobeChain X).rayCount η (footLast Y) % 2
      = (lobeChain X).rayCount η (x + R • ρ.r) % 2 := by
    have heq : footLast Y = x + tauLast Y • ρ.r := rfl
    rw [heq]
    exact transport_X_along_line X (tauLast Y) R hηX hdet
      (hfirst := by left; rw [lt_min_iff]; exact ⟨by linarith, by linarith⟩)
      (hlast := by left; rw [lt_min_iff]; exact ⟨by linarith, by linarith⟩)
  -- chain: odd = N(z₀) = N(z_R) = 0, contradiction.
  have hchain : (1 : ℤ) = 0 := by
    rw [← hodd, hp1, hp2, hp3, hzero]; rfl
  exact absurd hchain (by decide)

/-! ## §9. The lower mirror

`LowerLobe` (from `ZinanCh36LobeWiring`) has all strictly interior walk vertices on the
NEGATIVE side.  Reflecting the reference direction `r ↦ -r` flips every `side`, turning a lower
lobe's chain into one with `side (-r) ≥ 0`; the sweep direction is reflected to keep
`det2 (-r) η > 0`.  We re-run the whole §0–§8 argument with the negated reference; the chain
points (feet + interior `P.q`) are identical, only the side signs flip.  This block builds the
lower chain locally (the `LobeChain` file only provides the upper chain) and re-derives the
straddle/transport/genericity engine against the negated side. -/

/-- The last crossing edge of a lower lobe. -/
def lobeLastEdgeL (L : LowerLobe P ρ x) : Fin n := arcPos L.start (L.len - 1)

/-- The first foot of a lower lobe. -/
def footFirstL (L : LowerLobe P ρ x) : Pt := x + crossTau P ρ x L.start • ρ.r

/-- The last foot of a lower lobe. -/
def footLastL (L : LowerLobe P ρ x) : Pt := x + crossTau P ρ x (lobeLastEdgeL L) • ρ.r

@[simp] lemma side_footFirstL (L : LowerLobe P ρ x) : side ρ.r x (footFirstL L) = 0 :=
  side_ray_point _
@[simp] lemma side_footLastL (L : LowerLobe P ρ x) : side ρ.r x (footLastL L) = 0 :=
  side_ray_point _

/-- The clipped-chain vertices of a lower lobe (identical points to the upper case). -/
def chainPtL (L : LowerLobe P ρ x) (j : Fin (L.len + 1)) : Pt :=
  if j.val = 0 then footFirstL L
  else if j.val = L.len then footLastL L
  else P.q (arcPos L.start j.val)

/-- The clipped chain of a lower lobe. -/
def lobeChainL (L : LowerLobe P ρ x) : Chain L.len where
  p := chainPtL L

@[simp] lemma chainPtL_zero (L : LowerLobe P ρ x) :
    chainPtL L ⟨0, by omega⟩ = footFirstL L := by unfold chainPtL; simp

@[simp] lemma chainPtL_len (L : LowerLobe P ρ x) :
    chainPtL L ⟨L.len, by omega⟩ = footLastL L := by
  have hpos := L.len_pos; unfold chainPtL
  rw [if_neg (show ¬ L.len = 0 by omega), if_pos rfl]

lemma chainPtL_interior (L : LowerLobe P ρ x) {j : ℕ} (hj0 : 0 < j) (hjlen : j < L.len)
    (hj : j < L.len + 1) : chainPtL L ⟨j, hj⟩ = P.q (arcPos L.start j) := by
  unfold chainPtL; rw [if_neg (by simp; omega), if_neg (by simp; omega)]

/-- `side (-r)` is the negation of `side r`. -/
lemma negside_eq (r x p : Pt) : side (-r) x p = - side r x p := by
  unfold side
  rw [show det2 (-r) (p - x) = - det2 r (p - x) from by
    unfold det2; simp only [PiLp.neg_apply]; ring]

/-- Reflected sides of a lower-lobe chain vertex are `≥ 0`. -/
lemma chainPtL_negside_nonneg (L : LowerLobe P ρ x) (j : Fin (L.len + 1)) :
    0 ≤ side (-ρ.r) x (chainPtL L j) := by
  rw [negside_eq]
  rcases Nat.eq_zero_or_pos j.val with hj0 | hj0
  · have : chainPtL L j = footFirstL L := by unfold chainPtL; rw [if_pos hj0]
    rw [this, side_footFirstL]; simp
  · by_cases hjlen : j.val = L.len
    · have : chainPtL L j = footLastL L := by
        unfold chainPtL; rw [if_neg (by omega), if_pos hjlen]
      rw [this, side_footLastL]; simp
    · have hlt : j.val < L.len := by omega
      have : chainPtL L j = P.q (arcPos L.start j.val) := by
        unfold chainPtL; rw [if_neg (by omega), if_neg hjlen]
      rw [this]; linarith [L.interior_neg j.val hj0 hlt]

lemma chainPtL_negside_pos_interior (L : LowerLobe P ρ x) {j : ℕ} (hj0 : 0 < j) (hjlen : j < L.len)
    (hj : j < L.len + 1) : 0 < side (-ρ.r) x (chainPtL L ⟨j, hj⟩) := by
  rw [negside_eq, chainPtL_interior L hj0 hjlen hj]; linarith [L.interior_neg j hj0 hjlen]

lemma lobeChainL_segA (L : LowerLobe P ρ x) (i : Fin L.len) :
    (lobeChainL L).segA i = chainPtL L ⟨i.val, by omega⟩ := by
  unfold Chain.segA lobeChainL; congr 1
lemma lobeChainL_segB (L : LowerLobe P ρ x) (i : Fin L.len) :
    (lobeChainL L).segB i = chainPtL L ⟨i.val + 1, by omega⟩ := by
  unfold Chain.segB lobeChainL; congr 1

/-- Reflected side of any lower-chain carrier point is `≥ 0`. -/
lemma carrierL_negside_nonneg (L : LowerLobe P ρ x) {z : Pt}
    (hz : z ∈ (lobeChainL L).carrier) : 0 ≤ side (-ρ.r) x z := by
  obtain ⟨i, hi⟩ := hz
  rw [seg, segment_eq_image_lineMap] at hi
  obtain ⟨t, ht, rfl⟩ := hi
  rw [side_lineMap_right]
  have ha := chainPtL_negside_nonneg L ⟨i.val, by omega⟩
  have hb := chainPtL_negside_nonneg L ⟨i.val + 1, by omega⟩
  rw [lobeChainL_segA, lobeChainL_segB]
  nlinarith [ha, hb, ht.1, ht.2]

/-- Carrier ∩ base line ⊆ feet, for a lower lobe (via the reflected side). -/
lemma carrierL_side_zero_imp_foot (L : LowerLobe P ρ x) {z : Pt}
    (hz : z ∈ (lobeChainL L).carrier) (hside : side (-ρ.r) x z = 0) :
    z = footFirstL L ∨ z = footLastL L := by
  obtain ⟨i, hi⟩ := hz
  rw [seg, segment_eq_image_lineMap] at hi
  obtain ⟨t, ht, rfl⟩ := hi
  set j := i.val with hjdef
  have hjlt : j < L.len := i.isLt
  have ha0 : 0 ≤ side (-ρ.r) x (chainPtL L ⟨j, by omega⟩) := chainPtL_negside_nonneg L _
  have hb0 : 0 ≤ side (-ρ.r) x (chainPtL L ⟨j + 1, by omega⟩) := chainPtL_negside_nonneg L _
  rw [side_lineMap_right, lobeChainL_segA, lobeChainL_segB] at hside
  have htt := ht.1; have htt2 := ht.2
  by_cases hsA0 : side (-ρ.r) x (chainPtL L ⟨j, by omega⟩) = 0
  · have hj0 : j = 0 := by
      by_contra hjne
      have hjpos : 0 < j := Nat.pos_of_ne_zero hjne
      by_cases hjlen : j = L.len
      · omega
      · exact absurd hsA0 (ne_of_gt (chainPtL_negside_pos_interior L hjpos hjlt (by omega)))
    rcases eq_or_lt_of_le htt with ht0 | ht0
    · left; rw [← ht0, AffineMap.lineMap_apply_zero, lobeChainL_segA]
      unfold chainPtL; rw [if_pos (show j = 0 from hj0)]
    · have hsB0 : side (-ρ.r) x (chainPtL L ⟨j + 1, by omega⟩) = 0 := by
        rw [hsA0, mul_zero, zero_add] at hside
        rcases mul_eq_zero.mp hside with h | h
        · exact absurd h (ne_of_gt ht0)
        · exact h
      have hjlen1 : j + 1 = L.len := by
        by_contra hne
        exact absurd hsB0 (ne_of_gt (chainPtL_negside_pos_interior L (by omega) (by omega) (by omega)))
      left
      rw [AffineMap.lineMap_apply_module, lobeChainL_segA, lobeChainL_segB]
      have hA : chainPtL L ⟨j, by omega⟩ = footFirstL L := by
        unfold chainPtL; rw [if_pos (show j = 0 from hj0)]
      have hB : chainPtL L ⟨j + 1, by omega⟩ = footLastL L := by
        unfold chainPtL; rw [if_neg (by simp), if_pos (show j + 1 = L.len from hjlen1)]
      have hlen1 : L.len = 1 := by omega
      have hfeq : footFirstL L = footLastL L := by
        unfold footFirstL footLastL lobeLastEdgeL
        rw [hlen1]; simp [ZinanCh36LobeChain.arcPos_zero]
      rw [hA, hB, hfeq]; module
  · have hsApos : 0 < side (-ρ.r) x (chainPtL L ⟨j, by omega⟩) := lt_of_le_of_ne ha0 (Ne.symm hsA0)
    have ht1 : t = 1 := by nlinarith [hsApos, hb0, htt, htt2]
    have hsB0 : side (-ρ.r) x (chainPtL L ⟨j + 1, by omega⟩) = 0 := by
      rw [ht1] at hside; simp at hside; tauto
    have hjlen1 : j + 1 = L.len := by
      by_contra hne
      exact absurd hsB0 (ne_of_gt (chainPtL_negside_pos_interior L (by omega) (by omega) (by omega)))
    right
    rw [ht1, AffineMap.lineMap_apply_one, lobeChainL_segB]
    unfold chainPtL; rw [if_neg (by simp), if_pos (show j + 1 = L.len from hjlen1)]

/-! ### The lower straddle/transport engine (reference `-ρ.r`, line `x + ℝ•ρ.r`) -/

/-- Forward-only for a lower lobe (reference `-ρ.r`). -/
lemma lobeChainL_forward (L : LowerLobe P ρ x) {η : Pt} (u₀ : ℝ)
    (hη : (lobeChainL L).Transverse η) (hdet : 0 < det2 (-ρ.r) η) (i : Fin L.len)
    (hspan : Span (side η (x + u₀ • ρ.r) ((lobeChainL L).segA i))
                  (side η (x + u₀ • ρ.r) ((lobeChainL L).segB i))) :
    0 ≤ segTau η (x + u₀ • ρ.r) ((lobeChainL L).segA i) ((lobeChainL L).segB i) := by
  set z₀ := x + u₀ • ρ.r with hz₀
  set a := (lobeChainL L).segA i; set b := (lobeChainL L).segB i
  have hden : det2 η (b - a) ≠ 0 := hη.2 i
  set τ := segTau η z₀ a b with hτdef
  have hrec : z₀ + τ • η = AffineMap.lineMap a b (segU η z₀ a b) := seg_cross_eq hden
  have hz0R : side (-ρ.r) x z₀ = 0 := by rw [negside_eq, hz₀, side_ray_point]; simp
  have hside_ray : side (-ρ.r) x (z₀ + τ • η) = τ * det2 (-ρ.r) η := by
    rw [side_ray_eta, hz0R, zero_add]
  have hside_seg : side (-ρ.r) x (AffineMap.lineMap a b (segU η z₀ a b))
      = (1 - segU η z₀ a b) * side (-ρ.r) x a + segU η z₀ a b * side (-ρ.r) x b :=
    side_lineMap_right (-ρ.r) x a b _
  have hu := segU_mem_Icc_of_span hden hspan
  have ha0 : 0 ≤ side (-ρ.r) x a := by
    show 0 ≤ side (-ρ.r) x ((lobeChainL L).segA i)
    rw [lobeChainL_segA]; exact chainPtL_negside_nonneg L _
  have hb0 : 0 ≤ side (-ρ.r) x b := by
    show 0 ≤ side (-ρ.r) x ((lobeChainL L).segB i)
    rw [lobeChainL_segB]; exact chainPtL_negside_nonneg L _
  have hcross_nonneg : 0 ≤ side (-ρ.r) x (z₀ + τ • η) := by
    rw [hrec, hside_seg]
    have h1 : 0 ≤ 1 - segU η z₀ a b := by linarith [hu.2]
    have h2 : 0 ≤ segU η z₀ a b := hu.1
    have := mul_nonneg h1 ha0
    have := mul_nonneg h2 hb0
    linarith
  rw [hside_ray] at hcross_nonneg
  nlinarith [hcross_nonneg, hdet]

/-- `side η z₀` along the lower chain (total extension). -/
def chainSideL (L : LowerLobe P ρ x) (η : Pt) (u₀ : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then side η (x + u₀ • ρ.r) (footFirstL L)
  else if L.len ≤ k then side η (x + u₀ • ρ.r) (footLastL L)
  else side η (x + u₀ • ρ.r) (P.q (arcPos L.start k))

lemma chainSideL_eq (L : LowerLobe P ρ x) (η : Pt) (u₀ : ℝ) {k : ℕ} (hk : k ≤ L.len) :
    chainSideL L η u₀ k = side η (x + u₀ • ρ.r) (chainPtL L ⟨k, by omega⟩) := by
  have hpos := L.len_pos
  unfold chainSideL chainPtL
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp
  · rw [if_neg (show ¬ k = 0 by omega)]
    by_cases hklen : k = L.len
    · subst hklen; rw [if_pos (le_refl _), if_neg (show ¬ L.len = 0 by omega), if_pos rfl]
    · rw [if_neg (show ¬ L.len ≤ k by omega), if_neg (show ¬ k = 0 by omega), if_neg hklen]

lemma chainSideL_zero (L : LowerLobe P ρ x) (η : Pt) (u₀ : ℝ) :
    chainSideL L η u₀ 0 = side η (x + u₀ • ρ.r) (footFirstL L) := by unfold chainSideL; simp
lemma chainSideL_len (L : LowerLobe P ρ x) (η : Pt) (u₀ : ℝ) :
    chainSideL L η u₀ L.len = side η (x + u₀ • ρ.r) (footLastL L) := by
  have hpos := L.len_pos; unfold chainSideL; rw [if_neg (by omega), if_pos (le_refl _)]

lemma lobeChainL_segCrossInd_eq (L : LowerLobe P ρ x) {η : Pt} (u₀ : ℝ)
    (hη : (lobeChainL L).Transverse η) (hdet : 0 < det2 (-ρ.r) η) (i : Fin L.len)
    (ha : side η (x + u₀ • ρ.r) ((lobeChainL L).segA i) ≠ 0)
    (hb : side η (x + u₀ • ρ.r) ((lobeChainL L).segB i) ≠ 0) :
    segCrossInd η (x + u₀ • ρ.r) ((lobeChainL L).segA i) ((lobeChainL L).segB i)
      = crossInd 0 (side η (x + u₀ • ρ.r) ((lobeChainL L).segA i))
                   (side η (x + u₀ • ρ.r) ((lobeChainL L).segB i)) := by
  set z₀ := x + u₀ • ρ.r
  set a := (lobeChainL L).segA i; set b := (lobeChainL L).segB i
  set sa := side η z₀ a with hsadef; set sb := side η z₀ b with hsbdef
  have hcross : crossInd 0 sa sb = if Span sa sb then 1 else 0 := by
    unfold crossInd
    by_cases hsp : Span sa sb
    · rw [if_pos hsp, if_pos]; have := (span_iff_opp_sign ha hb).mp hsp; simpa using this
    · rw [if_neg hsp, if_neg]; intro h; exact hsp ((span_iff_opp_sign ha hb).mpr (by simpa using h))
  rw [hcross]; unfold segCrossInd SegCrossesRay
  by_cases hsp : Span sa sb
  · rw [if_pos hsp, if_pos]; exact ⟨hsp, lobeChainL_forward L u₀ hη hdet i hsp⟩
  · rw [if_neg hsp, if_neg]; rintro ⟨h, _⟩; exact hsp h

lemma lobeChainL_rayCount_parity (L : LowerLobe P ρ x) {η : Pt} (u₀ : ℝ)
    (hη : (lobeChainL L).Transverse η) (hdet : 0 < det2 (-ρ.r) η)
    (hgen : ∀ j : Fin (L.len + 1), side η (x + u₀ • ρ.r) (chainPtL L j) ≠ 0) :
    (lobeChainL L).rayCount η (x + u₀ • ρ.r) % 2
      = (aboveInd 0 (side η (x + u₀ • ρ.r) (footLastL L))
          - aboveInd 0 (side η (x + u₀ • ρ.r) (footFirstL L))) % 2 := by
  classical
  set z₀ := x + u₀ • ρ.r with hz₀
  set f : ℕ → ℤ := fun k => crossInd 0 (chainSideL L η u₀ k) (chainSideL L η u₀ (k + 1)) with hfdef
  have hper : ∀ i : Fin L.len,
      segCrossInd η z₀ ((lobeChainL L).segA i) ((lobeChainL L).segB i) = f i.val := by
    intro i
    have hsA : side η z₀ ((lobeChainL L).segA i) = chainSideL L η u₀ i.val := by
      rw [lobeChainL_segA, chainSideL_eq L η u₀ (le_of_lt i.isLt)]
    have hsB : side η z₀ ((lobeChainL L).segB i) = chainSideL L η u₀ (i.val + 1) := by
      rw [lobeChainL_segB, chainSideL_eq L η u₀ i.isLt]
    have ha : side η z₀ ((lobeChainL L).segA i) ≠ 0 := by
      rw [lobeChainL_segA]; exact hgen ⟨i.val, by omega⟩
    have hb : side η z₀ ((lobeChainL L).segB i) ≠ 0 := by
      rw [lobeChainL_segB]; exact hgen ⟨i.val + 1, by omega⟩
    rw [lobeChainL_segCrossInd_eq L u₀ hη hdet i ha hb, hfdef]; simp only []; rw [hsA, hsB]
  have hsum : (lobeChainL L).rayCount η z₀ = ∑ k ∈ Finset.range L.len, f k := by
    unfold Chain.rayCount
    rw [Finset.sum_congr rfl (fun i _ => hper i)]; exact Fin.sum_univ_eq_sum_range f L.len
  rw [hsum]
  have hne : ∀ k, k ≤ L.len → chainSideL L η u₀ k ≠ 0 := by
    intro k hk; rw [chainSideL_eq L η u₀ hk]; exact hgen ⟨k, by omega⟩
  have htel := sum_crossInd_emod_two L.len 0 (fun k => chainSideL L η u₀ k) hne
  simp only [hfdef] at htel ⊢
  rw [htel, chainSideL_zero, chainSideL_len]

/-- `tauFirst`/`tauLast` for a lower lobe. -/
def tauFirstL (L : LowerLobe P ρ x) : ℝ := crossTau P ρ x L.start
def tauLastL (L : LowerLobe P ρ x) : ℝ := crossTau P ρ x (lobeLastEdgeL L)

lemma side_eta_footFirstL (L : LowerLobe P ρ x) (η : Pt) (u₀ : ℝ) :
    side η (x + u₀ • ρ.r) (footFirstL L) = (u₀ - tauFirstL L) * det2 ρ.r η := by
  unfold footFirstL tauFirstL; exact side_eta_linePoint ρ.r η x u₀ (crossTau P ρ x L.start)
lemma side_eta_footLastL (L : LowerLobe P ρ x) (η : Pt) (u₀ : ℝ) :
    side η (x + u₀ • ρ.r) (footLastL L) = (u₀ - tauLastL L) * det2 ρ.r η := by
  unfold footLastL tauLastL; exact side_eta_linePoint ρ.r η x u₀ (crossTau P ρ x (lobeLastEdgeL L))

/-- Lower feet straddle: `u₀` between the feet ⟹ odd parity.  (`det2 ρ.r η ≠ 0` since
`det2 (-ρ.r) η > 0`.) -/
lemma aboveInd_feet_straddleL (L : LowerLobe P ρ x) (η : Pt) (u₀ : ℝ)
    (hdet : det2 ρ.r η ≠ 0)
    (hbetween : (tauFirstL L < u₀ ∧ u₀ < tauLastL L) ∨ (tauLastL L < u₀ ∧ u₀ < tauFirstL L)) :
    (aboveInd 0 (side η (x + u₀ • ρ.r) (footLastL L))
      - aboveInd 0 (side η (x + u₀ • ρ.r) (footFirstL L))) % 2 = 1 := by
  rw [side_eta_footFirstL, side_eta_footLastL]
  unfold aboveInd
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos (by nlinarith), if_neg (by nlinarith)]; decide
    · rw [if_neg (by nlinarith), if_pos (by nlinarith)]; decide
  · rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_neg (by nlinarith), if_pos (by nlinarith)]; decide
    · rw [if_pos (by nlinarith), if_neg (by nlinarith)]; decide

/-- **Even count when `u₀` is outside both feet.**  If `u₀` exceeds both feet coords (or is below
both) then the straddle indicator difference is `0` (parity even). -/
lemma aboveInd_feet_outsideL (L : LowerLobe P ρ x) (η : Pt) (u₀ : ℝ)
    (hdet : det2 ρ.r η ≠ 0)
    (houtside : (tauFirstL L < u₀ ∧ tauLastL L < u₀) ∨ (u₀ < tauFirstL L ∧ u₀ < tauLastL L)) :
    (aboveInd 0 (side η (x + u₀ • ρ.r) (footLastL L))
      - aboveInd 0 (side η (x + u₀ • ρ.r) (footFirstL L))) % 2 = 0 := by
  rw [side_eta_footFirstL, side_eta_footLastL]
  unfold aboveInd
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · rcases houtside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_neg (by nlinarith), if_neg (by nlinarith)]; decide
    · rw [if_pos (by nlinarith), if_pos (by nlinarith)]; decide
  · rcases houtside with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_pos (by nlinarith), if_pos (by nlinarith)]; decide
    · rw [if_neg (by nlinarith), if_neg (by nlinarith)]; decide

/-! ### Lower endpoint safety, transport, genericity (reference `-ρ.r`) -/

lemma lobeChainL_p_zero (L : LowerLobe P ρ x) : (lobeChainL L).p 0 = footFirstL L := by
  show chainPtL L 0 = footFirstL L; unfold chainPtL; simp
lemma lobeChainL_p_last (L : LowerLobe P ρ x) :
    (lobeChainL L).p (Fin.last L.len) = footLastL L := by
  show chainPtL L (Fin.last L.len) = footLastL L
  have hpos := L.len_pos; unfold chainPtL
  rw [if_neg (show ¬ (Fin.last L.len).val = 0 by simp; omega),
    if_pos (show (Fin.last L.len).val = L.len from rfl)]

/-- Lower EndpointSafe (reference `-ρ.r`, upper-halfplane wrt `-ρ.r`). -/
lemma lobeChainL_endpointSafe (L : LowerLobe P ρ x) {η z : Pt}
    (hη : (lobeChainL L).Transverse η) (hdet : 0 < det2 (-ρ.r) η)
    (hz : 0 ≤ side (-ρ.r) x z) (hoff : z ∉ (lobeChainL L).carrier) :
    (lobeChainL L).EndpointSafe η z := by
  have hpos := L.len_pos
  constructor
  · rw [lobeChainL_p_zero]
    by_cases hfoot : side η z (footFirstL L) = 0
    · right; refine ⟨hpos, ?_⟩
      set a := (lobeChainL L).segA ⟨0, hpos⟩ with hadef
      set b := (lobeChainL L).segB ⟨0, hpos⟩ with hbdef
      have hafoot : a = footFirstL L := by
        rw [hadef, lobeChainL_segA]; show chainPtL L ⟨0, by omega⟩ = footFirstL L
        unfold chainPtL; simp
      have hden : det2 η (b - a) ≠ 0 := hη.2 ⟨0, hpos⟩
      have haline : side η z a = 0 := by rw [hafoot]; exact hfoot
      have hfeq : z + segTau η z a b • η = a := seg_foot_at_start hden haline
      have hra : side (-ρ.r) x a = 0 := by rw [hafoot, negside_eq, side_footFirstL]; simp
      have hkey : side (-ρ.r) x z + segTau η z a b * det2 (-ρ.r) η = 0 := by
        have := side_ray_eta (-ρ.r) x z η (segTau η z a b); rw [hfeq, hra] at this; linarith
      rcases eq_or_lt_of_le hz with hz0 | hz0
      · exfalso
        have hτ0 : segTau η z a b = 0 := by
          have : segTau η z a b * det2 (-ρ.r) η = 0 := by rw [← hz0] at hkey; linarith
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd h (ne_of_gt hdet)
        apply hoff
        rw [show z = a from by rw [← hfeq, hτ0, zero_smul, add_zero]]
        exact ⟨⟨0, hpos⟩, by rw [hadef, seg]; exact left_mem_segment ℝ _ _⟩
      · show segTau η z a b < 0; nlinarith [hkey, hz0, hdet]
    · left; exact hfoot
  · rw [lobeChainL_p_last]
    by_cases hfoot : side η z (footLastL L) = 0
    · right; refine ⟨hpos, ?_⟩
      set i : Fin L.len := ⟨L.len - 1, by omega⟩ with hidef
      set a := (lobeChainL L).segA i with hadef
      set b := (lobeChainL L).segB i with hbdef
      have hbfoot : b = footLastL L := by
        rw [hbdef, lobeChainL_segB]
        show chainPtL L ⟨(L.len - 1) + 1, by omega⟩ = footLastL L
        have : (⟨(L.len - 1) + 1, by omega⟩ : Fin (L.len + 1)) = ⟨L.len, by omega⟩ := by
          apply Fin.ext; show (L.len - 1) + 1 = L.len; omega
        rw [this]; exact chainPtL_len L
      have hden : det2 η (b - a) ≠ 0 := hη.2 i
      have hbline : side η z b = 0 := by rw [hbfoot]; exact hfoot
      have hfeq : z + segTau η z a b • η = b := seg_foot_at_end hden hbline
      have hrb : side (-ρ.r) x b = 0 := by rw [hbfoot, negside_eq, side_footLastL]; simp
      have hkey : side (-ρ.r) x z + segTau η z a b * det2 (-ρ.r) η = 0 := by
        have := side_ray_eta (-ρ.r) x z η (segTau η z a b); rw [hfeq, hrb] at this; linarith
      rcases eq_or_lt_of_le hz with hz0 | hz0
      · exfalso
        have hτ0 : segTau η z a b = 0 := by
          have : segTau η z a b * det2 (-ρ.r) η = 0 := by rw [← hz0] at hkey; linarith
          rcases mul_eq_zero.mp this with h | h
          · exact h
          · exact absurd h (ne_of_gt hdet)
        apply hoff
        rw [show z = b from by rw [← hfeq, hτ0, zero_smul, add_zero]]
        exact ⟨i, by rw [hbdef, seg]; exact right_mem_segment ℝ _ _⟩
      · show (lobeChainL L).segTauOf η z ⟨L.len - 1, by omega⟩ < 0
        rw [Chain.segTauOf]; show segTau η z a b < 0; nlinarith [hkey, hz0, hdet]
    · left; exact hfoot

lemma transport_XL (X : LowerLobe P ρ x) {η z₀ z₁ : Pt}
    (hη : (lobeChainL X).Transverse η) (hdet : 0 < det2 (-ρ.r) η)
    (havoid : ∀ t ∈ Set.Icc (0:ℝ) 1, AffineMap.lineMap z₀ z₁ t ∉ (lobeChainL X).carrier)
    (hup : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ side (-ρ.r) x (AffineMap.lineMap z₀ z₁ t)) :
    (lobeChainL X).rayCount η z₀ % 2 = (lobeChainL X).rayCount η z₁ % 2 := by
  apply (lobeChainL X).rayCountParity_constant_on_segment hη havoid
  intro t ht; exact lobeChainL_endpointSafe X hη hdet (hup t ht) (havoid t ht)

lemma transport_XL_across_YL_seg (X Y : LowerLobe P ρ x) {η : Pt}
    (hη : (lobeChainL X).Transverse η) (hdet : 0 < det2 (-ρ.r) η)
    (hdisj : Disjoint (lobeChainL X).carrier (lobeChainL Y).carrier) (i : Fin Y.len) :
    (lobeChainL X).rayCount η ((lobeChainL Y).segA i) % 2
      = (lobeChainL X).rayCount η ((lobeChainL Y).segB i) % 2 := by
  apply transport_XL X hη hdet
  · intro t ht hmem
    have hY : AffineMap.lineMap ((lobeChainL Y).segA i) ((lobeChainL Y).segB i) t
        ∈ (lobeChainL Y).carrier := ⟨i, by rw [seg, segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩⟩
    exact (Set.disjoint_left.mp hdisj hmem) hY
  · intro t ht
    have hY : AffineMap.lineMap ((lobeChainL Y).segA i) ((lobeChainL Y).segB i) t
        ∈ (lobeChainL Y).carrier := ⟨i, by rw [seg, segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩⟩
    exact carrierL_negside_nonneg Y hY

lemma transport_XL_over_YL (X Y : LowerLobe P ρ x) {η : Pt}
    (hη : (lobeChainL X).Transverse η) (hdet : 0 < det2 (-ρ.r) η)
    (hdisj : Disjoint (lobeChainL X).carrier (lobeChainL Y).carrier) :
    (lobeChainL X).rayCount η (footFirstL Y) % 2
      = (lobeChainL X).rayCount η (footLastL Y) % 2 := by
  have key : ∀ k, (hk : k < Y.len + 1) →
      (lobeChainL X).rayCount η (footFirstL Y) % 2
        = (lobeChainL X).rayCount η (chainPtL Y ⟨k, hk⟩) % 2 := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [show (⟨0, by omega⟩ : Fin (Y.len + 1)) = 0 from rfl, ← lobeChainL_p_zero Y]; rfl
    | succ k ih =>
      intro hk
      have hklt : k < Y.len := by omega
      rw [ih (by omega)]
      have hstep := transport_XL_across_YL_seg X Y hη hdet hdisj ⟨k, hklt⟩
      rw [lobeChainL_segA, lobeChainL_segB] at hstep; rw [hstep]
  have h := key Y.len (by omega); rw [h, chainPtL_len Y]

lemma transport_XL_along_line (X : LowerLobe P ρ x) {η : Pt} (α β : ℝ)
    (hη : (lobeChainL X).Transverse η) (hdet : 0 < det2 (-ρ.r) η)
    (hfirst : tauFirstL X < min α β ∨ max α β < tauFirstL X)
    (hlast : tauLastL X < min α β ∨ max α β < tauLastL X) :
    (lobeChainL X).rayCount η (x + α • ρ.r) % 2
      = (lobeChainL X).rayCount η (x + β • ρ.r) % 2 := by
  apply transport_XL X hη hdet
  · intro t ht hmem
    set c := (1 - t) * α + t * β with hcdef
    have hpt : AffineMap.lineMap (x + α • ρ.r) (x + β • ρ.r) t = x + c • ρ.r := by
      rw [AffineMap.lineMap_apply_module]; rw [hcdef]; module
    rw [hpt] at hmem
    have hside0 : side (-ρ.r) x (x + c • ρ.r) = 0 := by rw [negside_eq, side_ray_point]; simp
    rcases carrierL_side_zero_imp_foot X hmem hside0 with hf | hf
    · have hc : c = tauFirstL X := by
        have := congrArg (fun p => uCoord ρ.r x p) hf
        simp only at this
        rw [show footFirstL X = x + crossTau P ρ x X.start • ρ.r from rfl,
          uCoord_ray, uCoord_ray] at this
        have := mul_right_cancel₀ (ne_of_gt (normSq_pos ρ.r ρ.r_ne_zero)) this
        rw [tauFirstL]; exact this
      have hcb : min α β ≤ c ∧ c ≤ max α β := by
        constructor
        · rw [hcdef]; nlinarith [ht.1, ht.2, min_le_left α β, min_le_right α β]
        · rw [hcdef]; nlinarith [ht.1, ht.2, le_max_left α β, le_max_right α β]
      rcases hfirst with h | h <;> rw [hc] at hcb <;> [linarith [hcb.1]; linarith [hcb.2]]
    · have hc : c = tauLastL X := by
        have := congrArg (fun p => uCoord ρ.r x p) hf
        simp only at this
        rw [show footLastL X = x + crossTau P ρ x (lobeLastEdgeL X) • ρ.r from rfl,
          uCoord_ray, uCoord_ray] at this
        have := mul_right_cancel₀ (ne_of_gt (normSq_pos ρ.r ρ.r_ne_zero)) this
        rw [tauLastL]; exact this
      have hcb : min α β ≤ c ∧ c ≤ max α β := by
        constructor
        · rw [hcdef]; nlinarith [ht.1, ht.2, min_le_left α β, min_le_right α β]
        · rw [hcdef]; nlinarith [ht.1, ht.2, le_max_left α β, le_max_right α β]
      rcases hlast with h | h <;> rw [hc] at hcb <;> [linarith [hcb.1]; linarith [hcb.2]]
  · intro t ht
    set c := (1 - t) * α + t * β with hcdef
    have hpt : AffineMap.lineMap (x + α • ρ.r) (x + β • ρ.r) t = x + c • ρ.r := by
      rw [AffineMap.lineMap_apply_module]; rw [hcdef]; module
    rw [hpt, negside_eq, side_ray_point]; simp

/-! ### Lower genericity and the lower theorem -/

lemma chainPtL_consecutive_ne (L : LowerLobe P ρ x) (hfeet : footFirstL L ≠ footLastL L)
    {j : ℕ} (hj : j < L.len) :
    chainPtL L ⟨j + 1, by omega⟩ ≠ chainPtL L ⟨j, by omega⟩ := by
  have hpos := L.len_pos
  have hn : 2 ≤ n := by have := P.hthree; omega
  by_cases hj0 : j = 0
  · subst hj0
    have h0 : chainPtL L ⟨0, by omega⟩ = footFirstL L := by unfold chainPtL; simp
    by_cases hlen1 : L.len = 1
    · have h1 : chainPtL L ⟨1, by omega⟩ = footLastL L := by
        rw [show (⟨1, by omega⟩ : Fin (L.len + 1)) = ⟨L.len, by omega⟩ from by
          apply Fin.ext; simp; omega]
        exact chainPtL_len L
      rw [h0, h1]; exact fun h => hfeet h.symm
    · have h1pos : 0 < side (-ρ.r) x (chainPtL L ⟨1, by omega⟩) :=
        chainPtL_negside_pos_interior L (by omega) (by omega) (by omega)
      rw [h0]; intro h
      rw [h, negside_eq, side_footFirstL, neg_zero] at h1pos; exact lt_irrefl _ h1pos
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    by_cases hjlen : j + 1 = L.len
    · have hL : chainPtL L ⟨j + 1, by omega⟩ = footLastL L := by
        rw [show (⟨j + 1, by omega⟩ : Fin (L.len + 1)) = ⟨L.len, by omega⟩ from by
          apply Fin.ext; simp; omega]
        exact chainPtL_len L
      have hjpos2 : 0 < side (-ρ.r) x (chainPtL L ⟨j, by omega⟩) :=
        chainPtL_negside_pos_interior L hjpos (by omega) (by omega)
      rw [hL]; intro h
      rw [← h, negside_eq, side_footLastL, neg_zero] at hjpos2; exact lt_irrefl _ hjpos2
    · have hjlt1 : j + 1 < L.len := by omega
      have hI1 : chainPtL L ⟨j + 1, by omega⟩ = P.q (arcPos L.start (j + 1)) :=
        chainPtL_interior L (by omega) hjlt1 (by omega)
      have hI0 : chainPtL L ⟨j, by omega⟩ = P.q (arcPos L.start j) :=
        chainPtL_interior L hjpos hj (by omega)
      rw [hI1, hI0]; intro h
      have hinj := P.injective_q h
      have hstep : arcPos L.start (j + 1) = cyclicNext (arcPos L.start j) :=
        (ZinanCh36LobeChain.cyclicNext_arcPos L.start j).symm
      rw [hstep] at hinj; exact cyclicNext_ne_self hn (arcPos L.start j) hinj

lemma lobeChainL_segVec_ne_zero (L : LowerLobe P ρ x) (hfeet : footFirstL L ≠ footLastL L)
    (i : Fin L.len) : (lobeChainL L).segB i - (lobeChainL L).segA i ≠ 0 := by
  rw [lobeChainL_segA, lobeChainL_segB, sub_ne_zero]
  exact chainPtL_consecutive_ne L hfeet i.isLt

lemma exists_transverse_lobeChainL (L : LowerLobe P ρ x) (hfeet : footFirstL L ≠ footLastL L) :
    ∃ bad : Finset ℝ, ∀ lam : ℝ, lam ∉ bad →
      (lobeChainL L).Transverse (sweepDir (-ρ.r) lam) := by
  classical
  have hrne : (-ρ.r) ≠ 0 := neg_ne_zero.mpr ρ.r_ne_zero
  let root : Fin L.len → ℝ := fun i =>
    - det2 (perpVec (-ρ.r)) ((lobeChainL L).segB i - (lobeChainL L).segA i)
      / det2 (-ρ.r) ((lobeChainL L).segB i - (lobeChainL L).segA i)
  refine ⟨Finset.univ.image root, fun lam hlam => ?_⟩
  refine ⟨?_, ?_⟩
  · intro h0
    have := det2_r_sweepDir_pos hrne lam; rw [h0] at this; simp [det2] at this
  · intro i
    set v := (lobeChainL L).segB i - (lobeChainL L).segA i with hvdef
    have hv0 : v ≠ 0 := lobeChainL_segVec_ne_zero L hfeet i
    rw [det2_sweepDir_left]
    by_cases hrv : det2 (-ρ.r) v = 0
    · rw [hrv, mul_zero, add_zero]; intro hp
      have hdet_pr : det2 (perpVec (-ρ.r)) (-ρ.r) ≠ 0 := by
        have : det2 (perpVec (-ρ.r)) (-ρ.r) = - det2 (-ρ.r) (perpVec (-ρ.r)) := det2_antisymm _ _
        rw [this]; exact neg_ne_zero.mpr (ne_of_gt (det2_perpVec_pos hrne))
      exact hv0 (eq_zero_of_det2_eq_zero hdet_pr hp hrv)
    · have hlamne : lam ≠ root i := fun h =>
        hlam (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, h.symm⟩)
      intro hz; apply hlamne
      show lam = - det2 (perpVec (-ρ.r)) v / det2 (-ρ.r) v
      field_simp; linarith [hz]

lemma exists_generic_u0L (X : LowerLobe P ρ x) {η : Pt} (hdet : det2 ρ.r η ≠ 0) :
    ∃ bad : Finset ℝ, ∀ u₀ : ℝ, u₀ ∉ bad →
      ∀ j : Fin (X.len + 1), side η (x + u₀ • ρ.r) (chainPtL X j) ≠ 0 := by
  classical
  let root : Fin (X.len + 1) → ℝ := fun j => - det2 η (chainPtL X j - x) / det2 ρ.r η
  refine ⟨Finset.univ.image root, fun u₀ hu₀ j => ?_⟩
  rw [side_eta_base_affine]; intro hz; apply hu₀
  refine Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩
  show - det2 η (chainPtL X j - x) / det2 ρ.r η = u₀
  field_simp; linarith [hz]

/-- **The lower-lobe noninterleaving theorem** (the fixed sweep path; reference `-ρ.r`). -/
theorem lower_lobes_not_interleave
    (X Y : LowerLobe P ρ x)
    (hdisj : Disjoint (lobeChainL X).carrier (lobeChainL Y).carrier)
    (hinter : crossTau P ρ x X.start < crossTau P ρ x Y.start ∧
              crossTau P ρ x Y.start < crossTau P ρ x (lobeLastEdgeL X) ∧
              crossTau P ρ x (lobeLastEdgeL X) < crossTau P ρ x (lobeLastEdgeL Y)) :
    False := by
  classical
  obtain ⟨hXY, hYX, hXYlast⟩ := hinter
  have hi1 : tauFirstL X < tauFirstL Y := hXY
  have hi2 : tauFirstL Y < tauLastL X := hYX
  have hi3 : tauLastL X < tauLastL Y := hXYlast
  have hfeetX : footFirstL X ≠ footLastL X := by
    intro h
    have := congrArg (uCoord ρ.r x) h
    rw [show footFirstL X = x + crossTau P ρ x X.start • ρ.r from rfl,
      show footLastL X = x + crossTau P ρ x (lobeLastEdgeL X) • ρ.r from rfl,
      uCoord_ray, uCoord_ray] at this
    have := mul_right_cancel₀ (ne_of_gt (normSq_pos ρ.r ρ.r_ne_zero)) this
    rw [← tauFirstL, ← tauLastL] at this; linarith
  have hfeetY : footFirstL Y ≠ footLastL Y := by
    intro h
    have := congrArg (uCoord ρ.r x) h
    rw [show footFirstL Y = x + crossTau P ρ x Y.start • ρ.r from rfl,
      show footLastL Y = x + crossTau P ρ x (lobeLastEdgeL Y) • ρ.r from rfl,
      uCoord_ray, uCoord_ray] at this
    have := mul_right_cancel₀ (ne_of_gt (normSq_pos ρ.r ρ.r_ne_zero)) this
    rw [← tauFirstL, ← tauLastL] at this; linarith
  obtain ⟨badX, hbadX⟩ := exists_transverse_lobeChainL X hfeetX
  obtain ⟨badY, hbadY⟩ := exists_transverse_lobeChainL Y hfeetY
  obtain ⟨lam, hlam⟩ := (badX ∪ badY).exists_notMem
  set η := sweepDir (-ρ.r) lam with hηdef
  have hηX : (lobeChainL X).Transverse η := hbadX lam (fun h => hlam (Finset.mem_union_left _ h))
  have hηY : (lobeChainL Y).Transverse η := hbadY lam (fun h => hlam (Finset.mem_union_right _ h))
  have hrne : (-ρ.r) ≠ 0 := neg_ne_zero.mpr ρ.r_ne_zero
  have hdetR : 0 < det2 (-ρ.r) η := det2_r_sweepDir_pos hrne lam
  -- det2 ρ.r η ≠ 0 (= - det2 (-ρ.r) η).
  have hdetr : det2 ρ.r η ≠ 0 := by
    have : det2 ρ.r η = - det2 (-ρ.r) η := by
      rw [show (-ρ.r) = (-1 : ℝ) • ρ.r from by module, det2_smul_left]; ring
    rw [this]; exact neg_ne_zero.mpr (ne_of_gt hdetR)
  -- u₀ ∈ (tauFirstL Y, tauLastL X) avoiding X-vertex projections.
  obtain ⟨badU, hbadU⟩ := exists_generic_u0L X (η := η) hdetr
  obtain ⟨u₀, hu₀io, hu₀bad⟩ : ∃ u₀ : ℝ, u₀ ∈ Set.Ioo (tauFirstL Y) (tauLastL X) ∧ u₀ ∉ badU := by
    have hinf : (Set.Ioo (tauFirstL Y) (tauLastL X)).Infinite := Set.Ioo_infinite hi2
    have hns : ¬ (Set.Ioo (tauFirstL Y) (tauLastL X) ⊆ (badU : Set ℝ)) := fun hsub =>
      hinf (badU.finite_toSet.subset hsub)
    rw [Set.not_subset] at hns; obtain ⟨u₀, hio, hnb⟩ := hns; exact ⟨u₀, hio, hnb⟩
  rw [Set.mem_Ioo] at hu₀io
  have hgenX : ∀ j : Fin (X.len + 1), side η (x + u₀ • ρ.r) (chainPtL X j) ≠ 0 := hbadU u₀ hu₀bad
  -- N(z₀) odd.
  have hodd : (lobeChainL X).rayCount η (x + u₀ • ρ.r) % 2 = 1 := by
    rw [lobeChainL_rayCount_parity X u₀ hηX hdetR hgenX]
    apply aboveInd_feet_straddleL X η u₀ hdetr
    left; exact ⟨by linarith [hu₀io.1], hu₀io.2⟩
  -- choose R > all four feet (far right), avoiding X-vertex projections (generic).
  obtain ⟨badUR, hbadUR⟩ := exists_generic_u0L X (η := η) hdetr
  obtain ⟨R, hRio, hRbad⟩ : ∃ R : ℝ, tauLastL Y < R ∧ R ∉ badUR := by
    have hinf : (Set.Ioo (tauLastL Y) (tauLastL Y + 1)).Infinite := Set.Ioo_infinite (by linarith)
    have hns : ¬ (Set.Ioo (tauLastL Y) (tauLastL Y + 1) ⊆ (badUR : Set ℝ)) := fun hsub =>
      hinf (badUR.finite_toSet.subset hsub)
    rw [Set.not_subset] at hns; obtain ⟨R, hio, hnb⟩ := hns
    rw [Set.mem_Ioo] at hio; exact ⟨R, hio.1, hnb⟩
  have hgenXR : ∀ j : Fin (X.len + 1), side η (x + R • ρ.r) (chainPtL X j) ≠ 0 := hbadUR R hRbad
  -- N(z_R) even.
  have heven : (lobeChainL X).rayCount η (x + R • ρ.r) % 2 = 0 := by
    rw [lobeChainL_rayCount_parity X R hηX hdetR hgenXR]
    apply aboveInd_feet_outsideL X η R hdetr
    left; exact ⟨by linarith, by linarith⟩
  -- transport along z₀ → footFirst Y → footLast Y → z_R.
  have hp1 : (lobeChainL X).rayCount η (x + u₀ • ρ.r) % 2
      = (lobeChainL X).rayCount η (footFirstL Y) % 2 := by
    have hT := transport_XL_along_line X u₀ (tauFirstL Y) hηX hdetR
      (hfirst := by left; rw [lt_min_iff]; exact ⟨by linarith, hi1⟩)
      (hlast := by right; rw [max_lt_iff]; exact ⟨hu₀io.2, by linarith⟩)
    have heq : footFirstL Y = x + tauFirstL Y • ρ.r := rfl
    rw [heq]; exact hT
  have hp2 : (lobeChainL X).rayCount η (footFirstL Y) % 2
      = (lobeChainL X).rayCount η (footLastL Y) % 2 :=
    transport_XL_over_YL X Y hηX hdetR hdisj
  have hp3 : (lobeChainL X).rayCount η (footLastL Y) % 2
      = (lobeChainL X).rayCount η (x + R • ρ.r) % 2 := by
    have heq : footLastL Y = x + tauLastL Y • ρ.r := rfl
    rw [heq]
    exact transport_XL_along_line X (tauLastL Y) R hηX hdetR
      (hfirst := by left; rw [lt_min_iff]; exact ⟨by linarith, by linarith⟩)
      (hlast := by left; rw [lt_min_iff]; exact ⟨by linarith, by linarith⟩)
  have hchain : (1 : ℤ) = 0 := by rw [← hodd, hp1, hp2, hp3, heven]
  exact absurd hchain (by decide)

end

end ProofsInTheBook.ZinanCh36NonInterleave

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.ZinanCh36NonInterleave.lobeChain_rayCount_parity
#print axioms ProofsInTheBook.ZinanCh36NonInterleave.lobeChain_endpointSafe
#print axioms ProofsInTheBook.ZinanCh36NonInterleave.transport_X_over_Y
#print axioms ProofsInTheBook.ZinanCh36NonInterleave.exists_transverse_lobeChain
#print axioms ProofsInTheBook.ZinanCh36NonInterleave.upper_lobes_not_interleave
#print axioms ProofsInTheBook.ZinanCh36NonInterleave.lower_lobes_not_interleave
