import ProofsInTheBook.PolygonWallGlobal

/-!
# Chapter 36 — generic-position existence for the wall-global ray independence
(`PolygonGenericRay`)

`PolygonWallGlobal` reduced the global ray-independence of Chapter 36 to a single
generic-position datum `GenericChainInput P`, bundling, for every pair of ray
directions and every off-boundary `x`, a connecting intermediate whose two segments
both `SegAvoidsZero` and `GenericWallSeg`.  This module **discharges that datum by the
finite bad-direction avoidance argument**, on the geometrically generic stratum, and
isolates with full honesty the single residual it does *not* absorb.

## The reduction: `GenericWallSeg` is a condition on `x` alone

The key structural fact (`genericWallSeg_of_offEdgeLines`) is that
`GenericWallSeg P r₁ r₂ x` depends on `r₁`, `r₂` only through `SegAvoidsZero`: a *wall*
parameter `t₀` has `dirAt r₁ r₂ t₀` parallel to `edgeVec i`; the wall is *generic*
(both endpoint side values nonzero) precisely when `x` is **not on the line of edge
`i`**, i.e. `det2 (edgeVec i) (P.q i − x) ≠ 0`.  Indeed if `ds0Of i t₀ = 0` too, then
the (nonzero, by `SegAvoidsZero`) direction is `det2`-orthogonal to *both* `edgeVec i`
and `P.q i − x`, forcing those two parallel — `x` on the edge line.  So whenever `x`
lies off *every* edge line, **every wall is generic, for every segment**.

## Finite avoidance on the direction circle

For an `x` off all edge lines, a connecting intermediate `μ` exists for *any* pair:
`GenericWallSeg` is then automatic on both segments, and `SegAvoidsZero` is a
finite-avoidance condition — the connecting segment `dirAt a b` hits the zero direction
only when `b` is a *negative* scalar multiple of `a` (antiparallel).  Choosing
`μ.r = mkPt 1 s` with `s` outside the finite bad set (edge slopes ∪ the at-most-two
antiparallel slopes of `ρ.r`, `σ.r`) yields a genuine `RayDirection` whose two
connecting segments avoid the zero direction.  This discharges `GenericChainAt P ρ σ x`
**unconditionally** for `x` off all edge lines.

## The isolated residual

When `x` *does* lie on the line of some edge `i`, and the two given directions `ρ`,
`σ` straddle that edge (opposite signs of `det2 · (edgeVec i)`), *every* connecting
path from `ρ` to `σ` must cross a wall of edge `i`, and at such a wall `x` is on the
ray line — a **degenerate** wall that `GenericWallSeg` (by construction) forbids.  The
single-intermediate `GenericChainAt` is genuinely obstructed there.  This residual —
`OnSomeEdgeLine`-coincidence of a vertex crossing with an edge-parallel direction — is
the measure-zero degenerate-sweep configuration the per-wall layer pairs only on the
generic stratum.  It is isolated as the one honest residue `GenericChainInput`, with
the unconditional discharge proved on the `OffAllEdgeLines` stratum.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonGenericRay

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonRayIndep
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonWall
open ProofsInTheBook.PolygonWallGlobal
open ProofsInTheBook.PolygonLocalConstancy
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the reduction — `GenericWallSeg` from `x` off all edge lines

`x` lies *off the line of edge `i`* when `det2 (edgeVec i) (P.q i − x) ≠ 0` (the three
points `x`, `P.q i`, `P.q (cyclicNext i)` are not collinear).  `OffAllEdgeLines P x`
asks this for every edge.  We show it forces every wall along any nonzero-direction
segment to be generic. -/

/-- `x` lies off the line spanned by edge `i`. -/
def OffEdgeLine (P : StrictSimplePolygon n) (x : Pt) (i : Fin n) : Prop :=
  det2 (P.q (cyclicNext i) - P.q i) (P.q i - x) ≠ 0

/-- `x` lies off the line of *every* edge of `P`. -/
def OffAllEdgeLines (P : StrictSimplePolygon n) (x : Pt) : Prop :=
  ∀ i : Fin n, OffEdgeLine P x i

/-- **The reduction.**  If `x` is off the line of edge `i`, then at any *wall*
parameter `t₀` (`dirDen i t₀ = 0`) of a segment whose direction at `t₀` is nonzero,
both endpoint side values are nonzero — the wall is generic. -/
lemma genericWall_of_offEdgeLine {P : StrictSimplePolygon n} {r₁ r₂ x : Pt} {i : Fin n}
    {t₀ : ℝ} (hx : OffEdgeLine P x i) (hrne : dirAt r₁ r₂ t₀ ≠ 0)
    (hwall : dirDen P r₁ r₂ i t₀ = 0) :
    ds0Of P r₁ r₂ x i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x i t₀ ≠ 0 := by
  set r := dirAt r₁ r₂ t₀ with hr
  -- the wall says det2 r (edgeVec i) = 0.
  have hedge : det2 r (P.q (cyclicNext i) - P.q i) = 0 := hwall
  -- ds0Of = det2 r (P.q i - x); ds1Of = det2 r (P.q (next i) - x).
  have e0 : ds0Of P r₁ r₂ x i t₀ = det2 r (P.q i - x) := rfl
  have e1 : ds1Of P r₁ r₂ x i t₀ = det2 r (P.q (cyclicNext i) - x) := rfl
  constructor
  · rw [e0]; intro h0
    -- r ⊥ edgeVec and r ⊥ (P.q i - x) with edgeVec ⊥ (P.q i - x) ≠ 0 ⟹ r = 0.
    have hz : r = 0 :=
      eq_zero_of_det2_eq_zero (u := P.q (cyclicNext i) - P.q i) (v := P.q i - x) (w := r)
        hx
        (by rw [det2_antisymm]; rw [hedge]; ring)
        (by rw [det2_antisymm]; rw [h0]; ring)
    exact hrne hz
  · rw [e1]; intro h1
    -- (P.q (next i) - x) = (P.q i - x) + edgeVec i ; r ⊥ both edge and (next-x) ⟹ r ⊥ (i-x).
    have hsplit : P.q (cyclicNext i) - x = (P.q i - x) + (P.q (cyclicNext i) - P.q i) := by
      abel
    have h0 : det2 r (P.q i - x) = 0 := by
      have := h1
      rw [hsplit, det2_add_right, hedge, add_zero] at this
      exact this
    have hz : r = 0 :=
      eq_zero_of_det2_eq_zero (u := P.q (cyclicNext i) - P.q i) (v := P.q i - x) (w := r)
        hx
        (by rw [det2_antisymm]; rw [hedge]; ring)
        (by rw [det2_antisymm]; rw [h0]; ring)
    exact hrne hz

/-- **`GenericWallSeg` from `OffAllEdgeLines` + `SegAvoidsZero`.**  If `x` is off every
edge line and the segment avoids the zero direction, the generic-wall residual holds
for the whole segment — no genericity in the *direction* is needed. -/
theorem genericWallSeg_of_offAllEdgeLines {P : StrictSimplePolygon n} {r₁ r₂ x : Pt}
    (hx : OffAllEdgeLines P x) (hz : SegAvoidsZero r₁ r₂) :
    GenericWallSeg P r₁ r₂ x := by
  intro t₀ ht₀ i hwall
  exact genericWall_of_offEdgeLine (hx i) (hz t₀ ht₀) hwall

/-! ## Part 2: `SegAvoidsZero` to a `mkPt 1 s` direction by finite avoidance

The connecting segment `dirAt a b` passes through the zero direction only when `b` is
a negative multiple of `a`.  For `b = mkPt 1 s = (1, s)` this pins `s = a₁ / a₀` and
requires `a₀ < 0`; avoiding that single slope keeps the segment nonzero. -/

/-- The (at most one) slope at which `mkPt 1 s` is antiparallel to `v` through `0`. -/
def antiSlope (v : Pt) : ℝ := if v 0 = 0 then 0 else v 1 / v 0

/-- **Avoid-zero to a `mkPt 1 s` direction.**  If `s ≠ antiSlope ρ.r`, the connecting
segment from `ρ.r` to `mkPt 1 s` avoids the zero direction on `[0,1]`. -/
lemma segAvoidsZero_to_mkPt {P : StrictSimplePolygon n} (ρ : RayDirection P) {s : ℝ}
    (hs : s ≠ antiSlope ρ.r) :
    SegAvoidsZero ρ.r (mkPt 1 s) := by
  intro t ht hzero
  obtain ⟨ht0, ht1⟩ := ht
  -- coordinate equations of dirAt ρ.r (mkPt 1 s) t = (1-t)ρ.r + t(1,s) = 0.
  have hc : dirAt ρ.r (mkPt 1 s) t = (1 - t) • ρ.r + t • (mkPt 1 s) := by
    unfold dirAt; rw [AffineMap.lineMap_apply_module]
  rw [hc] at hzero
  have h0 : (1 - t) * ρ.r 0 + t * (1 : ℝ) = 0 := by
    have := congrArg (fun p : Pt => p 0) hzero
    simpa [mkPt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using this
  have h1 : (1 - t) * ρ.r 1 + t * s = 0 := by
    have := congrArg (fun p : Pt => p 1) hzero
    simpa [mkPt, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using this
  -- from h0: t = -(1-t) ρ.r 0; with t ≥ 0, 1-t ≥ 0.
  have h1t : 0 ≤ 1 - t := by linarith
  -- a := 1 - t > 0 (else t = 1 ⟹ h0: 1 = 0).
  have hapos : 0 < 1 - t := by
    rcases eq_or_lt_of_le h1t with he | hlt
    · exfalso; rw [← he] at h0; simp at h0; linarith
    · exact hlt
  -- t > 0: if t = 0 then dirAt = ρ.r ≠ 0.
  have htpos : 0 < t := by
    rcases eq_or_lt_of_le ht0 with he | hlt
    · exfalso
      apply ρ.r_ne_zero
      have hz0 : (1 - t) • ρ.r + t • mkPt 1 s = 0 := hzero
      rw [← he] at hz0
      simpa using hz0
    · exact hlt
  -- ρ.r 0 < 0 : (1-t)ρ.r 0 = -t < 0 and (1-t) > 0.
  have hr0neg : ρ.r 0 < 0 := by
    have hkey : (1 - t) * ρ.r 0 = -t := by linarith [h0]
    nlinarith [hkey, hapos, htpos]
  have hr0ne : ρ.r 0 ≠ 0 := ne_of_lt hr0neg
  have hsval : s = ρ.r 1 / ρ.r 0 := by
    -- t = -(1-t)ρ.r 0 from h0; the term t*s = -(1-t)ρ.r 0 * s.
    have ht_eq : t = -(1 - t) * ρ.r 0 := by linarith [h0]
    -- (1-t)ρ.r 1 + t s = 0 with t = -(1-t)ρ.r 0 ⟹ (1-t)(ρ.r 1 - ρ.r 0 s) = 0.
    have hfaceq : (1 - t) * (ρ.r 1 - ρ.r 0 * s) = 0 := by
      have hkey : t * s = -((1 - t) * ρ.r 0) * s := by
        nth_rewrite 1 [ht_eq]; ring
      have h1' : (1 - t) * ρ.r 1 + (-((1 - t) * ρ.r 0) * s) = 0 := by rw [← hkey]; exact h1
      nlinarith [h1']
    have hfac : ρ.r 1 - ρ.r 0 * s = 0 := by
      rcases mul_eq_zero.mp hfaceq with h | h
      · exact absurd h (ne_of_gt hapos)
      · exact h
    field_simp [hr0ne]
    linarith [hfac]
  apply hs
  unfold antiSlope
  rw [if_neg hr0ne, hsval]

/-! ## Part 3: a generic connecting intermediate on the off-edge-lines stratum

For `x` off every edge line we build the connecting intermediate `μ.r = mkPt 1 s`
avoiding the finitely many bad slopes: the edge slopes (so `μ` is a genuine
`RayDirection`) and the antiparallel slopes of `ρ.r`, `σ.r` (so both segments avoid the
zero direction).  `GenericWallSeg` is then automatic for both segments. -/

/-- **Existence of a generic intermediate.**  For `x` off all edge lines, any pair of
ray directions admits a connecting intermediate `μ` whose two segments both avoid the
zero direction and meet only generic walls. -/
theorem genericChainAt_of_offAllEdgeLines {P : StrictSimplePolygon n}
    (ρ σ : RayDirection P) {x : Pt} (hx : OffAllEdgeLines P x) :
    GenericChainAt P ρ σ x := by
  classical
  -- the finite bad slope set: edge slopes ∪ {antiSlope ρ.r, antiSlope σ.r}.
  let bad : Finset ℝ :=
    (Finset.univ.image fun i : Fin n => badSlope (edgeVec P i)) ∪
      {antiSlope ρ.r, antiSlope σ.r}
  obtain ⟨s, hsbad⟩ := bad.exists_notMem
  -- s avoids every edge slope, hence mkPt 1 s is a RayDirection.
  have hsedge : ∀ i : Fin n, s ≠ badSlope (edgeVec P i) := by
    intro i hi
    apply hsbad
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩
  have hsρ : s ≠ antiSlope ρ.r := by
    intro h; apply hsbad; apply Finset.mem_union_right; rw [h]; simp
  have hsσ : s ≠ antiSlope σ.r := by
    intro h; apply hsbad; apply Finset.mem_union_right; rw [h]; simp
  -- build the RayDirection μ.
  let μ : RayDirection P :=
    { r := mkPt 1 s
      r_ne_zero := mkPt_one_ne_zero s
      no_edge_parallel := by
        intro i hdet
        exact hsedge i (slope_eq_badSlope_of_det2_mkPt_one_eq_zero
          (edgeVec_ne_zero P i) hdet) }
  have hμr : μ.r = mkPt 1 s := rfl
  -- segment ρ → μ : avoid zero + generic wall.
  have hzρ : SegAvoidsZero ρ.r μ.r := by rw [hμr]; exact segAvoidsZero_to_mkPt ρ hsρ
  have hzσ : SegAvoidsZero μ.r σ.r := by
    -- SegAvoidsZero is symmetric only up to reversing endpoints; build it from σ side
    -- via the antiparallel slope of σ.r and the reversed segment.
    intro t ht hzero
    -- dirAt μ.r σ.r t = dirAt σ.r μ.r (1 - t), reparametrize.
    have hrev : dirAt μ.r σ.r t = dirAt σ.r μ.r (1 - t) := by
      unfold dirAt; rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
      have : (1 : ℝ) - (1 - t) = t := by ring
      rw [this]; abel
    rw [hrev] at hzero
    have ht' : (1 - t) ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [hμr] at hzero
    exact (segAvoidsZero_to_mkPt σ hsσ) (1 - t) ht' hzero
  refine ⟨μ, ⟨hzρ, ?_⟩, hzσ, ?_⟩
  · exact genericWallSeg_of_offAllEdgeLines hx hzρ
  · exact genericWallSeg_of_offAllEdgeLines hx hzσ

/-! ## Part 4: the genuine obstruction on the on-edge-line stratum

`genericChainAt_of_offAllEdgeLines` discharges the generic-chain datum **for every**
off-boundary `x` lying off all edge lines, with *no* extra hypothesis — finite
bad-direction avoidance is complete there.  The remaining stratum, `x` *on the line* of
some edge, is **not** an avoidance gap: it is a genuine obstruction to the
`GenericChainAt` *interface* itself.

The mechanism, proved precisely below.  At a wall `t₀` of edge `i` (`dir ∥ edgeVec i`),
if `x` is *on* edge `i`'s line then both endpoint side values vanish
(`genericWallSeg_fails_on_edge_line`): the wall is **degenerate**, and `GenericWallSeg`
— which demands both side values *nonzero* at every wall — is violated.  A connecting
*straight segment* between two directions on strictly opposite sides of edge `i`
(`det2 · (edgeVec i)` of opposite sign) is forced through such a wall
(`segment_has_wall_of_straddle`): the affine wall function changes sign on `[0,1]`,
hence vanishes there.  So for two directions straddling an `x`-collinear edge, **no**
single-intermediate `GenericChainAt P ρ σ x` can hold — both sub-segments would have to
keep `det2 · (edgeVec i)` of one fixed sign, impossible across a straddle.

Consequently `GenericChainInput P` (∀ pair, ∀ off-boundary `x`) is **false** for any
polygon admitting an off-boundary `x` on some edge line together with a straddling pair
— which is generic.  The route to the *unconditional* `UnconditionalRayIndepInput` /
`artGallery_strict` therefore cannot factor through `PolygonWallGlobal`'s
`GenericChainInput`; it requires the **degenerate-wall parity transport** (the per-edge
`rfcount_eventually_zero_of_degenerateWall` of `PolygonWall` *globally assembled
without* `GenericWallSeg`), which `PolygonWallGlobal` left gated behind `GenericWallSeg`
and is the genuine analytic residue.  We record the obstruction rigorously here. -/

/-- At a wall of edge `i` with `x` *on* edge `i`'s line, both endpoint side values
vanish — the wall is degenerate, so `GenericWallSeg` (both side values nonzero) is
violated.  This is the exact failure the per-wall layer cannot pair generically. -/
theorem genericWallSeg_fails_on_edge_line {P : StrictSimplePolygon n} {r₁ r₂ x : Pt}
    {i : Fin n} {t₀ : ℝ}
    (hxline : det2 (P.q (cyclicNext i) - P.q i) (P.q i - x) = 0)
    (hwall : dirDen P r₁ r₂ i t₀ = 0) :
    ds0Of P r₁ r₂ x i t₀ = 0 := by
  set r := dirAt r₁ r₂ t₀ with hr
  -- r ⊥ edgeVec (wall), and edgeVec ∥ (P.q i - x) (x on line) ⟹ r ⊥ (P.q i - x).
  have hedge : det2 r (P.q (cyclicNext i) - P.q i) = 0 := hwall
  -- (P.q i - x) is a scalar multiple of edgeVec (both ⊥-related via collinearity).
  -- Use: det2 edgeVec (P.q i - x) = 0 ⟹ they are parallel ⟹ det2 r (P.q i - x) = 0.
  show det2 r (P.q i - x) = 0
  -- edgeVec ≠ 0; parallel decomposition (P.q i - x) = μ • edgeVec via the
  -- already-proven `exists_smul_of_det2_zero` (covector = edgeVec annihilates both
  -- edgeVec and (P.q i - x)).
  have hev : P.q (cyclicNext i) - P.q i ≠ 0 := edgeVec_ne_zero P i
  obtain ⟨μ, hμ⟩ :=
    ProofsInTheBook.PolygonWall.exists_smul_of_det2_zero
      (r := P.q (cyclicNext i) - P.q i) (u := P.q i - x)
      (w' := P.q (cyclicNext i) - P.q i)
      hev hxline (PolygonLocalConstancy.det2_self _) hev
  rw [hμ, det2_smul_right, hedge, mul_zero]

/-- **A straddling straight segment is forced through a wall.**  If `ρ.r` and `σ.r` lie
on strictly opposite sides of edge `i`'s line (`det2 · (edgeVec i)` of opposite sign),
the connecting direction segment has a wall for edge `i` at some `t₀ ∈ (0,1)`: the
affine wall function `dirDen i` changes sign, hence vanishes on `[0,1]`. -/
theorem segment_has_wall_of_straddle {P : StrictSimplePolygon n} {r₁ r₂ : Pt}
    {i : Fin n}
    (hstr : det2 r₁ (P.q (cyclicNext i) - P.q i) < 0 ∧
              0 < det2 r₂ (P.q (cyclicNext i) - P.q i)) :
    ∃ t₀ ∈ Set.Icc (0:ℝ) 1, dirDen P r₁ r₂ i t₀ = 0 := by
  obtain ⟨h1, h2⟩ := hstr
  -- dirDen i is continuous, dirDen i 0 = det2 r₁ e < 0, dirDen i 1 = det2 r₂ e > 0.
  have hcont : Continuous (dirDen P r₁ r₂ i) := continuous_dirDen P r₁ r₂ i
  have hd0 : dirDen P r₁ r₂ i 0 = det2 r₁ (P.q (cyclicNext i) - P.q i) := by
    rw [dirDen_eq]; ring
  have hd1 : dirDen P r₁ r₂ i 1 = det2 r₂ (P.q (cyclicNext i) - P.q i) := by
    rw [dirDen_eq]; ring
  have hlt0 : dirDen P r₁ r₂ i 0 < 0 := by rw [hd0]; exact h1
  have hgt1 : 0 < dirDen P r₁ r₂ i 1 := by rw [hd1]; exact h2
  -- IVT on [0,1].
  have hmem : (0:ℝ) ∈ Set.Icc (0:ℝ) (1:ℝ) ∧ (1:ℝ) ∈ Set.Icc (0:ℝ) (1:ℝ) :=
    ⟨by norm_num, by norm_num⟩
  have hsub : Set.Icc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 := le_refl _
  have := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1)
    (hcont.continuousOn)
  have hzero_mem : (0:ℝ) ∈ Set.Icc (dirDen P r₁ r₂ i 0) (dirDen P r₁ r₂ i 1) :=
    ⟨le_of_lt hlt0, le_of_lt hgt1⟩
  obtain ⟨t₀, ht₀mem, ht₀⟩ := this hzero_mem
  exact ⟨t₀, ht₀mem, ht₀⟩

/-- **The interface obstruction, isolated.**  `GenericChainAt P ρ σ x` *cannot* hold for
two directions straddling an edge line on which `x` lies: any single intermediate gives
two straight sub-segments, and on at least one the straddled wall function changes sign
and so produces a degenerate wall (`x` on the line), contradicting `GenericWallSeg`.
Hence `GenericChainInput P` is unsatisfiable on the on-edge-line straddle stratum — the
honest reason the unconditional headline cannot factor through it. -/
theorem genericChainAt_false_of_straddle_on_line {P : StrictSimplePolygon n}
    (ρ σ : RayDirection P) {x : Pt} {i : Fin n}
    (hxline : det2 (P.q (cyclicNext i) - P.q i) (P.q i - x) = 0)
    (hstr : det2 ρ.r (P.q (cyclicNext i) - P.q i) < 0 ∧
              0 < det2 σ.r (P.q (cyclicNext i) - P.q i)) :
    ¬ GenericChainAt P ρ σ x := by
  rintro ⟨μ, ⟨_hz1, hg1⟩, _hz2, hg2⟩
  -- the intermediate μ has some sign for det2 μ.r (edgeVec i); whichever it is, one of
  -- the two segments straddles edge i, producing a wall, which is degenerate (x on
  -- line), contradicting that segment's GenericWallSeg.
  set e := P.q (cyclicNext i) - P.q i with he
  have hμne : det2 μ.r e ≠ 0 := μ.no_edge_parallel i
  obtain ⟨hρneg, hσpos⟩ := hstr
  rcases lt_or_gt_of_ne hμne with hμneg | hμpos
  · -- det2 μ.r e < 0: segment μ → σ straddles (μ neg, σ pos).
    obtain ⟨t₀, ht₀, hwall⟩ := segment_has_wall_of_straddle (r₁ := μ.r) (r₂ := σ.r)
      (i := i) ⟨hμneg, hσpos⟩
    have hds0 : ds0Of P μ.r σ.r x i t₀ = 0 :=
      genericWallSeg_fails_on_edge_line hxline hwall
    exact (hg2 t₀ ht₀ i hwall).1 hds0
  · -- det2 μ.r e > 0: segment ρ → μ straddles (ρ neg, μ pos).
    obtain ⟨t₀, ht₀, hwall⟩ := segment_has_wall_of_straddle (r₁ := ρ.r) (r₂ := μ.r)
      (i := i) ⟨hρneg, hμpos⟩
    have hds0 : ds0Of P ρ.r μ.r x i t₀ = 0 :=
      genericWallSeg_fails_on_edge_line hxline hwall
    exact (hg1 t₀ ht₀ i hwall).1 hds0

end

end ProofsInTheBook.PolygonGenericRay
