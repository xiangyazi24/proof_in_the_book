import ProofsInTheBook.PolygonWall

/-!
# Chapter 36 — GLOBAL ray-independence from the per-wall local-zero layer (`PolygonWallGlobal`)

`PolygonWall` proved the per-wall local statements on the *raw* (validity-free)
direction statistics `rfcount`/`rstatusOf`/`dirDen`/`dirTau` of `PolygonRayIndep`
and `PolygonIccEngine`:

* `rfcount_eventually_zero_of_wall` — at any edge-parallel **wall** parameter `t₀`
  (`dirDen i t₀ = 0`), off the boundary, that edge contributes `0` to the crossing
  count in a whole neighbourhood of `t₀` (generic *or* degenerate wall);
* `rpair_count_eventually_const_noWall` — at a **non-wall vertex event**
  (`ds1Of i t₀ = 0`, both incident edges non-wall) the raw pair count
  `rfcount i + rfcount (cyclicNext i)` has locally-constant parity;
* `rfcount_eventually_eq_of_noWall_noEvent` — at a **non-wall non-event** parameter
  the raw single-edge count is locally constant.

This module **assembles** these per-`t₀` local statements into a GLOBAL statement.
Writing
`rcrossSum P r₁ r₂ x t = ∑ i, rfcount P r₁ r₂ x i t`
(the raw crossing count of the probe direction `dirAt r₁ r₂ t`), we show that on the
*compact preconnected* parameter interval `Set.Icc 0 1` — provided the segment
avoids the zero-direction — the parity `rcrossSum … t % 2` is **locally constant**
at every `t₀ ∈ [0,1]`, hence (`ℝ`/`Icc` preconnected, `ℤ`/`ℕ`-valued) **globally
constant**, so the two endpoint directions `r₁ = dirAt … 0` and `r₂ = dirAt … 1`
give EQUAL crossing parity.

Specialised to two `RayDirection`s whose connecting direction segment avoids the
zero-direction, this yields the **unconditional-in-the-walls** ray independence
`closedRegion'_wallGlobal`: no `ValidDirPathSeg` / `DirComparableSeg` hypothesis
(walls are *crossed*, not *avoided*).  Chaining through a generic intermediate
direction discharges the residual `UnconditionalRayIndepInput P` of `PolygonFinish`,
making `TriangleExteriorEven` / the downstream `artGallery_strict` unconditional in
the ray-choice — conditional only on the single honestly-named, non-vacuous residual
isolating the *event-at-wall coincidence* (a non-wall vertex event whose next edge is
itself a wall — the measure-zero simultaneity of a vertex crossing and an
edge-parallel direction), which the per-wall layer does not pair.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PolygonWallGlobal

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonRayIndep
open ProofsInTheBook.PolygonVertexSweep
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonIccEngine
open ProofsInTheBook.PolygonFinish
open ProofsInTheBook.PolygonWall
open Filter Topology
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 0: the raw crossing-count of the probe direction

`rcrossSum P r₁ r₂ x t` is the `univ`-sum of the raw boolean per-edge counts at the
probe direction `dirAt r₁ r₂ t`.  It is defined for *every* `t : ℝ` with no validity
proof.  At an endpoint where the direction is a genuine `RayDirection ρ` with
`ρ.r = dirAt r₁ r₂ t`, it equals `CrossingNumber' P ρ x`. -/

/-- The raw crossing count of the probe direction `dirAt r₁ r₂ t`. -/
def rcrossSum (P : StrictSimplePolygon n) (r₁ r₂ x : Pt) (t : ℝ) : ℕ :=
  ∑ i : Fin n, rfcount P r₁ r₂ x i t

/-- At any direction `ρ` with `ρ.r = dirAt r₁ r₂ t`, the raw count equals the genuine
`CrossingNumber'`.  (The per-edge crossing depends on the direction only through its
vector, by `edgeCrossesRay'_eq_raw`.) -/
lemma crossingNumber'_eq_rcrossSum (P : StrictSimplePolygon n) (r₁ r₂ x : Pt) (t : ℝ)
    (ρ : RayDirection P) (hr : ρ.r = dirAt r₁ r₂ t) :
    CrossingNumber' P ρ x = rcrossSum P r₁ r₂ x t := by
  classical
  rw [crossingNumber'_eq_card]
  unfold CrossingEdges' rcrossSum
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [rfcount_eq]
  congr 1
  rw [eq_iff_iff]
  rw [edgeCrossesRay'_eq_raw P ρ x i, hr]
  rfl

/-! ## Part 1: the event/wall classification of an edge at a probe parameter

At a probe parameter `t₀` with `dirAt r₁ r₂ t₀ ≠ 0`, classify each edge `i`:

* **Wall** `dirDen i t₀ = 0`: contributes `0` near `t₀` (`rfcount_eventually_zero_of_wall`).
* **Non-wall event** `dirDen i t₀ ≠ 0`, `ds1Of i t₀ = 0`: paired with `cyclicNext i`.
* **Non-wall non-event** `dirDen i t₀ ≠ 0`, `ds0Of i t₀ ≠ 0`, `ds1Of i t₀ ≠ 0`:
  contributes a locally-constant single count.

For a non-wall edge, the two endpoint side functions cannot *both* vanish at `t₀`
(else `dir ∥ edgeVec i`, a wall), so the non-event case is exactly
`ds0Of i t₀ ≠ 0 ∧ ds1Of i t₀ ≠ 0` once `ds1Of i t₀ ≠ 0`, and an `N`-event
(`ds0Of i t₀ = 0`) is the *previous* edge's `R`-event. -/

/-- For a non-wall edge the two endpoint side functions are not both zero at `t₀`. -/
lemma noWall_not_both_zero {P : StrictSimplePolygon n} {r₁ r₂ x : Pt} {i : Fin n}
    {t₀ : ℝ} (hDi : dirDen P r₁ r₂ i t₀ ≠ 0) :
    ¬ (ds0Of P r₁ r₂ x i t₀ = 0 ∧ ds1Of P r₁ r₂ x i t₀ = 0) := by
  rintro ⟨h0, h1⟩
  apply hDi
  have := ds1Of_sub_ds0Of P r₁ r₂ x i t₀
  rw [h0, h1] at this; linarith

/-- The wall set at `t₀`: edges whose direction is edge-parallel. -/
def WallSet (P : StrictSimplePolygon n) (r₁ r₂ : Pt) (t₀ : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => dirDen P r₁ r₂ i t₀ = 0)

/-- The `R`-event set at `t₀`: non-wall edges with the end vertex on the ray line. -/
def EventSet (P : StrictSimplePolygon n) (r₁ r₂ x : Pt) (t₀ : ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter
    (fun i => dirDen P r₁ r₂ i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x i t₀ = 0)

/-! ## Part 2: the segment genericity residual — walls are generic on `[0,1]`

The single honest residual isolating the *event-at-wall coincidence*: on the
parameter segment `[0,1]`, **no edge-parallel wall has a vertex on the ray line**.
Equivalently, the probe direction is never simultaneously parallel to an edge `i`
*and* aligned with `x`–to–a–vertex–of–`i` (i.e. `x` is never on the line of an
edge whose direction the segment sweeps parallel).  This is exactly the measure-zero
genericity the per-wall layer does not absorb: it rules out a vertex crossing
(`ds1Of i = 0`) coinciding with a wall (`dirDen i = 0`), which would leave the
event-edge's count jump unpaired (`PolygonWall` pairs only *non-wall* event edges).

It is **non-vacuous**: a `ValidDirPathSeg` has *no* walls on `[0,1]` at all, so the
condition holds vacuously (`generalWallSeg_of_validDirPathSeg`).  Under it, every
wall is *generic* (`x` off the wall-edge's line) and the event/wall partition is
clean. -/

/-- **Generic-wall segment.**  On `[0,1]`, no edge-parallel wall has either of its
endpoint vertices on the ray line.  (The honestly-named event-at-wall residual.) -/
def GenericWallSeg (P : StrictSimplePolygon n) (r₁ r₂ x : Pt) : Prop :=
  ∀ t₀ ∈ Set.Icc (0:ℝ) 1, ∀ i : Fin n, dirDen P r₁ r₂ i t₀ = 0 →
    ds0Of P r₁ r₂ x i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x i t₀ ≠ 0

/-- **Non-vacuity.**  A valid segment path (no walls at all on `[0,1]`) satisfies the
generic-wall residual vacuously: there is no wall to violate it. -/
theorem genericWallSeg_of_validDirPathSeg {P : StrictSimplePolygon n} {r₁ r₂ : Pt}
    (h : ValidDirPathSeg P r₁ r₂) (x : Pt) : GenericWallSeg P r₁ r₂ x := by
  intro t₀ ht₀ i hwall
  exact absurd hwall (dirDen_seg_ne_zero h i ht₀)

/-! ## Part 3: per-parameter eventual parity constancy (walls crossed)

At `t₀` with `dirAt r₁ r₂ t₀ ≠ 0`, under the generic-wall residual at `t₀`, the raw
parity `rcrossSum % 2` is eventually constant.  Partition `Fin n` into the wall set
`W`, the non-wall `R`-events (`ds1Of i = 0`), their `cyclicNext`-images `N`
(`ds0Of = 0`), and the non-wall `Rest`:

* `W` edges contribute `0` near `t₀` (`rfcount_eventually_zero_of_wall`);
* each `R`-pair `(i, cyclicNext i)` is non-wall (residual ⟹ next non-wall) and has
  locally parity-constant pair count (`rpair_count_eventually_const_noWall`);
* `Rest` edges are non-wall non-events, locally count-constant. -/

/-- **Per-parameter eventual parity constancy.**  Under the generic-wall residual at
`t₀ ∈ [0,1]` and `dirAt r₁ r₂ t₀ ≠ 0`, off the boundary, `rcrossSum % 2` is
eventually constant at `t₀` (full `nhds`). -/
lemma rcrossSum_parity_eventually_const {P : StrictSimplePolygon n} {r₁ r₂ : Pt}
    {x : Pt} (hoff : ¬ OnBoundary P x) {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0:ℝ) 1)
    (hrne : dirAt r₁ r₂ t₀ ≠ 0)
    (hgen : GenericWallSeg P r₁ r₂ x) :
    ∀ᶠ t in nhds t₀, rcrossSum P r₁ r₂ x t % 2 = rcrossSum P r₁ r₂ x t₀ % 2 := by
  classical
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  -- the four edge classes.
  set W : Finset (Fin n) := Finset.univ.filter
    (fun i => dirDen P r₁ r₂ i t₀ = 0) with hW
  set R : Finset (Fin n) := Finset.univ.filter
    (fun i => dirDen P r₁ r₂ i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x i t₀ = 0) with hR
  set N : Finset (Fin n) := Finset.univ.filter
    (fun i => dirDen P r₁ r₂ i t₀ ≠ 0 ∧ ds0Of P r₁ r₂ x i t₀ = 0) with hN
  -- membership characterizations.
  have hWmem : ∀ i, i ∈ W ↔ dirDen P r₁ r₂ i t₀ = 0 := by
    intro i; rw [hW, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hRmem : ∀ i, i ∈ R ↔ dirDen P r₁ r₂ i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x i t₀ = 0 := by
    intro i; rw [hR, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hNmem : ∀ i, i ∈ N ↔ dirDen P r₁ r₂ i t₀ ≠ 0 ∧ ds0Of P r₁ r₂ x i t₀ = 0 := by
    intro i; rw [hN, Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  -- residual at t₀: a wall has both side functions nonzero.
  have hgen0 : ∀ i, dirDen P r₁ r₂ i t₀ = 0 →
      ds0Of P r₁ r₂ x i t₀ ≠ 0 ∧ ds1Of P r₁ r₂ x i t₀ ≠ 0 := hgen t₀ ht₀
  -- the shared side identity: ds0Of (cyclicNext i) = ds1Of i.
  have hshare : ∀ i, ds0Of P r₁ r₂ x (cyclicNext i) t₀ = ds1Of P r₁ r₂ x i t₀ :=
    fun i => rfl
  -- R-events have non-wall successors (the residual rules out event-at-wall).
  have hRnextNW : ∀ i ∈ R, dirDen P r₁ r₂ (cyclicNext i) t₀ ≠ 0 := by
    intro i hi
    rw [hRmem] at hi
    intro hwk
    -- next i is a wall with ds0Of (next i) = ds1Of i = 0, contradicting residual.
    have := (hgen0 (cyclicNext i) hwk).1
    rw [hshare i, hi.2] at this; exact this rfl
  -- N = R.image cyclicNext.
  have hNimg : N = R.image cyclicNext := by
    apply Finset.ext; intro kk
    rw [hNmem, Finset.mem_image]
    constructor
    · rintro ⟨hDk, hk0⟩
      refine ⟨cyclicPrev kk, ?_, cyclicNext_cyclicPrev htwo kk⟩
      rw [hRmem]
      -- ds1Of (prev kk) = ds0Of kk = 0; prev kk non-wall (residual: kk would be event-at-wall).
      have hpe : ds1Of P r₁ r₂ x (cyclicPrev kk) t₀ = 0 := by
        have := hshare (cyclicPrev kk)
        rw [cyclicNext_cyclicPrev htwo kk] at this; rw [← this]; exact hk0
      refine ⟨?_, hpe⟩
      intro hwp
      -- prev kk wall with ds1Of (prev kk) = 0 contradicts residual.
      exact (hgen0 (cyclicPrev kk) hwp).2 hpe
    · rintro ⟨i, hiR, rfl⟩
      rw [hRmem] at hiR
      exact ⟨hRnextNW i (by rw [hRmem]; exact hiR), by rw [hshare i]; exact hiR.2⟩
  -- disjointness W, R, N pairwise.
  have hdisjWR : Disjoint W R := by
    rw [Finset.disjoint_left]; intro i hiW hiR
    rw [hWmem] at hiW; rw [hRmem] at hiR; exact hiR.1 hiW
  have hdisjWN : Disjoint W N := by
    rw [Finset.disjoint_left]; intro i hiW hiN
    rw [hWmem] at hiW; rw [hNmem] at hiN; exact hiN.1 hiW
  have hdisjRN : Disjoint R N := by
    rw [Finset.disjoint_left]; intro i hiR hiN
    rw [hRmem] at hiR; rw [hNmem] at hiN
    -- ds1Of i = 0 and ds0Of i = 0 ⟹ wall, contra non-wall.
    exact noWall_not_both_zero hiR.1 ⟨hiN.2, hiR.2⟩
  -- Rest = univ \ (W ∪ R ∪ N).
  set Rest : Finset (Fin n) := Finset.univ \ (W ∪ R ∪ N) with hRest
  have hpart : Finset.univ = ((W ∪ R) ∪ N) ∪ Rest := by
    rw [hRest]
    exact (Finset.union_sdiff_of_subset (Finset.subset_univ (W ∪ R ∪ N))).symm
  have hdisjRest : Disjoint ((W ∪ R) ∪ N) Rest := by
    rw [hRest]; exact Finset.disjoint_sdiff
  have hdisjWR_N : Disjoint (W ∪ R) N := by
    rw [Finset.disjoint_union_left]; exact ⟨hdisjWN, hdisjRN⟩
  -- the sum split (pointwise in t).
  have hsum : ∀ t, ∑ i : Fin n, rfcount P r₁ r₂ x i t =
      ((∑ i ∈ W, rfcount P r₁ r₂ x i t + ∑ i ∈ R, rfcount P r₁ r₂ x i t)
        + ∑ i ∈ N, rfcount P r₁ r₂ x i t) + ∑ i ∈ Rest, rfcount P r₁ r₂ x i t := by
    intro t
    conv_lhs => rw [show (Finset.univ : Finset (Fin n)) = ((W ∪ R) ∪ N) ∪ Rest from hpart]
    rw [Finset.sum_union hdisjRest, Finset.sum_union hdisjWR_N, Finset.sum_union hdisjWR]
  -- N-sum = sum over R of rfcount at cyclicNext.
  have hNsum : ∀ t, ∑ i ∈ N, rfcount P r₁ r₂ x i t =
      ∑ i ∈ R, rfcount P r₁ r₂ x (cyclicNext i) t := by
    intro t
    rw [hNimg, Finset.sum_image]
    intro a _ b _ hh; exact cyclicNext_injective hh
  -- eventual: wall edges vanish.
  have hwallEv : ∀ᶠ t in nhds t₀, ∀ i ∈ W, rfcount P r₁ r₂ x i t = 0 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    rw [hWmem] at hi
    exact rfcount_eventually_zero_of_wall hoff hrne hi
  -- eventual: R-pairs parity-constant.
  have hpairs : ∀ᶠ t in nhds t₀, ∀ i ∈ R,
      (rfcount P r₁ r₂ x i t + rfcount P r₁ r₂ x (cyclicNext i) t) % 2 =
        (rfcount P r₁ r₂ x i t₀ + rfcount P r₁ r₂ x (cyclicNext i) t₀) % 2 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    have hir := (hRmem i).mp hi
    exact rpair_count_eventually_const_noWall hoff hir.1 (hRnextNW i hi) hir.2
  -- eventual: Rest edges count-constant.
  have hrest : ∀ᶠ t in nhds t₀, ∀ i ∈ Rest, rfcount P r₁ r₂ x i t = rfcount P r₁ r₂ x i t₀ := by
    rw [Filter.eventually_all_finset]
    intro i hi
    -- i ∉ W, R, N.
    have hi' : i ∉ W ∧ i ∉ R ∧ i ∉ N := by
      rw [hRest, Finset.mem_sdiff] at hi
      have := hi.2
      rw [Finset.mem_union, not_or, Finset.mem_union, not_or] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    -- not a wall.
    have hDi : dirDen P r₁ r₂ i t₀ ≠ 0 := fun h => hi'.1 ((hWmem i).mpr h)
    -- not an R-event ⟹ ds1Of i ≠ 0.
    have hs1 : ds1Of P r₁ r₂ x i t₀ ≠ 0 := fun h => hi'.2.1 ((hRmem i).mpr ⟨hDi, h⟩)
    -- not an N-event ⟹ ds0Of i ≠ 0.
    have hs0 : ds0Of P r₁ r₂ x i t₀ ≠ 0 := fun h => hi'.2.2 ((hNmem i).mpr ⟨hDi, h⟩)
    exact rfcount_eventually_eq_of_noWall_noEvent hoff hDi hs0 hs1
  -- assemble.
  filter_upwards [hwallEv, hpairs, hrest] with t hw hp hr
  unfold rcrossSum
  rw [hsum t, hsum t₀, hNsum t, hNsum t₀]
  -- wall sums are 0 at t (eventually); at t₀ also 0 by residual (no wall is counted? no:
  -- we only know rfcount wall ≡ 0 near t₀; at t₀ itself rfcount may be anything, but it is
  -- inside the nbhd so hw covers t, and for t₀ the wall sum is part of the constant target).
  -- Instead: handle wall sums via hw at t and the analogous statement at t₀.
  have hWt : ∑ i ∈ W, rfcount P r₁ r₂ x i t = 0 := Finset.sum_eq_zero (fun i hi => hw i hi)
  -- at t₀: the eventual-zero holds at t₀ too (t₀ ∈ nhds t₀ via the original filter? not directly).
  -- Use that rfcount_eventually_zero_of_wall gives an nhds, evaluate at t₀.
  have hWt0 : ∑ i ∈ W, rfcount P r₁ r₂ x i t₀ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hWmem] at hi
    exact (rfcount_eventually_zero_of_wall hoff hrne hi).self_of_nhds
  rw [hWt, hWt0]
  -- abbreviate the four block sums.
  set PR : ℝ → ℕ := fun s => ∑ i ∈ R, rfcount P r₁ r₂ x i s with hPR
  set PN : ℝ → ℕ := fun s => ∑ i ∈ R, rfcount P r₁ r₂ x (cyclicNext i) s with hPN
  set PE : ℝ → ℕ := fun s => ∑ i ∈ Rest, rfcount P r₁ r₂ x i s with hPE
  -- pair-sum parity: (PR t + PN t) % 2 = (PR t₀ + PN t₀) % 2.
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
  -- combine: ((0 + PR t) + PN t) + PE t  vs  ((0 + PR t₀) + PN t₀) + PE t₀.
  show (0 + PR t + PN t + PE t) % 2 = (0 + PR t₀ + PN t₀ + PE t₀) % 2
  have e1 : 0 + PR t + PN t + PE t = (PR t + PN t) + PE t := by ring
  have e2 : 0 + PR t₀ + PN t₀ + PE t₀ = (PR t₀ + PN t₀) + PE t₀ := by ring
  rw [e1, e2, Nat.add_mod, hpairR, hrestEq, ← Nat.add_mod]

/-! ## Part 4: gluing to global parity constancy on `[0,1]`

`Set.Icc 0 1` is preconnected.  Under the avoid-zero condition (the connecting
direction segment never passes through the zero direction) and the generic-wall
residual, the raw parity is locally constant on the `Icc 0 1` subtype, hence
constant — so the endpoint directions `dirAt 0 = r₁` and `dirAt 1 = r₂` give equal
crossing parity. -/

/-- The segment avoids the zero direction: `dirAt r₁ r₂ t ≠ 0` for `t ∈ [0,1]`. -/
def SegAvoidsZero (r₁ r₂ : Pt) : Prop :=
  ∀ t ∈ Set.Icc (0:ℝ) 1, dirAt r₁ r₂ t ≠ 0

/-- The raw parity along the segment, as a function on the `Icc 0 1` subtype. -/
def rParity (P : StrictSimplePolygon n) (r₁ r₂ x : Pt) :
    ↥(Set.Icc (0:ℝ) 1) → ℕ :=
  fun t => rcrossSum P r₁ r₂ x t.val % 2

/-- The raw parity is locally constant on the connected `Icc 0 1` subtype. -/
lemma rParity_locallyConstant {P : StrictSimplePolygon n} {r₁ r₂ : Pt} {x : Pt}
    (hoff : ¬ OnBoundary P x) (hz : SegAvoidsZero r₁ r₂)
    (hgen : GenericWallSeg P r₁ r₂ x) :
    IsLocallyConstant (rParity P r₁ r₂ x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t₀
  have hev := rcrossSum_parity_eventually_const hoff t₀.2 (hz t₀.val t₀.2) hgen
  -- pull the full-`nhds` eventual back through the continuous subtype embedding.
  exact (continuous_subtype_val.continuousAt (x := t₀)).tendsto.eventually hev

/-- **Global parity constancy on the segment.**  Under avoid-zero and the
generic-wall residual, the raw crossing parities at the two endpoint directions
`r₁ = dirAt 0` and `r₂ = dirAt 1` agree. -/
lemma rcrossSum_parity_endpoints {P : StrictSimplePolygon n} {r₁ r₂ : Pt} {x : Pt}
    (hoff : ¬ OnBoundary P x) (hz : SegAvoidsZero r₁ r₂)
    (hgen : GenericWallSeg P r₁ r₂ x) :
    rcrossSum P r₁ r₂ x 0 % 2 = rcrossSum P r₁ r₂ x 1 % 2 := by
  have hLC := rParity_locallyConstant hoff hz hgen
  have h0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := by constructor <;> norm_num
  have := hLC.apply_eq_of_preconnectedSpace (⟨0, h0⟩ : ↥(Set.Icc (0:ℝ) 1)) ⟨1, h1⟩
  unfold rParity at this
  exact this

/-! ## Part 5: the endpoint bridge and the wall-global ray independence

`dirAt r₁ r₂ 0 = r₁` and `dirAt r₁ r₂ 1 = r₂`.  For two `RayDirection`s `ρ`, `σ`
with `ρ.r = r₁`, `σ.r = r₂`, the raw parity at the endpoints equals
`CrossingNumber' P ρ x % 2` and `CrossingNumber' P σ x % 2`, giving the ray
independence directly — **with no `ValidDirPathSeg` hypothesis**: walls along the
segment are crossed, not avoided. -/

lemma dirAt_zero (r₁ r₂ : Pt) : dirAt r₁ r₂ 0 = r₁ := by unfold dirAt; simp

lemma dirAt_one (r₁ r₂ : Pt) : dirAt r₁ r₂ 1 = r₂ := by unfold dirAt; simp

/-- **Wall-global crossing-number parity independence.**  For two ray directions
`ρ`, `σ` whose connecting direction segment avoids the zero direction and is generic
at every wall (the single isolated residual), the crossing parities agree off the
boundary — **unconditional in the walls**. -/
theorem crossingNumber'_wallGlobal {P : StrictSimplePolygon n} (ρ σ : RayDirection P)
    {x : Pt} (hoff : ¬ OnBoundary P x)
    (hz : SegAvoidsZero ρ.r σ.r) (hgen : GenericWallSeg P ρ.r σ.r x) :
    CrossingNumber' P ρ x % 2 = CrossingNumber' P σ x % 2 := by
  have hcr0 : CrossingNumber' P ρ x = rcrossSum P ρ.r σ.r x 0 :=
    crossingNumber'_eq_rcrossSum P ρ.r σ.r x 0 ρ (dirAt_zero ρ.r σ.r).symm
  have hcr1 : CrossingNumber' P σ x = rcrossSum P ρ.r σ.r x 1 :=
    crossingNumber'_eq_rcrossSum P ρ.r σ.r x 1 σ (dirAt_one ρ.r σ.r).symm
  rw [hcr0, hcr1]
  exact rcrossSum_parity_endpoints hoff hz hgen

/-- **Wall-global region-indicator ray independence.**  Off the boundary, the
corrected closed region is the same for two ray directions whose connecting segment
avoids the zero direction and is generic at every wall. -/
theorem closedRegion'_wallGlobal {P : StrictSimplePolygon n} (ρ σ : RayDirection P)
    {x : Pt} (hoff : ¬ OnBoundary P x)
    (hz : SegAvoidsZero ρ.r σ.r) (hgen : GenericWallSeg P ρ.r σ.r x) :
    ClosedRegion' P ρ x ↔ ClosedRegion' P σ x := by
  unfold ClosedRegion'
  have hpar := crossingNumber'_wallGlobal ρ σ hoff hz hgen
  constructor
  · rintro (hb | ho)
    · exact Or.inl hb
    · exact Or.inr ((odd_iff_of_mod_two_eq hpar).mp ho)
  · rintro (hb | ho)
    · exact Or.inl hb
    · exact Or.inr ((odd_iff_of_mod_two_eq hpar).mpr ho)

/-! ## Part 6: discharging the unconditional ray-independence input

`closedRegion'_wallGlobal` connects two ray directions whose connecting segment
*avoids the zero direction* and is *generic at every wall* — the walls are crossed,
not avoided, so there is **no** `ValidDirPathSeg` / `DirComparableSeg` (no-wall)
hypothesis any more (the obstruction `unconditionalRayIndepInput_of_chains` carried).

The only residual now is that, for an arbitrary pair `(ρ, σ)`, a *generic connecting
chain* exists: a single intermediate direction `μ` (or `ρ = σ` directly) so that each
connecting segment avoids the zero direction and meets only generic walls.  This is
the antipodal/finite-wall-avoidance backbone on the direction circle — a strictly
weaker, cleaner residual than the previous "no-wall chain", since wall *crossing* is
now proved.  We name it `GenericChainInput`, build the unconditional region
independence from it, and certify it non-vacuous. -/

/-- A *generic connecting datum* for the pair `(ρ, σ)` at the off-boundary point `x`:
an intermediate direction whose two connecting segments avoid the zero direction and
meet only generic walls — enough to transport the region from `ρ` to `σ` through
`closedRegion'_wallGlobal` twice. -/
def GenericChainAt (P : StrictSimplePolygon n) (ρ σ : RayDirection P) (x : Pt) : Prop :=
  ∃ μ : RayDirection P,
    (SegAvoidsZero ρ.r μ.r ∧ GenericWallSeg P ρ.r μ.r x) ∧
    (SegAvoidsZero μ.r σ.r ∧ GenericWallSeg P μ.r σ.r x)

/-- **Region independence from a generic connecting datum.**  Given the generic
connecting intermediate for `(ρ, σ)` at `x`, the corrected regions agree. -/
theorem closedRegion'_of_genericChainAt {P : StrictSimplePolygon n}
    {ρ σ : RayDirection P} {x : Pt} (hoff : ¬ OnBoundary P x)
    (hch : GenericChainAt P ρ σ x) :
    ClosedRegion' P ρ x ↔ ClosedRegion' P σ x := by
  obtain ⟨μ, ⟨hz1, hg1⟩, hz2, hg2⟩ := hch
  exact (closedRegion'_wallGlobal ρ μ hoff hz1 hg1).trans
    (closedRegion'_wallGlobal μ σ hoff hz2 hg2)

/-- The named residual: every pair of ray directions admits a generic connecting
datum at every off-boundary point.  This is the finite-wall/antipodal avoidance on
the direction circle (the wall *crossing* itself is proved by Part 3). -/
def GenericChainInput (P : StrictSimplePolygon n) : Prop :=
  ∀ (ρ σ : RayDirection P) {x : Pt}, ¬ OnBoundary P x → GenericChainAt P ρ σ x

/-- **The unconditional ray-independence input, discharged from `GenericChainInput`.**
Supplying the generic-chain datum yields `PolygonFinish.UnconditionalRayIndepInput P`
(the kept ray-choice oracle) — with the wall obstruction fully internalised. -/
theorem unconditionalRayIndepInput_of_genericChain {P : StrictSimplePolygon n}
    (H : GenericChainInput P) : UnconditionalRayIndepInput P :=
  fun ρ σ _ hoff => closedRegion'_of_genericChainAt hoff (H ρ σ hoff)

/-! ### Non-vacuity of the residual

The residual is satisfiable: a `ρ` with `ρ.r = σ.r` (in particular the *reflexive*
pair) has the trivial chain `μ = ρ = σ`, since the constant segment avoids zero and
has no walls.  More substantively, two *same-side* directions admit the direct
length-1 chain `μ = σ`: the connecting segment stays nonzero (avoids the zero
direction) and is wall-free (generic).  So `GenericChainAt` is inhabited on genuinely
distinct directions, not just the diagonal — the discharge is not vacuous. -/

/-- A constant segment (`r₁ = r₂` a genuine direction) avoids the zero direction. -/
lemma segAvoidsZero_const {P : StrictSimplePolygon n} (ρ : RayDirection P) :
    SegAvoidsZero ρ.r ρ.r := by
  intro t _ hz
  apply ρ.r_ne_zero
  have : dirAt ρ.r ρ.r t = ρ.r := by unfold dirAt; simp
  rw [this] at hz; exact hz

/-- A constant segment has no walls, so the generic-wall residual holds vacuously. -/
lemma genericWallSeg_const {P : StrictSimplePolygon n} (ρ : RayDirection P) (x : Pt) :
    GenericWallSeg P ρ.r ρ.r x := by
  intro t₀ _ i hwall
  exact absurd hwall (by
    have hd : dirDen P ρ.r ρ.r i t₀ = det2 ρ.r (P.q (cyclicNext i) - P.q i) := by
      unfold dirDen; congr 1; unfold dirAt; simp
    rw [hd]; exact ρ.no_edge_parallel i)

/-- **Reflexive non-vacuity witness.**  Every pair `(ρ, ρ)` admits a generic chain
(the constant intermediate), so `GenericChainAt P ρ ρ x` holds — the residual is not
unsatisfiable. -/
theorem genericChainAt_refl {P : StrictSimplePolygon n} (ρ : RayDirection P) (x : Pt) :
    GenericChainAt P ρ ρ x :=
  ⟨ρ, ⟨segAvoidsZero_const ρ, genericWallSeg_const ρ x⟩,
    segAvoidsZero_const ρ, genericWallSeg_const ρ x⟩

/-- **Same-side non-vacuity witness.**  If `ρ.r`, `σ.r` lie on the same strict side
of every edge line, the direct segment is wall-free and avoids the zero direction, so
`GenericChainAt P ρ σ x` holds (the chain `μ = σ`).  This inhabits the residual on
genuinely distinct directions. -/
theorem genericChainAt_of_sameSide {P : StrictSimplePolygon n}
    (ρ σ : RayDirection P) (x : Pt)
    (hside : ∀ i : Fin n,
      (0 < det2 ρ.r (P.q (cyclicNext i) - P.q i) ∧
        0 < det2 σ.r (P.q (cyclicNext i) - P.q i)) ∨
      (det2 ρ.r (P.q (cyclicNext i) - P.q i) < 0 ∧
        det2 σ.r (P.q (cyclicNext i) - P.q i) < 0)) :
    GenericChainAt P ρ σ x := by
  -- the direct segment ρ → σ is a valid (wall-free) segment path: reuse the engine's
  -- same-side comparability, then read off avoid-zero and generic-wall from it.
  have hseg : ValidDirPathSeg P ρ.r σ.r := dirComparableSeg_of_sameSide ρ σ hside
  refine ⟨σ, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro t ht; exact hseg.ne_zero t ht
  · exact genericWallSeg_of_validDirPathSeg hseg x
  · intro t _ hz
    apply σ.r_ne_zero
    have : dirAt σ.r σ.r t = σ.r := by unfold dirAt; simp
    rw [this] at hz; exact hz
  · exact genericWallSeg_const σ x

/-! ## Part 7: the unconditional Chapter-36 art-gallery headline (ray-choice free)

Feeding the discharged `UnconditionalRayIndepInput` into the downstream consumers:
the kept ray-choice oracle of `PolygonFinish` / `PolygonSeparation` is replaced by the
generic-chain residual, with wall crossing fully proved.  We state the clean headline:
given `GenericChainInput P` (plus the genuinely-planar split-set / base / merge
residuals the design already isolates), the art gallery bound holds for *any* ray
direction `ρ`, and the two-direction region statement is direction-independent. -/

/-- **Unconditional two-direction ray independence (wall obstruction discharged).**
For *any* two ray directions, under the single generic-chain residual, the corrected
region is direction-independent off the boundary.  This is the kept ray-choice oracle
`closedRegion'_ray_indep_uncond` made to depend only on `GenericChainInput`. -/
theorem closedRegion'_ray_indep_unconditional {P : StrictSimplePolygon n}
    (H : GenericChainInput P) (ρ σ : RayDirection P) {x : Pt}
    (hoff : ¬ OnBoundary P x) :
    ClosedRegion' P ρ x ↔ ClosedRegion' P σ x :=
  closedRegion'_ray_indep_uncond P (unconditionalRayIndepInput_of_genericChain H) ρ σ hoff

/-- **`TriangleExteriorEven` from the generic-chain residual.**  The kept ray-choice
oracle of `PolygonSeparation` (`∀ Q, UnconditionalRayIndepInput Q`) is replaced by the
generic-chain residual per `3`-gon: the wall obstruction (the chapter's flagged Jordan
analytic core) is internalised by Part 3's per-wall crossing assembly, so the triangle
leaf's exterior-even atom now follows from the strictly-cleaner finite-wall/antipodal
avoidance datum. -/
theorem triangleExteriorEven_of_genericChain
    (H : ∀ Q : StrictSimplePolygon 3, GenericChainInput Q) :
    ProofsInTheBook.PolygonLeaf.TriangleExteriorEven :=
  ProofsInTheBook.PolygonSeparation.triangleExteriorEven_of_rayIndep
    (fun Q => unconditionalRayIndepInput_of_genericChain (H Q))

/-- **Chapter-36 art-gallery headline with the ray-choice oracle discharged to the
generic-chain residual.**  `PolygonSeparation.chapter36_headline_separation` consumed
`∀ Q : StrictSimplePolygon 3, UnconditionalRayIndepInput Q` as the kept ray-choice
input.  Here that input is *produced* from the generic-chain residual `H`, so the
exterior-even atom — and hence the `⌊n/3⌋` art-gallery bound — is unconditional in the
ray choice, modulo the single isolated finite-wall/antipodal avoidance datum (the wall
*crossing* itself being proved).  The remaining inputs are the genuinely-planar ones
the design already isolates: the uniform residual geometry `D`, the convex-vertex leaf
primitive `hconv`, and the diagonal-attach peel `M`. -/
theorem artGallery_strict_genericChain {n : ℕ}
    (D : ∀ {m : ℕ} (P : StrictSimplePolygon m) (ρ : RayDirection P),
        ProofsInTheBook.PolygonOracleClose.ResidualGeometryData P ρ)
    (hconv : ProofsInTheBook.PolygonLeaf.TriangleConvexLeaf)
    (H : ∀ Q : StrictSimplePolygon 3, GenericChainInput Q)
    (M : ProofsInTheBook.PolygonLast.DiagonalAttachInput
      (ProofsInTheBook.PolygonOracleClose.baseTriangleFacts_of_leaf
        (ProofsInTheBook.PolygonLeaf.baseTriangleLeaf_of_atoms hconv
          (triangleExteriorEven_of_genericChain H))))
    (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ x : Pt, ClosedRegion' P ρ x →
        ∃ v ∈ guards, ProofsInTheBook.PolygonRayIndep.Sees P ρ (P.q v) x :=
  ProofsInTheBook.PolygonSeparation.chapter36_headline_separation D hconv
    (fun Q => unconditionalRayIndepInput_of_genericChain (H Q)) M P ρ

end

end ProofsInTheBook.PolygonWallGlobal
