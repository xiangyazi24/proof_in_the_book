import ProofsInTheBook.ZinanCh36SignSync
import ProofsInTheBook.ZinanCh36NonInterleave

/-!
# `ZinanCh36Perturb` — the perturb-wrapper chain of the Ch36 sign-sync design

This file implements the PERTURB-WRAPPER bricks (8, 10, 11) of the Chapter-36 peel-tree
sign-synchronization design (`HANDOFF/design-rounds/ch36-peel-tree-sign-sync.md`).

The load-bearing brick is **10** (`exists_near_point_off_all_generic`): from an off-(parent)-boundary
point `x` and any neighbourhood `U`, it produces a nearby `y ∈ U` that is OFF all three polygon
boundaries AND vertex-generic for all three polygons (no ray hits a vertex).  The construction is a
single normal-segment perturbation `y = x + t • w`:

* the direction `w = sweepDir ρ.r λ = perpVec ρ.r + λ • ρ.r` is **always** transverse to the ray
  `ρ.r` (`det2 ρ.r w = ‖ρ.r‖² > 0`), so every vertex-guard line `{y | side ρ.r y q = 0}` is met by
  `t ↦ x + t•w` in at most ONE `t`;
* choosing `λ` outside finitely many bad values makes `w` transverse to every edge of `P`, `L`, `R`
  (each edge `v` has `det2 ρ.r v ≠ 0` because `σL.r = σR.r = ρ.r` are ray directions of `L`, `R`),
  so each edge line is met in at most one `t`;
* collecting all bad `t` into a `Finset` and picking `t ∈ (0, ε)` (with `ε` small enough that
  `x + t•w ∈ U`) outside it yields the generic `y`.

Brick **8** (`rayWindValues_split_offAll`) splits the parent value at such a generic point via
`windCross_split_common` + the guard-free child packages + `windCross_mem_final`, then transfers
back to `x` by parent local constancy.  Brick **11** (`rayWindValues_split`) is the perturb wrapper
assembling the induction step.

## hLoff / hRoff DROPPED.

The strengthened brick 10 (which produces the genericity guards itself) lets brick 8's *general*
form (`rayWindValues_split_offAll`) require ONLY `hPoff : ¬ OnBoundary P x` — the child boundaries
and child local constancy are never consulted: the child values at the perturbed generic point `y`
come directly from the guard-free packages `HVL`, `HVR` (off-`L`/off-`R` at `y` provided by brick
10).  Consequently the perturb wrapper `rayWindValues_split` collapses with no `by_cases` on the
child boundaries — `subBoundary_of_parentOff_is_diag` is not even needed.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36Perturb

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonWinding
  (windCross windCross_split_common)
open ProofsInTheBook.PolygonWindingExterior (windCross_locally_constant_off_boundary)
open ProofsInTheBook.PolygonWindingZero (perpVec det2_perpVec_pos)
open ProofsInTheBook.ZinanCh36NonInterleave
  (sweepDir det2_r_sweepDir det2_r_sweepDir_pos det2_sweepDir_left)
open ProofsInTheBook.ZinanCh36SignSync (RayWindValuesWithSign)
open ProofsInTheBook.ZinanCh36Interval (windCross_mem_final)

noncomputable section

variable {n : ℕ}

/-! ## §0. Affine-in-`t` algebra of the normal segment `t ↦ x + t • w` -/

/-- `orient a b (x + t•w)` is affine in `t`: constant term `orient a b x`, slope `det2 (b-a) w`. -/
lemma orient_perturb_affine (a b x w : Pt) (t : ℝ) :
    orient a b (x + t • w) = orient a b x + t * det2 (b - a) w := by
  unfold orient det2
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- `side r (x + t•w) v` is affine in `t`: constant term `side r x v`, slope `- t * det2 r w`. -/
lemma side_perturb_affine (r x w v : Pt) (t : ℝ) :
    side r (x + t • w) v = side r x v - t * det2 r w := by
  unfold side det2
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-! ## §1. Direction selection: `w = sweepDir ρ.r λ` transverse to every edge of one polygon

For a polygon `Q` whose ray `σ` reuses the parent direction (`σ.r = ρ.r`), every edge vector `v` of
`Q` satisfies `det2 ρ.r v ≠ 0` (`σ.no_edge_parallel`), so the slope
`det2 v (sweepDir ρ.r λ) = -(det2 (perpVec ρ.r) v + λ·det2 ρ.r v)` is affine non-constant in `λ`,
vanishing at exactly one `λ`.  Collecting those over all edges gives the bad-`λ` finite set. -/

/-- The finite set of `λ` at which `sweepDir ρ.r λ` is parallel to SOME edge of `Q`.  Outside it,
`det2 (edgeVec Q k) (sweepDir ρ.r λ) ≠ 0` for every edge `k`. -/
lemma exists_lambda_transverse_edges {m : ℕ} (r : Pt) (Q : StrictSimplePolygon m)
    (hQr : ∀ k : Fin m, det2 r (Q.q (cyclicNext k) - Q.q k) ≠ 0) :
    ∃ bad : Finset ℝ, ∀ lam : ℝ, lam ∉ bad →
      ∀ k : Fin m, det2 (Q.q (cyclicNext k) - Q.q k) (sweepDir r lam) ≠ 0 := by
  classical
  -- For each edge `k`, the unique root of `λ ↦ det2 (perpVec r) v + λ·det2 r v`.
  set root : Fin m → ℝ := fun k =>
    - det2 (perpVec r) (Q.q (cyclicNext k) - Q.q k) / det2 r (Q.q (cyclicNext k) - Q.q k) with hroot
  refine ⟨Finset.univ.image root, fun lam hlam k => ?_⟩
  set v : Pt := Q.q (cyclicNext k) - Q.q k with hv
  have hrv : det2 r v ≠ 0 := hQr k
  -- `det2 v (sweepDir r λ) = - det2 (sweepDir r λ) v = -(det2 (perpVec r) v + λ·det2 r v)`.
  rw [det2_antisymm v (sweepDir r lam), det2_sweepDir_left r lam v]
  intro hzero
  apply hlam
  refine Finset.mem_image.mpr ⟨k, Finset.mem_univ k, ?_⟩
  -- recover `λ = root k` from `-(det2 (perpVec r) v + λ·det2 r v) = 0`.
  show - det2 (perpVec r) v / det2 r v = lam
  field_simp
  -- `det2 (perpVec r) v + lam * det2 r v = 0`  ⟹  `det2 (perpVec r) v = - (lam * det2 r v)`.
  have : det2 (perpVec r) v + lam * det2 r v = 0 := by linarith [neg_eq_zero.mp hzero]
  linarith

/-! ## §2. Per-polygon: avoiding the boundary and the vertex guards along the fixed normal segment

With `w` fixed (transverse to every edge of `Q`), each edge line and each vertex-guard line is met
by `t ↦ x + t•w` in at most one `t`.  We collect both finite bad-`t` sets, so off them the perturbed
point is off `Q`'s boundary and vertex-generic for `Q`. -/

/-- The bad-`t` finite set for one polygon `Q`: for `t` outside it, `x + t•w` is off `Q`'s boundary
AND `σ.r`-vertex-generic (no guard line hit), provided `w` is edge-transverse and `σ.r = r` with
`det2 r w ≠ 0` (so the guard lines are also non-degenerate in `t`). -/
lemma exists_badt_polygon {m : ℕ} (r : Pt) (Q : StrictSimplePolygon m) (x w : Pt)
    (hedge : ∀ k : Fin m, det2 (Q.q (cyclicNext k) - Q.q k) w ≠ 0)
    (hrw : det2 r w ≠ 0) :
    ∃ bad : Finset ℝ, ∀ t : ℝ, t ∉ bad →
      ¬ OnBoundary Q (x + t • w) ∧ ∀ k : Fin m, side r (x + t • w) (Q.q k) ≠ 0 := by
  classical
  -- edge roots: `t ↦ orient (Q.q k) (Q.q (next k)) (x+t•w)` has the unique root
  --   `tEdge k = - orient (Q.q k)(Q.q (next k)) x / det2 (edgeVec) w`.
  set tEdge : Fin m → ℝ := fun k =>
    - orient (Q.q k) (Q.q (cyclicNext k)) x
      / det2 (Q.q (cyclicNext k) - Q.q k) w with htEdge
  -- guard roots: `t ↦ side r (x+t•w) (Q.q k)` has the unique root `tGuard k = side r x (Q.q k)/det2 r w`.
  set tGuard : Fin m → ℝ := fun k => side r x (Q.q k) / det2 r w with htGuard
  refine ⟨Finset.univ.image tEdge ∪ Finset.univ.image tGuard, fun t ht => ?_⟩
  rw [Finset.mem_union, not_or] at ht
  obtain ⟨htE, htG⟩ := ht
  constructor
  · -- off boundary
    rintro ⟨k, hk⟩
    -- `hk : x + t•w ∈ Edge Q.q k = seg (Q.q k) (Q.q (next k))`, so the orient vanishes.
    rw [Edge] at hk
    have ho : orient (Q.q k) (Q.q (cyclicNext k)) (x + t • w) = 0 :=
      PolygonTriangleConvex.orient_eq_zero_of_mem_seg hk
    rw [orient_perturb_affine] at ho
    have hslope : det2 (Q.q (cyclicNext k) - Q.q k) w ≠ 0 := hedge k
    apply htE
    refine Finset.mem_image.mpr ⟨k, Finset.mem_univ k, ?_⟩
    show - orient (Q.q k) (Q.q (cyclicNext k)) x / det2 (Q.q (cyclicNext k) - Q.q k) w = t
    field_simp
    linarith
  · -- vertex-generic
    intro k hguard
    rw [side_perturb_affine] at hguard
    apply htG
    refine Finset.mem_image.mpr ⟨k, Finset.mem_univ k, ?_⟩
    show side r x (Q.q k) / det2 r w = t
    field_simp
    linarith
/-! ## §3. Small-`t` neighbourhood capture

The map `t ↦ x + t•w` is continuous and sends `0 ↦ x`, so for any `U ∈ nhds x` the preimage is a
neighbourhood of `0`, hence contains `Ioo 0 ε` for some `ε > 0`. -/

/-- For `U ∈ nhds x`, some `ε > 0` has `x + t•w ∈ U` for all `t ∈ (0, ε)`. -/
lemma exists_eps_segment_in_nhds (x w : Pt) {U : Set Pt} (hU : U ∈ nhds x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) ε → x + t • w ∈ U := by
  have hcont : Continuous (fun t : ℝ => x + t • w) := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hpre : (fun t : ℝ => x + t • w) ⁻¹' U ∈ nhds (0 : ℝ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    show U ∈ nhds (x + (0 : ℝ) • w)
    rw [zero_smul, add_zero]; exact hU
  rw [Metric.mem_nhds_iff] at hpre
  obtain ⟨ε, hε, hball⟩ := hpre
  refine ⟨ε, hε, fun t ht => ?_⟩
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_of_pos ht.1]
  exact ht.2

/-! ## §4. Brick 10 — the off-all + vertex-generic point selector

The load-bearing brick.  From `x` off the PARENT boundary and any neighbourhood `U`, we produce a
nearby `y ∈ U` off all three boundaries and vertex-generic for all three polygons.  Direction
`w = sweepDir ρ.r λ` (λ avoiding the three edge-transversality bad sets) is transverse to every edge
of `P`, `L`, `R` and (always) to the ray `ρ.r`; then `t ∈ (0, ε)` avoiding the three per-polygon
bad-`t` sets lands `y = x + t•w` off everything. -/

theorem exists_near_point_off_all_generic {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hLr : σL.r = ρ.r) (hRr : σR.r = ρ.r)
    {x : Pt} (hPoff : ¬ OnBoundary P x) {U : Set Pt} (hU : U ∈ nhds x) :
    ∃ y ∈ U, ¬ OnBoundary P y ∧ ¬ OnBoundary (buildLeftPoly h lax) y ∧
      ¬ OnBoundary (buildRightPoly h rax) y ∧
      (∀ k : Fin n, side ρ.r y (P.q k) ≠ 0) ∧
      (∀ k, side σL.r y ((buildLeftPoly h lax).q k) ≠ 0) ∧
      (∀ k, side σR.r y ((buildRightPoly h rax).q k) ≠ 0) := by
  classical
  -- Edge-transversality bad-λ sets for P, L, R (their edges are non-parallel to ρ.r).
  obtain ⟨badLP, hbadLP⟩ := exists_lambda_transverse_edges ρ.r P ρ.no_edge_parallel
  obtain ⟨badLL, hbadLL⟩ := exists_lambda_transverse_edges ρ.r (buildLeftPoly h lax)
    (fun k => hLr ▸ σL.no_edge_parallel k)
  obtain ⟨badLR, hbadLR⟩ := exists_lambda_transverse_edges ρ.r (buildRightPoly h rax)
    (fun k => hRr ▸ σR.no_edge_parallel k)
  -- Pick λ outside all three.
  obtain ⟨lam, hlam⟩ := (badLP ∪ badLL ∪ badLR).exists_notMem
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at hlam
  obtain ⟨⟨hlamP, hlamL⟩, hlamR⟩ := hlam
  set w : Pt := sweepDir ρ.r lam with hwdef
  have hedgeP : ∀ k : Fin n, det2 (P.q (cyclicNext k) - P.q k) w ≠ 0 := hbadLP lam hlamP
  have hedgeL := hbadLL lam hlamL
  have hedgeR := hbadLR lam hlamR
  have hrw : det2 ρ.r w ≠ 0 := ne_of_gt (det2_r_sweepDir_pos ρ.r_ne_zero lam)
  -- Per-polygon bad-t sets.
  obtain ⟨badtP, hbadtP⟩ := exists_badt_polygon ρ.r P x w hedgeP hrw
  obtain ⟨badtL, hbadtL⟩ := exists_badt_polygon ρ.r (buildLeftPoly h lax) x w hedgeL hrw
  obtain ⟨badtR, hbadtR⟩ := exists_badt_polygon ρ.r (buildRightPoly h rax) x w hedgeR hrw
  -- Neighbourhood capture: t ∈ (0, ε) ⟹ x + t•w ∈ U.
  obtain ⟨ε, hε, hUseg⟩ := exists_eps_segment_in_nhds x w hU
  -- Pick t ∈ (0, ε) avoiding all three bad-t sets.
  obtain ⟨t, htio, htbad⟩ :
      ∃ t : ℝ, t ∈ Set.Ioo (0 : ℝ) ε ∧ t ∉ (badtP ∪ badtL ∪ badtR) := by
    have hinf : (Set.Ioo (0 : ℝ) ε).Infinite := Set.Ioo_infinite hε
    have hns : ¬ (Set.Ioo (0 : ℝ) ε ⊆ ((badtP ∪ badtL ∪ badtR : Finset ℝ) : Set ℝ)) :=
      fun hsub => hinf ((badtP ∪ badtL ∪ badtR).finite_toSet.subset hsub)
    rw [Set.not_subset] at hns
    obtain ⟨t, hio, hnb⟩ := hns; exact ⟨t, hio, hnb⟩
  rw [Finset.mem_union, Finset.mem_union, not_or, not_or] at htbad
  obtain ⟨⟨htP, htL⟩, htR⟩ := htbad
  refine ⟨x + t • w, hUseg t htio, ?_⟩
  obtain ⟨hoffP, hvertP⟩ := hbadtP t htP
  obtain ⟨hoffL, hvertL⟩ := hbadtL t htL
  obtain ⟨hoffR, hvertR⟩ := hbadtR t htR
  refine ⟨hoffP, hoffL, hoffR, hvertP, ?_, ?_⟩
  · intro k; rw [hLr]; exact hvertL k
  · intro k; rw [hRr]; exact hvertR k

/-! ## §5. Brick 8 — the ray-indexed off-all parent value split

At a point off all three boundaries WITH the parent vertex guard, the parent value lies in `{0, s}`:
the child values come from the guard-free packages (`RayWindValuesWithSign`), the parent bound from
`windCross_mem_final` (needs the parent guard), and `windCross_split_common` + `omega` finish, the
both-interior state `P = 2s` being excluded.  This is the ray-indexed mirror of
`windValues_split_offAll`, with the child guard packages swapped for the guard-free ray packages. -/

theorem rayWindValues_split_offAll_generic {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hLr : σL.r = ρ.r) (hRr : σR.r = ρ.r) {s : ℤ}
    (HVL : RayWindValuesWithSign (buildLeftPoly h lax) σL s)
    (HVR : RayWindValuesWithSign (buildRightPoly h rax) σR s)
    {y : Pt}
    (hoffP : ¬ OnBoundary P y) (hvertP : ∀ k : Fin n, side ρ.r y (P.q k) ≠ 0)
    (hoffL : ¬ OnBoundary (buildLeftPoly h lax) y)
    (hoffR : ¬ OnBoundary (buildRightPoly h rax) y) :
    windCross P ρ y = 0 ∨ windCross P ρ y = s := by
  have hsplit := windCross_split_common h lax rax σL σR hLr hRr y
  have hLval := HVL.values y hoffL
  have hRval := HVR.values y hoffR
  have hPb := windCross_mem_final (P := P) (ρ := ρ) (x := y) hoffP hvertP
  have hsu : s = 1 ∨ s = -1 := HVL.sign_unit
  rcases hLval with hL0 | hLs <;> rcases hRval with hR0 | hRs <;>
    rcases hPb with hP0 | hP1 | hPm1 <;> rcases hsu with hs1 | hsm1 <;> omega

/-! ### The general off-all form (only `hPoff` needed)

`x` off the parent boundary ⟹ parent local constancy gives a neighbourhood `U` on which
`windCross P ρ = windCross P ρ x`; brick 10 produces a generic `y ∈ U` off all three boundaries with
the parent guard; the generic split pins `windCross P ρ y ∈ {0, s}`; transfer back to `x` along the
local-constancy equality.  The child boundaries / child local constancy at `x` are never consulted —
so `hLoff` / `hRoff` are DROPPED. -/
theorem rayWindValues_split_offAll {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hLr : σL.r = ρ.r) (hRr : σR.r = ρ.r) {s : ℤ}
    (HVL : RayWindValuesWithSign (buildLeftPoly h lax) σL s)
    (HVR : RayWindValuesWithSign (buildRightPoly h rax) σR s)
    {x : Pt} (hPoff : ¬ OnBoundary P x) :
    windCross P ρ x = 0 ∨ windCross P ρ x = s := by
  -- Parent local constancy at the off-boundary point `x`.
  have hloc : ∀ᶠ y in nhds x, windCross P ρ y = windCross P ρ x :=
    windCross_locally_constant_off_boundary P ρ hPoff
  rw [Filter.eventually_iff] at hloc
  -- Generic nearby point `y` off all three boundaries (+ parent guard).
  obtain ⟨y, hyU, _hoffPy, hoffLy, hoffRy, hvertPy, _, _⟩ :=
    exists_near_point_off_all_generic h lax rax σL σR hLr hRr hPoff hloc
  -- `hyU` says `windCross P ρ y = windCross P ρ x`; reuse `_hoffPy` for the split.
  have heq : windCross P ρ y = windCross P ρ x := hyU
  have hsplit := rayWindValues_split_offAll_generic h lax rax σL σR hLr hRr HVL HVR
    _hoffPy hvertPy hoffLy hoffRy
  rwa [heq] at hsplit

/-! ## §6. Brick 11 — the full perturb wrapper

Since `rayWindValues_split_offAll` needs only `hPoff`, the perturb wrapper is immediate: the package
sign is the common child sign, and the value dichotomy at every off-(parent)-boundary point is
exactly brick 8's general form.  No `by_cases` on the child boundaries, no
`subBoundary_of_parentOff_is_diag`. -/
theorem rayWindValues_split {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hLr : σL.r = ρ.r) (hRr : σR.r = ρ.r) {s : ℤ}
    (HVL : RayWindValuesWithSign (buildLeftPoly h lax) σL s)
    (HVR : RayWindValuesWithSign (buildRightPoly h rax) σR s) :
    RayWindValuesWithSign P ρ s :=
  ⟨HVL.sign_unit, fun _x hPoff =>
    rayWindValues_split_offAll h lax rax σL σR hLr hRr HVL HVR hPoff⟩

end

end ProofsInTheBook.ZinanCh36Perturb

/-! ## Axiom audit (clean-3 expected: `propext`, `Classical.choice`, `Quot.sound`) -/

#print axioms ProofsInTheBook.ZinanCh36Perturb.exists_near_point_off_all_generic
#print axioms ProofsInTheBook.ZinanCh36Perturb.rayWindValues_split_offAll
#print axioms ProofsInTheBook.ZinanCh36Perturb.rayWindValues_split
