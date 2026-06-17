import ProofsInTheBook.ZinanCh36NonInterleave
import ProofsInTheBook.ZinanCh36Alternation
import ProofsInTheBook.ZinanCh36SuccBij

/-!
# `ZinanCh36Interval` — the INTERVAL-form same-side lobe noninterleaving (the last Ch36 residue).

The landed `ZinanCh36NonInterleave.upper_lobes_not_interleave` rules out the **ascending**
foot order `crossTau X.start < crossTau Y.start < crossTau (lobeLastEdge X) <
crossTau (lobeLastEdge Y)`.  But an upper lobe's `start` foot need not be its τ-LEFT foot:
the two feet `{crossTau start, crossTau (lobeLastEdge)}` can be in either order.  The
`hposNI` / `hnegNI` slots of `ZinanCh36Alternation` ask for the **interval** form
`¬ TauInterleaves (crossTau …) X.start (lobeLastEdge X) Y.start (lobeLastEdge Y)`, which is
min/max-symmetric — i.e. it forbids ALL non-nesting foot orders, not just the ascending one.

## Why the landed substrate suffices (master's design audit, replayed here)

The fixed-direction parity sweep depends only on the lobes' **τ-intervals** and side-positivity,
NOT on which foot is the walk start:

* `aboveInd_feet_straddle` (landed) already takes the *both-order* between-condition
  `(τFirst < u₀ < τLast) ∨ (τLast < u₀ < τFirst)` — so "`X`'s feet straddle `u₀`" is orientation
  free.
* `transport_X_over_Y` (landed) relates the parity at `footFirst Y` and `footLast Y` using ONLY
  carrier disjointness — direction-free (the same finite set of `Y`-segments either way).
* `transport_X_along_line` (landed) is already min/max-symmetric in its two endpoints and forbids
  BOTH `X`-feet from the spanned interval.

The orientation enters only through the naming `footFirst`/`footLast`.  We route the sweep path
through `Y`'s τ-LEFT and τ-RIGHT feet (a `le_total` split on `Y`'s two foot coordinates identifies
them with `footFirst`/`footLast`), replaying the landed §0–§8 assembly with the interval endpoints
in place of `start`/`lastEdge`.  CRUCIALLY the entry line piece must land on `Y`'s τ-LEFT foot (not
`footFirst`, which could be `Y`'s τ-RIGHT foot and would make the entry segment cross `X`'s right
foot).

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36Interval

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.ZinanCh36Lobes
open ProofsInTheBook.ZinanCh36ArcSweep
open ProofsInTheBook.ZinanCh36LobeChain
open ProofsInTheBook.ZinanCh36LobeWiring
open ProofsInTheBook.ZinanCh36NonInterleave
open ProofsInTheBook.ZinanCh36Comb (TauInterleaves)
open ProofsInTheBook.PolygonWinding (windCross)
open ProofsInTheBook.PolygonWindingExterior (eSign)
open ProofsInTheBook.PolygonWindingBound
  (Alt RayCrossingAlternation eSign_mem windCross_mem_of_alternation)
open ProofsInTheBook.ZinanCh36RankParity (alt_of_twoSide_noncrossing_cycle)
open ProofsInTheBook.ZinanCh36LobeWiring
  (boundarySucc boundarySucc_eq_nextCrossing boundarySucc_mem boundarySucc_sign_flip
    upperLobeOfPos upperLobeOfPos_last lowerLobeOfNeg lowerLobeOfNeg_last)
open ProofsInTheBook.ZinanCh36SuccBij
  (boundarySucc_cycle_connected_unconditional upperLobes_carrier_disjoint lowerLobes_carrier_disjoint)
open ProofsInTheBook.ZinanCh36Theta
  (LineCrossingEdges crossTau_injOn_lineCrossingEdges exists_sorted_enum
    rayWindingDichotomy_of_fullLineAlternation rayCrossingAlternation_of_fullLineAlternation
    rayCrossingAlternation_of_ray_dichotomy)
open Filter Topology
open scoped RealInnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1600000

variable {n : ℕ}
variable {P : StrictSimplePolygon n} {ρ : RayDirection P} {x : Pt}

/-! ## §0. Min/max bridges for the two foot coordinates of a lobe.

`{tauFirst L, tauLast L}` as a set equals `{min, max}`; so a fact stated for `tauFirst`/`tauLast`
(the landed `transport_X_along_line` hypotheses) converts to a fact about the τ-min/τ-max feet. -/

/-- The two foot coordinates of `X` are `min`/`max` in one of the two orders. -/
lemma tau_eq_min_or_max (L : UpperLobe P ρ x) :
    (tauFirst L = min (tauFirst L) (tauLast L) ∧ tauLast L = max (tauFirst L) (tauLast L)) ∨
    (tauFirst L = max (tauFirst L) (tauLast L) ∧ tauLast L = min (tauFirst L) (tauLast L)) := by
  rcases le_total (tauFirst L) (tauLast L) with h | h
  · left; exact ⟨(min_eq_left h).symm, (max_eq_right h).symm⟩
  · right; exact ⟨(max_eq_left h).symm, (min_eq_right h).symm⟩

/-- **Min/max line transport (upper).**  Re-statement of `transport_X_along_line` whose
out-of-interval conditions are phrased on `X`'s τ-min `xL` and τ-max `xR` feet directly. -/
lemma transport_X_along_line_mm (X : UpperLobe P ρ x) {η : Pt} (α β : ℝ)
    (hη : (lobeChain X).Transverse η) (hdet : 0 < det2 ρ.r η)
    (hL : min (tauFirst X) (tauLast X) < min α β ∨ max α β < min (tauFirst X) (tauLast X))
    (hmaxL : max (tauFirst X) (tauLast X) < min α β ∨ max α β < max (tauFirst X) (tauLast X)) :
    (lobeChain X).rayCount η (x + α • ρ.r) % 2
      = (lobeChain X).rayCount η (x + β • ρ.r) % 2 := by
  apply transport_X_along_line X α β hη hdet
  · -- tauFirst X is one of xL, xR; both excluded.
    rcases tau_eq_min_or_max X with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; exact hL
    · rw [h1]; exact hmaxL
  · rcases tau_eq_min_or_max X with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h2]; exact hmaxL
    · rw [h2]; exact hL

/-! ## §1. The interval core (upper): the ascending-interval order is impossible. -/

/-- **Interval core (upper).**  Two `UpperLobe`s with disjoint clipped-chain carriers cannot have
their τ-intervals interleave in the ascending order
`min(τFirst X, τLast X) < min(τFirst Y, τLast Y) < max(τFirst X, τLast X) < max(τFirst Y, τLast Y)`. -/
theorem upper_interval_core
    (X Y : UpperLobe P ρ x)
    (hdisj : Disjoint (lobeChain X).carrier (lobeChain Y).carrier)
    (hxLyL : min (tauFirst X) (tauLast X) < min (tauFirst Y) (tauLast Y))
    (hyLxR : min (tauFirst Y) (tauLast Y) < max (tauFirst X) (tauLast X))
    (hxRyR : max (tauFirst X) (tauLast X) < max (tauFirst Y) (tauLast Y)) :
    False := by
  classical
  set xL := min (tauFirst X) (tauLast X) with hxLdef
  set xR := max (tauFirst X) (tauLast X) with hxRdef
  set yL := min (tauFirst Y) (tauLast Y) with hyLdef
  set yR := max (tauFirst Y) (tauLast Y) with hyRdef
  have hxLR : xL ≤ xR := min_le_max
  have hyLR : yL ≤ yR := min_le_max
  have hxLR' : xL < xR := lt_trans hxLyL hyLxR
  have hyLR' : yL < yR := lt_trans hyLxR hxRyR
  -- feet of X and Y are distinct (xL < xR, yL < yR).
  have hfeetX : footFirst X ≠ footLast X := by
    intro h
    have := congrArg (uCoord ρ.r x) h
    rw [show footFirst X = x + crossTau P ρ x X.start • ρ.r from rfl,
      show footLast X = x + crossTau P ρ x (lobeLastEdge X) • ρ.r from rfl,
      uCoord_ray, uCoord_ray] at this
    have heq := mul_right_cancel₀ (ne_of_gt (normSq_pos ρ.r ρ.r_ne_zero)) this
    have htf : tauFirst X = tauLast X := heq
    rw [hxLdef, hxRdef, htf, min_self, max_self] at hxLR'; exact lt_irrefl _ hxLR'
  have hfeetY : footFirst Y ≠ footLast Y := by
    intro h
    have := congrArg (uCoord ρ.r x) h
    rw [show footFirst Y = x + crossTau P ρ x Y.start • ρ.r from rfl,
      show footLast Y = x + crossTau P ρ x (lobeLastEdge Y) • ρ.r from rfl,
      uCoord_ray, uCoord_ray] at this
    have heq := mul_right_cancel₀ (ne_of_gt (normSq_pos ρ.r ρ.r_ne_zero)) this
    have htf : tauFirst Y = tauLast Y := heq
    rw [hyLdef, hyRdef, htf, min_self, max_self] at hyLR'; exact lt_irrefl _ hyLR'
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
  -- pick u₀ ∈ (yL, xR) avoiding the X-vertex projections.
  obtain ⟨badU, hbadU⟩ := exists_generic_u0 X (η := η) hdet
  obtain ⟨u₀, hu₀io, hu₀bad⟩ : ∃ u₀ : ℝ, u₀ ∈ Set.Ioo yL xR ∧ u₀ ∉ badU := by
    have hinf : (Set.Ioo yL xR).Infinite := Set.Ioo_infinite hyLxR
    have hns : ¬ (Set.Ioo yL xR ⊆ (badU : Set ℝ)) := fun hsub =>
      hinf (badU.finite_toSet.subset hsub)
    rw [Set.not_subset] at hns
    obtain ⟨u₀, hio, hnb⟩ := hns; exact ⟨u₀, hio, hnb⟩
  rw [Set.mem_Ioo] at hu₀io
  have hgenX : ∀ j : Fin (X.len + 1), side η (x + u₀ • ρ.r) (chainPt X j) ≠ 0 :=
    hbadU u₀ hu₀bad
  -- N(z₀) odd: X's feet straddle u₀ (xL < yL < u₀ < xR), orientation-free.
  have hodd : (lobeChain X).rayCount η (x + u₀ • ρ.r) % 2 = 1 := by
    rw [lobeChain_rayCount_parity X u₀ hηX hdet hgenX]
    apply aboveInd_feet_straddle X η u₀ hdet
    have hlo : xL < u₀ := lt_trans hxLyL hu₀io.1
    have hhi : u₀ < xR := hu₀io.2
    rcases le_total (tauFirst X) (tauLast X) with hle | hle
    · left
      rw [hxLdef, min_eq_left hle] at hlo; rw [hxRdef, max_eq_right hle] at hhi
      exact ⟨hlo, hhi⟩
    · right
      rw [hxLdef, min_eq_right hle] at hlo; rw [hxRdef, max_eq_left hle] at hhi
      exact ⟨hlo, hhi⟩
  -- pick R far right (R > yR ≥ all four feet), strictly exceeding X-vertex coords.
  obtain ⟨R, hRmax, hRt⟩ := exists_far_R X η yR
  -- N(z_R) = 0.
  have hzero : (lobeChain X).rayCount η (x + R • ρ.r) = 0 :=
    lobeChain_rayCount_far X R hηX hdet hRmax
  -- transport path: z₀ → yL-foot → (Y walk) → yR-foot → z_R.
  -- piece 1: u₀ → yL-foot.  span [yL, u₀]: X feet xL < yL ✓, xR > u₀ ✓.
  have hp1 : (lobeChain X).rayCount η (x + u₀ • ρ.r) % 2
      = (lobeChain X).rayCount η (x + yL • ρ.r) % 2 := by
    apply transport_X_along_line_mm X u₀ yL hηX hdet
    · -- xL < min u₀ yL.
      left; rw [lt_min_iff]; constructor <;> [linarith [hu₀io.1]; linarith]
    · -- max u₀ yL < xR.
      right; rw [max_lt_iff]; exact ⟨hu₀io.2, hyLxR⟩
  -- piece 2: yL-foot → yR-foot (over Y's walk), via footFirst/footLast.
  have hp2 : (lobeChain X).rayCount η (x + yL • ρ.r) % 2
      = (lobeChain X).rayCount η (x + yR • ρ.r) % 2 := by
    have hwalk : (lobeChain X).rayCount η (footFirst Y) % 2
        = (lobeChain X).rayCount η (footLast Y) % 2 :=
      transport_X_over_Y X Y hηX hdet hdisj
    -- footFirst Y = x + (tauFirst Y)•r, footLast Y = x + (tauLast Y)•r.
    rcases tau_eq_min_or_max Y with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- tauFirst Y = yL, tauLast Y = yR.
      rw [show (x + yL • ρ.r) = footFirst Y from by rw [show footFirst Y = x + tauFirst Y • ρ.r from rfl, h1],
        show (x + yR • ρ.r) = footLast Y from by rw [show footLast Y = x + tauLast Y • ρ.r from rfl, h2]]
      exact hwalk
    · -- tauFirst Y = yR, tauLast Y = yL.
      rw [show (x + yL • ρ.r) = footLast Y from by rw [show footLast Y = x + tauLast Y • ρ.r from rfl, h2],
        show (x + yR • ρ.r) = footFirst Y from by rw [show footFirst Y = x + tauFirst Y • ρ.r from rfl, h1]]
      exact hwalk.symm
  -- piece 3: yR-foot → z_R.  span [yR, R]: X feet xL < yR ✓, xR < yR ✓; R > yR.
  have hp3 : (lobeChain X).rayCount η (x + yR • ρ.r) % 2
      = (lobeChain X).rayCount η (x + R • ρ.r) % 2 := by
    apply transport_X_along_line_mm X yR R hηX hdet
    · -- xL < min yR R.
      left; rw [lt_min_iff]; constructor <;> [linarith; linarith [hRt]]
    · -- xR < min yR R.
      left; rw [lt_min_iff]; exact ⟨hxRyR, lt_trans hxRyR hRt⟩
  -- chain: odd = N(z₀) = N(z_R) = 0, contradiction.
  have hchain : (1 : ℤ) = 0 := by rw [← hodd, hp1, hp2, hp3, hzero]; rfl
  exact absurd hchain (by decide)

/-! ## §2. The interval theorem (upper): no `TauInterleaves`. -/

/-- **Upper interval noninterleave.**  Two `UpperLobe`s with disjoint clipped-chain carriers cannot
have `TauInterleaves (crossTau …) X.start (lobeLastEdge X) Y.start (lobeLastEdge Y)` — the
min/max-symmetric (interval) form.  Both disjuncts reduce to `upper_interval_core` (the second by
the `X ↔ Y` symmetry of the interleave). -/
theorem upper_lobes_not_tauInterleave
    (X Y : UpperLobe P ρ x)
    (hdisj : Disjoint (lobeChain X).carrier (lobeChain Y).carrier) :
    ¬ TauInterleaves (crossTau P ρ x) X.start (lobeLastEdge X) Y.start (lobeLastEdge Y) := by
  rw [TauInterleaves]
  -- crossTau X.start = tauFirst X, crossTau (lobeLastEdge X) = tauLast X, etc.
  show ¬ ((min (tauFirst X) (tauLast X) < min (tauFirst Y) (tauLast Y) ∧
            min (tauFirst Y) (tauLast Y) < max (tauFirst X) (tauLast X) ∧
            max (tauFirst X) (tauLast X) < max (tauFirst Y) (tauLast Y)) ∨
          (min (tauFirst Y) (tauLast Y) < min (tauFirst X) (tauLast X) ∧
            min (tauFirst X) (tauLast X) < max (tauFirst Y) (tauLast Y) ∧
            max (tauFirst Y) (tauLast Y) < max (tauFirst X) (tauLast X)))
  rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  · exact upper_interval_core X Y hdisj h1 h2 h3
  · exact upper_interval_core Y X hdisj.symm h1 h2 h3

/-! ## §3. The lower mirror.

The lower lobe lives on the NEGATIVE side; the landed `ZinanCh36NonInterleave` re-runs the entire
engine with reference `-ρ.r` and exports the mirror helpers (`tauFirstL`, `tauLastL`,
`aboveInd_feet_straddleL`, `aboveInd_feet_outsideL`, `transport_XL_along_line`,
`transport_XL_over_YL`, `lobeChainL_rayCount_parity`, `exists_transverse_lobeChainL`,
`exists_generic_u0L`).  We replay the interval routing in that mirror engine. -/

/-- The two foot coordinates of a lower lobe `L` are `min`/`max` in one of two orders. -/
lemma tauL_eq_min_or_max (L : LowerLobe P ρ x) :
    (tauFirstL L = min (tauFirstL L) (tauLastL L) ∧ tauLastL L = max (tauFirstL L) (tauLastL L)) ∨
    (tauFirstL L = max (tauFirstL L) (tauLastL L) ∧ tauLastL L = min (tauFirstL L) (tauLastL L)) := by
  rcases le_total (tauFirstL L) (tauLastL L) with h | h
  · left; exact ⟨(min_eq_left h).symm, (max_eq_right h).symm⟩
  · right; exact ⟨(max_eq_left h).symm, (min_eq_right h).symm⟩

/-- **Min/max line transport (lower).** -/
lemma transport_XL_along_line_mm (X : LowerLobe P ρ x) {η : Pt} (α β : ℝ)
    (hη : (lobeChainL X).Transverse η) (hdet : 0 < det2 (-ρ.r) η)
    (hL : min (tauFirstL X) (tauLastL X) < min α β ∨ max α β < min (tauFirstL X) (tauLastL X))
    (hmaxL : max (tauFirstL X) (tauLastL X) < min α β ∨ max α β < max (tauFirstL X) (tauLastL X)) :
    (lobeChainL X).rayCount η (x + α • ρ.r) % 2
      = (lobeChainL X).rayCount η (x + β • ρ.r) % 2 := by
  apply transport_XL_along_line X α β hη hdet
  · rcases tauL_eq_min_or_max X with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; exact hL
    · rw [h1]; exact hmaxL
  · rcases tauL_eq_min_or_max X with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h2]; exact hmaxL
    · rw [h2]; exact hL

/-- **Interval core (lower).** -/
theorem lower_interval_core
    (X Y : LowerLobe P ρ x)
    (hdisj : Disjoint (lobeChainL X).carrier (lobeChainL Y).carrier)
    (hxLyL : min (tauFirstL X) (tauLastL X) < min (tauFirstL Y) (tauLastL Y))
    (hyLxR : min (tauFirstL Y) (tauLastL Y) < max (tauFirstL X) (tauLastL X))
    (hxRyR : max (tauFirstL X) (tauLastL X) < max (tauFirstL Y) (tauLastL Y)) :
    False := by
  classical
  set xL := min (tauFirstL X) (tauLastL X) with hxLdef
  set xR := max (tauFirstL X) (tauLastL X) with hxRdef
  set yL := min (tauFirstL Y) (tauLastL Y) with hyLdef
  set yR := max (tauFirstL Y) (tauLastL Y) with hyRdef
  have hxLR : xL ≤ xR := min_le_max
  have hyLR : yL ≤ yR := min_le_max
  have hxLR' : xL < xR := lt_trans hxLyL hyLxR
  have hyLR' : yL < yR := lt_trans hyLxR hxRyR
  have hfeetX : footFirstL X ≠ footLastL X := by
    intro h
    have := congrArg (uCoord ρ.r x) h
    rw [show footFirstL X = x + crossTau P ρ x X.start • ρ.r from rfl,
      show footLastL X = x + crossTau P ρ x (lobeLastEdgeL X) • ρ.r from rfl,
      uCoord_ray, uCoord_ray] at this
    have heq := mul_right_cancel₀ (ne_of_gt (normSq_pos ρ.r ρ.r_ne_zero)) this
    have htf : tauFirstL X = tauLastL X := heq
    rw [hxLdef, hxRdef, htf, min_self, max_self] at hxLR'; exact lt_irrefl _ hxLR'
  have hfeetY : footFirstL Y ≠ footLastL Y := by
    intro h
    have := congrArg (uCoord ρ.r x) h
    rw [show footFirstL Y = x + crossTau P ρ x Y.start • ρ.r from rfl,
      show footLastL Y = x + crossTau P ρ x (lobeLastEdgeL Y) • ρ.r from rfl,
      uCoord_ray, uCoord_ray] at this
    have heq := mul_right_cancel₀ (ne_of_gt (normSq_pos ρ.r ρ.r_ne_zero)) this
    have htf : tauFirstL Y = tauLastL Y := heq
    rw [hyLdef, hyRdef, htf, min_self, max_self] at hyLR'; exact lt_irrefl _ hyLR'
  obtain ⟨badX, hbadX⟩ := exists_transverse_lobeChainL X hfeetX
  obtain ⟨badY, hbadY⟩ := exists_transverse_lobeChainL Y hfeetY
  obtain ⟨lam, hlam⟩ := (badX ∪ badY).exists_notMem
  set η := sweepDir (-ρ.r) lam with hηdef
  have hηX : (lobeChainL X).Transverse η := hbadX lam (fun h => hlam (Finset.mem_union_left _ h))
  have hηY : (lobeChainL Y).Transverse η := hbadY lam (fun h => hlam (Finset.mem_union_right _ h))
  have hrne : (-ρ.r) ≠ 0 := neg_ne_zero.mpr ρ.r_ne_zero
  have hdetR : 0 < det2 (-ρ.r) η := det2_r_sweepDir_pos hrne lam
  have hdetr : det2 ρ.r η ≠ 0 := by
    have : det2 ρ.r η = - det2 (-ρ.r) η := by
      rw [show (-ρ.r) = (-1 : ℝ) • ρ.r from by module, det2_smul_left]; ring
    rw [this]; exact neg_ne_zero.mpr (ne_of_gt hdetR)
  -- u₀ ∈ (yL, xR) avoiding X-vertex projections.
  obtain ⟨badU, hbadU⟩ := exists_generic_u0L X (η := η) hdetr
  obtain ⟨u₀, hu₀io, hu₀bad⟩ : ∃ u₀ : ℝ, u₀ ∈ Set.Ioo yL xR ∧ u₀ ∉ badU := by
    have hinf : (Set.Ioo yL xR).Infinite := Set.Ioo_infinite hyLxR
    have hns : ¬ (Set.Ioo yL xR ⊆ (badU : Set ℝ)) := fun hsub =>
      hinf (badU.finite_toSet.subset hsub)
    rw [Set.not_subset] at hns; obtain ⟨u₀, hio, hnb⟩ := hns; exact ⟨u₀, hio, hnb⟩
  rw [Set.mem_Ioo] at hu₀io
  have hgenX : ∀ j : Fin (X.len + 1), side η (x + u₀ • ρ.r) (chainPtL X j) ≠ 0 := hbadU u₀ hu₀bad
  -- N(z₀) odd.
  have hodd : (lobeChainL X).rayCount η (x + u₀ • ρ.r) % 2 = 1 := by
    rw [lobeChainL_rayCount_parity X u₀ hηX hdetR hgenX]
    apply aboveInd_feet_straddleL X η u₀ hdetr
    have hlo : xL < u₀ := lt_trans hxLyL hu₀io.1
    have hhi : u₀ < xR := hu₀io.2
    rcases le_total (tauFirstL X) (tauLastL X) with hle | hle
    · left
      rw [hxLdef, min_eq_left hle] at hlo; rw [hxRdef, max_eq_right hle] at hhi
      exact ⟨hlo, hhi⟩
    · right
      rw [hxLdef, min_eq_right hle] at hlo; rw [hxRdef, max_eq_left hle] at hhi
      exact ⟨hlo, hhi⟩
  -- R far right (R > yR), avoiding X-vertex projections.
  obtain ⟨badUR, hbadUR⟩ := exists_generic_u0L X (η := η) hdetr
  obtain ⟨R, hRio, hRbad⟩ : ∃ R : ℝ, yR < R ∧ R ∉ badUR := by
    have hinf : (Set.Ioo yR (yR + 1)).Infinite := Set.Ioo_infinite (by linarith)
    have hns : ¬ (Set.Ioo yR (yR + 1) ⊆ (badUR : Set ℝ)) := fun hsub =>
      hinf (badUR.finite_toSet.subset hsub)
    rw [Set.not_subset] at hns; obtain ⟨R, hio, hnb⟩ := hns
    rw [Set.mem_Ioo] at hio; exact ⟨R, hio.1, hnb⟩
  have hgenXR : ∀ j : Fin (X.len + 1), side η (x + R • ρ.r) (chainPtL X j) ≠ 0 := hbadUR R hRbad
  -- N(z_R) even (R outside both X feet: xL < xR < yR < R).
  have heven : (lobeChainL X).rayCount η (x + R • ρ.r) % 2 = 0 := by
    rw [lobeChainL_rayCount_parity X R hηX hdetR hgenXR]
    apply aboveInd_feet_outsideL X η R hdetr
    -- tauFirstL X < R ∧ tauLastL X < R: both ≤ xR < yR < R.
    have hxLlt : xL < R := lt_of_le_of_lt hxLR (lt_trans hxRyR hRio)
    have hxRlt : xR < R := lt_trans hxRyR hRio
    rcases le_total (tauFirstL X) (tauLastL X) with hle | hle
    · left
      constructor
      · rw [show tauFirstL X = xL from by rw [hxLdef, min_eq_left hle]]; exact hxLlt
      · rw [show tauLastL X = xR from by rw [hxRdef, max_eq_right hle]]; exact hxRlt
    · left
      constructor
      · rw [show tauFirstL X = xR from by rw [hxRdef, max_eq_left hle]]; exact hxRlt
      · rw [show tauLastL X = xL from by rw [hxLdef, min_eq_right hle]]; exact hxLlt
  -- transport path: z₀ → yL-foot → (Y walk) → yR-foot → z_R.
  have hp1 : (lobeChainL X).rayCount η (x + u₀ • ρ.r) % 2
      = (lobeChainL X).rayCount η (x + yL • ρ.r) % 2 := by
    apply transport_XL_along_line_mm X u₀ yL hηX hdetR
    · left; rw [lt_min_iff]; constructor <;> [linarith [hu₀io.1]; linarith]
    · right; rw [max_lt_iff]; exact ⟨hu₀io.2, hyLxR⟩
  have hp2 : (lobeChainL X).rayCount η (x + yL • ρ.r) % 2
      = (lobeChainL X).rayCount η (x + yR • ρ.r) % 2 := by
    have hwalk : (lobeChainL X).rayCount η (footFirstL Y) % 2
        = (lobeChainL X).rayCount η (footLastL Y) % 2 :=
      transport_XL_over_YL X Y hηX hdetR hdisj
    rcases tauL_eq_min_or_max Y with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [show (x + yL • ρ.r) = footFirstL Y from by rw [show footFirstL Y = x + tauFirstL Y • ρ.r from rfl, h1],
        show (x + yR • ρ.r) = footLastL Y from by rw [show footLastL Y = x + tauLastL Y • ρ.r from rfl, h2]]
      exact hwalk
    · rw [show (x + yL • ρ.r) = footLastL Y from by rw [show footLastL Y = x + tauLastL Y • ρ.r from rfl, h2],
        show (x + yR • ρ.r) = footFirstL Y from by rw [show footFirstL Y = x + tauFirstL Y • ρ.r from rfl, h1]]
      exact hwalk.symm
  have hp3 : (lobeChainL X).rayCount η (x + yR • ρ.r) % 2
      = (lobeChainL X).rayCount η (x + R • ρ.r) % 2 := by
    apply transport_XL_along_line_mm X yR R hηX hdetR
    · left; rw [lt_min_iff]; constructor <;> [linarith; linarith [hRio]]
    · left; rw [lt_min_iff]; exact ⟨hxRyR, lt_trans hxRyR hRio⟩
  have hchain : (1 : ℤ) = 0 := by rw [← hodd, hp1, hp2, hp3, heven]
  exact absurd hchain (by decide)

/-- **Lower interval noninterleave.** -/
theorem lower_lobes_not_tauInterleave
    (X Y : LowerLobe P ρ x)
    (hdisj : Disjoint (lobeChainL X).carrier (lobeChainL Y).carrier) :
    ¬ TauInterleaves (crossTau P ρ x) X.start (lobeLastEdgeL X) Y.start (lobeLastEdgeL Y) := by
  rw [TauInterleaves]
  show ¬ ((min (tauFirstL X) (tauLastL X) < min (tauFirstL Y) (tauLastL Y) ∧
            min (tauFirstL Y) (tauLastL Y) < max (tauFirstL X) (tauLastL X) ∧
            max (tauFirstL X) (tauLastL X) < max (tauFirstL Y) (tauLastL Y)) ∨
          (min (tauFirstL Y) (tauLastL Y) < min (tauFirstL X) (tauLastL X) ∧
            min (tauFirstL X) (tauLastL X) < max (tauFirstL Y) (tauLastL Y) ∧
            max (tauFirstL Y) (tauLastL Y) < max (tauFirstL X) (tauLastL X)))
  rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
  · exact lower_interval_core X Y hdisj h1 h2 h3
  · exact lower_interval_core Y X hdisj.symm h1 h2 h3

/-! ## §4. The Alternation-slot adapters and the UNCONDITIONAL Ch36 kernel.

The interval theorems discharge the `hposNI` / `hnegNI` slots of
`alt_of_twoSide_noncrossing_cycle` for ALL same-sign chord pairs (not just ascending), and
`ZinanCh36SuccBij.upperLobes_carrier_disjoint` / `lowerLobes_carrier_disjoint` supply the carrier
disjointness those interval theorems need.  Together with
`boundarySucc_cycle_connected_unconditional` (the single-cycle property, no residue) this closes the
full-line `Alt` with NO external geometric input — and hence the ray dichotomy / Jordan kernel /
winding bound for every strict simple polygon at every generic off-boundary point. -/

/-- **Slot adapter (upper).**  Exactly the `hposNI` shape: distinct same-`+1`-sign crossings never
τ-interleave their boundary-successor chords.  Wires `upper_lobes_not_tauInterleave` through the
lobe builders, with carrier disjointness from `upperLobes_carrier_disjoint`. -/
theorem upper_noninterleaving_full
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a b : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hb : b ∈ LineCrossingEdges P ρ x)
    (hab : a ≠ b) (hσa : eSign P ρ a = 1) (hσb : eSign P ρ b = 1) :
    ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b) := by
  set X := upperLobeOfPos P ρ x hvert ha hσa with hXdef
  set Y := upperLobeOfPos P ρ x hvert hb hσb with hYdef
  have hXs : X.start = a := rfl
  have hYs : Y.start = b := rfl
  have hXl : lobeLastEdge X = boundarySucc P ρ x a := by
    rw [boundarySucc_eq_nextCrossing P ρ x ha]; exact upperLobeOfPos_last P ρ x hvert ha hσa
  have hYl : lobeLastEdge Y = boundarySucc P ρ x b := by
    rw [boundarySucc_eq_nextCrossing P ρ x hb]; exact upperLobeOfPos_last P ρ x hvert hb hσb
  have hdisj : Disjoint (lobeChain X).carrier (lobeChain Y).carrier :=
    upperLobes_carrier_disjoint hvert ha hb hab hσa hσb
  have := upper_lobes_not_tauInterleave X Y hdisj
  rwa [hXs, hYs, hXl, hYl] at this

/-- **Slot adapter (lower).**  Exactly the `hnegNI` shape. -/
theorem lower_noninterleaving_full
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a b : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hb : b ∈ LineCrossingEdges P ρ x)
    (hab : a ≠ b) (hσa : eSign P ρ a = -1) (hσb : eSign P ρ b = -1) :
    ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b) := by
  set X := lowerLobeOfNeg P ρ x hvert ha hσa with hXdef
  set Y := lowerLobeOfNeg P ρ x hvert hb hσb with hYdef
  have hXs : X.start = a := rfl
  have hYs : Y.start = b := rfl
  have hXl : lobeLastEdgeL X = boundarySucc P ρ x a := by
    rw [boundarySucc_eq_nextCrossing P ρ x ha]; exact lowerLobeOfNeg_last P ρ x hvert ha hσa
  have hYl : lobeLastEdgeL Y = boundarySucc P ρ x b := by
    rw [boundarySucc_eq_nextCrossing P ρ x hb]; exact lowerLobeOfNeg_last P ρ x hvert hb hσb
  have hdisj : Disjoint (lobeChainL X).carrier (lobeChainL Y).carrier :=
    lowerLobes_carrier_disjoint hvert ha hb hab hσa hσb
  have := lower_lobes_not_tauInterleave X Y hdisj
  rwa [hXs, hYs, hXl, hYl] at this

/-- **The full-line crossing alternation, UNCONDITIONAL.**  For every strict simple polygon and
generic line, the line-crossing edges, sorted by `crossTau`, have an alternating `eSign` image —
with no external geometric residue.  All four `alt_of_twoSide_noncrossing_cycle` inputs are landed:
`hτinj`, `hνmem`, `hcycle` (the unconditional single cycle), `hpm`/`hflip`, and the two
`¬ TauInterleaves` slots (the interval adapters above). -/
theorem fullLineCrossingAlternation_unconditional
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) :
    ∃ L : List (Fin n), L.Nodup ∧
      (∀ i, i ∈ L ↔ i ∈ LineCrossingEdges P ρ x) ∧
      L.Pairwise (fun a b => crossTau P ρ x a < crossTau P ρ x b) ∧
      Alt (L.map (eSign P ρ)) := by
  classical
  have hτinj : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      crossTau P ρ x a = crossTau P ρ x b → a = b := by
    intro a ha b hb hEq
    by_contra hne
    exact crossTau_injOn_lineCrossingEdges P ρ x hvert ha hb hne hEq
  obtain ⟨L, hnd, hmem, hsort⟩ :=
    exists_sorted_enum (crossTau P ρ x) (LineCrossingEdges P ρ x) hτinj
  refine ⟨L, hnd, hmem, hsort, ?_⟩
  have hνmem : ∀ a ∈ LineCrossingEdges P ρ x, boundarySucc P ρ x a ∈ LineCrossingEdges P ρ x :=
    fun a ha => boundarySucc_mem P ρ x hvert ha
  have hpm : ∀ a ∈ LineCrossingEdges P ρ x, eSign P ρ a = 1 ∨ eSign P ρ a = -1 :=
    fun a _ => eSign_mem P ρ a
  have hflip : ∀ a ∈ LineCrossingEdges P ρ x,
      eSign P ρ (boundarySucc P ρ x a) = - eSign P ρ a :=
    fun a ha => boundarySucc_sign_flip P ρ x hvert ha
  have hcycle : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      ∃ k : ℕ, (boundarySucc P ρ x)^[k] a = b :=
    fun a ha b hb => boundarySucc_cycle_connected_unconditional P ρ x hvert ha hb
  have hposNI : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      a ≠ b → eSign P ρ a = 1 → eSign P ρ b = 1 →
      ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b) :=
    fun a ha b hb hab hσa hσb => upper_noninterleaving_full hvert ha hb hab hσa hσb
  have hnegNI : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      a ≠ b → eSign P ρ a = -1 → eSign P ρ b = -1 →
      ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b) :=
    fun a ha b hb hab hσa hσb => lower_noninterleaving_full hvert ha hb hab hσa hσb
  exact alt_of_twoSide_noncrossing_cycle hτinj hνmem hcycle hpm hflip hposNI hnegNI hnd hmem hsort

/-- **The ray Jordan kernel, UNCONDITIONAL** (general `n`).  `RayCrossingAlternation` holds at every
generic off-boundary point of every strict simple polygon — no external input.  This is the Ch36
kernel itself. -/
theorem rayCrossingAlternation_final
    (hoff : ¬ OnBoundary P x)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) :
    RayCrossingAlternation P ρ x :=
  rayCrossingAlternation_of_fullLineAlternation P ρ x hoff hvert
    (fullLineCrossingAlternation_unconditional hvert)

/-- **Chapter winding bound, UNCONDITIONAL** (general `n`).  Composing the kernel with the landed
`windCross_mem_of_alternation`: every generic off-boundary point of a strict simple polygon has
signed forward-ray winding in `{0, 1, -1}`. -/
theorem windCross_mem_final
    (hoff : ¬ OnBoundary P x)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) :
    windCross P ρ x = 0 ∨ windCross P ρ x = 1 ∨ windCross P ρ x = -1 :=
  windCross_mem_of_alternation P ρ (rayCrossingAlternation_final hoff hvert)

end

/-! ## Axiom audit (clean-3 expected: `propext`, `Classical.choice`, `Quot.sound`) -/

section Audit
open ProofsInTheBook.ZinanCh36Interval
#print axioms upper_interval_core
#print axioms upper_lobes_not_tauInterleave
#print axioms lower_interval_core
#print axioms lower_lobes_not_tauInterleave
#print axioms upper_noninterleaving_full
#print axioms lower_noninterleaving_full
#print axioms fullLineCrossingAlternation_unconditional
#print axioms rayCrossingAlternation_final
#print axioms windCross_mem_final
end Audit

end ProofsInTheBook.ZinanCh36Interval
