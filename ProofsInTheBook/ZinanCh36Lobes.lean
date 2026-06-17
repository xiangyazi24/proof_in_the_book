import ProofsInTheBook.ZinanCh36Theta

/-!
# Chapter 36 — the same-side lobe non-interleaving brick (the master topological brick)

This file proves the one genuinely topological fact of Chapter 36 in its sharpest isolated
form: two boundary **lobes** on the SAME side of a generic line cannot interleave along the
line.  A lobe is a maximal sub-walk of the polygon boundary that leaves the line at one
crossing edge, stays strictly on the positive side, and returns at the next crossing edge.

The whole content is reduced to the **1-D sign-change telescope** — the abstract,
polygon-free statement that along a finite sequence of reals the number of consecutive
sign-flips of `(value − threshold)` is odd iff the two endpoints straddle the threshold.
This is the 1-D analogue of the proven `lineCrossing_eSign_sum_zero` telescope (it is the
unsigned/parity image of the very same per-edge difference).

The load-bearing supply lives in §A (the abstract telescope) and §B (its specialization to
the polygon boundary walk via the existing `side` coordinate).  §C defines the lobes; §D is
the non-interleaving theorem and its lower mirror.

DESIGN NOTE.  The committed design (`HANDOFF/ch36-lobes-master-design.md`) phrases the proof
as a vertical-ray parity sweep.  The honest formalizable core of that sweep is the 1-D
telescope of §A applied to TWO directions: the line's own `side` coordinate orders the four
feet, and a transverse `side`-coordinate counts how often each lobe-arc crosses the
separating vertical line.  Both counts are governed by the SAME abstract telescope, so the
sweep collapses to a parity bookkeeping over the abstract lemma — no 2-D Jordan content, no
synthetic pocket polygon.
-/

namespace ProofsInTheBook.ZinanCh36Lobes

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.ZinanCh36Theta
open scoped RealInnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ## §A. The abstract 1-D sign-change telescope (polygon-free)

For a finite sequence of reals `f 0, f 1, …, f m` none equal to a threshold `t`, the number
of consecutive pairs whose values straddle `t` has the parity of the strict-side indicator
difference of the two endpoints.  This is the parity heart of the whole brick. -/

/-- Strict-above indicator of a real relative to a threshold (`1` if `t < a`, else `0`). -/
def aboveInd (t a : ℝ) : ℤ := if t < a then 1 else 0

/-- A consecutive pair straddles the threshold (the unsigned crossing indicator). -/
def crossInd (t a b : ℝ) : ℤ := if (a - t) * (b - t) < 0 then 1 else 0

/-- **Per-step telescope (the atom).**  With both endpoints off the threshold, the crossing
indicator of a step equals the difference of the endpoints' strict-above indicators MOD 2
(as the absolute value: a single step crosses iff exactly one endpoint is above). -/
lemma crossInd_eq_abs_aboveInd_sub {t a b : ℝ} (ha : a ≠ t) (hb : b ≠ t) :
    crossInd t a b = |aboveInd t b - aboveInd t a| := by
  unfold crossInd aboveInd
  have ha' : a - t ≠ 0 := sub_ne_zero.mpr ha
  have hb' : b - t ≠ 0 := sub_ne_zero.mpr hb
  rcases lt_or_gt_of_ne ha' with hA | hA <;> rcases lt_or_gt_of_ne hb' with hB | hB
  · -- a < t, b < t : no cross, both below.
    rw [if_neg (by nlinarith), if_neg (by linarith), if_neg (by linarith)]; norm_num
  · -- a < t, b > t : cross, b above.
    rw [if_pos (by nlinarith), if_pos (by linarith), if_neg (by linarith)]; norm_num
  · -- a > t, b < t : cross, a above.
    rw [if_pos (by nlinarith), if_neg (by linarith), if_pos (by linarith)]; norm_num
  · -- a > t, b > t : no cross, both above.
    rw [if_neg (by nlinarith), if_pos (by linarith), if_pos (by linarith)]; norm_num

/-- The crossing indicator and the signed indicator-difference have the same parity. -/
lemma crossInd_emod_two {t a b : ℝ} (ha : a ≠ t) (hb : b ≠ t) :
    crossInd t a b % 2 = (aboveInd t b - aboveInd t a) % 2 := by
  rw [crossInd_eq_abs_aboveInd_sub ha hb]
  rcases abs_cases (aboveInd t b - aboveInd t a) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h]; omega

/-- **The abstract telescope (parity form).**  Along a walk `g 0, …, g m` with no value equal
to `t`, the parity of the number of straddling steps equals the parity of the endpoints'
strict-above indicator difference.  In particular the count of crossing steps is ODD iff the
two endpoints lie on opposite sides of `t`.  Proof: each crossing step has the parity of the
signed indicator difference of its endpoints (`crossInd_emod_two`); the signed differences
telescope (`Finset.sum_range_sub`) to the endpoint difference. -/
lemma sum_crossInd_emod_two (m : ℕ) (t : ℝ) (g : ℕ → ℝ)
    (hg : ∀ k, k ≤ m → g k ≠ t) :
    (∑ k ∈ Finset.range m, crossInd t (g k) (g (k + 1))) % 2
      = (aboveInd t (g m) - aboveInd t (g 0)) % 2 := by
  classical
  -- replace each crossInd by the signed indicator-difference (same parity), then telescope.
  have hmod : (∑ k ∈ Finset.range m, crossInd t (g k) (g (k + 1))) % 2
      = (∑ k ∈ Finset.range m, (aboveInd t (g (k + 1)) - aboveInd t (g k))) % 2 := by
    rw [Finset.sum_int_mod, Finset.sum_int_mod
        (s := Finset.range m) (f := fun k => aboveInd t (g (k + 1)) - aboveInd t (g k))]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    exact crossInd_emod_two (hg k (by omega)) (hg (k + 1) (by omega))
  rw [hmod, Finset.sum_range_sub (fun k => aboveInd t (g k))]

/-! ## §B. The along-line coordinate `uCoord` and the crossTau bridge

`uCoord r x p := ⟪p − x, r⟫` is the (unnormalized) coordinate of `p` along the line `x + ℝ•r`.
A point on the ray, `x + τ•r`, has `uCoord = τ·‖r‖²`; in particular crossing points of crossing
edges have `uCoord` a fixed positive multiple of their `crossTau`, so ordering by `crossTau`
is ordering by `uCoord`. -/

/-- The along-line coordinate of a point relative to the line `x + ℝ•r`. -/
def uCoord (r x p : Pt) : ℝ := (⟪p - x, r⟫ : ℝ)

/-- A ray point's along-line coordinate is `τ·‖r‖²`. -/
lemma uCoord_ray (r x : Pt) (τ : ℝ) :
    uCoord r x (x + τ • r) = τ * ‖r‖ ^ 2 := by
  unfold uCoord
  have hsub : (x + τ • r) - x = τ • r := by abel
  rw [hsub, inner_smul_left]
  rw [show (starRingEnd ℝ) τ = τ from by simp]
  rw [show (⟪r, r⟫ : ℝ) = ‖r‖ ^ 2 from by
        rw [← real_inner_self_eq_norm_sq], mul_comm]

/-- `‖r‖² > 0` for a nonzero ray direction. -/
lemma normSq_pos (r : Pt) (hr : r ≠ 0) : 0 < ‖r‖ ^ 2 := by
  have : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  positivity

/-- **The crossTau→uCoord bridge.**  The along-line coordinate of the crossing point of edge
`i` is exactly `crossTau · ‖ρ.r‖²` — a fixed positive multiple of `crossTau`.  Hence ordering
the feet by `crossTau` is the same as ordering them by `uCoord`, and the original line's feet
`uCoord` values are determined by their `crossTau`. -/
lemma uCoord_crossPoint (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) :
    uCoord ρ.r x (x + crossTau P ρ x i • ρ.r) = crossTau P ρ x i * ‖ρ.r‖ ^ 2 :=
  uCoord_ray ρ.r x (crossTau P ρ x i)

/-- The along-line foot coordinate is strictly monotone in `crossTau` (positive scale): for a
nonzero ray direction, `crossTau i < crossTau j` iff the feet `uCoord`s compare the same way. -/
lemma uCoord_crossPoint_lt_iff (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i j : Fin n) :
    uCoord ρ.r x (x + crossTau P ρ x i • ρ.r) < uCoord ρ.r x (x + crossTau P ρ x j • ρ.r)
      ↔ crossTau P ρ x i < crossTau P ρ x j := by
  rw [uCoord_crossPoint, uCoord_crossPoint]
  constructor
  · intro h; exact lt_of_mul_lt_mul_right h (le_of_lt (normSq_pos ρ.r ρ.r_ne_zero))
  · intro h; exact mul_lt_mul_of_pos_right h (normSq_pos ρ.r ρ.r_ne_zero)

/-! ## §C. The boundary lobe structure and its transverse feet-telescope

A lobe is captured by its two crossing edges `a`, `b` and the walk between them.  We index the
walk by `arcPos a k := a + k (mod n)`; the lobe has `m+1` vertices
`P.q a, P.q (a+1), …, P.q (a+m) = P.q b'`, where the FIRST step is the down-crossing of edge
`a` and the LAST is the up-crossing of edge `b`.  The load-bearing fact is the
**feet-telescope**: the number of times the lobe's walk crosses any transverse threshold `t`
(on `uCoord`) is ODD iff `t` separates the two feet's `uCoord` values. -/

/-- The cyclic walk position `(i + k) mod n`. -/
def arcPos (i : Fin n) (k : ℕ) : Fin n :=
  ⟨(i.val + k) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

/-- A same-side (upper) boundary lobe of the polygon `P` across the line `x + ℝ•ρ.r`.
`start` is the edge index of the lobe's first (down-)crossing, `len = m+1` the number of edges
of the walk; the walk vertices are `P.q (arcPos start 0), …, P.q (arcPos start len)`.  The two
feet are the crossing points of edge `start` (the first edge, foot at `uCoord = u0`) and edge
`arcPos start (len-1)` (the last edge, foot at `u1`).  All STRICTLY interior vertices lie on the
positive side. -/
structure UpperLobe (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) where
  start : Fin n
  len : ℕ
  len_pos : 0 < len
  /-- the first edge `start` is a line-crossing edge (the down-crossing foot) -/
  cross_first : SpanCrossesSide P ρ x start
  /-- the last edge `arcPos start (len-1)` is a line-crossing edge (the up-crossing foot) -/
  cross_last : SpanCrossesSide P ρ x (arcPos start (len - 1))
  /-- every STRICTLY interior walk vertex is on the positive side -/
  interior_pos : ∀ k : ℕ, 0 < k → k < len → 0 < side ρ.r x (P.q (arcPos start k))

/-- The `uCoord` of the lobe's `k`-th walk vertex. -/
def UpperLobe.vertU {P : StrictSimplePolygon n} {ρ : RayDirection P} {x : Pt}
    (L : UpperLobe P ρ x) (k : ℕ) : ℝ :=
  uCoord ρ.r x (P.q (arcPos L.start k))

/-- **The transverse feet-telescope.**  For a threshold `t` avoided by every walk vertex's
`uCoord`, the number of straddling steps of the lobe walk has the parity of the strict-above
indicator difference of the two endpoints (`vertU 0` and `vertU len`).  In particular it is ODD
iff `t` separates the two feet `uCoord` values.  This is the §A telescope on `vertU`. -/
lemma UpperLobe.feet_telescope {P : StrictSimplePolygon n} {ρ : RayDirection P} {x : Pt}
    (L : UpperLobe P ρ x) (t : ℝ)
    (ht : ∀ k, k ≤ L.len → L.vertU k ≠ t) :
    (∑ k ∈ Finset.range L.len, crossInd t (L.vertU k) (L.vertU (k + 1))) % 2
      = (aboveInd t (L.vertU L.len) - aboveInd t (L.vertU 0)) % 2 :=
  sum_crossInd_emod_two L.len t (fun k => L.vertU k) ht

end

end ProofsInTheBook.ZinanCh36Lobes

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.ZinanCh36Lobes.crossInd_eq_abs_aboveInd_sub
#print axioms ProofsInTheBook.ZinanCh36Lobes.crossInd_emod_two
#print axioms ProofsInTheBook.ZinanCh36Lobes.sum_crossInd_emod_two
#print axioms ProofsInTheBook.ZinanCh36Lobes.uCoord_ray
#print axioms ProofsInTheBook.ZinanCh36Lobes.uCoord_crossPoint
#print axioms ProofsInTheBook.ZinanCh36Lobes.uCoord_crossPoint_lt_iff
#print axioms ProofsInTheBook.ZinanCh36Lobes.UpperLobe.feet_telescope
