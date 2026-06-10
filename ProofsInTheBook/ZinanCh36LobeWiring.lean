import ProofsInTheBook.ZinanCh36Lobes
import ProofsInTheBook.ZinanCh36RayDichotomy

/-!
# Chapter 36 — the lobe-pairing combinatorial wiring (Bricks 1–5)

This file supplies the *combinatorial wiring* of the Ch36 lobe-pairing design
(`HANDOFF/design-rounds/ch36-lobe-pairing-comb.md`): starting from the abstract `UpperLobe`
structure of `ZinanCh36Lobes` and the full-line crossing substrate of `ZinanCh36RayDichotomy`,
it builds the boundary-successor structure on line crossings and the lobe constructors that
the final alternation master will consume.

Everything here is *combinatorial* in the cyclic walk index and the `±1` `eSign` data.  The
genuinely geometric noninterleaving theorems, the combinatorial alternation master, and the
final assembly are NOT in scope.

## What is proved here

* **Brick 1 (`nextCrossing`).**  For a crossing edge `i`, the next line-crossing edge along the
  cyclic walk: `crossingDists` is the set of positive cyclic offsets `k` with `arcPos i k` a
  line crossing; `nextCrossDist` is its minimum (total via a `0` default), `nextCrossing` the
  edge at that offset.  Supplied with existence (`crossingDists_nonempty`, from
  `lineCrossing_exists_other`: a lone crossing would make the `eSign` sum `±1 ≠ 0`),
  positivity, membership, distinctness, and minimality (`no_crossing_before_next`).

* **Brick 2 (sign persistence runs).**  `noSpan_preserves_pos/neg`: a non-spanning edge keeps
  its start vertex's strict sign.  The run inductions `side_pos_between_next` /
  `side_neg_between_next`: across `[1, nextCrossDist]` the strict side sign of the start foot
  persists (no crossing before the next one).

* **Brick 3 (`eSign` convention).**  `eSign_eq_one_of_neg_pos`, `eSign_eq_neg_one_of_pos_neg`
  and the crossing-conditional `iff` forms, from `eSign_eq_osign` and `span_iff_opp_sign`.

* **Brick 4 (lobe constructors).**  `upperLobeOfPos` / `LowerLobe` + `lowerLobeOfNeg`, with the
  endpoint lemmas and `upperLobe_signs` (first foot `eSign = 1`, last foot `eSign = −1`).

* **Brick 5 (boundary cycle).**  `boundaryCrossingList` via `exists_sorted_enum` keyed on the
  cyclic offset `cyclicSteps i₀ ·` (injective on the crossings); `boundarySucc` (total via a
  `0` default), its membership, sign-flip, and cyclic-connectedness.

NOT IN SCOPE: the geometric noninterleaving theorems, the combinatorial alternation master,
the final assembly.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36LobeWiring

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonWindingExterior (eSign osign eSign_eq_osign)
open ProofsInTheBook.PolygonWindingBound (eSign_mem)
open ProofsInTheBook.ZinanCh36Theta (LineCrossingEdges mem_lineCrossingEdges_iff
  crossTau_injOn_lineCrossingEdges lineCrossing_eSign_sum_zero exists_sorted_enum)
open ProofsInTheBook.ZinanCh36Lobes (arcPos UpperLobe)
open scoped RealInnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ## §0. Cyclic-walk index arithmetic (`arcPos` successor and the `cyclicSteps` retraction) -/

/-- `arcPos i 0 = i`. -/
lemma arcPos_zero (i : Fin n) : arcPos i 0 = i := by
  unfold arcPos
  apply Fin.ext
  simp [Nat.mod_eq_of_lt i.isLt]

/-- The cyclic successor of `arcPos i k` is `arcPos i (k+1)`. -/
lemma cyclicNext_arcPos (i : Fin n) (k : ℕ) :
    cyclicNext (arcPos i k) = arcPos i (k + 1) := by
  apply Fin.ext
  rw [ProofsInTheBook.PolygonConvexVertex.cyclicNext_val]
  unfold arcPos
  simp only
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hlt : (i.val + k) % n < n := Nat.mod_lt _ hn
  have hmod : (i.val + (k + 1)) % n = ((i.val + k) % n + 1) % n := by
    rw [Nat.mod_add_mod, ← Nat.add_assoc]
  rw [hmod]
  by_cases h : (i.val + k) % n + 1 < n
  · rw [if_pos h, Nat.mod_eq_of_lt h]
  · rw [if_neg h]
    have heq : (i.val + k) % n + 1 = n := by omega
    rw [heq, Nat.mod_self]

/-! ## §A. Brick 1 — the next line-crossing edge along the cyclic walk

`crossingDists` is the finite set of *positive* cyclic offsets at which the walk hits another
line crossing; its minimum is `nextCrossDist`. -/

/-- The positive cyclic offsets `k < n` for which `arcPos i k` is a line crossing. -/
def crossingDists (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) :
    Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun k => 0 < k ∧ arcPos i k ∈ LineCrossingEdges P ρ x)

lemma mem_crossingDists_iff (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i : Fin n) (k : ℕ) :
    k ∈ crossingDists P ρ x i ↔
      k < n ∧ 0 < k ∧ arcPos i k ∈ LineCrossingEdges P ρ x := by
  classical
  unfold crossingDists
  rw [Finset.mem_filter, Finset.mem_range]

/-- **A lone line crossing is impossible.**  If `i` is the *only* line crossing, the full-line
`eSign` sum would equal `eSign i = ±1 ≠ 0`, contradicting `lineCrossing_eSign_sum_zero`.  Hence
some `j ≠ i` is also a line crossing. -/
lemma lineCrossing_exists_other (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    ∃ j : Fin n, j ≠ i ∧ j ∈ LineCrossingEdges P ρ x := by
  classical
  by_contra hcon
  push_neg at hcon
  -- every line crossing equals `i`, so the crossing set is `{i}`.
  have hsingle : (Finset.univ.filter (fun k => SpanCrossesSide P ρ x k)) = {i} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (mem_lineCrossingEdges_iff P ρ x i).mp hi⟩
    · intro j hj
      rw [Finset.mem_filter] at hj
      have hjmem : j ∈ LineCrossingEdges P ρ x := (mem_lineCrossingEdges_iff P ρ x j).mpr hj.2
      by_contra hne
      exact hcon j hne hjmem
  have hsum := lineCrossing_eSign_sum_zero P ρ x hvert
  rw [hsingle, Finset.sum_singleton] at hsum
  rcases eSign_mem P ρ i with h | h <;> rw [h] at hsum <;> exact absurd hsum (by norm_num)

/-- **`crossingDists` is nonempty.**  Some other line crossing `j` exists
(`lineCrossing_exists_other`); writing `j = arcPos i (cyclicSteps i j)` exhibits a positive
cyclic offset `< n` that lands on a crossing. -/
lemma crossingDists_nonempty (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    (crossingDists P ρ x i).Nonempty := by
  classical
  obtain ⟨j, hji, hjmem⟩ := lineCrossing_exists_other P ρ x hvert hi
  refine ⟨cyclicSteps i j, ?_⟩
  rw [mem_crossingDists_iff]
  have hkpos : 0 < cyclicSteps i j := cyclicSteps_pos_of_ne i j (Ne.symm hji)
  have hkadd := cyclicSteps_add_reverse i j (Ne.symm hji)
  have hother_pos : 0 < cyclicSteps j i := cyclicSteps_pos_of_ne j i hji
  have hklt : cyclicSteps i j < n := by omega
  have harceq : arcPos i (cyclicSteps i j) = j := by
    apply Fin.ext
    unfold arcPos cyclicSteps
    simp only
    by_cases hle : i.val ≤ j.val
    · rw [if_pos hle]
      have : i.val + (j.val - i.val) = j.val := by omega
      rw [this, Nat.mod_eq_of_lt j.isLt]
    · rw [if_neg hle]
      have hjv : j.val < i.val := by omega
      have : i.val + (n - i.val + j.val) = n + j.val := by
        have := i.isLt; omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt j.isLt]
  rw [harceq]
  exact ⟨hklt, hkpos, hjmem⟩

/-- The cyclic offset to the next line crossing (`0` if there is none). -/
def nextCrossDist (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) : ℕ := by
  classical
  exact if h : (crossingDists P ρ x i).Nonempty then (crossingDists P ρ x i).min' h else 0

/-- The next line-crossing edge along the cyclic walk. -/
def nextCrossing (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) : Fin n :=
  arcPos i (nextCrossDist P ρ x i)

/-- `nextCrossDist` is in `crossingDists` when there is another crossing. -/
lemma nextCrossDist_mem (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    nextCrossDist P ρ x i ∈ crossingDists P ρ x i := by
  classical
  have hne := crossingDists_nonempty P ρ x hvert hi
  unfold nextCrossDist
  rw [dif_pos hne]
  exact (crossingDists P ρ x i).min'_mem hne

/-- `nextCrossDist` is strictly positive (given another crossing). -/
lemma nextCrossDist_pos (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    0 < nextCrossDist P ρ x i :=
  ((mem_crossingDists_iff P ρ x i _).mp (nextCrossDist_mem P ρ x hvert hi)).2.1

/-- `nextCrossDist < n`. -/
lemma nextCrossDist_lt (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    nextCrossDist P ρ x i < n :=
  ((mem_crossingDists_iff P ρ x i _).mp (nextCrossDist_mem P ρ x hvert hi)).1

/-- The next crossing IS a line crossing. -/
lemma nextCrossing_mem (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    nextCrossing P ρ x i ∈ LineCrossingEdges P ρ x :=
  ((mem_crossingDists_iff P ρ x i _).mp (nextCrossDist_mem P ρ x hvert hi)).2.2

/-- The next crossing is a *span* crossing (unfolded membership). -/
lemma nextCrossing_span (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    SpanCrossesSide P ρ x (nextCrossing P ρ x i) :=
  (mem_lineCrossingEdges_iff P ρ x _).mp (nextCrossing_mem P ρ x hvert hi)

/-- **No crossing strictly before the next one.**  By minimality of `nextCrossDist`, for
`0 < k < nextCrossDist`, `arcPos i k` is NOT a line crossing. -/
lemma no_crossing_before_next (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) {k : ℕ}
    (hk0 : 0 < k) (hk : k < nextCrossDist P ρ x i) :
    arcPos i k ∉ LineCrossingEdges P ρ x := by
  classical
  intro hcross
  -- `k < n` since `k < nextCrossDist < n`.
  have hlt := nextCrossDist_lt P ρ x hvert hi
  have hkn : k < n := lt_trans hk hlt
  have hkmem : k ∈ crossingDists P ρ x i :=
    (mem_crossingDists_iff P ρ x i k).mpr ⟨hkn, hk0, hcross⟩
  have hne := crossingDists_nonempty P ρ x hvert hi
  have hmin : nextCrossDist P ρ x i ≤ k := by
    unfold nextCrossDist; rw [dif_pos hne]
    exact (crossingDists P ρ x i).min'_le k hkmem
  omega

/-- `nextCrossing ≠ i` (the next crossing is a strict cyclic step away). -/
lemma nextCrossing_ne (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    nextCrossing P ρ x i ≠ i := by
  classical
  unfold nextCrossing
  intro hEq
  -- `arcPos i d = i = arcPos i 0` with `0 < d < n` would force `d % n = 0`, contradiction.
  have hpos := nextCrossDist_pos P ρ x hvert hi
  have hlt := nextCrossDist_lt P ρ x hvert hi
  have hval := congrArg Fin.val hEq
  unfold arcPos at hval
  simp only at hval
  -- `(i + d) % n = i.val`, with `i.val < n` and `0 < d < n`.
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hil : i.val < n := i.isLt
  -- case split on whether `i.val + d` already < n.
  by_cases hsmall : i.val + nextCrossDist P ρ x i < n
  · rw [Nat.mod_eq_of_lt hsmall] at hval
    omega
  · -- `i.val + d ≥ n` and `< 2n`, so `% n = i.val + d - n`.
    have hge : n ≤ i.val + nextCrossDist P ρ x i := by omega
    have h2n : i.val + nextCrossDist P ρ x i < 2 * n := by omega
    have hmodeq : (i.val + nextCrossDist P ρ x i) % n = i.val + nextCrossDist P ρ x i - n := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hmodeq] at hval
    omega

/-! ## §B. Brick 2 — sign persistence runs

A non-spanning edge keeps its start vertex's strict sign; iterating across `[1, nextCrossDist]`
(no crossing before the next one) the start foot's strict sign persists. -/

/-- The strict positive side value of the walk's `k`-th vertex. -/
abbrev sideAt (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) (k : ℕ) : ℝ :=
  side ρ.r x (P.q (arcPos i k))

/-- **A non-spanning edge preserves a positive start sign.**  If the edge `arcPos i k` does NOT
span (`¬ SpanCrossesSide`), both endpoints are off the line (`hvert`), and the start vertex is
positive, then the end vertex is positive. -/
lemma noSpan_preserves_pos (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) (i : Fin n) (k : ℕ)
    (hns : ¬ SpanCrossesSide P ρ x (arcPos i k))
    (hpos : 0 < sideAt P ρ x i k) :
    0 < sideAt P ρ x i (k + 1) := by
  -- the next vertex is the cyclic successor of `arcPos i k`.
  have hsucc : arcPos i (k + 1) = cyclicNext (arcPos i k) := (cyclicNext_arcPos i k).symm
  have ha : side ρ.r x (P.q (arcPos i k)) ≠ 0 := hvert _
  have hb : side ρ.r x (P.q (cyclicNext (arcPos i k))) ≠ 0 := hvert _
  -- not spanning ⇒ same sign; start positive ⇒ end positive.
  unfold SpanCrossesSide at hns
  rw [span_iff_opp_sign ha hb] at hns
  push_neg at hns
  -- `¬ (a * b < 0)` with `a, b ≠ 0` and `a > 0` ⇒ `b > 0`.
  unfold sideAt
  rw [hsucc]
  by_contra hbnn
  push_neg at hbnn
  have hbneg : side ρ.r x (P.q (cyclicNext (arcPos i k))) < 0 := lt_of_le_of_ne hbnn hb
  have : side ρ.r x (P.q (arcPos i k)) *
      side ρ.r x (P.q (cyclicNext (arcPos i k))) < 0 := mul_neg_of_pos_of_neg hpos hbneg
  exact absurd this (not_lt.mpr (hns))

/-- **A non-spanning edge preserves a negative start sign.** -/
lemma noSpan_preserves_neg (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) (i : Fin n) (k : ℕ)
    (hns : ¬ SpanCrossesSide P ρ x (arcPos i k))
    (hneg : sideAt P ρ x i k < 0) :
    sideAt P ρ x i (k + 1) < 0 := by
  have hsucc : arcPos i (k + 1) = cyclicNext (arcPos i k) := (cyclicNext_arcPos i k).symm
  have ha : side ρ.r x (P.q (arcPos i k)) ≠ 0 := hvert _
  have hb : side ρ.r x (P.q (cyclicNext (arcPos i k))) ≠ 0 := hvert _
  unfold SpanCrossesSide at hns
  rw [span_iff_opp_sign ha hb] at hns
  push_neg at hns
  unfold sideAt
  rw [hsucc]
  by_contra hbnn
  push_neg at hbnn
  have hbpos : 0 < side ρ.r x (P.q (cyclicNext (arcPos i k))) := lt_of_le_of_ne hbnn (Ne.symm hb)
  have : side ρ.r x (P.q (arcPos i k)) *
      side ρ.r x (P.q (cyclicNext (arcPos i k))) < 0 := mul_neg_of_neg_of_pos hneg hbpos
  exact absurd this (not_lt.mpr (hns))

/-- **The positive run between consecutive crossings.**  Starting from a positive first foot
(`0 < sideAt i 1`), the strict side value stays positive through `sideAt i k` for every
`1 ≤ k ≤ nextCrossDist`.  Induction: no crossing strictly before `nextCrossDist`, so each
intermediate edge does not span and `noSpan_preserves_pos` carries the sign. -/
lemma side_pos_between_next (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x)
    (h1 : 0 < sideAt P ρ x i 1) :
    ∀ k : ℕ, 1 ≤ k → k ≤ nextCrossDist P ρ x i → 0 < sideAt P ρ x i k := by
  intro k
  induction k with
  | zero => intro h _; omega
  | succ m ih =>
    intro _ hle
    rcases Nat.lt_or_ge m 1 with hm | hm
    · -- m = 0 ⇒ k = 1.
      interval_cases m
      simpa using h1
    · -- m ≥ 1: use IH at m, edge `arcPos i m` does not span (m < nextCrossDist).
      have hmle : m ≤ nextCrossDist P ρ x i := by omega
      have hposm : 0 < sideAt P ρ x i m := ih hm hmle
      have hmlt : m < nextCrossDist P ρ x i := by omega
      have hns : ¬ SpanCrossesSide P ρ x (arcPos i m) := by
        intro hsp
        exact no_crossing_before_next P ρ x hvert hi (by omega) hmlt
          ((mem_lineCrossingEdges_iff P ρ x _).mpr hsp)
      exact noSpan_preserves_pos P ρ x hvert i m hns hposm

/-- **The negative run between consecutive crossings.** -/
lemma side_neg_between_next (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x)
    (h1 : sideAt P ρ x i 1 < 0) :
    ∀ k : ℕ, 1 ≤ k → k ≤ nextCrossDist P ρ x i → sideAt P ρ x i k < 0 := by
  intro k
  induction k with
  | zero => intro h _; omega
  | succ m ih =>
    intro _ hle
    rcases Nat.lt_or_ge m 1 with hm | hm
    · interval_cases m
      simpa using h1
    · have hmle : m ≤ nextCrossDist P ρ x i := by omega
      have hnegm : sideAt P ρ x i m < 0 := ih hm hmle
      have hmlt : m < nextCrossDist P ρ x i := by omega
      have hns : ¬ SpanCrossesSide P ρ x (arcPos i m) := by
        intro hsp
        exact no_crossing_before_next P ρ x hvert hi (by omega) hmlt
          ((mem_lineCrossingEdges_iff P ρ x _).mpr hsp)
      exact noSpan_preserves_neg P ρ x hvert i m hns hnegm

/-! ## §C. Brick 3 — `eSign` sign convention bricks

`eSign i = osign (side(end) − side(start))`; resolving the two endpoint signs reads off the
crossing direction. -/

/-- A crossing whose start foot is negative and end foot positive has `eSign = 1`. -/
lemma eSign_eq_one_of_neg_pos (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i : Fin n) (ha : side ρ.r x (P.q i) < 0)
    (hb : 0 < side ρ.r x (P.q (cyclicNext i))) :
    eSign P ρ i = 1 := by
  rw [eSign_eq_osign P ρ x i]
  unfold osign
  rw [if_pos (by linarith)]

/-- A crossing whose start foot is positive and end foot negative has `eSign = −1`. -/
lemma eSign_eq_neg_one_of_pos_neg (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i : Fin n) (ha : 0 < side ρ.r x (P.q i))
    (hb : side ρ.r x (P.q (cyclicNext i)) < 0) :
    eSign P ρ i = -1 := by
  rw [eSign_eq_osign P ρ x i]
  unfold osign
  rw [if_neg (by linarith)]

/-- **Crossing-conditional `iff` (positive direction).**  At a span crossing with both feet off
the line, `eSign = 1` iff the start foot is negative (equivalently the end foot positive). -/
lemma eSign_eq_one_iff_start_neg (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i : Fin n) (ha : side ρ.r x (P.q i) ≠ 0)
    (hb : side ρ.r x (P.q (cyclicNext i)) ≠ 0)
    (hsp : SpanCrossesSide P ρ x i) :
    eSign P ρ i = 1 ↔ side ρ.r x (P.q i) < 0 := by
  unfold SpanCrossesSide at hsp
  rw [span_iff_opp_sign ha hb] at hsp
  constructor
  · intro _
    -- `eSign = 1` ⇒ end − start > 0; with opposite signs forces start < 0.
    by_contra hnn
    push_neg at hnn
    have hapos : 0 < side ρ.r x (P.q i) := lt_of_le_of_ne hnn (Ne.symm ha)
    -- opposite signs ⇒ end < 0.
    have hbneg : side ρ.r x (P.q (cyclicNext i)) < 0 := by nlinarith [hsp]
    rw [eSign_eq_neg_one_of_pos_neg P ρ x i hapos hbneg] at *
    exact absurd ‹(-1 : ℤ) = 1› (by norm_num)
  · intro hneg
    have hbpos : 0 < side ρ.r x (P.q (cyclicNext i)) := by nlinarith [hsp]
    exact eSign_eq_one_of_neg_pos P ρ x i hneg hbpos

/-- **Crossing-conditional `iff` (negative direction).**  At a span crossing with both feet off
the line, `eSign = −1` iff the start foot is positive. -/
lemma eSign_eq_neg_one_iff_start_pos (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i : Fin n) (ha : side ρ.r x (P.q i) ≠ 0)
    (hb : side ρ.r x (P.q (cyclicNext i)) ≠ 0)
    (hsp : SpanCrossesSide P ρ x i) :
    eSign P ρ i = -1 ↔ 0 < side ρ.r x (P.q i) := by
  unfold SpanCrossesSide at hsp
  rw [span_iff_opp_sign ha hb] at hsp
  constructor
  · intro _
    by_contra hnn
    push_neg at hnn
    have haneg : side ρ.r x (P.q i) < 0 := lt_of_le_of_ne hnn ha
    have hbpos : 0 < side ρ.r x (P.q (cyclicNext i)) := by nlinarith [hsp]
    rw [eSign_eq_one_of_neg_pos P ρ x i haneg hbpos] at *
    exact absurd ‹(1 : ℤ) = -1› (by norm_num)
  · intro hpos
    have hbneg : side ρ.r x (P.q (cyclicNext i)) < 0 := by nlinarith [hsp]
    exact eSign_eq_neg_one_of_pos_neg P ρ x i hpos hbneg

/-! ## §D. Brick 4 — the lobe constructors

`upperLobeOfPos`: from a crossing `i` with `eSign = 1` (so the post-`i` walk is positive), the
`UpperLobe` with `start = i`, `len = nextCrossDist + 1`. -/

/-- A same-side (lower) boundary lobe: the mirror of `UpperLobe`, with all strictly interior
walk vertices on the NEGATIVE side. -/
structure LowerLobe (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) where
  start : Fin n
  len : ℕ
  len_pos : 0 < len
  cross_first : SpanCrossesSide P ρ x start
  cross_last : SpanCrossesSide P ρ x (arcPos start (len - 1))
  interior_neg : ∀ k : ℕ, 0 < k → k < len → side ρ.r x (P.q (arcPos start k)) < 0

/-- The first foot of an `eSign = 1` crossing has a positive end vertex (`sideAt i 1 > 0`):
`arcPos i 1 = cyclicNext i`, and `eSign = 1` with both feet off the line forces the end positive.
-/
lemma sideAt_one_pos_of_eSign_one (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) (hesign : eSign P ρ i = 1) :
    0 < sideAt P ρ x i 1 := by
  have hsp := (mem_lineCrossingEdges_iff P ρ x i).mp hi
  have hstart_neg : side ρ.r x (P.q i) < 0 :=
    (eSign_eq_one_iff_start_neg P ρ x i (hvert i) (hvert _) hsp).mp hesign
  -- end foot: opposite sign of start ⇒ positive.
  have hspan := hsp
  unfold SpanCrossesSide at hspan
  rw [span_iff_opp_sign (hvert i) (hvert _)] at hspan
  have hbpos : 0 < side ρ.r x (P.q (cyclicNext i)) := by nlinarith [hspan]
  unfold sideAt
  have : arcPos i 1 = cyclicNext i := by rw [← cyclicNext_arcPos i 0, arcPos_zero]
  rw [this]
  exact hbpos

/-- The first foot of an `eSign = −1` crossing has a negative end vertex (`sideAt i 1 < 0`). -/
lemma sideAt_one_neg_of_eSign_neg_one (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) (hesign : eSign P ρ i = -1) :
    sideAt P ρ x i 1 < 0 := by
  have hsp := (mem_lineCrossingEdges_iff P ρ x i).mp hi
  have hstart_pos : 0 < side ρ.r x (P.q i) :=
    (eSign_eq_neg_one_iff_start_pos P ρ x i (hvert i) (hvert _) hsp).mp hesign
  have hspan := hsp
  unfold SpanCrossesSide at hspan
  rw [span_iff_opp_sign (hvert i) (hvert _)] at hspan
  have hbneg : side ρ.r x (P.q (cyclicNext i)) < 0 := by nlinarith [hspan]
  unfold sideAt
  have : arcPos i 1 = cyclicNext i := by rw [← cyclicNext_arcPos i 0, arcPos_zero]
  rw [this]
  exact hbneg

/-- The endpoint vertex of the `nextCrossDist`-run is the start of `nextCrossing`. -/
lemma arcPos_nextCrossDist (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) :
    arcPos i (nextCrossDist P ρ x i) = nextCrossing P ρ x i := rfl

/-- **`upperLobeOfPos`.**  A line crossing `i` with `eSign = 1` produces an `UpperLobe` with
`start = i`, `len = nextCrossDist + 1`.  The first edge crosses (`hi`), the last edge
(`arcPos i (len-1) = nextCrossing i`) crosses (`nextCrossing_span`), and every strictly interior
vertex is positive (`side_pos_between_next`). -/
def upperLobeOfPos (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) (hesign : eSign P ρ i = 1) :
    UpperLobe P ρ x where
  start := i
  len := nextCrossDist P ρ x i + 1
  len_pos := Nat.succ_pos _
  cross_first := by
    simpa using (mem_lineCrossingEdges_iff P ρ x i).mp hi
  cross_last := by
    rw [show nextCrossDist P ρ x i + 1 - 1 = nextCrossDist P ρ x i from by omega,
      arcPos_nextCrossDist]
    exact nextCrossing_span P ρ x hvert hi
  interior_pos := by
    intro k hk0 hk
    have hkle : k ≤ nextCrossDist P ρ x i := by omega
    have h1 := sideAt_one_pos_of_eSign_one P ρ x hvert hi hesign
    exact side_pos_between_next P ρ x hvert hi h1 k hk0 hkle

/-- The last walk vertex of `upperLobeOfPos` is the start vertex of `nextCrossing i`. -/
lemma upperLobeOfPos_last (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) (hesign : eSign P ρ i = 1) :
    arcPos (upperLobeOfPos P ρ x hvert hi hesign).start
      ((upperLobeOfPos P ρ x hvert hi hesign).len - 1)
      = nextCrossing P ρ x i := by
  show arcPos i (nextCrossDist P ρ x i + 1 - 1) = nextCrossing P ρ x i
  rw [show nextCrossDist P ρ x i + 1 - 1 = nextCrossDist P ρ x i from by omega,
    arcPos_nextCrossDist]

/-- **`lowerLobeOfNeg`.**  Mirror of `upperLobeOfPos`: a line crossing `i` with `eSign = −1`
produces a `LowerLobe`. -/
def lowerLobeOfNeg (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) (hesign : eSign P ρ i = -1) :
    LowerLobe P ρ x where
  start := i
  len := nextCrossDist P ρ x i + 1
  len_pos := Nat.succ_pos _
  cross_first := by
    simpa using (mem_lineCrossingEdges_iff P ρ x i).mp hi
  cross_last := by
    rw [show nextCrossDist P ρ x i + 1 - 1 = nextCrossDist P ρ x i from by omega,
      arcPos_nextCrossDist]
    exact nextCrossing_span P ρ x hvert hi
  interior_neg := by
    intro k hk0 hk
    have hkle : k ≤ nextCrossDist P ρ x i := by omega
    have h1 := sideAt_one_neg_of_eSign_neg_one P ρ x hvert hi hesign
    exact side_neg_between_next P ρ x hvert hi h1 k hk0 hkle

/-- The last walk vertex of `lowerLobeOfNeg` is the start vertex of `nextCrossing i`. -/
lemma lowerLobeOfNeg_last (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) (hesign : eSign P ρ i = -1) :
    arcPos (lowerLobeOfNeg P ρ x hvert hi hesign).start
      ((lowerLobeOfNeg P ρ x hvert hi hesign).len - 1)
      = nextCrossing P ρ x i := by
  show arcPos i (nextCrossDist P ρ x i + 1 - 1) = nextCrossing P ρ x i
  rw [show nextCrossDist P ρ x i + 1 - 1 = nextCrossDist P ρ x i from by omega,
    arcPos_nextCrossDist]

/-- **`upperLobe_signs`.**  For an `eSign = 1` crossing `i`: the first foot `i` has `eSign = 1`,
and the last foot `nextCrossing i` has `eSign = −1`.  The run is positive through the last edge's
START vertex (`side_pos_between_next` at `k = nextCrossDist`), and the last edge crosses, so its
NEXT vertex is negative ⇒ `eSign = −1`. -/
lemma upperLobe_signs (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) (hesign : eSign P ρ i = 1) :
    eSign P ρ i = 1 ∧ eSign P ρ (nextCrossing P ρ x i) = -1 := by
  refine ⟨hesign, ?_⟩
  -- the last edge's start vertex is `arcPos i nextCrossDist`, which is positive (run).
  have hlaststart_pos : 0 < side ρ.r x (P.q (nextCrossing P ρ x i)) := by
    have h1 := sideAt_one_pos_of_eSign_one P ρ x hvert hi hesign
    have hpos := side_pos_between_next P ρ x hvert hi h1 (nextCrossDist P ρ x i)
      (nextCrossDist_pos P ρ x hvert hi) le_rfl
    -- `sideAt i nextCrossDist = side (P.q (nextCrossing i))`.
    unfold sideAt at hpos
    rw [arcPos_nextCrossDist] at hpos
    exact hpos
  have hsp := nextCrossing_span P ρ x hvert hi
  exact (eSign_eq_neg_one_iff_start_pos P ρ x (nextCrossing P ρ x i)
    (hvert _) (hvert _) hsp).mpr hlaststart_pos

/-- **`lowerLobe_signs`.**  For an `eSign = −1` crossing `i`: the first foot has `eSign = −1`,
and the last foot `nextCrossing i` has `eSign = 1`. -/
lemma lowerLobe_signs (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) (hesign : eSign P ρ i = -1) :
    eSign P ρ i = -1 ∧ eSign P ρ (nextCrossing P ρ x i) = 1 := by
  refine ⟨hesign, ?_⟩
  have hlaststart_neg : side ρ.r x (P.q (nextCrossing P ρ x i)) < 0 := by
    have h1 := sideAt_one_neg_of_eSign_neg_one P ρ x hvert hi hesign
    have hneg := side_neg_between_next P ρ x hvert hi h1 (nextCrossDist P ρ x i)
      (nextCrossDist_pos P ρ x hvert hi) le_rfl
    unfold sideAt at hneg
    rw [arcPos_nextCrossDist] at hneg
    exact hneg
  have hsp := nextCrossing_span P ρ x hvert hi
  exact (eSign_eq_one_iff_start_neg P ρ x (nextCrossing P ρ x i)
    (hvert _) (hvert _) hsp).mpr hlaststart_neg

/-! ## §E. Brick 5 — the boundary crossing cycle

`boundaryCrossingList` enumerates the line crossings sorted by the cyclic offset from a fixed
base crossing `i₀`.  `boundarySucc` is the next-crossing map; it flips `eSign` and connects all
crossings cyclically. -/

/-- The `eSign` sign-flip of `boundarySucc`/`nextCrossing`: for a line crossing `i`,
`eSign (nextCrossing i) = − eSign i`.  (From `upperLobe_signs` / `lowerLobe_signs` by the two
cases of `eSign i = ±1`.) -/
lemma eSign_nextCrossing (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    eSign P ρ (nextCrossing P ρ x i) = - eSign P ρ i := by
  rcases eSign_mem P ρ i with h | h
  · rw [h, (upperLobe_signs P ρ x hvert hi h).2]
  · rw [h, (lowerLobe_signs P ρ x hvert hi h).2]; norm_num

/-- **`cyclicSteps i₀ ·` is injective on `Fin n`** (with the basepoint fixed): two indices with
the same cyclic offset from `i₀` are equal.  (`arcPos i₀ (cyclicSteps i₀ a) = a` retracts.) -/
lemma cyclicSteps_injOn (i₀ : Fin n) :
    ∀ a b : Fin n, cyclicSteps i₀ a = cyclicSteps i₀ b → a = b := by
  intro a b hab
  -- `a.val = (i₀.val + cyclicSteps i₀ a) % n`, similarly for `b`; equal offsets ⇒ equal vals.
  have key : ∀ c : Fin n, c.val = (i₀.val + cyclicSteps i₀ c) % n := by
    intro c
    unfold cyclicSteps
    by_cases hle : i₀.val ≤ c.val
    · rw [if_pos hle]
      have : i₀.val + (c.val - i₀.val) = c.val := by omega
      rw [this, Nat.mod_eq_of_lt c.isLt]
    · rw [if_neg hle]
      have hcv : c.val < i₀.val := by omega
      have : i₀.val + (n - i₀.val + c.val) = n + c.val := by
        have := i₀.isLt; omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt c.isLt]
  apply Fin.ext
  rw [key a, key b, hab]

/-- The cast key `cyclicSteps i₀ · : ℝ` is injective on `Fin n` (the form `exists_sorted_enum`
consumes). -/
lemma cyclicSteps_cast_injOn (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i₀ : Fin n) :
    ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      (cyclicSteps i₀ a : ℝ) = (cyclicSteps i₀ b : ℝ) → a = b := by
  intro a _ b _ h
  exact cyclicSteps_injOn i₀ a b (by exact_mod_cast h)

/-- **The boundary crossing list.**  The line crossings, enumerated by ASCENDING cyclic offset
from a chosen base crossing `i₀` (`exists_sorted_enum` on the key `cyclicSteps i₀ ·`, injective
on the crossings). -/
def boundaryCrossingList (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i₀ : Fin n) :
    List (Fin n) := by
  classical
  exact (exists_sorted_enum (fun a => (cyclicSteps i₀ a : ℝ)) (LineCrossingEdges P ρ x)
    (cyclicSteps_cast_injOn P ρ x i₀)).choose

lemma boundaryCrossingList_spec (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i₀ : Fin n) :
    (boundaryCrossingList P ρ x i₀).Nodup ∧
      (∀ a, a ∈ boundaryCrossingList P ρ x i₀ ↔ a ∈ LineCrossingEdges P ρ x) ∧
      (boundaryCrossingList P ρ x i₀).Pairwise
        (fun a b => (cyclicSteps i₀ a : ℝ) < (cyclicSteps i₀ b : ℝ)) := by
  classical
  exact (exists_sorted_enum (fun a => (cyclicSteps i₀ a : ℝ)) (LineCrossingEdges P ρ x)
    (cyclicSteps_cast_injOn P ρ x i₀)).choose_spec

lemma boundaryCrossingList_nodup (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i₀ : Fin n) : (boundaryCrossingList P ρ x i₀).Nodup :=
  (boundaryCrossingList_spec P ρ x i₀).1

lemma mem_boundaryCrossingList (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (i₀ : Fin n) (a : Fin n) :
    a ∈ boundaryCrossingList P ρ x i₀ ↔ a ∈ LineCrossingEdges P ρ x :=
  (boundaryCrossingList_spec P ρ x i₀).2.1 a

/-- **`boundarySucc`.**  The boundary-successor map on line crossings: `nextCrossing` when `i` is
a crossing, identity (`i`) otherwise — total. -/
def boundarySucc (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) (i : Fin n) : Fin n := by
  classical
  exact if i ∈ LineCrossingEdges P ρ x then nextCrossing P ρ x i else i

/-- For a crossing, `boundarySucc = nextCrossing`. -/
lemma boundarySucc_eq_nextCrossing (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    {i : Fin n} (hi : i ∈ LineCrossingEdges P ρ x) :
    boundarySucc P ρ x i = nextCrossing P ρ x i := by
  unfold boundarySucc; rw [if_pos hi]

/-- **`boundarySucc_mem`.**  The boundary successor of a crossing is a crossing. -/
lemma boundarySucc_mem (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    boundarySucc P ρ x i ∈ LineCrossingEdges P ρ x := by
  rw [boundarySucc_eq_nextCrossing P ρ x hi]
  exact nextCrossing_mem P ρ x hvert hi

/-- **`boundarySucc_sign_flip`.**  `eSign (boundarySucc i) = − eSign i` for crossings. -/
lemma boundarySucc_sign_flip (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) :
    eSign P ρ (boundarySucc P ρ x i) = - eSign P ρ i := by
  rw [boundarySucc_eq_nextCrossing P ρ x hi]
  exact eSign_nextCrossing P ρ x hvert hi

/-- `boundarySucc` iterated stays in the crossings. -/
lemma boundarySucc_iterate_mem (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {i : Fin n}
    (hi : i ∈ LineCrossingEdges P ρ x) (m : ℕ) :
    (boundarySucc P ρ x)^[m] i ∈ LineCrossingEdges P ρ x := by
  induction m with
  | zero => simpa using hi
  | succ p ih =>
    rw [Function.iterate_succ_apply']
    exact boundarySucc_mem P ρ x hvert ih

/-! ### Cyclic connectedness of `boundarySucc`

The crossings on the cyclic walk are exactly the finite set `LineCrossingEdges`.  Iterating
`boundarySucc` from any crossing `i` traverses ALL crossings: the offset `cyclicSteps i₀ ·`
strictly increases along `nextCrossing` until it wraps, and the finite crossing set is exhausted
in `card` steps.  We package the reachability statement abstractly via the orbit of
`boundarySucc` on the finite crossing set. -/

/-- The crossing set as a finite type carrier (subtype). -/
def CrossSet (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) :=
  {i : Fin n // i ∈ LineCrossingEdges P ρ x}

instance (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) :
    Fintype (CrossSet P ρ x) := by
  classical
  unfold CrossSet
  infer_instance

/-- `boundarySucc` as an endo-map on the crossing subtype. -/
def boundarySuccSub (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) :
    CrossSet P ρ x → CrossSet P ρ x :=
  fun i => ⟨boundarySucc P ρ x i.1, boundarySucc_mem P ρ x hvert i.2⟩

/-- The subtype iterate commutes with the underlying `boundarySucc` iterate. -/
lemma boundarySuccSub_iterate_val (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) (p : ℕ) (a : CrossSet P ρ x) :
    ((boundarySuccSub P ρ x hvert)^[p] a).1 = (boundarySucc P ρ x)^[p] a.1 := by
  induction p generalizing a with
  | zero => simp
  | succ q ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ih (boundarySuccSub P ρ x hvert a)]
    rfl

/-- **Finite-orbit return.**  An injective self-map of the finite crossing subtype has, from any
point, a strictly positive iterate returning to it (its order divides the carrier size).  This is
the pigeonhole half of the cycle structure — pure finite combinatorics, no geometry. -/
lemma boundarySuccSub_returns (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (hinj : Function.Injective (boundarySuccSub P ρ x hvert)) (a : CrossSet P ρ x) :
    ∃ p : ℕ, 0 < p ∧ (boundarySuccSub P ρ x hvert)^[p] a = a := by
  classical
  set f := boundarySuccSub P ρ x hvert with hf
  -- pigeonhole: `m ↦ f^[m] a` over `Fin (card+1)` cannot be injective, giving a repeat.
  have hfin : ¬ Function.Injective (fun m : Fin (Fintype.card (CrossSet P ρ x) + 1) =>
      f^[m.val] a) := by
    intro hinjm
    have hcard := Fintype.card_le_of_injective _ hinjm
    simp [Fintype.card_fin] at hcard
  rw [Function.not_injective_iff] at hfin
  obtain ⟨s, t, hst, hne⟩ := hfin
  -- WLOG `s < t`; cancel the common prefix `f^[s]` using injectivity of `f`.
  have hiter_inj : ∀ r : ℕ, Function.Injective (f^[r]) := by
    intro r
    exact Function.Injective.iterate hinj r
  rcases Nat.lt_or_ge s.val t.val with hlt | hge
  · refine ⟨t.val - s.val, by omega, ?_⟩
    have : f^[s.val] (f^[t.val - s.val] a) = f^[s.val] a := by
      rw [← Function.iterate_add_apply]
      rw [show s.val + (t.val - s.val) = t.val from by omega]
      exact hst.symm
    exact hiter_inj s.val this
  · have hlt' : t.val < s.val := by
      rcases Nat.lt_or_ge t.val s.val with h | h
      · exact h
      · exact absurd (Fin.ext (le_antisymm hge h)) (Ne.symm hne)
    refine ⟨s.val - t.val, by omega, ?_⟩
    have : f^[t.val] (f^[s.val - t.val] a) = f^[t.val] a := by
      rw [← Function.iterate_add_apply]
      rw [show t.val + (s.val - t.val) = s.val from by omega]
      exact hst
    exact hiter_inj t.val this

/-- **`boundarySucc_cycle_connected`.**  Any two crossings are connected by iterating
`boundarySucc`: for crossings `i, j` there is some `k` with `(boundarySucc)^[k] i = j`.

This is the honest combinatorial conclusion from TWO inputs, both pure finite combinatorics
EXCEPT for the single named geometric input:

* `hinj` — `nextCrossing` is injective on the crossing subtype (`boundarySuccSub` injective).  On
  a finite carrier this upgrades to a permutation; `boundarySuccSub_returns` then supplies the
  cycle return.  Injectivity of the boundary successor is the geometric noninterleaving content
  NOT in scope for this file, so it is taken as a named hypothesis.
* `hcover` — the orbit of ONE fixed crossing `i₀` covers ALL crossings (the SINGLE-cycle
  property).  This too is downstream of noninterleaving; it is taken as a named hypothesis for
  one fixed basepoint only.

From these two the *symmetric* `∀ i j` connectedness is genuine combinatorics: write
`i = succ^[a] i₀`, `j = succ^[b] i₀`; go `i → i₀` by completing the period (`p − a mod p` steps,
using the return `succ^[p] = id`), then `i₀ → j` in `b` steps.  No tautology: `hcover` is asserted
only at the single fixed `i₀`, not at every point. -/
theorem boundarySucc_cycle_connected (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (hinj : Function.Injective (boundarySuccSub P ρ x hvert))
    {i₀ : Fin n} (hi₀ : i₀ ∈ LineCrossingEdges P ρ x)
    (hcover : ∀ b : CrossSet P ρ x, ∃ m : ℕ,
        (boundarySuccSub P ρ x hvert)^[m] ⟨i₀, hi₀⟩ = b)
    {i j : Fin n} (hi : i ∈ LineCrossingEdges P ρ x) (hj : j ∈ LineCrossingEdges P ρ x) :
    ∃ k : ℕ, (boundarySucc P ρ x)^[k] i = j := by
  classical
  set a₀ : CrossSet P ρ x := ⟨i₀, hi₀⟩ with ha₀
  -- `i` and `j` are both reached from `i₀`.
  obtain ⟨a, ha⟩ := hcover ⟨i, hi⟩
  obtain ⟨b, hb⟩ := hcover ⟨j, hj⟩
  -- the orbit returns to `a₀` after a positive period `p`.
  obtain ⟨p, hp0, hp⟩ := boundarySuccSub_returns P ρ x hvert hinj a₀
  -- from `i = succ^[a] a₀`, applying `succ^[p*a]` more times returns to `a₀` (period closes),
  -- so `succ^[p*(a+1) - a]` sends `i` to `a₀`; then `succ^[b]` sends `a₀` to `j`.
  -- Concretely: succ^[(p - a % p) ...]. Use `succ^[p * N] a₀ = a₀` for any N, with N large.
  have hperiod : ∀ N : ℕ, (boundarySuccSub P ρ x hvert)^[p * N] a₀ = a₀ := by
    intro N
    induction N with
    | zero => simp
    | succ M ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, hp, ih]
  -- choose `N` with `p*N ≥ a`; then `succ^[p*N - a] i = a₀`.
  refine ⟨(p * (a + 1) - a) + b, ?_⟩
  have hNa : a ≤ p * (a + 1) := by nlinarith [hp0, Nat.one_le_iff_ne_zero.mpr (by omega : p ≠ 0)]
  -- `succ^[(p*(a+1)-a)] i = succ^[(p*(a+1)-a)] (succ^[a] a₀).val = (succ^[p*(a+1)] a₀).val = i₀`.
  have hi_eq : (boundarySuccSub P ρ x hvert)^[a] a₀ = ⟨i, hi⟩ := ha
  have hstep1 : (boundarySuccSub P ρ x hvert)^[p * (a + 1) - a] ⟨i, hi⟩ = a₀ := by
    rw [← hi_eq, ← Function.iterate_add_apply]
    rw [show (p * (a + 1) - a) + a = p * (a + 1) from by omega]
    exact hperiod (a + 1)
  have hstep2 : (boundarySuccSub P ρ x hvert)^[b] a₀ = ⟨j, hj⟩ := hb
  -- chain in the subtype, then push to the underlying map.
  have hchain : (boundarySuccSub P ρ x hvert)^[(p * (a + 1) - a) + b] ⟨i, hi⟩ = ⟨j, hj⟩ := by
    rw [Nat.add_comm (p * (a + 1) - a) b, Function.iterate_add_apply, hstep1, hstep2]
  have hval := congrArg Subtype.val hchain
  rw [boundarySuccSub_iterate_val P ρ x hvert] at hval
  simpa using hval

end

end ProofsInTheBook.ZinanCh36LobeWiring

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.cyclicNext_arcPos
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.lineCrossing_exists_other
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.crossingDists_nonempty
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.nextCrossDist_pos
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.nextCrossing_mem
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.nextCrossing_ne
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.no_crossing_before_next
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.noSpan_preserves_pos
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.noSpan_preserves_neg
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.side_pos_between_next
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.side_neg_between_next
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.eSign_eq_one_of_neg_pos
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.eSign_eq_neg_one_of_pos_neg
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.eSign_eq_one_iff_start_neg
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.eSign_eq_neg_one_iff_start_pos
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.upperLobeOfPos
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.upperLobeOfPos_last
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.lowerLobeOfNeg
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.lowerLobeOfNeg_last
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.upperLobe_signs
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.lowerLobe_signs
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.eSign_nextCrossing
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.cyclicSteps_injOn
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.boundaryCrossingList_spec
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.boundarySucc_mem
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.boundarySucc_sign_flip
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.boundarySucc_iterate_mem
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.boundarySuccSub_returns
#print axioms ProofsInTheBook.ZinanCh36LobeWiring.boundarySucc_cycle_connected
