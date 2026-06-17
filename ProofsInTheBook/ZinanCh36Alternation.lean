import ProofsInTheBook.ZinanCh36NonInterleave
import ProofsInTheBook.ZinanCh36RankParity

/-!
# `ZinanCh36Alternation` — the FINAL Ch36 wiring: compose the landed components into the
  full-line `RayCrossingAlternation` pipeline and the chapter-kernel consumers.

This file is the assembly stage of the Chapter-36 lobe-pairing programme
(`HANDOFF/design-rounds/ch36-lobe-pairing-comb.md` §7+§10).  Every mathematical brick is
already landed clean-3 on HEAD; here we *wire* them:

* `ZinanCh36NonInterleave` — `upper_lobes_not_interleave` / `lower_lobes_not_interleave`
  (the geometric fixed-sweep noninterleaving, **ascending-foot** form).
* `ZinanCh36RankParity` — `alt_of_twoSide_noncrossing_cycle` (the rank-parity master theorem:
  one ν-cycle + sign-flip + two-sided `¬ TauInterleaves` ⟹ `Alt` in τ-sorted order).
* `ZinanCh36LobeWiring` — `boundarySucc`, `boundarySucc_mem`, `boundarySucc_sign_flip`,
  `boundarySucc_cycle_connected`, `upperLobeOfPos` / `lowerLobeOfNeg` + endpoint lemmas.
* `ZinanCh36RayDichotomy` / `ZinanCh36Theta` — `crossTau_injOn_lineCrossingEdges`,
  `rayWindingDichotomy_of_fullLineAlternation`, `rayCrossingAlternation_of_fullLineAlternation`,
  `triangle_rayCrossingAlternation`, `rayCrossingAlternation_of_ray_dichotomy`.

## What is delivered here

* **Brick 1 (partial wiring).**  `upper_noninterleaving_ascending` / `lower_noninterleaving_ascending`:
  for two same-sign crossings whose lobe chains have **disjoint carriers**, the boundary-successor
  chord pair `(a, boundarySucc a)`, `(b, boundarySucc b)` does NOT `TauInterleaves` *in the
  ascending sub-configuration* — wired directly to `upper_lobes_not_interleave` by matching the lobe
  feet to `crossTau a` / `crossTau (boundarySucc a)` via `upperLobeOfPos_last`.

* **Brick 2 (`fullLineCrossingAlternation`, CONDITIONAL).**  `fullLineCrossingAlternation_of_geom`:
  instantiating `alt_of_twoSide_noncrossing_cycle` at `S := LineCrossingEdges`, `τ := crossTau`,
  `σ := eSign`, `ν := boundarySucc`, with the landed `hτinj` / `hνmem` / `hpm` / `hflip`, the
  cycle hypothesis from `boundarySucc_cycle_connected`, and the two `¬ TauInterleaves` clauses
  supplied as explicit named geometric residues.

* **Brick 3 (CONDITIONAL).**  `rayWindingDichotomy_of_geom` / `rayCrossingAlternation_of_geom`:
  feed `fullLineCrossingAlternation_of_geom` through the landed conditional pipeline.

* **Brick 3' (UNCONDITIONAL triangle).**  `triangle_rayCrossingAlternation` re-exported, and the
  unconditional chapter bridge specialised to `n = 3`.

* **Brick 4 (CHAPTER BRIDGES).**  `windCross_mem_of_rayCrossingAlternation` (unconditional, from
  any `RayCrossingAlternation`): `windCross ∈ {0, 1, -1}`; and the triangle end-to-end bound.

## The residual geometric inputs (honestly named, NOT smuggled)

`alt_of_twoSide_noncrossing_cycle`'s `hcycle` is discharged by `boundarySucc_cycle_connected`,
which itself takes TWO geometric residues left out of scope by `ZinanCh36LobeWiring`:
`hinj` (boundarySucc injective on the crossing subtype) and `hcover` (the orbit of one fixed
crossing covers all crossings — the single-cycle property).  Its `hposNI`/`hnegNI` ask for
`¬ TauInterleaves` for *every* same-sign chord pair.  The landed `upper_lobes_not_interleave`
discharges this only for the **ascending** sub-configuration (`crossTau start < crossTau lastEdge`
for both lobes); the foot-order-symmetric form (an upper chord's left foot need not have a fixed
sign — see the rank-parity design note) and carrier-disjointness are NOT in the landed substrate.
We therefore take the four `¬ TauInterleaves` / injectivity / cover facts as explicit hypotheses of
the conditional theorems, and reduce the ascending part of them to the landed geometry in Brick 1.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

namespace ProofsInTheBook.ZinanCh36Alternation

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonLocalConstancy
open ProofsInTheBook.PolygonWinding (windCross)
open ProofsInTheBook.PolygonWindingExterior (eSign)
open ProofsInTheBook.PolygonWindingBound
  (Alt RayCrossingAlternation eSign_mem windCross_mem_of_alternation)
open ProofsInTheBook.ZinanCh36Comb (TauInterleaves)
open ProofsInTheBook.ZinanCh36RankParity (alt_of_twoSide_noncrossing_cycle)
open ProofsInTheBook.ZinanCh36LobeChain (lobeChain lobeLastEdge)
open ProofsInTheBook.ZinanCh36LobeWiring
  (boundarySucc boundarySucc_eq_nextCrossing nextCrossing boundarySucc_mem
    boundarySucc_sign_flip boundarySucc_cycle_connected boundarySuccSub CrossSet
    upperLobeOfPos upperLobeOfPos_last lowerLobeOfNeg lowerLobeOfNeg_last)
open ProofsInTheBook.ZinanCh36NonInterleave
  (upper_lobes_not_interleave lower_lobes_not_interleave lobeChainL lobeLastEdgeL)
open ProofsInTheBook.ZinanCh36Theta
  (LineCrossingEdges mem_lineCrossingEdges_iff crossTau_injOn_lineCrossingEdges exists_sorted_enum
    rayWindingDichotomy_of_fullLineAlternation rayCrossingAlternation_of_fullLineAlternation
    triangle_rayCrossingAlternation rayCrossingAlternation_of_ray_dichotomy)
open scoped RealInnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1600000

variable {n : ℕ}

/-! ## §1. Brick 1 — the ascending noninterleaving wiring

`upperLobeOfPos a` has `start = a` and `lobeLastEdge = nextCrossing a = boundarySucc a` (for a
crossing `a`).  So its two feet are `crossTau a` and `crossTau (boundarySucc a)`.  When two `+1`
crossings `a, b` have disjoint lobe carriers, `upper_lobes_not_interleave` rules out the
ascending interleaving `crossTau a < crossTau b < crossTau (boundarySucc a) < crossTau (boundarySucc b)`. -/

variable {P : StrictSimplePolygon n} {ρ : RayDirection P} {x : Pt}

/-- `lobeLastEdge (upperLobeOfPos … a …) = boundarySucc a` (for a crossing `a`). -/
lemma lobeLastEdge_upperLobeOfPos
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hσa : eSign P ρ a = 1) :
    lobeLastEdge (upperLobeOfPos P ρ x hvert ha hσa) = boundarySucc P ρ x a := by
  rw [boundarySucc_eq_nextCrossing P ρ x ha]
  -- `lobeLastEdge L = arcPos L.start (L.len - 1)`, which `upperLobeOfPos_last` evaluates.
  exact upperLobeOfPos_last P ρ x hvert ha hσa

/-- `lobeLastEdgeL (lowerLobeOfNeg … a …) = boundarySucc a` (for a crossing `a`). -/
lemma lobeLastEdgeL_lowerLobeOfNeg
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hσa : eSign P ρ a = -1) :
    lobeLastEdgeL (lowerLobeOfNeg P ρ x hvert ha hσa) = boundarySucc P ρ x a := by
  rw [boundarySucc_eq_nextCrossing P ρ x ha]
  exact lowerLobeOfNeg_last P ρ x hvert ha hσa

/-- **Brick 1 (upper, ascending).**  Two `+1` crossings `a ≠ b` with disjoint lobe carriers do not
interleave in the ascending order `crossTau a < crossTau b < crossTau (boundarySucc a) < crossTau
(boundarySucc b)`.  Direct wiring to `upper_lobes_not_interleave`. -/
theorem upper_noninterleaving_ascending
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a b : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hb : b ∈ LineCrossingEdges P ρ x)
    (hσa : eSign P ρ a = 1) (hσb : eSign P ρ b = 1)
    (hdisj : Disjoint (lobeChain (upperLobeOfPos P ρ x hvert ha hσa)).carrier
                      (lobeChain (upperLobeOfPos P ρ x hvert hb hσb)).carrier)
    (hasc : crossTau P ρ x a < crossTau P ρ x b ∧
            crossTau P ρ x b < crossTau P ρ x (boundarySucc P ρ x a) ∧
            crossTau P ρ x (boundarySucc P ρ x a) < crossTau P ρ x (boundarySucc P ρ x b)) :
    False := by
  set X := upperLobeOfPos P ρ x hvert ha hσa with hXdef
  set Y := upperLobeOfPos P ρ x hvert hb hσb with hYdef
  -- X.start = a, Y.start = b, lobeLastEdge X = boundarySucc a, lobeLastEdge Y = boundarySucc b.
  have hXs : X.start = a := rfl
  have hYs : Y.start = b := rfl
  have hXl : lobeLastEdge X = boundarySucc P ρ x a := lobeLastEdge_upperLobeOfPos hvert ha hσa
  have hYl : lobeLastEdge Y = boundarySucc P ρ x b := lobeLastEdge_upperLobeOfPos hvert hb hσb
  apply upper_lobes_not_interleave X Y hdisj
  rw [hXs, hYs, hXl, hYl]
  exact hasc

/-- **Brick 1 (lower, ascending).**  Mirror for two `-1` crossings. -/
theorem lower_noninterleaving_ascending
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0) {a b : Fin n}
    (ha : a ∈ LineCrossingEdges P ρ x) (hb : b ∈ LineCrossingEdges P ρ x)
    (hσa : eSign P ρ a = -1) (hσb : eSign P ρ b = -1)
    (hdisj : Disjoint (lobeChainL (lowerLobeOfNeg P ρ x hvert ha hσa)).carrier
                      (lobeChainL (lowerLobeOfNeg P ρ x hvert hb hσb)).carrier)
    (hasc : crossTau P ρ x a < crossTau P ρ x b ∧
            crossTau P ρ x b < crossTau P ρ x (boundarySucc P ρ x a) ∧
            crossTau P ρ x (boundarySucc P ρ x a) < crossTau P ρ x (boundarySucc P ρ x b)) :
    False := by
  set X := lowerLobeOfNeg P ρ x hvert ha hσa with hXdef
  set Y := lowerLobeOfNeg P ρ x hvert hb hσb with hYdef
  have hXs : X.start = a := rfl
  have hYs : Y.start = b := rfl
  have hXl : lobeLastEdgeL X = boundarySucc P ρ x a := lobeLastEdgeL_lowerLobeOfNeg hvert ha hσa
  have hYl : lobeLastEdgeL Y = boundarySucc P ρ x b := lobeLastEdgeL_lowerLobeOfNeg hvert hb hσb
  apply lower_lobes_not_interleave X Y hdisj
  rw [hXs, hYs, hXl, hYl]
  exact hasc

/-! ## §2. Brick 2 — `fullLineCrossingAlternation` (CONDITIONAL on the geometric residues)

`alt_of_twoSide_noncrossing_cycle` instantiated at `S := LineCrossingEdges`, `τ := crossTau`,
`σ := eSign`, `ν := boundarySucc`.  The landed hypotheses (`hτinj` from
`crossTau_injOn_lineCrossingEdges`, `hνmem` from `boundarySucc_mem`, `hpm` from `eSign_mem`,
`hflip` from `boundarySucc_sign_flip`) are discharged here; `hcycle` is reduced to the geometric
`hinj`/`hcover` of `boundarySucc_cycle_connected`; the two `¬ TauInterleaves` clauses are taken as
named geometric residues. -/

/-- **`fullLineCrossingAlternation`, CONDITIONAL.**  Under the genericity guard `hvert` and the
named geometric residues — `hinj`/`hcover` (boundarySucc is a single cycle on the crossings) and
`hposNI`/`hnegNI` (same-sign boundary chords never τ-interleave) — the line-crossing edges, sorted
by `crossTau`, have an alternating `eSign` image.  This is exactly the `Halt` hypothesis the landed
dichotomy pipeline consumes. -/
theorem fullLineCrossingAlternation_of_geom
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (hinj : Function.Injective (boundarySuccSub P ρ x hvert))
    {i₀ : Fin n} (hi₀ : i₀ ∈ LineCrossingEdges P ρ x)
    (hcover : ∀ b : CrossSet P ρ x, ∃ m : ℕ,
        (boundarySuccSub P ρ x hvert)^[m] ⟨i₀, hi₀⟩ = b)
    (hposNI : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      a ≠ b → eSign P ρ a = 1 → eSign P ρ b = 1 →
      ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b))
    (hnegNI : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      a ≠ b → eSign P ρ a = -1 → eSign P ρ b = -1 →
      ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b)) :
    ∃ L : List (Fin n), L.Nodup ∧
      (∀ i, i ∈ L ↔ i ∈ LineCrossingEdges P ρ x) ∧
      L.Pairwise (fun a b => crossTau P ρ x a < crossTau P ρ x b) ∧
      Alt (L.map (eSign P ρ)) := by
  classical
  -- the sorted enumeration (Brick 5, landed) supplies the list.
  have hτinj : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      crossTau P ρ x a = crossTau P ρ x b → a = b := by
    intro a ha b hb hEq
    by_contra hne
    exact crossTau_injOn_lineCrossingEdges P ρ x hvert ha hb hne hEq
  obtain ⟨L, hnd, hmem, hsort⟩ :=
    exists_sorted_enum (crossTau P ρ x) (LineCrossingEdges P ρ x) hτinj
  refine ⟨L, hnd, hmem, hsort, ?_⟩
  -- the master theorem closes `Alt` from the cycle data.
  have hνmem : ∀ a ∈ LineCrossingEdges P ρ x, boundarySucc P ρ x a ∈ LineCrossingEdges P ρ x :=
    fun a ha => boundarySucc_mem P ρ x hvert ha
  have hpm : ∀ a ∈ LineCrossingEdges P ρ x, eSign P ρ a = 1 ∨ eSign P ρ a = -1 :=
    fun a _ => eSign_mem P ρ a
  have hflip : ∀ a ∈ LineCrossingEdges P ρ x,
      eSign P ρ (boundarySucc P ρ x a) = - eSign P ρ a :=
    fun a ha => boundarySucc_sign_flip P ρ x hvert ha
  have hcycle : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      ∃ k : ℕ, (boundarySucc P ρ x)^[k] a = b :=
    fun a ha b hb => boundarySucc_cycle_connected P ρ x hvert hinj hi₀ hcover ha hb
  exact alt_of_twoSide_noncrossing_cycle hτinj hνmem hcycle hpm hflip hposNI hnegNI hnd hmem hsort

/-! ## §3. Brick 3 — the CONDITIONAL ray dichotomy / `RayCrossingAlternation`

Feed `fullLineCrossingAlternation_of_geom` through the landed conditional pipeline
(`rayWindingDichotomy_of_fullLineAlternation` / `rayCrossingAlternation_of_fullLineAlternation`). -/

/-- **Brick 3 (CONDITIONAL): the ray winding dichotomy.**  At a generic off-boundary point, under
the geometric residues, the signed winding takes at most the two values `{0, s}` along the forward
ray. -/
theorem rayWindingDichotomy_of_geom
    (hoff : ¬ OnBoundary P x)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (hinj : Function.Injective (boundarySuccSub P ρ x hvert))
    {i₀ : Fin n} (hi₀ : i₀ ∈ LineCrossingEdges P ρ x)
    (hcover : ∀ b : CrossSet P ρ x, ∃ m : ℕ,
        (boundarySuccSub P ρ x hvert)^[m] ⟨i₀, hi₀⟩ = b)
    (hposNI : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      a ≠ b → eSign P ρ a = 1 → eSign P ρ b = 1 →
      ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b))
    (hnegNI : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      a ≠ b → eSign P ρ a = -1 → eSign P ρ b = -1 →
      ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b)) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      ∀ c : ℝ, 0 ≤ c → ¬ OnBoundary P (x + c • ρ.r) →
        windCross P ρ (x + c • ρ.r) = 0 ∨ windCross P ρ (x + c • ρ.r) = s :=
  rayWindingDichotomy_of_fullLineAlternation P ρ x hoff hvert
    (fullLineCrossingAlternation_of_geom hvert hinj hi₀ hcover hposNI hnegNI)

/-- **Brick 3 (CONDITIONAL): the `RayCrossingAlternation` Jordan kernel.**  At a generic
off-boundary point, under the geometric residues, the forward-ray crossing kernel holds. -/
theorem rayCrossingAlternation_of_geom
    (hoff : ¬ OnBoundary P x)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (hinj : Function.Injective (boundarySuccSub P ρ x hvert))
    {i₀ : Fin n} (hi₀ : i₀ ∈ LineCrossingEdges P ρ x)
    (hcover : ∀ b : CrossSet P ρ x, ∃ m : ℕ,
        (boundarySuccSub P ρ x hvert)^[m] ⟨i₀, hi₀⟩ = b)
    (hposNI : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      a ≠ b → eSign P ρ a = 1 → eSign P ρ b = 1 →
      ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b))
    (hnegNI : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      a ≠ b → eSign P ρ a = -1 → eSign P ρ b = -1 →
      ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b)) :
    RayCrossingAlternation P ρ x :=
  rayCrossingAlternation_of_fullLineAlternation P ρ x hoff hvert
    (fullLineCrossingAlternation_of_geom hvert hinj hi₀ hcover hposNI hnegNI)

/-! ## §4. Brick 3' — the UNCONDITIONAL triangle base case (re-exported) -/

/-- **The triangle Jordan kernel, UNCONDITIONAL** (re-export of `triangle_rayCrossingAlternation`).
For a strict simple triangle, `RayCrossingAlternation` holds at every generic off-boundary point
with NO external input. -/
theorem triangle_rayCrossingAlternation_final (Q : StrictSimplePolygon 3) (ρ : RayDirection Q)
    (x : Pt) (hoff : ¬ OnBoundary Q x)
    (hvert : ∀ k : Fin 3, side ρ.r x (Q.q k) ≠ 0) :
    RayCrossingAlternation Q ρ x :=
  triangle_rayCrossingAlternation Q ρ x hoff hvert

/-! ## §5. Brick 4 — THE CHAPTER BRIDGES

`windCross_mem_of_alternation` (landed, UNCONDITIONAL given the kernel) is the immediate consumer:
`RayCrossingAlternation ⟹ windCross ∈ {0, 1, -1}`.  We deliver the bridge from any
`RayCrossingAlternation` and its unconditional triangle instance. -/

/-- **Chapter bridge (UNCONDITIONAL from the kernel): the winding bound.**  Any point carrying the
`RayCrossingAlternation` kernel has signed winding in `{0, 1, -1}`. -/
theorem windCross_mem_of_rayCrossingAlternation
    (halt : RayCrossingAlternation P ρ x) :
    windCross P ρ x = 0 ∨ windCross P ρ x = 1 ∨ windCross P ρ x = -1 :=
  windCross_mem_of_alternation P ρ halt

/-- **Chapter bridge (UNCONDITIONAL, triangle): the winding bound for a triangle.**  For a strict
simple triangle, every generic off-boundary point has signed winding in `{0, 1, -1}` — the planar
Jordan winding bound with NO external alternation input. -/
theorem triangle_windCross_mem (Q : StrictSimplePolygon 3) (ρ : RayDirection Q) (x : Pt)
    (hoff : ¬ OnBoundary Q x) (hvert : ∀ k : Fin 3, side ρ.r x (Q.q k) ≠ 0) :
    windCross Q ρ x = 0 ∨ windCross Q ρ x = 1 ∨ windCross Q ρ x = -1 :=
  windCross_mem_of_alternation Q ρ (triangle_rayCrossingAlternation Q ρ x hoff hvert)

/-- **Chapter bridge (CONDITIONAL, general `n`): the winding bound from the geometric residues.**
Composing Brick 3 with the landed `windCross_mem_of_alternation`. -/
theorem windCross_mem_of_geom
    (hoff : ¬ OnBoundary P x)
    (hvert : ∀ k : Fin n, side ρ.r x (P.q k) ≠ 0)
    (hinj : Function.Injective (boundarySuccSub P ρ x hvert))
    {i₀ : Fin n} (hi₀ : i₀ ∈ LineCrossingEdges P ρ x)
    (hcover : ∀ b : CrossSet P ρ x, ∃ m : ℕ,
        (boundarySuccSub P ρ x hvert)^[m] ⟨i₀, hi₀⟩ = b)
    (hposNI : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      a ≠ b → eSign P ρ a = 1 → eSign P ρ b = 1 →
      ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b))
    (hnegNI : ∀ a ∈ LineCrossingEdges P ρ x, ∀ b ∈ LineCrossingEdges P ρ x,
      a ≠ b → eSign P ρ a = -1 → eSign P ρ b = -1 →
      ¬ TauInterleaves (crossTau P ρ x) a (boundarySucc P ρ x a) b (boundarySucc P ρ x b)) :
    windCross P ρ x = 0 ∨ windCross P ρ x = 1 ∨ windCross P ρ x = -1 :=
  windCross_mem_of_alternation P ρ
    (rayCrossingAlternation_of_geom hoff hvert hinj hi₀ hcover hposNI hnegNI)

end

/-! ## Axiom audit (clean-3 expected: `propext`, `Classical.choice`, `Quot.sound`) -/

section Audit
open ProofsInTheBook.ZinanCh36Alternation
#print axioms upper_noninterleaving_ascending
#print axioms lower_noninterleaving_ascending
#print axioms fullLineCrossingAlternation_of_geom
#print axioms rayWindingDichotomy_of_geom
#print axioms rayCrossingAlternation_of_geom
#print axioms triangle_rayCrossingAlternation_final
#print axioms windCross_mem_of_rayCrossingAlternation
#print axioms triangle_windCross_mem
#print axioms windCross_mem_of_geom
end Audit

end ProofsInTheBook.ZinanCh36Alternation
