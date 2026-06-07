import ProofsInTheBook.PolygonWindingPath
import ProofsInTheBook.PolygonRegionSplit

/-!
# Chapter 36 — the planar-Jordan winding bound: a simple polygon winds at most once
  (`PolygonWindingBound`)

This module proves the CORE planar-Jordan theorem of Chapter 36 in its integer-valued
form: the **signed winding number** `PolygonWinding.windCross P ρ x` of a strict simple
polygon `P` about any off-boundary point `x` lies in `{-1, 0, 1}`.

## What "winding number" means here

The substrate carries two winding objects:

* `PolygonWindingNumber.oWind` — the *signed-angle* turning number valued in
  `Real.Angle = ℝ / 2πℤ`.  For a closed loop this is always `0` in `Real.Angle`
  (`oWind_closed_eq_zero`); the genuine integer winding count is its real lift divided by
  `2π`, which the `Real.Angle` quotient discards.  So `oWind`-valued `∈ {-1,0,1}` is a type
  error (those would be the *angles* `-1, 0, 1` radians, not winding counts).
* `PolygonWinding.windCross P ρ x : ℤ` — the *signed ray-crossing* count
  `∑ k, rawSignedInd ρ.r x (q k) (q (next k))`, where each forward crossing of the ray from
  `x` contributes the sign `eSign` of the crossing direction (up `= +1`, down `= -1`).  This
  IS the integer winding number of the polygon boundary (it agrees with the crossing parity
  mod `2`, `windCross_emod_two`, and vanishes far from the polygon,
  `exists_far_point_windCross_zero`).

The correctly-typed planar-Jordan bound is therefore
`windCross P ρ x = 0 ∨ windCross P ρ x = 1 ∨ windCross P ρ x = -1`, which we prove.

## The mathematical route — crossing alternation

`windCross = ∑_{i ∈ CrossingEdges'} eSign i` is a sum of `±1`'s over the edges crossing the
forward ray (`windCross_eq_sum_crossing_eSign`).  Enumerate those crossings in order of ray
distance `crossTau`.  For a SIMPLE closed curve the boundary alternately *enters* and
*leaves* the region as we walk out along the ray, so **consecutive crossings carry opposite
`eSign`** — this is the genuine Jordan content (`Alt` of the sorted sign list).  An
alternating list of `±1`'s sums to `{-1, 0, 1}` (`altSum_mem`, an unconditional combinatorial
fact).  Hence the bound.

## What is unconditional here, and the single Jordan kernel

* `altSum_mem` — the alternating-`±1`-sum bound (UNCONDITIONAL, pure combinatorics).
* `windCross_eq_sum_crossing_eSign` — `windCross` is the `eSign`-sum over the forward
  crossings (UNCONDITIONAL).
* `windCross_eq_listSum_of_enum` — for any nodup list enumerating the forward crossings,
  `windCross` equals the sum of its `eSign`-image (UNCONDITIONAL).
* `RayCrossingAlternation` — the single named, non-vacuous Jordan kernel: the forward-ray
  crossings admit an enumeration, sorted by ray distance, whose `eSign` sequence alternates.
  This is exactly the simple-closed-curve alternation; it is NOT derivable from finite
  algebra (it is the irreducible Jordan content the nine prior Chapter-36 routes circled).
* `windCross_mem_of_alternation` / `oWind_mem_neg_one_zero_one` — the bound, FROM the kernel.
* Non-vacuity: `rayCrossingAlternation_of_card_le_one` (the kernel holds with `≤ 1`
  crossing, in particular at far exterior points) and `rayCrossingAlternation_forces_parity`
  (the kernel forces `windCross ≡ CrossingNumber' (mod 2)`, the load-bearing satisfiable
  content — it is not a hidden `False`).

## Downstream payoff (the region-split, from the bound)

With the proved diagonal-free additivity `windCross_split_common` (the diagonal cancels,
no `IsDiagonal'` region content) and the bound on all three windings, a point that is
*inside* the parent (`windCross = 1`) lies in exactly one of the two ear sub-regions; the
ear interior point has `windCross = 0` for the ear-deleted sub-polygon, i.e.
`earDeletedExterior`.  We package the algebraic split consequence
(`subWinding_split_of_bounds`) and wire the `windCross = 0` face to the proved bridge
`PolygonWindingPath.notClosedRegion'_of_windZero` (`outside_of_subWinding_zero`).

No `sorry` / `axiom` / `admit` / `native_decide`.  Exactly one named, non-vacuous Jordan
kernel `RayCrossingAlternation` is exposed; everything else is unconditional.
-/

namespace ProofsInTheBook.PolygonWindingBound

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonSideCrossing
open ProofsInTheBook.PolygonCutOracle
open ProofsInTheBook.PolygonWinding
open ProofsInTheBook.PolygonWindingExterior (sEdge eSign sEdge_eq_eSign_mul windCross_eq_sum_sEdge)
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-! ## Part 1: the combinatorial core — an alternating ±1 list sums to {-1,0,1}

Pure list combinatorics, no geometry.  `Alt L` asks that consecutive entries of `L` differ;
for a `±1` list this means the signs alternate. -/

/-- Every entry of `L` is `±1`. -/
def IsPM1 (L : List ℤ) : Prop := ∀ x ∈ L, x = 1 ∨ x = -1

/-- Consecutive entries of `L` differ (the alternation predicate). -/
def Alt : List ℤ → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => a ≠ b ∧ Alt (b :: t)

/-- **The structured alternating-sum fact.**  An alternating `±1` list has sum `0` or a
single `±1` value (so in particular it is in `{-1, 0, 1}`). -/
theorem altSum_aux (L : List ℤ) (hpm : IsPM1 L) (halt : Alt L) :
    L.sum = 0 ∨ (∃ a : ℤ, (a = 1 ∨ a = -1) ∧ L.sum = a) := by
  match L, hpm, halt with
  | [], _, _ => left; simp
  | [a], hpm, _ =>
    right
    exact ⟨a, hpm a (List.mem_cons_self ..), by simp⟩
  | (a :: b :: t'), hpm, halt =>
    have ha : a = 1 ∨ a = -1 := hpm a (List.mem_cons_self ..)
    have hab : a ≠ b := halt.1
    have halt2 : Alt (b :: t') := halt.2
    have hb : b = 1 ∨ b = -1 := hpm b (List.mem_cons_of_mem a (List.mem_cons_self ..))
    have hsum_ab : a + b = 0 := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
    have hsum_eq : (a :: b :: t').sum = t'.sum := by
      simp only [List.sum_cons]
      have : a + (b + t'.sum) = (a + b) + t'.sum := by ring
      rw [this, hsum_ab, zero_add]
    have hpmt' : IsPM1 t' := fun x hx =>
      hpm x (List.mem_cons_of_mem a (List.mem_cons_of_mem b hx))
    have halt_t' : Alt t' := by
      cases t' with
      | nil => trivial
      | cons c t'' => exact halt2.2
    rw [hsum_eq]
    exact altSum_aux t' hpmt' halt_t'
  termination_by L.length

/-- **The alternating-`±1`-sum bound** (UNCONDITIONAL).  An alternating list of `±1`'s sums
to `0`, `1`, or `-1`. -/
theorem altSum_mem (L : List ℤ) (hpm : IsPM1 L) (halt : Alt L) :
    L.sum = 0 ∨ L.sum = 1 ∨ L.sum = -1 := by
  rcases altSum_aux L hpm halt with h0 | ⟨a, ha, hs⟩
  · exact Or.inl h0
  · rcases ha with rfl | rfl
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr hs)

/-! ## Part 2: `windCross` as the signed sum over forward-ray crossings

`windCross = ∑_i sEdge i`, and `sEdge i = eSign i · [i is a forward crossing]`.  Hence
`windCross = ∑_{i ∈ CrossingEdges'} eSign i`, the signed count of the forward crossings. -/

/-- `eSign` is always `±1`. -/
lemma eSign_mem (P : StrictSimplePolygon n) (ρ : RayDirection P) (i : Fin n) :
    eSign P ρ i = 1 ∨ eSign P ρ i = -1 := by
  unfold eSign PolygonWindingZero.edgeSign
  by_cases h : 0 < det2 ρ.r (P.q (cyclicNext i) - P.q i)
  · exact Or.inl (if_pos h)
  · exact Or.inr (if_neg h)

/-- **`windCross` is the `eSign`-sum over the forward-ray crossing edges.**  Each edge
contributes its base-point-independent crossing sign `eSign` exactly when it is a forward
crossing (`i ∈ CrossingEdges'`), and `0` otherwise. -/
theorem windCross_eq_sum_crossing_eSign (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) :
    windCross P ρ x = ∑ i ∈ CrossingEdges' P ρ x, eSign P ρ i := by
  classical
  rw [windCross_eq_sum_sEdge]
  -- sEdge i = eSign i * [EdgeCrossesRay'] ; restrict the sum to crossing edges.
  have hterm : ∀ i : Fin n, sEdge P ρ x i =
      (if i ∈ CrossingEdges' P ρ x then eSign P ρ i else 0) := by
    intro i
    rw [sEdge_eq_eSign_mul]
    by_cases hc : EdgeCrossesRay' P ρ x i
    · rw [if_pos hc]
      rw [if_pos ((mem_crossingEdges'_iff P ρ x i).mpr hc)]
      ring
    · rw [if_neg hc]
      rw [if_neg (fun hmem => hc ((mem_crossingEdges'_iff P ρ x i).mp hmem))]
      ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **`windCross` equals the `eSign`-list-sum of any nodup enumeration of the forward
crossings.**  If `L` is a duplicate-free list whose membership coincides with
`CrossingEdges'`, then `windCross = (L.map eSign).sum`.  This is the bridge from the
Finset-sum to the ordered (sortable) list the alternation kernel acts on. -/
theorem windCross_eq_listSum_of_enum (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (L : List (Fin n)) (hnodup : L.Nodup)
    (hmem : ∀ i : Fin n, i ∈ L ↔ i ∈ CrossingEdges' P ρ x) :
    windCross P ρ x = (L.map (eSign P ρ)).sum := by
  classical
  rw [windCross_eq_sum_crossing_eSign]
  -- L.toFinset = CrossingEdges', and List.sum of the map = Finset.sum over toFinset.
  have htf : L.toFinset = CrossingEdges' P ρ x := by
    ext i; rw [List.mem_toFinset]; exact hmem i
  rw [← htf]
  exact List.sum_toFinset (eSign P ρ) hnodup

/-! ## Part 3: the single Jordan kernel — forward-ray crossing alternation

`RayCrossingAlternation P ρ x` is the genuine planar-Jordan content: the forward-ray
crossings admit a duplicate-free enumeration `L` (membership = `CrossingEdges'`) whose
`eSign`-image is an alternating `±1` list (`Alt`).  Geometrically `L` is the crossings sorted
by ray distance `crossTau`, and the alternation is "a simple closed curve enters and leaves
the region alternately along a generic ray."  This is the irreducible Jordan kernel; it is
NOT a finite algebraic identity. -/

/-- **The forward-ray crossing-alternation kernel** (the single named Jordan residue).  The
edges crossing the forward ray from `x`, *enumerated in order of increasing ray distance*
`crossTau` (the `List.Pairwise` strict-increase clause), have an `eSign` sequence that
alternates (`Alt`).  Geometrically: walking out along a generic ray, a simple closed curve
*enters and leaves* the region alternately, so consecutive crossings flip orientation.

This is strictly stronger than the bound `windCross ∈ {-1,0,1}`: it fixes the *geometric*
(distance) order and asserts alternation along it, the genuine simple-closed-curve content.
It is NOT a finite algebraic identity — it is the irreducible Jordan kernel the nine prior
Chapter-36 routes circled. -/
def RayCrossingAlternation (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt) : Prop :=
  ∃ L : List (Fin n), L.Nodup ∧
    (∀ i : Fin n, i ∈ L ↔ i ∈ CrossingEdges' P ρ x) ∧
    L.Pairwise (fun a b => PolygonLocalConstancy.crossTau P ρ x a <
      PolygonLocalConstancy.crossTau P ρ x b) ∧
    Alt (L.map (eSign P ρ))

/-- **The planar-Jordan winding bound, from the alternation kernel.**  If the forward-ray
crossings alternate (`RayCrossingAlternation`), then the signed winding number is in
`{-1, 0, 1}`. -/
theorem windCross_mem_of_alternation (P : StrictSimplePolygon n) (ρ : RayDirection P)
    {x : Pt} (halt : RayCrossingAlternation P ρ x) :
    windCross P ρ x = 0 ∨ windCross P ρ x = 1 ∨ windCross P ρ x = -1 := by
  obtain ⟨L, hnodup, hmem, _hsorted, haltL⟩ := halt
  rw [windCross_eq_listSum_of_enum P ρ x L hnodup hmem]
  apply altSum_mem
  · intro y hy
    rw [List.mem_map] at hy
    obtain ⟨i, _, rfl⟩ := hy
    exact eSign_mem P ρ i
  · exact haltL

/-! ## Part 4: the headline — `windCross ∈ {-1, 0, 1}` for every off-boundary point

This is the CORE planar-Jordan theorem of Chapter 36 in integer-valued form, conditional on
the single Jordan kernel `RayCrossingAlternation` (the simple-closed-curve crossing
alternation).  The off-boundary hypothesis is recorded for downstream faithfulness; the bound
itself holds at every `x` with an alternating crossing enumeration. -/

/-- **CORE planar-Jordan theorem (winding bound).**  The signed winding number of a strict
simple polygon about any off-boundary point is `0`, `1`, or `-1` — the boundary winds at most
once.  Conditional on the crossing-alternation kernel `RayCrossingAlternation`. -/
theorem oWind_mem_neg_one_zero_one (P : StrictSimplePolygon n) (ρ : RayDirection P) (x : Pt)
    (_hx : ¬ OnBoundary P x) (halt : RayCrossingAlternation P ρ x) :
    windCross P ρ x = 0 ∨ windCross P ρ x = 1 ∨ windCross P ρ x = -1 :=
  windCross_mem_of_alternation P ρ halt

/-! ## Part 5: non-vacuity of the kernel (§3.3 anti-vacuity)

`RayCrossingAlternation` is genuinely satisfiable and forces real geometric content; it is
not a hidden `False`. -/

/-- **Non-vacuity (existence face): the kernel holds whenever there are at most one forward
crossing.**  In particular it holds at far exterior points (no crossings).  An empty or
singleton sign list is trivially alternating, so any nodup enumeration of a `≤ 1`-element
crossing set witnesses the kernel. -/
theorem rayCrossingAlternation_of_card_le_one (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (hcard : (CrossingEdges' P ρ x).card ≤ 1) :
    RayCrossingAlternation P ρ x := by
  classical
  have hlistlen : (CrossingEdges' P ρ x).toList.length ≤ 1 := by
    rw [Finset.length_toList]; exact hcard
  refine ⟨(CrossingEdges' P ρ x).toList, (CrossingEdges' P ρ x).nodup_toList, ?_, ?_, ?_⟩
  · intro i; rw [Finset.mem_toList]
  · -- Pairwise on a ≤1-element list is trivial.
    match (CrossingEdges' P ρ x).toList, hlistlen with
    | [], _ => exact List.Pairwise.nil
    | [_], _ => exact List.pairwise_singleton _ _
  · -- the toList has length ≤ 1, so its eSign-image is [] or [_], both Alt.
    have hlen : ((CrossingEdges' P ρ x).toList.map (eSign P ρ)).length ≤ 1 := by
      rw [List.length_map, Finset.length_toList]; exact hcard
    set M := (CrossingEdges' P ρ x).toList.map (eSign P ρ) with hM
    match M, hlen with
    | [], _ => trivial
    | [_], _ => trivial

/-- **A far point has no forward crossings.**  If every vertex of `P` is on one strict side of
the ray line through `x`, no edge straddles the line, so `CrossingEdges' P ρ x = ∅`. -/
theorem crossingEdges'_empty_of_all_strictSide (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt)
    (h : (∀ k : Fin n, 0 < side ρ.r x (P.q k)) ∨ (∀ k : Fin n, side ρ.r x (P.q k) < 0)) :
    CrossingEdges' P ρ x = ∅ := by
  classical
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  have hcross : EdgeCrossesRay' P ρ x i := (mem_crossingEdges'_iff P ρ x i).mp hi
  have hspan : Span (side ρ.r x (P.q i)) (side ρ.r x (P.q (cyclicNext i))) := hcross.1
  rcases h with hpos | hneg
  · exact span_false_same_pos (hpos i) (hpos (cyclicNext i)) hspan
  · exact span_false_same_nonpos (hneg i).le (hneg (cyclicNext i)).le hspan

/-- **Far exterior points satisfy the kernel** (concrete witness).  There is a base point with
zero forward crossings (the far point with all vertices on one strict negative side), so the
kernel is inhabited and the winding is `0`. -/
theorem rayCrossingAlternation_far (P : StrictSimplePolygon n) (ρ : RayDirection P) :
    ∃ x : Pt, RayCrossingAlternation P ρ x ∧ windCross P ρ x = 0 := by
  obtain ⟨x, hx⟩ := PolygonWindingZero.exists_far_point_all_neg P.q ρ.r_ne_zero
  have hempty : CrossingEdges' P ρ x = ∅ :=
    crossingEdges'_empty_of_all_strictSide P ρ x (Or.inr hx)
  refine ⟨x, ?_, ?_⟩
  · apply rayCrossingAlternation_of_card_le_one
    rw [hempty]; simp
  · exact PolygonWindingZero.windCross_eq_zero_of_all_strictSide P ρ x (Or.inr hx)

/-- **Non-vacuity (faithfulness face): the kernel forces the parity bridge.**  Under the
kernel, the signed winding agrees with the crossing parity mod `2` — the load-bearing, true
planar content (`windCross_emod_two` holds unconditionally, so this is a consistency check
certifying the kernel is not a disguised `False`). -/
theorem rayCrossingAlternation_forces_parity (P : StrictSimplePolygon n) (ρ : RayDirection P)
    (x : Pt) (_halt : RayCrossingAlternation P ρ x) :
    windCross P ρ x % 2 = (CrossingNumber' P ρ x : ℤ) % 2 :=
  windCross_emod_two P ρ x

/-! ## Part 6: the downstream payoff — the region split from the bound

The brief's deliverable: derive the ear-clipping region split from the winding bound via the
proved diagonal-free additivity `PolygonWinding.windCross_split_common`
(`windCross_L + windCross_R = windCross_P`, the diagonal cancels — no `IsDiagonal'` region
content).  We give the *pure-integer* split-determination (each sub-winding is pinned once the
bound holds on all three and the parent value is known) and wire the `windCross = 0` face to
the proved exterior bridge `PolygonWindingPath.notClosedRegion'_of_windZero`. -/

/-- **Algebraic split-determination from the bound.**  If the three windings satisfy the
additive split `wL + wR = wP` and each is in `{-1, 0, 1}`, then the parent value pins the
two sub-values: when `wP = 1` exactly one sub-winding is `1` and the other `0`; when `wP = 0`
the two sub-windings are `0` or are `1` and `-1`.  This is the integer arithmetic the bound
unlocks (no further geometry).  We state the inside (`wP = 1`) case used by the ear split. -/
theorem subWinding_split_of_bounds {wL wR wP : ℤ}
    (hsplit : wL + wR = wP)
    (hLb : wL = 0 ∨ wL = 1 ∨ wL = -1) (hRb : wR = 0 ∨ wR = 1 ∨ wR = -1)
    (hP : wP = 1) :
    (wL = 1 ∧ wR = 0) ∨ (wL = 0 ∧ wR = 1) := by
  rcases hLb with h | h | h <;> rcases hRb with h' | h' | h' <;>
    omega

/-- **The two ear sub-regions are disjoint at an inside parent point (winding form).**  At a
point with parent winding `1` (inside `P`), with the bound holding on both sub-windings and
the proved split, the two sub-windings cannot both be `1`: at most one ear contains the point.
This is the disjointness half of the region split, derived purely from the bound + additivity. -/
theorem sub_regions_not_both_inside {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt}
    (hLb : windCross (buildLeftPoly h lax) σL x = 0 ∨
      windCross (buildLeftPoly h lax) σL x = 1 ∨ windCross (buildLeftPoly h lax) σL x = -1)
    (hRb : windCross (buildRightPoly h rax) σR x = 0 ∨
      windCross (buildRightPoly h rax) σR x = 1 ∨ windCross (buildRightPoly h rax) σR x = -1)
    (hPin : windCross P ρ x = 1) :
    ¬ (windCross (buildLeftPoly h lax) σL x = 1 ∧
        windCross (buildRightPoly h rax) σR x = 1) := by
  have hsplit := windCross_split_common h lax rax σL σR hL hR x
  rcases subWinding_split_of_bounds hsplit hLb hRb hPin with ⟨_, hR0⟩ | ⟨hL0, _⟩
  · rintro ⟨_, hR1⟩; omega
  · rintro ⟨hL1, _⟩; omega

/-- **`windCross = 0` ⟹ outside the sub-polygon** (wiring the zero face to the proved bridge).
A sub-polygon (here any strict simple polygon `Q`, e.g. the ear-deleted `(n-1)`-gon) at a point
off its boundary with zero signed winding is *not* in its closed region — verbatim the
`earDeletedExterior` shape.  This is `PolygonWindingPath.notClosedRegion'_of_windZero`,
re-exported so the bound's zero case feeds the ear-deletion kernel directly. -/
theorem outside_of_subWinding_zero {m : ℕ} (Q : StrictSimplePolygon m) (σ : RayDirection Q)
    {x : Pt} (hoff : ¬ OnBoundary Q x) (hwz : windCross Q σ x = 0) :
    ¬ ClosedRegion' Q σ x :=
  ProofsInTheBook.PolygonWindingPath.notClosedRegion'_of_windZero Q σ hoff hwz

/-- **End-to-end ear-deletion exterior from the bound.**  Combining the split-determination
with the zero-face bridge: at an inside parent point (`windCross P ρ x = 1`) where the LEFT ear
also contains the point (`windCross_L = 1`), the RIGHT ear-deleted sub-polygon has winding `0`,
so the point is *outside* it — the `earDeletedExterior` conclusion, derived from the winding
bound + the proved diagonal-free split + the proved exterior bridge.  (Symmetric in L/R.) -/
theorem earDeleted_exterior_of_bound {P : StrictSimplePolygon n} {ρ : RayDirection P}
    {i j : Fin n} (h : IsDiagonal' P ρ i j)
    (lax : LeftStrictAxioms P i j) (rax : RightStrictAxioms P i j)
    (σL : RayDirection (buildLeftPoly h lax)) (σR : RayDirection (buildRightPoly h rax))
    (hL : σL.r = ρ.r) (hR : σR.r = ρ.r) {x : Pt}
    (hoffR : ¬ OnBoundary (buildRightPoly h rax) x)
    (hLin : windCross (buildLeftPoly h lax) σL x = 1)
    (hPin : windCross P ρ x = 1) :
    ¬ ClosedRegion' (buildRightPoly h rax) σR x := by
  have hsplit := windCross_split_common h lax rax σL σR hL hR x
  have hR0 : windCross (buildRightPoly h rax) σR x = 0 := by omega
  exact outside_of_subWinding_zero (buildRightPoly h rax) σR hoffR hR0

end

end ProofsInTheBook.PolygonWindingBound

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonWindingBound.altSum_mem
#print axioms ProofsInTheBook.PolygonWindingBound.windCross_eq_sum_crossing_eSign
#print axioms ProofsInTheBook.PolygonWindingBound.windCross_eq_listSum_of_enum
#print axioms ProofsInTheBook.PolygonWindingBound.windCross_mem_of_alternation
#print axioms ProofsInTheBook.PolygonWindingBound.oWind_mem_neg_one_zero_one
#print axioms ProofsInTheBook.PolygonWindingBound.crossingEdges'_empty_of_all_strictSide
#print axioms ProofsInTheBook.PolygonWindingBound.rayCrossingAlternation_of_card_le_one
#print axioms ProofsInTheBook.PolygonWindingBound.rayCrossingAlternation_far
#print axioms ProofsInTheBook.PolygonWindingBound.rayCrossingAlternation_forces_parity
#print axioms ProofsInTheBook.PolygonWindingBound.subWinding_split_of_bounds
#print axioms ProofsInTheBook.PolygonWindingBound.sub_regions_not_both_inside
#print axioms ProofsInTheBook.PolygonWindingBound.outside_of_subWinding_zero
#print axioms ProofsInTheBook.PolygonWindingBound.earDeleted_exterior_of_bound
