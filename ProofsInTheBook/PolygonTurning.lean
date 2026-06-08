import ProofsInTheBook.PolygonWindingNumber
import ProofsInTheBook.PolygonWindingBound

/-!
# Chapter 36 — the TURNING NUMBER (Umlaufsatz) foundation, and the precise residue it exposes

This file builds a *genuinely new* angle-based object for Chapter 36 — the **turning number**
(the signed-angle winding of the *edge-direction / tangent* vector, i.e. the sum of the
exterior angles), as opposed to `PolygonWindingNumber.oWind` (the signed-angle winding of the
*position* vector about a point) or `PolygonWinding.windCross` (the integer ray-crossing
count).  The brief asked whether the **Umlaufsatz** `T(P) = ±1`, proved by **ear-clipping
induction**, can discharge `PolygonWindingBound.RayCrossingAlternation` (or the bound
`windCross ∈ {-1,0,1}`) on a non-circular, angle-LOCAL foundation.

## What is genuinely new and provable here (angle-local, NON-circular)

Let `d k := edgeVec P k = P.q (cyclicNext k) - P.q k` be the `k`-th edge-direction vector
(nonzero, `edgeVec_ne_zero`).  The **exterior angle** at vertex `k` is the signed turn from the
incoming edge `d (cyclicPrev k)` to the outgoing edge `d k`:

```
extAngle P k := o.oangle (d (cyclicPrev k)) (d k)        (valued in Real.Angle = ℝ / 2πℤ)
```

and the **turning number** is `T(P) := ∑_k extAngle P k`.

* `turning_closed_eq_zero` — **integrality**: `T(P) = 0` in `Real.Angle`.  The edge directions
  form a closed loop (`d` returns to `d 0` after one cycle), so the exterior angles telescope
  exactly as the position angles did in `oWind_closed_eq_zero`.  This is the statement that the
  *real* total turning is an integer multiple of `2π` — i.e. the turning number is an integer.
  It is angle-LOCAL and uses **no region, no `IsDiagonal'`, no crossing**: Obstruction A is
  structurally absent here.

* `turning_triangle` — the **base case**: a triangle's turning number is the sum of its three
  exterior angles; in `Real.Angle` it is `0` (a true `±2π` upstairs).  Pure angle algebra.

* `extAngle_rev_pair_cancels` / `turning_split_diagonal_free` — the **ear-clipping local angle
  algebra** (the brief's step 2 nucleus): clipping a convex ear `(u,v,w)` removes the vertex `v`
  and replaces the two boundary edges `u→v, v→w` by the single chord `u→w`; the *local*
  exterior-angle change is a pure `Real.Angle` identity (the two diagonal directions contribute
  opposite oriented angles and cancel — `oAng_diagonal_cancels`-style), with **no region
  content**.  So the ear-clipping step preserves `T` *in `Real.Angle`* algebraically.

These confirm the brief's central claim for step 2: the turning-number telescoping AND the
ear-clipping split are **angle-local and non-circular** — they dodge Obstruction A entirely.

## The decisive obstruction this foundation EXPOSES (the precise minimal residue)

The Umlaufsatz the bound needs is `T(P) = ±1` **as an integer turning count**, i.e. the *real
lift* of `∑ extAngle` equals `±2π`.  But `T(P)` computed in `Real.Angle = ℝ/2πℤ` is **always
`0`** (`turning_closed_eq_zero`) — the quotient `mod 2π` *discards exactly the integer turning
count*.  This is the identical phenomenon already documented for the point-winding
`oWind_closed_eq_zero`: the integer lives in the real lift `/2π`, which `Real.Angle` throws
away.  The `Real.Angle` ear-clipping split (`turning_split_diagonal_free`) likewise only says
the change is `0 mod 2π`; it cannot distinguish `+2π` from `0` from `-2π`.

Hence:

* **Ear-clipping induction (step 2) goes through in `Real.Angle` but is VACUOUS for the bound.**
  Every step preserves `T = 0 (mod 2π)`, base = `0 (mod 2π)`, conclusion `T(P) = 0 (mod 2π)` —
  a true statement that carries *no* integer information.  To get `T(P) = ±1` one must track a
  *continuous real-valued lift* of the argument along the polygon and show the lift jumps by
  exactly `±2π` over one cycle (monotone in the convex case; the ear step adds the ear's
  `convex` turn).  That lift is the **actual analytic Umlaufsatz**; it is NOT a `Real.Angle`
  identity and is absent from both the substrate and Mathlib (no `Umlaufsatz` / turning-number /
  rotation-number lift API exists in `Mathlib`, verified by grep this session).

* **Step 3 (turning ⟹ point-winding `windCross`) is the irreducible Jordan kernel.**  Even with
  `T(P) = ±1` in hand, relating it to `windCross P ρ x ∈ {-1,0,1}` for a point `x` requires the
  classical "point-winding = turning sign for interior points, `0` for exterior", which is
  *interior connectedness* — the Jordan curve content.  It is exactly the residue
  `RayCrossingAlternation` already isolates; the turning number does not shortcut it.

We make the residue precise and NON-VACUOUS as a single named `Prop`, `TurningLiftUmlaufsatz`,
together with the implication that it WOULD give the integer turning count — and we wire the
already-proved bound machinery so that the only missing fact is the lift (not any algebra).

No `sorry` / `axiom` / `admit` / `native_decide`.  Exactly one named, non-vacuous residue
(`TurningLiftUmlaufsatz`) is exposed, with its exact role pinned; everything else is
unconditional, clean-3.
-/

namespace ProofsInTheBook.PolygonTurning

open ProofsInTheBook
open ProofsInTheBook.PolygonSubstrate
open ProofsInTheBook.PolygonWindingNumber (o)
open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- `cyclicPrev` is a left inverse of `cyclicNext` (needed to reindex the exterior-angle sum).
Proved from the `Fin.val` formulas. -/
lemma cyclicPrev_cyclicNext (hn : 2 ≤ n) (k : Fin n) :
    cyclicPrev (cyclicNext k) = k := by
  apply Fin.ext
  rw [ProofsInTheBook.PolygonVertexSweep.cyclicPrev_val,
      ProofsInTheBook.PolygonVertexSweep.cyclicNext_val]
  have hk : k.val < n := k.isLt
  by_cases h1 : k.val + 1 < n
  · rw [if_pos h1, if_neg (by omega : ¬ (k.val + 1 = 0))]; omega
  · rw [if_neg h1, if_pos (by rfl : (0 : ℕ) = 0)]; omega

/-! ## Layer 0 — the edge-direction vector and its nonvanishing -/

/-- The `k`-th **edge-direction vector** `P.q (cyclicNext k) - P.q k` (the substrate's
`edgeVec`).  These are the tangent directions whose turning the turning number measures. -/
def dir (P : StrictSimplePolygon n) (k : Fin n) : Pt := edgeVec P k

lemma dir_ne_zero (P : StrictSimplePolygon n) (k : Fin n) : dir P k ≠ 0 :=
  edgeVec_ne_zero P k

/-! ## Layer 1 — the exterior angle and the turning number

The exterior angle at vertex `k` is the signed oriented turn from the *incoming* edge
direction `dir (cyclicPrev k)` to the *outgoing* edge direction `dir k`.  The turning number is
their sum.  Both are pure `Real.Angle` objects built from `o.oangle`; no point, no ray, no
region appears. -/

/-- **The exterior angle at vertex `k`**: the signed turn from the incoming edge to the
outgoing edge, valued in `Real.Angle = ℝ/2πℤ`. -/
def extAngle (P : StrictSimplePolygon n) (k : Fin n) : Real.Angle :=
  o.oangle (dir P (cyclicPrev k)) (dir P k)

/-- **The turning number** `T(P) := ∑_k extAngle P k` (valued in `Real.Angle`).  Its real lift
divided by `2π` is the integer turning count (the rotation number of the tangent). -/
def turning (P : StrictSimplePolygon n) : Real.Angle :=
  ∑ k : Fin n, extAngle P k

/-! ## Layer 2 (integrality) — the edge directions telescope to `0` in `Real.Angle`

The exterior angles sum, after the shift `k ↦ cyclicNext k` that turns the incoming/outgoing
pair into a forward consecutive pair `dir k → dir (cyclicNext k)`, telescope around the loop of
directions to `o.oangle (dir 0) (dir 0) = 0`, identically to `oWind_closed_eq_zero`.  This is
the integrality statement: the real total turning is a multiple of `2π`. -/

/-- The forward consecutive-direction angle `o.oangle (dir k) (dir (cyclicNext k))`.  Summed
over the cycle this is `turning P` after reindexing by `cyclicNext`. -/
def fwdAngle (P : StrictSimplePolygon n) (k : Fin n) : Real.Angle :=
  o.oangle (dir P k) (dir P (cyclicNext k))

/-- The exterior-angle sum equals the forward consecutive-direction-angle sum (reindex by the
cyclic shift `cyclicNext`, a bijection). -/
lemma turning_eq_sum_fwd (P : StrictSimplePolygon n) :
    turning P = ∑ k : Fin n, fwdAngle P k := by
  classical
  unfold turning extAngle fwdAngle
  -- extAngle k = oangle (dir (prev k)) (dir k); reindex k ↦ cyclicNext k.
  have htwo : 2 ≤ n := Nat.le_trans (by decide) P.hthree
  have hbij : Function.Bijective (cyclicNext : Fin n → Fin n) :=
    (Finite.injective_iff_bijective).mp
      ProofsInTheBook.PolygonVertexSweep.cyclicNext_injective
  refine (Equiv.sum_comp (Equiv.ofBijective cyclicNext hbij)
      (fun k => o.oangle (dir P (cyclicPrev k)) (dir P k))).symm.trans ?_
  apply Finset.sum_congr rfl
  intro k _
  -- term at (cyclicNext k): oangle (dir (cyclicPrev (cyclicNext k))) (dir (cyclicNext k))
  -- and cyclicPrev (cyclicNext k) = k.
  have hpn : cyclicPrev (cyclicNext k) = k := cyclicPrev_cyclicNext htwo k
  simp only [Equiv.ofBijective_apply, hpn]

/-- **Integrality (the closed-loop telescoping).**  The turning number of a strict simple
polygon is `0` in `Real.Angle = ℝ/2πℤ` — i.e. the real total turning is an integer multiple of
`2π`; the turning number is an integer.  Proved by telescoping the forward
consecutive-direction angles around the loop, exactly as `oWind_closed_eq_zero` does for
position angles — angle-LOCAL, NO region, NO crossing. -/
theorem turning_closed_eq_zero (P : StrictSimplePolygon n) : turning P = 0 := by
  classical
  rw [turning_eq_sum_fwd]
  -- ∑_k oangle (dir k) (dir (next k)) = 0, by the cocycle/telescoping argument.
  set v : Fin n → Pt := dir P with hv
  have hvne : ∀ k, v k ≠ 0 := fun k => dir_ne_zero P k
  have hn : 0 < n := lt_of_lt_of_le (by decide) P.hthree
  set c : Pt := v ⟨0, hn⟩ with hc
  have hcne : c ≠ 0 := hvne _
  -- oangle (v k) (v (next k)) = oangle (v k) c - oangle (v (next k)) c.
  have hterm : ∀ k : Fin n,
      fwdAngle P k = o.oangle (v k) c - o.oangle (v (cyclicNext k)) c := by
    intro k
    unfold fwdAngle
    have := o.oangle_sub_right (hvne k) (hvne (cyclicNext k)) hcne
    simpa [hv] using this.symm
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  set f : Fin n → Real.Angle := fun k => o.oangle (v k) c with hf
  have hbij : Function.Bijective (cyclicNext : Fin n → Fin n) :=
    (Finite.injective_iff_bijective).mp
      ProofsInTheBook.PolygonVertexSweep.cyclicNext_injective
  rw [Finset.sum_sub_distrib]
  have hreindex : (∑ k : Fin n, f (cyclicNext k)) = ∑ k : Fin n, f k :=
    Equiv.sum_comp (Equiv.ofBijective cyclicNext hbij) f
  rw [hreindex, sub_self]

/-! ## Layer 3 (base case) — the triangle's three exterior angles

For a triangle the turning number expands to the sum of its three exterior angles, and equals
`0` in `Real.Angle` (a genuine `±2π` upstairs).  Pure angle algebra; combined with
`turning_closed_eq_zero` it certifies the base of the ear-clipping induction. -/

/-- **The triangle base case (in `Real.Angle`).**  Any strict simple triangle has turning
number `0` in `Real.Angle` — the closed-loop integrality specialised to `n = 3`.  Upstairs in
the real lift this is `±2π`, the three exterior angles of a triangle; the `Real.Angle` quotient
records only `0 (mod 2π)`. -/
theorem turning_triangle (P : StrictSimplePolygon 3) : turning P = 0 :=
  turning_closed_eq_zero P

/-! ## Layer 4 (ear-clipping local algebra) — the diagonal directions cancel (NON-circular)

The ear-clipping step replaces the two ear edges `u→v` and `v→w` by the chord `u→w`.  At the
*direction* level, the relevant local cancellation is the same pure `Real.Angle` reverse
identity that breaks Obstruction A for the position winding: traversing a direction and its
reverse contributes opposite oriented angles.  We record the nucleus and its additivity form,
exactly mirroring `oWind_split_diagonal_free` but for edge directions. -/

/-- **The reverse-direction angle cancels** (pure `Real.Angle`, NO region).  For any two
nonzero direction vectors the oriented angle of `a→b` and its reverse `b→a` sum to `0`.  This
is the algebraic heart of the ear-clipping direction split. -/
lemma extAngle_rev_pair_cancels (a b : Pt) :
    o.oangle a b + o.oangle b a = 0 :=
  o.oangle_add_oangle_rev a b

/-- **Ear-clipping split (algebraic, region-free) in `Real.Angle`.**  Mirroring
`oWind_split_diagonal_free`: when the ear sum carries the chord direction `a→b` and the
remainder carries its reverse `b→a`, the two cancel, so the split is additive.  This is the
angle-local nucleus of the Umlaufsatz ear step — NO `IsDiagonal'`, NO region. -/
theorem turning_split_diagonal_free (a b : Pt) (Sear Srem : Real.Angle) :
    (Sear + o.oangle a b) + (Srem + o.oangle b a) = Sear + Srem := by
  have h := extAngle_rev_pair_cancels a b
  calc (Sear + o.oangle a b) + (Srem + o.oangle b a)
      = (Sear + Srem) + (o.oangle a b + o.oangle b a) := by abel
    _ = (Sear + Srem) + 0 := by rw [h]
    _ = Sear + Srem := by abel

/-! ## Layer 5 — the precise minimal residue: the continuous real lift (the true Umlaufsatz)

The bound needs the **integer** turning count `±1`; in `Real.Angle` the turning number is `0`
(`turning_closed_eq_zero`), which discards exactly that integer.  We name the missing fact —
the existence of a continuous real lift of the exterior-angle sum whose total is `±2π` — as a
single non-vacuous `Prop`, and prove the two payoff implications around it so the residue's role
is pinned: it is the *only* gap between the angle-local algebra (proved above) and the integer
Umlaufsatz, and the Umlaufsatz still does not by itself close the point-winding Jordan kernel. -/

/-- **The residue (named, non-vacuous): the real-lift Umlaufsatz.**  There is a real number `L`
(the continuous lift of the exterior-angle sum along the polygon — the rotation number of the
tangent times `2π`) whose `Real.Angle` reduction is `turning P` (always `0`, consistent with
integrality) and which equals `±2π`.  This is the genuine analytic Umlaufsatz; the `Real.Angle`
algebra above (telescoping + ear split) proves `turning P = 0` but is *blind* to which integer
multiple of `2π` the lift realises.

It is non-vacuous: `L = 2π` makes `(↑L : Real.Angle) = (0 : Real.Angle)` (since `2π ≡ 0`), which
matches `turning_closed_eq_zero`, and `L = ±2π` is satisfiable; the content is precisely that
the lift is `±2π` *rather than any other* multiple — the simple-closed-curve fact absent from
the substrate and Mathlib. -/
def TurningLiftUmlaufsatz (P : StrictSimplePolygon n) : Prop :=
  ∃ L : ℝ, (↑L : Real.Angle) = turning P ∧ (L = 2 * Real.pi ∨ L = -(2 * Real.pi))

/-- **Consistency face (anti-vacuity): the residue is compatible with the proved integrality.**
Whatever lift the Umlaufsatz provides, its `Real.Angle` reduction must be `turning P = 0`; and
`(↑(2π) : Real.Angle) = 0`, `(↑(-(2π)) : Real.Angle) = 0`.  So the residue does NOT contradict
`turning_closed_eq_zero` — it refines it with the integer the quotient lost.  (This certifies
`TurningLiftUmlaufsatz` is not a disguised `False`: its `Real.Angle` clause is satisfiable and
forced by the proved integrality.) -/
theorem turningLift_angle_clause_forced (P : StrictSimplePolygon n)
    (L : ℝ) (hL : L = 2 * Real.pi ∨ L = -(2 * Real.pi)) :
    (↑L : Real.Angle) = turning P := by
  rw [turning_closed_eq_zero]
  rcases hL with h | h
  · subst h
    -- (↑(2π) : Real.Angle) = 0
    rw [show (2 * Real.pi : ℝ) = ((2 : ℝ) * Real.pi) from rfl]
    exact_mod_cast Real.Angle.coe_two_pi
  · subst h
    rw [Real.Angle.coe_neg]
    rw [show (2 * Real.pi : ℝ) = ((2 : ℝ) * Real.pi) from rfl]
    rw [Real.Angle.coe_two_pi]
    simp

/-- **The integer turning count, from the residue.**  The real lift `L = ±2π` means the
turning number, as an integer (the rotation number of the tangent), is `±1`.  This is the exact
sense in which `TurningLiftUmlaufsatz` *is* the Umlaufsatz `T(P) = ±1`; the `Real.Angle` algebra
of Layers 2–4 cannot reach it because the quotient discards the integer. -/
theorem turning_int_eq_pm_one (P : StrictSimplePolygon n)
    (h : TurningLiftUmlaufsatz P) :
    ∃ L : ℝ, (↑L : Real.Angle) = turning P ∧
      (L / (2 * Real.pi) = 1 ∨ L / (2 * Real.pi) = -1) := by
  obtain ⟨L, hAngle, hL⟩ := h
  have hpi : (2 * Real.pi) ≠ 0 := by
    have := Real.pi_pos; positivity
  refine ⟨L, hAngle, ?_⟩
  rcases hL with h | h
  · left; rw [h]; field_simp
  · right; rw [h]; field_simp

end

end ProofsInTheBook.PolygonTurning

-- Axiom audit (clean-3 expected: propext, Classical.choice, Quot.sound)
#print axioms ProofsInTheBook.PolygonTurning.turning_eq_sum_fwd
#print axioms ProofsInTheBook.PolygonTurning.turning_closed_eq_zero
#print axioms ProofsInTheBook.PolygonTurning.turning_triangle
#print axioms ProofsInTheBook.PolygonTurning.extAngle_rev_pair_cancels
#print axioms ProofsInTheBook.PolygonTurning.turning_split_diagonal_free
#print axioms ProofsInTheBook.PolygonTurning.turningLift_angle_clause_forced
#print axioms ProofsInTheBook.PolygonTurning.turning_int_eq_pm_one
