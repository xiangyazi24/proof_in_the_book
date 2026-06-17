import Mathlib
import ProofsInTheBook.Chapter13
import ProofsInTheBook.Ch13CyclicSigns
import ProofsInTheBook.Ch13ArmVertex

/-!
# Ch13 count reconciliation (Cauchy rigidity, ℝ³ realization — piece B)

This file reconciles the **two independent cyclic-flip-count machineries** that occur
in the ℝ³-realization layer of the discrete Cauchy rigidity proof:

* `Ch13ArmVertex.cyclicFlips : List Bool → ℕ`, fed by
  `Ch13ArmVertex.nzSigns : (Fin m → ℝ) → List Bool` — the *Bool*-based count used by
  `Ch13ArmVertexFull.signChangesFull` on real link-angle differences.  `nzSigns d`
  keeps the nonzero signs of `d` in index order (`true = positive`), and `cyclicFlips`
  counts the cyclic adjacent flips by closing the cycle (`flips ((h::t)++[h])`).

* `Ch13CyclicSigns.cyclicFlipCountSkipZeros : List EdgeSign → ℕ` — the *EdgeSign*-based
  count used by `Ch13MarkedSphere.vertexFlipCountSkipZeros`.  It drops the zeros
  (`filterMap EdgeSign.toStrict`) and takes the cyclic flip count of the resulting
  strict (`StrictEdgeSign`) sub-sequence.

Both machineries drop zeros and count cyclic two-valued flips; the only content is the
two-valued identification `Bool (true/false) ↔ StrictEdgeSign (plus/minus)` and that
both skip the zeros.  We make the bridge explicit through

* `boolToStrict : Bool → StrictEdgeSign` — the two-valued bijection;
* `realSignToEdgeSign : ℝ → EdgeSign` — the real sign map (`+, -, 0`),

and prove, with **no `sorry`, no `axiom`, no `native_decide`**:

* `cyclicFlips_eq_cyclicFlipCount_map`: `cyclicFlips bs = cyclicFlipCount (bs.map boolToStrict)`
  (the pure two-valued / cycle-closing identification, on `List Bool`);
* `nzSigns_map_boolToStrict`: `(nzSigns d).map boolToStrict =
  (List.ofFn d).filterMap (EdgeSign.toStrict ∘ realSignToEdgeSign)` (both skip the zeros);
* the headline `cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros`:
  `cyclicFlips (nzSigns d) = cyclicFlipCountSkipZeros ((List.ofFn d).map realSignToEdgeSign)`.
-/

namespace ProofsInTheBook.Ch13CountReconcile

open ProofsInTheBook.Chapter13
open ProofsInTheBook.Ch13CyclicSigns
open ProofsInTheBook.Ch13ArmVertex
open EdgeSign

/-! ## The two-valued bridge `Bool ↔ StrictEdgeSign` -/

/-- The two-valued bijection used everywhere: `true = positive = plus`,
`false = negative = minus`. -/
def boolToStrict : Bool → StrictEdgeSign
  | true => StrictEdgeSign.plus
  | false => StrictEdgeSign.minus

/-- `boolToStrict` is injective (the two-valued bijection preserves distinctness),
so it transports the inequality indicator `[a ≠ b]` unchanged. -/
theorem boolToStrict_inj : Function.Injective boolToStrict := by
  intro a b h; cases a <;> cases b <;> simp_all [boolToStrict]

@[simp] theorem boolToStrict_eq_iff (a b : Bool) :
    boolToStrict a = boolToStrict b ↔ a = b :=
  ⟨fun h => boolToStrict_inj h, fun h => by rw [h]⟩

/-! ## `flips` (Bool) ↔ `flipAux`/`cyclicFlipCount` (StrictEdgeSign)

`cyclicFlips (h::t)` closes the cycle by computing `flips ((h::t) ++ [h])`, walking the
*linear* differences of the closed list.  `cyclicFlipCount (x::xs) = flipAux x x xs`
walks the tail comparing each entry to its predecessor and finally to the first entry.
Both express the same cyclic adjacent-flip count; we identify them through `boolToStrict`.

We first relate `flips` of a closed Bool list to `flipAux` of the mapped open list. -/

/-- The linear flip count `flips` of a Bool list, *with the cyclic closer `[first]`
appended*, equals `flipAux (boolToStrict first)` walking the mapped list.  This is the
single structural induction carrying the whole identification. -/
theorem flips_append_eq_flipAux (first : Bool) :
    ∀ (prev : Bool) (t : List Bool),
      flips ((prev :: t) ++ [first])
        = flipAux (boolToStrict first) (boolToStrict prev) (t.map boolToStrict)
  | prev, [] => by
      -- `flips [prev, first] = [prev ≠ first]`; `flipAux f (b prev) [] = [b prev ≠ f]`.
      simp only [List.nil_append, List.cons_append, List.map_nil, flips, flipAux]
      by_cases h : prev = first
      · simp [h]
      · simp only [ne_eq, h, not_false_eq_true, if_pos]
        rw [if_pos]
        intro hc; exact h (boolToStrict_inj hc)
  | prev, x :: t => by
      -- peel one comparison `[prev ≠ x]` on both sides, recurse on `x :: t`.
      have ih := flips_append_eq_flipAux first x t
      simp only [List.cons_append, List.map_cons, flips, flipAux] at *
      rw [ih]
      by_cases h : prev = x
      · simp [h]
      · rw [if_pos h, if_pos]
        intro hc; exact h (boolToStrict_inj hc)

/-- **The pure two-valued / cycle-closing identification.**  The Bool-based cyclic flip
count of a list equals the `StrictEdgeSign`-based cyclic flip count of its image under
`boolToStrict`. -/
theorem cyclicFlips_eq_cyclicFlipCount_map (bs : List Bool) :
    cyclicFlips bs = cyclicFlipCount (bs.map boolToStrict) := by
  cases bs with
  | nil => simp [cyclicFlips, cyclicFlipCount]
  | cons h t =>
      -- LHS = flips ((h::t)++[h]); RHS = flipAux (b h) (b h) (t.map b).
      show flips ((h :: t) ++ [h]) = cyclicFlipCount ((h :: t).map boolToStrict)
      rw [flips_append_eq_flipAux h h t]
      simp only [List.map_cons, cyclicFlipCount]

/-! ## The real sign map and zero-skipping reconciliation -/

open scoped Classical in
/-- The sign of a real number as an `EdgeSign` (`+, -, 0`), matching the conventions
of `nzSigns` (`0 < d` ↦ `plus`, `d < 0` ↦ `minus`, `d = 0` ↦ `zero`). -/
noncomputable def realSignToEdgeSign (x : ℝ) : EdgeSign :=
  if 0 < x then EdgeSign.plus else if x < 0 then EdgeSign.minus else EdgeSign.zero

open scoped Classical in
/-- On a nonzero real, `toStrict ∘ realSignToEdgeSign` matches `boolToStrict ∘ (decide (0 < x))`:
both record the strict sign.  (Used to align the two zero-skipping filters.) -/
theorem toStrict_realSign_of_ne (x : ℝ) (hx : x ≠ 0) :
    (realSignToEdgeSign x).toStrict = some (boolToStrict (decide (0 < x))) := by
  unfold realSignToEdgeSign
  rcases lt_trichotomy x 0 with h | h | h
  · have hnp : ¬ (0 < x) := not_lt.mpr h.le
    simp only [hnp, if_false, h, if_true]
    simp [EdgeSign.toStrict, boolToStrict]
  · exact absurd h hx
  · simp only [h, if_true]
    simp [EdgeSign.toStrict, boolToStrict]

open scoped Classical in
/-- On a zero real, `toStrict ∘ realSignToEdgeSign` is `none` (the zero is dropped). -/
theorem toStrict_realSign_of_zero {x : ℝ} (hx : x = 0) :
    (realSignToEdgeSign x).toStrict = none := by
  subst hx
  simp [realSignToEdgeSign, EdgeSign.toStrict]

/-- `(L.filter p).map g = L.filterMap (fun a => if p a then some (g a) else none)`:
a filtered-then-mapped list is the `filterMap` of the guarded option. -/
theorem filter_map_eq_filterMap {β γ : Type*} (p : β → Bool) (g : β → γ) :
    ∀ (L : List β),
      (L.filter p).map g = L.filterMap (fun a => if p a then some (g a) else none)
  | [] => by simp
  | a :: L => by
      simp only [List.filter_cons, List.filterMap_cons]
      by_cases h : p a
      · simp [h, filter_map_eq_filterMap p g L]
      · simp [h, filter_map_eq_filterMap p g L]

open scoped Classical in
/-- **Both machineries skip the zeros identically.**  Mapping `nzSigns d` through the
two-valued bridge `boolToStrict` reproduces exactly the strict sub-sequence obtained by
`filterMap toStrict` on the `EdgeSign` sign list `(List.ofFn d).map realSignToEdgeSign`. -/
theorem nzSigns_map_boolToStrict {m : ℕ} (d : Fin m → ℝ) :
    (nzSigns d).map boolToStrict
      = ((List.ofFn d).map realSignToEdgeSign).filterMap EdgeSign.toStrict := by
  -- RHS: rewrite `List.ofFn d` as a map over `finRange m`, fuse the maps and filterMap.
  rw [List.ofFn_eq_map, List.map_map, List.filterMap_map]
  -- LHS: `nzSigns d = (finRange.filter (d i ≠ 0)).map (decide (0 < d i))`,
  -- then map `boolToStrict`, fuse, and turn filter+map into a guarded filterMap.
  unfold nzSigns
  rw [List.map_map, filter_map_eq_filterMap]
  -- Both sides are now `(List.finRange m).filterMap (·)`; compare the kernels pointwise.
  apply List.filterMap_congr
  intro i _
  simp only [Function.comp_apply]
  by_cases hi : d i = 0
  · -- zero index: both drop it.
    rw [toStrict_realSign_of_zero hi]
    rw [if_neg]
    simp [hi]
  · -- nonzero index: both keep the strict sign, aligned by `toStrict_realSign_of_ne`.
    rw [toStrict_realSign_of_ne (d i) hi, if_pos]
    simp [hi]

/-! ## The headline reconciliation -/

open scoped Classical in
/-- **The reconciliation theorem (piece B).**  The `Bool`-based cyclic flip count of the
real sign sequence `nzSigns d` (used by `signChangesFull`) equals the `EdgeSign`-based
skip-zero cyclic flip count of the corresponding `+, -, 0` sign list (used by
`vertexFlipCountSkipZeros`).  Both drop the zeros and count cyclic two-valued flips. -/
theorem cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros {m : ℕ} (d : Fin m → ℝ) :
    cyclicFlips (nzSigns d)
      = cyclicFlipCountSkipZeros ((List.ofFn d).map realSignToEdgeSign) := by
  rw [cyclicFlips_eq_cyclicFlipCount_map, cyclicFlipCountSkipZeros_eq_strict,
    nzSigns_map_boolToStrict]

/-! ## Non-vacuity

On the concrete real sequence `[1, 0, -1, 0]` (one positive, one zero, one negative, one
zero) both count machineries return `2`: the single cyclic plus-minus split, with the two zeros
skipped on both sides.  This witnesses the equality as a genuine, derived identity. -/

/-- The concrete `Fin 4 → ℝ` witness `[1, 0, -1, 0]`. -/
noncomputable def witness : Fin 4 → ℝ := ![1, 0, -1, 0]

/-- The nonzero-sign Bool list of the witness is `[true, false]`: indices `0` (value `1`,
positive ↦ `true`) and `2` (value `-1`, negative ↦ `false`) survive, the two zeros drop. -/
theorem nzSigns_witness : nzSigns witness = [true, false] := by
  have h4 : List.finRange 4 = [(0 : Fin 4), 1, 2, 3] := by decide
  have v0 : witness 0 = 1 := rfl
  have v1 : witness 1 = 0 := rfl
  have v2 : witness 2 = -1 := rfl
  have v3 : witness 3 = 0 := rfl
  -- the four filter guards `witness i ≠ 0`
  have f0 : decide (witness 0 ≠ 0) = true := by rw [v0]; norm_num
  have f1 : decide (witness 1 ≠ 0) = false := by rw [v1]; simp
  have f2 : decide (witness 2 ≠ 0) = true := by rw [v2]; norm_num
  have f3 : decide (witness 3 ≠ 0) = false := by rw [v3]; simp
  -- the two surviving signs `0 < witness i`
  have s0 : decide (0 < witness 0) = true := by rw [v0]; norm_num
  have s2 : decide (0 < witness 2) = false := by rw [v2]; norm_num
  simp only [nzSigns, h4, List.filter, f0, f1, f2, f3, List.map, s0, s2]

example : cyclicFlips (nzSigns witness) = 2 := by
  have : nzSigns witness = [true, false] := nzSigns_witness
  rw [this]; decide

example :
    cyclicFlipCountSkipZeros ((List.ofFn witness).map realSignToEdgeSign) = 2 := by
  rw [← cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros]
  have : nzSigns witness = [true, false] := nzSigns_witness
  rw [this]; decide

example :
    cyclicFlips (nzSigns witness)
      = cyclicFlipCountSkipZeros ((List.ofFn witness).map realSignToEdgeSign) :=
  cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros witness

end ProofsInTheBook.Ch13CountReconcile

#print axioms ProofsInTheBook.Ch13CountReconcile.cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros
