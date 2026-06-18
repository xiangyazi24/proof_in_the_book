I do **not** think the proof you are asking for can exist with obligation **(2)** as stated. The blocker is not a missing Lean trick; there is a genuine `n = 3` counterexample to the “both rotated blocks lift to the two open arc interiors” construction.

The current repo’s two-arc builder also reflects this: `twoArcSplitData_of_indices` needs numeric cuts, both nondegeneracy bounds, and the per-arc monotonicity facts as inputs; its strict field is only on Arc1, not both arcs. fileciteturn13file0L18-L36 The full-link assembler still takes the two-arc split as an explicit hypothesis. fileciteturn11file0L20-L32

Here is the bad pattern:

```lean
-- n = 3, so Fin (n+1) = Fin 4
-- signs around the original full circle:
--   index:  0   1   2   3
--   d:      +   -   0   0
--
-- compressed nonzero signs = [true, false]
-- cyclicFlips [true, false] = 2
```

The only nondegenerate cuts `t < s ≤ 3` with

```lean
2 ≤ s - t
2 ≤ wrapLen 3 s t
```

are:

```text
(t,s) = (0,2)
(t,s) = (1,3)
```

because `wrapLen 3 s t = 4 - (s - t)`, so `2 ≤ s-t` and `2 ≤ 4-(s-t)` force `s-t = 2`.

Now inspect both cuts:

```text
cut (0,2):
  nonwrap interior = {1}      -- negative
  wrap interior    = {3}      -- zero
  positive block at {0} is a cut endpoint, not an interior point

cut (1,3):
  nonwrap interior = {2}      -- zero
  wrap interior    = {0}      -- positive
  negative block at {1} is a cut endpoint, not an interior point
```

So there is **no** cut whose two open arc interiors are exactly the positive block and negative block, even after adding adjacent zeros. One nonzero sign-block is necessarily swallowed by a cut endpoint.

A Lean version of the arithmetic core is:

```lean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Range
import Mathlib.Tactic

open scoped Classical

def wrapLen (n s t : ℕ) : ℕ := (n + 1) - (s - t)

def badD : Fin 4 → ℝ := fun i =>
  if i = (0 : Fin 4) then 1
  else if i = (1 : Fin 4) then -1
  else 0

lemma badD_zero : badD (0 : Fin 4) = 1 := by
  simp [badD]

lemma badD_one : badD (1 : Fin 4) = -1 := by
  simp [badD]

lemma badD_two : badD (2 : Fin 4) = 0 := by
  simp [badD]
  decide

lemma badD_three : badD (3 : Fin 4) = 0 := by
  simp [badD]
  decide

lemma badD_only_nontrivial_cuts
    {t s : ℕ}
    (hts : t < s)
    (hsn : s ≤ 3)
    (hm1 : 2 ≤ s - t)
    (hm2 : 2 ≤ wrapLen 3 s t) :
    (t = 0 ∧ s = 2) ∨ (t = 1 ∧ s = 3) := by
  unfold wrapLen at hm2
  have hdiff : s - t = 2 := by omega
  omega
```

And the sign-change side is exactly:

```lean
-- With your definitions:
--   nzIdx d       = (List.finRange 4).filter (fun i => decide (d i ≠ 0))
--   nzSignedIdx d = (nzIdx d).map (fun i => (i, decide (0 < d i)))
--   nzSigns d     = (nzSignedIdx d).map Prod.snd
--
-- For badD:
--
--   nzIdx badD       = [0, 1]
--   nzSignedIdx badD = [(0, true), (1, false)]
--   nzSigns badD     = [true, false]
--   signChangesFull badD = cyclicFlips [true, false] = 2
```

So the precise residual is:

> A sign-flip gap may have no zero position. If a sign block next to that gap is a singleton, one of the two opposite sign blocks can be forced onto a cut endpoint. Then the compressed two-block decomposition cannot be lifted to two strict open arc interiors.

This is not repaired by `n ≥ 3`; the example above has `n = 3`.

The way to close the project is **not** to prove obligation (2) as written. You need one of these two API changes:

```lean
/--
Weak/seam-lax cut: one arc is weakly `≥ 0`, the other weakly `≤ 0`,
and there is a strict witness on either open arc, not necessarily both.
This handles `+,-,0,0` by cutting `(0,2)` or `(1,3)`.
-/
structure TwoArcCutWeakPlusMinus {n : ℕ} (d : Fin (n + 1) → ℝ) where
  t s : ℕ
  hts : t < s
  hsn : s ≤ n
  hm1 : 2 ≤ s - t
  hm2 : 2 ≤ wrapLen n s t
  nonwrap_nonneg :
    ∀ i : Fin (s - t - 1),
      0 ≤ d ⟨t + i.val + 1, by omega⟩
  wrap_nonpos :
    ∀ i : Fin (wrapLen n s t - 1),
      d ((⟨i.val + 1, by
            have := i.isLt
            unfold wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩) ≤ 0
  strict_either :
    (∃ i : Fin (s - t - 1),
      0 < d ⟨t + i.val + 1, by omega⟩)
    ∨
    (∃ i : Fin (wrapLen n s t - 1),
      d ((⟨i.val + 1, by
            have := i.isLt
            unfold wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩) < 0)
```

or add a seam structure:

```lean
/--
The missing case: a strict sign is at one of the two cut endpoints,
so it is visible in `signChangesFull`, but not in either open arc
interior used by `subArc` / `subArcWrap`.
-/
structure TwoArcCutSeamStrict {n : ℕ} (d : Fin (n + 1) → ℝ) where
  t s : ℕ
  hts : t < s
  hsn : s ≤ n
  hm1 : 2 ≤ s - t
  hm2 : 2 ≤ wrapLen n s t
  nonwrap_weak :
    (∀ i : Fin (s - t - 1),
      0 ≤ d ⟨t + i.val + 1, by omega⟩)
    ∨
    (∀ i : Fin (s - t - 1),
      d ⟨t + i.val + 1, by omega⟩ ≤ 0)
  wrap_weak :
    (∀ i : Fin (wrapLen n s t - 1),
      0 ≤ d ((⟨i.val + 1, by
            have := i.isLt
            unfold wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩))
    ∨
    (∀ i : Fin (wrapLen n s t - 1),
      d ((⟨i.val + 1, by
            have := i.isLt
            unfold wrapLen at this
            omega⟩ : Fin (n + 1)) + ⟨s, by omega⟩) ≤ 0)
  seam_strict :
    d ⟨t, by omega⟩ ≠ 0 ∨ d ⟨s, by omega⟩ ≠ 0
```

If your existing `TwoArcCutPlusMinus` / `TwoArcCutMinusPlus` already has only a **single** `strict_either` field, then the bad case is dispatchable. For the example `+,-,0,0`, use:

```lean
-- MinusPlus-style weak cut
t = 0
s = 2

-- nonwrap interior = {1}, strictly negative
-- wrap interior    = {3}, zero, hence weakly nonnegative
```

But then obligation **(2)** must be weakened: the arcs do **not** contain both sign blocks as interiors. One sign block may be represented only at a seam endpoint. That is the exact residual case.
