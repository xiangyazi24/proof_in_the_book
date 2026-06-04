# ANSWER_24_01_agy — Singularity handling for Ch24 Herglotz

## Important framing

The book's statement is about pointwise convergence of partial sums to π·cot(πx)
**for x ∉ ℤ**. At integer points both sides have poles (or junk values in Lean's
`Real.cot` and `1/x` — see below). The cleanest Lean statement is the **limit
version with x ∉ ℤ as hypothesis**, not a literal pointwise equality.

### Mathlib's junk values (important)

- `Real.cot (π·k) = Real.cos (π·k) / Real.sin (π·k) = (±1) / 0 = 0` for any integer k.
- `1/x` at x = 0 equals `0` (Mathlib's div by zero).
- For x = k ≠ 0: partial-fraction sum has a `2k/(k² - k²) = 2k/0 = 0` term plus
  other finite terms, but the OTHER terms `1/k + ∑_{j≠k} 2k/(k²-j²)` are
  generally nonzero. So partial sum is NOT 0 here.

→ **Pointwise equality at integer x ≠ 0 fails** because junk values don't match.

The right statement: convergence for x ∉ ℤ.

## Recommended `chapter24` statement

```lean
theorem chapter24 (x : ℝ) (hx : ∀ k : ℤ, x ≠ k) :
    Filter.Tendsto
      (fun N : ℕ => 1/x + ∑ k ∈ Finset.range N \ {0},
        2 * x / (x^2 - (k : ℝ)^2))
      Filter.atTop
      (nhds (Real.pi * Real.cot (Real.pi * x)))
```

Or the equivalent form with symmetric partial sums `∑_{k = -N}^{N} 1/(x - k)`.

This avoids the singularity issue entirely. The book proves exactly this limit.

## How to use the existing `HerglotzClass` machinery

Two HerglotzClass instances:
1. `f₁ := fun x => π·cot(π·x)` — Herglotz by Real analysis (Real.cot duplication formula).
2. `f₂ := fun x => 1/x + ∑_{k≥1} 2x/(x² - k²)` (as a LIMIT) — Herglotz by termwise check.

Show `(f₁ - f₂).Continuous` and `(f₁ - f₂).HerglotzClass` and `(f₁ - f₂)(1/2) = 0`,
hence by `herglotz_uniqueness_of_continuous_periodic_odd`, f₁ = f₂.

But continuity of f₁ - f₂ on **all of ℝ** requires the removable-singularity
argument at integers. Two paths:

### Path A (simpler): work on ℝ \ ℤ + extend

Don't use `herglotz_uniqueness_of_continuous_periodic_odd` directly on the
WHOLE real line. Instead:

1. Show f₁ and f₂ are equal on (0, 1) by Herglotz uniqueness applied to that
   open set (where both are continuous + analytic).
2. Extend the equality to ℝ \ ℤ by periodicity (both are 1-periodic).
3. State the main theorem with `hx : ∀ k : ℤ, x ≠ k` hypothesis.

This avoids the removable singularity entirely. `Continuous` is replaced by
`ContinuousOn (Set.Ioo 0 1)`.

If `herglotz_uniqueness_of_continuous_periodic_odd` only takes global
`Continuous`, you may need a variant or to prove a `ContinuousOn` variant.

### Path B (faithful to book): explicit removable extension

1. Define `h : ℝ → ℝ` piecewise: `h x = if (∃ k : ℤ, x = k) then 0 else f₁ x - f₂ x`.
2. Prove `Continuous h` via `Real.cot_sub_one_div_continuous_at_zero` (or
   prove it manually using `Real.cos_pi_int_mul = ±1` and `Real.sin` Taylor
   expansion at 0).
3. Show `h.HerglotzClass` (`cancel` + `eval_half`).
4. Apply uniqueness: `h = 0` globally.
5. Translate back to `f₁ = f₂` on ℝ \ ℤ.

This is the book's actual approach but requires the analytic continuity
proof at integers (~50 LOC).

## Recommendation: Path A

Given that the chapter result is naturally a STATEMENT about x ∉ ℤ, just
prove that. Skip the extension. Saves you ~100 LOC.

## Mathlib API to use

- `Real.cot` (in `Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`)
- `Real.cot_pi_div_two_sub : cot(π/2 - x) = tan x` — useful for uniqueness setup
- For convergence: search `Filter.Tendsto`, `Summable.tendsto_sum`, 
  `HasSum`, `Real.tsum_atTop`. The partial fraction sum series convergence
  for x ∉ ℤ is standard analysis (1/(x²-k²) ~ -1/k² for large k, so absolutely
  convergent).
- `summable_one_div_nat_pow_iff`: gives `Summable (fun k => 1/k^p)` for p > 1.
  Adapt for `2x/(x²-k²)` via comparison.

## Skeleton

```lean
section MainTheorem

variable (x : ℝ)

-- The partial-fraction series term.
noncomputable def cotTerm (k : ℕ) : ℝ :=
  if k = 0 then 1 / x else 2 * x / (x^2 - (k : ℝ)^2)

-- Show absolute summability for x ∉ ℤ.
lemma cotTerm_summable (hx : ∀ k : ℤ, x ≠ k) : Summable (cotTerm x) := by
  -- Bound |cotTerm k| ≤ 2|x|/(k² - x²) for k > |x|, comparison with 1/k².
  sorry  -- ~40 LOC of bounding

-- Define the partial-fraction function as the sum.
noncomputable def partialFraction (x : ℝ) : ℝ := ∑' k, cotTerm x k

-- Show it's HerglotzClass.
lemma partialFraction_HerglotzClass : HerglotzClass partialFraction := by
  sorry  -- termwise check of cancel + eval_half + duplication

-- The cot side is HerglotzClass.
lemma cot_pi_HerglotzClass : HerglotzClass (fun x => Real.pi * Real.cot (Real.pi * x)) := by
  sorry  -- from existing cot symmetries in your file

-- Main theorem: equality off integers.
theorem chapter24 (hx : ∀ k : ℤ, x ≠ k) :
    Filter.Tendsto
      (fun N => ∑ k ∈ Finset.range N, cotTerm x k)
      Filter.atTop
      (nhds (Real.pi * Real.cot (Real.pi * x))) := by
  -- Convergence of partial sums to tsum (already known via Summable).
  have h_sum : HasSum (cotTerm x) (partialFraction x) := (cotTerm_summable hx).hasSum
  -- partialFraction x = π·cot(π·x) by HerglotzClass uniqueness.
  have h_eq : partialFraction x = Real.pi * Real.cot (Real.pi * x) := by
    -- Apply herglotz_uniqueness_of_continuous_periodic_odd to the difference
    -- (restricted to Set.Ioo 0 1, then by periodicity extend to ℝ \ ℤ)
    sorry  -- the uniqueness argument
  rw [← h_eq]
  exact h_sum.tendsto_sum_nat

end MainTheorem
```

Each `sorry` is a focused sub-task; total ~150-250 LOC. The hardest piece
is the uniqueness step (uses your existing HerglotzClass machinery + a
ContinuousOn analog).

## If `herglotz_uniqueness_of_continuous_periodic_odd` requires global continuity

You'll need to either:
(a) prove a ContinuousOn variant (~30 LOC), or
(b) do the explicit removable-singularity extension (Path B, +50 LOC).

(a) is cleaner. Open Set.Ioo 0 1 is enough for the uniqueness argument
since periodicity extends it.

Go.
