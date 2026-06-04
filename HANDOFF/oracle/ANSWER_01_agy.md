# ANSWER_01_agy

Key API facts I confirmed:
- `Polynomial.Chebyshev.T R n` takes `n : ℤ`, not `ℕ`. So `T ℝ q` for `q : ℕ` requires casting `q : ℤ`.
- `T_add_two : ∀ n : ℤ, T R (n + 2) = 2 * X * T R (n + 1) - T R n`
- `T_real_cos (θ : ℝ) (n : ℕ) : Real.cos (n * θ) = (T ℝ (n : ℤ)).eval (Real.cos θ)` — exists in
  `Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev.lean`. Use it directly.

Your recurrence `2 * a(q+1) - 9 * a(q)` is **correct** (I gave you the wrong coefficient `6` in the
dispatch — apologies). Re-derivation:
T_{n+2}(x) = 2x T_{n+1}(x) - T_n(x)
At x = 1/3, multiply by 3^{n+2}:
  3^{n+2} T_{n+2}(1/3) = (2/3) · 3^{n+2} · T_{n+1}(1/3) - 3^{n+2} · T_n(1/3)
                       = 2 · 3^{n+1} · T_{n+1}(1/3) - 9 · 3^n · T_n(1/3)
                       = 2 · a(n+1) - 9 · a(n)  ✓

Your `a_zmod_3` is OK structurally. Note: a(0) = a(1) = 1 mod 3; a(2) = 2 · 1 − 9 · 1 = −7 ≡ 2 mod 3;
a(3) = 2 · (−7) − 9 · 1 = −23 ≡ 1 mod 3; alternates between {1, 2} mod 3 (never 0).

## Fix for `a_eq_T`

The cast pain comes from `T ℝ ↑(q + 1)` vs `T ℝ (↑q + 1)`. Solution: use strong induction on `ℕ`
and bridge via an explicit cast lemma.

```lean
lemma a_eq_T (q : ℕ) :
    (a q : ℝ) = (3 : ℝ)^q * (T ℝ (q : ℤ)).eval (1/3) := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    match q with
    | 0 =>
      simp [a, show ((0 : ℕ) : ℤ) = 0 from rfl, T_zero, eval_one]
    | 1 =>
      simp [a, show ((1 : ℕ) : ℤ) = 1 from rfl, T_one, eval_X]
      norm_num
    | q + 2 =>
      have ih_q  : (a q : ℝ) = (3 : ℝ)^q * (T ℝ (q : ℤ)).eval (1/3) := ih q (by omega)
      have ih_q1 : (a (q+1) : ℝ) = (3 : ℝ)^(q+1) * (T ℝ ((q+1 : ℕ) : ℤ)).eval (1/3) :=
        ih (q+1) (by omega)
      -- Rewrite the Chebyshev recurrence at the integer index.
      have hcast : ((q + 2 : ℕ) : ℤ) = (q : ℤ) + 2 := by push_cast; ring
      have hT :
          (T ℝ ((q + 2 : ℕ) : ℤ)).eval (1/3 : ℝ) =
            2 * (1/3) * (T ℝ ((q+1 : ℕ) : ℤ)).eval (1/3) -
              (T ℝ ((q : ℕ) : ℤ)).eval (1/3) := by
        rw [hcast, T_add_two]
        have hcast1 : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; ring
        rw [hcast1]
        simp [eval_sub, eval_mul, eval_X]
      -- Unfold `a (q+2)` and substitute.
      show ((a (q + 2) : ℤ) : ℝ) = (3 : ℝ)^(q+2) * (T ℝ ((q+2 : ℕ) : ℤ)).eval (1/3)
      have ha_rec : a (q + 2) = 2 * a (q + 1) - 9 * a q := rfl
      rw [ha_rec, hT]
      push_cast
      rw [ih_q, ih_q1]
      ring
```

If `Nat.strong_induction_on` argument shape is wrong on your Mathlib snapshot, try
`Nat.strong_induction` or `Nat.strongRecOn`. The key idea is identical.

## Fix for `arccos_one_third_irrational_over_pi`

Strategy:
1. `arccos(1/3) > 0` rules out `q = 0`.
2. From `arccos(1/3) = q * π`, multiply by `q.den` to get `q.den * arccos(1/3) = q.num * π`.
3. Take `cos` of both sides:
   - LHS = `cos(q.den * arccos(1/3)) = T_{q.den}(1/3)` by `T_real_cos`.
   - RHS = `cos(q.num * π) = (-1)^q.num.natAbs` (sign-aware).
4. So `3^{q.den} * T_{q.den}(1/3) = ± 3^{q.den}`, i.e., `(a q.den : ℤ) = ± 3^{q.den}`.
5. `q.den ≥ 1`, so `3 ∣ 3^{q.den}`, hence `(a q.den : ZMod 3) = 0`.
6. Contradicts `a_zmod_3 q.den`, which says it's `1` or `2`.

```lean
theorem arccos_one_third_irrational_over_pi (q : ℚ) :
    Real.arccos (1/3) ≠ q * Real.pi := by
  intro h
  -- (1) arccos(1/3) > 0
  have h_pos : 0 < Real.arccos (1/3) := by
    apply Real.arccos_pos.mpr
    constructor <;> norm_num
  -- (2) q ≠ 0 (q = 0 ⇒ arccos(1/3) = 0, contradicting h_pos)
  rcases eq_or_ne q 0 with hq | hq
  · rw [hq] at h; simp at h; linarith
  -- (3) Multiply by q.den
  have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have h_int : (q.den : ℝ) * Real.arccos (1/3) = (q.num : ℝ) * Real.pi := by
    have hq_eq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      rw [Rat.cast_def]
    rw [h, hq_eq]
    field_simp
    ring
  -- (4) cos(q.den * arccos(1/3)) = T_{q.den}(1/3) via T_real_cos
  have h_cos_lhs :
      Real.cos ((q.den : ℕ) * Real.arccos (1/3)) =
        (T ℝ ((q.den : ℕ) : ℤ)).eval (1/3) := by
    have hcos_arccos : Real.cos (Real.arccos (1/3)) = 1/3 := by
      rw [Real.cos_arccos] <;> norm_num
    rw [← hcos_arccos]
    exact T_real_cos (Real.arccos (1/3)) q.den
  -- (5) cos(q.num * π) = (-1)^q.num.natAbs
  -- LHS of h_int divided/promoted: cos((q.den : ℝ) * arccos(1/3)) = cos((q.num : ℝ) * π)
  have h_cos_eq : Real.cos ((q.den : ℝ) * Real.arccos (1/3)) =
                  Real.cos ((q.num : ℝ) * Real.pi) := by
    rw [h_int]
  have h_cos_rhs : Real.cos ((q.num : ℝ) * Real.pi) = (-1 : ℝ)^q.num.natAbs := by
    rw [show (q.num : ℝ) * Real.pi = ((q.num : ℤ) : ℝ) * Real.pi from by push_cast; ring]
    -- Use Mathlib: Real.cos_int_mul_pi gives cos(n * π) = (-1)^n.natAbs (or n.negOnePow as ℝ).
    -- Lemma name: `Real.cos_int_mul_pi`
    rw [Real.cos_int_mul_pi]
    rcases q.num.even_or_odd with he | ho
    · rw [Int.negOnePow_eq_one_iff_even.mpr he]
      have : Even q.num.natAbs := by
        rwa [Int.natAbs_even]
      rw [Even.neg_one_pow this]
    · rw [Int.negOnePow_eq_neg_one_iff_odd.mpr ho]
      have : Odd q.num.natAbs := by
        rwa [Int.natAbs_odd]
      rw [Odd.neg_one_pow this]
  -- Combine: T_{q.den}(1/3) = ± 1
  have h_T_eval : (T ℝ ((q.den : ℕ) : ℤ)).eval (1/3) = (-1 : ℝ)^q.num.natAbs := by
    rw [← h_cos_lhs]
    have hpush : ((q.den : ℕ) : ℝ) = (q.den : ℝ) := by push_cast; rfl
    rw [hpush]
    rw [h_cos_eq, h_cos_rhs]
  -- (6) Hence a q.den = ± 3^q.den
  have h_a_eq : (a q.den : ℝ) = (3 : ℝ)^q.den * (-1)^q.num.natAbs := by
    rw [a_eq_T q.den, h_T_eval]
  -- (7) Mod 3: a q.den ≡ 0 mod 3 since 3 ∣ 3^q.den (q.den ≥ 1)
  have h_den_pos : 1 ≤ q.den := q.pos
  have h_a_zmod : (a q.den : ZMod 3) = 0 := by
    have h_int_eq : a q.den = 3^q.den * (-1)^q.num.natAbs ∨
                    a q.den = -(3^q.den * 1) := by
      -- a q.den is an integer equal to ± 3^q.den
      rcases Nat.even_or_odd q.num.natAbs with he | ho
      · left
        have : (-1 : ℝ)^q.num.natAbs = 1 := by
          rw [Even.neg_one_pow he]
        rw [this, mul_one] at h_a_eq
        -- (a q.den : ℝ) = (3 : ℝ)^q.den, hence (in ℤ) a q.den = 3^q.den.
        have : ((a q.den : ℤ) : ℝ) = ((3^q.den : ℕ) : ℝ) := by
          rw [h_a_eq]; push_cast; ring
        exact_mod_cast this
      · right
        have : (-1 : ℝ)^q.num.natAbs = -1 := by
          rw [Odd.neg_one_pow ho]
        rw [this, mul_neg_one] at h_a_eq
        have : ((a q.den : ℤ) : ℝ) = -((3^q.den : ℕ) : ℝ) := by
          rw [h_a_eq]; push_cast; ring
        exact_mod_cast this
    -- 3 | 3^q.den for q.den ≥ 1
    rcases h_int_eq with heven | hodd
    · rw [heven]
      push_cast
      have : ((3 : ℤ)^q.den : ZMod 3) = 0 := by
        have : (3 : ZMod 3) = 0 := by decide
        rw [show ((3 : ℤ)^q.den : ZMod 3) = (3 : ZMod 3)^q.den from by push_cast; rfl, this]
        exact zero_pow (by omega)
      rw [show ((3 : ℕ)^q.den : ZMod 3) = ((3 : ℤ)^q.den : ZMod 3) from by push_cast; rfl]
      rw [this]
      ring
    · rw [hodd]
      push_cast
      have : ((3 : ℤ)^q.den : ZMod 3) = 0 := by
        have h3 : (3 : ZMod 3) = 0 := by decide
        have : ((3 : ℤ)^q.den : ZMod 3) = (3 : ZMod 3)^q.den := by push_cast; rfl
        rw [this, h3]; exact zero_pow (by omega)
      rw [show ((3 : ℕ)^q.den * 1 : ℤ) = (3 : ℤ)^q.den * 1 from by push_cast; ring]
      simp [this]
  -- (8) Contradiction with a_zmod_3
  rcases a_zmod_3 q.den with h1 | h2
  · rw [h_a_zmod] at h1; exact absurd h1 (by decide)
  · rw [h_a_zmod] at h2; exact absurd h2 (by decide)
```

## Critical notes

1. **The `h_cos_rhs` block is the most fragile** — Mathlib's `Real.cos_int_mul_pi` returns
   `Int.negOnePow n` (a `Units ℤ` or similar). I split into even/odd cases to coerce to `ℝ`.
   If that lemma is named differently in your snapshot (e.g. `Real.cos_int_mul_pi_eq` or just
   computed via `Real.cos_nat_mul_pi` after splitting on sign of `q.num`), grep first and adapt.

2. **The `h_a_zmod` block has redundant pushcast/simp** — depending on whether `(3 : ℕ)` or
   `(3 : ℤ)` is the working type at that point. If `decide` is too slow, replace
   `(3 : ZMod 3) = 0` with the explicit `show (3 : ZMod 3) = 0 from rfl` after checking.

3. **If Mathlib lacks `Real.arccos_pos`** in your snapshot: replace with the calculation
   `Real.arccos (1/3) ≠ 0` via `Real.arccos_eq_zero_iff` and `(1/3) ≠ 1`.

4. **`Nat.strong_induction_on` syntax** has changed across Mathlib versions. Alternatives:
   `Nat.strongRecOn`, `Nat.strong_induction` (no `_on`), or just `induction' q using
   Nat.strong_induction_on with q ih`.

5. **Remote build remains your judge.** Don't trust this file as-is — iterate with
   `bash ~/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book --file ProofsInTheBook/Chapter09.lean`
   and fix individual lemma-name mismatches. The math is correct; only the API names are at risk.

Good luck.
