# ANSWER_03_04 — Use `zify` to escape ℕ subtraction

## The fix: cast to ℤ

The ℕ subtraction `k * k - k + 2` is the only obstacle. `nlinarith` works
beautifully in ℤ. `zify` lifts the goal cleanly when you supply the
non-truncation hypothesis `k ≤ k * k`.

```lean
example (k : ℕ) (hk : 4 ≤ k) : k * k < 4 * (k * k - k + 2) := by
  have h_no_trunc : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
  zify [h_no_trunc]
  -- Goal is now in ℤ: (k:ℤ)*k < 4*((k:ℤ)*k - k + 2)
  -- ⇔ 3*k² - 4*k + 8 > 0, which nlinarith handles via sq_nonneg.
  nlinarith [sq_nonneg ((k : ℤ) - 2), hk]
```

`sq_nonneg ((k : ℤ) - 2)` gives `(k - 2)² ≥ 0`, i.e., `k² - 4k + 4 ≥ 0`,
i.e., `k² ≥ 4k - 4`. Then `3k² - 4k + 8 ≥ 3(4k - 4) - 4k + 8 = 8k - 4`,
positive for k ≥ 1. `nlinarith` chains this.

If `nlinarith` is still slow:

```lean
example (k : ℕ) (hk : 4 ≤ k) : k * k < 4 * (k * k - k + 2) := by
  have h_no_trunc : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
  zify [h_no_trunc]
  have hk_z : (4 : ℤ) ≤ k := by exact_mod_cast hk
  have hsq : ((k : ℤ) - 2)^2 ≥ 0 := sq_nonneg _
  nlinarith [hsq, hk_z]
```

## Why `omega` and `nlinarith` fail without `zify`

- `omega` is linear arithmetic; `k * k` (nonlinear) is opaque to it.
- `nlinarith` in ℕ deals badly with ℕ-subtraction (`k * k - k` might
  truncate to 0 if elaborated wrong; the hypothesis `k ≤ k * k` doesn't
  always get applied).

`zify` rewrites all ℕ-subtractions in the goal to ℤ-subtractions
provided non-truncation hypotheses are supplied. Once in ℤ, `nlinarith`
has full polynomial inequality reasoning.

## If `zify` complains about other terms

Add more `[le_hyp]`s to its argument list:

```lean
zify [h_no_trunc, ...other ≤ hypotheses for any ℕ subtraction in goal...]
```

## Standalone snippet to test

```lean
example : 4 * 4 < 4 * (4 * 4 - 4 + 2) := by decide  -- k = 4 case (56 > 16 ✓)
example (k : ℕ) (hk : 4 ≤ k) : k * k < 4 * (k * k - k + 2) := by
  have h_no_trunc : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
  zify [h_no_trunc]
  nlinarith [sq_nonneg ((k : ℤ) - 2), hk]
```

Drop this in. Should compile in seconds.

## Generalization

For any "ℕ goal with polynomial inequalities + subtractions": `zify`
then `nlinarith` with `sq_nonneg` hints. This is the standard Lean 4
idiom; don't try to grind in ℕ directly.

Go.
