# `_CHATGPT_DROP_dm1`: Lean 4 denominator proof attempt for `w² = u³ + u² - u`

Requested target:

```lean
theorem rat_curve_den_eq_one
    (u w : ℚ) (hw : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    u.den = 1 := by
  ...
```

## Status

I cannot honestly turn the supplied “no quartic needed” argument into a Lean proof, because the key divisibility step in the `p = -1` branch has the wrong exponent.  The formalized statement that comes out of reduced denominators is

```text
w.den ^ 2 = q ^ 3
```

not

```text
q = w.den ^ 2.
```

That exponent mismatch is exactly where the proposed divisibility contradiction breaks.

## The precise obstruction in the `p = -1` branch

Assume `u.num = -1` and set `q = u.den`.  The equation becomes

```text
w² = (q² + q - 1) / q³.
```

Write `w = a / b` in lowest terms.  Clearing denominators gives

```text
a² q³ = b² (q² + q - 1).        (1)
```

Also

```text
gcd(q, q² + q - 1) = 1,
```

because `q² + q - 1 ≡ -1 (mod q)`.

From (1), coprimality gives both divisibilities

```text
q³ ∣ b²,
b² ∣ q³,
```

hence

```text
b² = q³.                         (2)
```

This is the reduced-denominator uniqueness result that Lean will force.  It does **not** give `q = b²`.  Instead (2) gives `q = d²` and `b = d³` for some natural `d`.

Substituting `q = d²`, `b = d³` into the reduced equation yields the corrected integer equation

```text
a² = d⁴ + d² - 1.                (3)
```

For `d ≥ 2`, (3) is impossible by the elementary consecutive-square bound

```text
d⁴ < d⁴ + d² - 1 < (d² + 1)².
```

So the corrected `p = -1` branch still closes, but it necessarily passes through the small quartic expression `d⁴ + d² - 1` (no descent is needed, just the inequality between consecutive squares).

A Lean-facing helper for this corrected branch would be:

```lean
import Mathlib

lemma no_sq_d4_add_d2_sub_one {a : ℤ} {d : ℕ} (hd : 2 ≤ d) :
    a ^ 2 ≠ (d ^ 4 + d ^ 2 - 1 : ℤ) := by
  intro h
  /-
  Let D : ℤ := (d : ℤ) ^ 2.  Then h says
      a^2 = D^2 + D - 1.
  Since 2 ≤ d, we have 1 < D, hence
      D^2 < a^2 < (D + 1)^2.
  This contradicts the fact that no integer square lies strictly between
  consecutive squares.  One convenient implementation route is:
    * convert to `Nat` using `Int.natAbs`,
    * prove `(D.natAbs)^2 < a.natAbs^2`,
    * prove `a.natAbs^2 < (D.natAbs + 1)^2`,
    * use monotonicity of `Nat.pow`/`Nat.mul_self_lt_mul_self_iff`, then `omega`.
  -/
  omega -- placeholder: the surrounding square-monotonicity facts are the real work
```

The `omega` line is deliberately marked as a placeholder: it will not solve the goal until the square-monotonicity reductions above have been supplied.

## The separate missing step: `p = ±1`

The prompt also says “just show `p = ±1`” from prime divisors of `p.natAbs`.  That step is not derivable from the displayed argument.

Let

```text
p = u.num,
q = u.den,
N = p² + p q - q².
```

For a prime `ℓ ∣ p.natAbs`, reducedness gives `ℓ ∤ q`, and

```text
N ≡ -q² (mod ℓ),
```

so `ℓ ∤ N`.  From the cleared equation, this only forces the `ℓ`-adic valuation of `p` to be even.  Equivalently, it shows that `|p|` is a square; it does **not** rule out `|p| = 4, 9, 16, ...`.  Thus it proves at most

```text
∃ r : ℕ, p.natAbs = r ^ 2,
```

not

```text
p.natAbs = 1.
```

A full Lean proof of `u.den = 1` therefore still needs an additional argument eliminating nontrivial square numerators.  The supplied proof does not contain that argument.

## Minimal corrected roadmap

A sound Lean development should split the work as follows.

```lean
import Mathlib

namespace RatCurveScratch

/-- From the curve equation and reducedness: the denominator of `u` is a square. -/
lemma den_is_square
    (u w : ℚ) (hw : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    ∃ d : ℕ, u.den = d ^ 2 := by
  /-
  Use `Rat.divCasesOn` or `u.num/u.den` and `w.num/w.den`.
  The numerator `p * (p^2 + p*q - q^2)` is coprime to `q`, because
    gcd(p,q)=1
  and
    gcd(q, p^2 + p*q - q^2)=1.
  Therefore the reduced denominator of the RHS is `q^3`; since it equals
  the reduced denominator of `w^2`, it is a square.  Hence `q` is a square.
  -/
  sorry

/-- What the prime-divisor argument actually proves: the numerator has square absolute value. -/
lemma num_abs_is_square
    (u w : ℚ) (hw : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    ∃ r : ℕ, u.num.natAbs = r ^ 2 := by
  /-
  For each prime `ℓ ∣ u.num.natAbs`, reducedness gives `ℓ ∤ u.den`, and
  `p^2 + p*q - q^2 ≡ -q^2 (mod ℓ)`, so `ℓ ∤ N`.  Comparing valuations in
  the square equation shows every exponent in `p.natAbs` is even.
  -/
  sorry

/-- This is the genuinely missing arithmetic input. -/
lemma num_abs_eq_one
    (u w : ℚ) (hw : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    u.num.natAbs = 1 := by
  /-
  Not supplied by the proposed proof.  This is where nontrivial square
  numerators must be eliminated.
  -/
  sorry

lemma p_eq_neg_one_branch_den_one
    (u w : ℚ) (hw : w ^ 2 = u ^ 3 + u ^ 2 - u)
    (hnum : u.num = -1) :
    u.den = 1 := by
  /-
  Correct branch:
    q := u.den.
    RHS reduced denominator gives `w.den^2 = q^3`.
    Hence `q = d^2` and `w.den = d^3`.
    Numerator equality gives `w.num^2 = d^4 + d^2 - 1`.
    If `2 ≤ d`, contradiction by `no_sq_d4_add_d2_sub_one`.
    Therefore `d = 1`, hence `q = 1`.
  -/
  sorry

lemma p_eq_pos_one_branch_den_one
    (u w : ℚ) (hw : w ^ 2 = u ^ 3 + u ^ 2 - u)
    (hnum : u.num = 1) :
    u.den = 1 := by
  /-
  If `q = u.den ≥ 2`, then
      w² = (1 + q - q²) / q³ < 0,
  contradicting `sq_nonneg w`.
  -/
  sorry

/-- Final theorem once the missing numerator lemma is supplied. -/
theorem rat_curve_den_eq_one
    (u w : ℚ) (hw : w ^ 2 = u ^ 3 + u ^ 2 - u) (hu : u ≠ 0) :
    u.den = 1 := by
  have hnum_abs : u.num.natAbs = 1 := num_abs_eq_one u w hw hu
  have hnum_cases : u.num = 1 ∨ u.num = -1 := by
    -- from `Int.natAbs_eq_one.mp hnum_abs`
    exact Int.natAbs_eq_one.mp hnum_abs
  rcases hnum_cases with hpos | hneg
  · exact p_eq_pos_one_branch_den_one u w hw hpos
  · exact p_eq_neg_one_branch_den_one u w hw hneg

end RatCurveScratch
```

## Bottom line

The proposed proof cannot be formalized as stated.  The correct reduced-denominator conclusion in the negative branch is `w.den² = q³`, not `q = w.den²`; and the prime-divisor discussion for `p` proves only that `|p|` is a square, not that `p = ±1`.
