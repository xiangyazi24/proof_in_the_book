# `_CHATGPT_DROP_dm3`: CAS check for the `n = 3` tangent bridge

Request: test the first non-vacuous tangent-bridge case for multiplication by `n`, using `n = 3` rather than `n = 2`.

Curve used here:

```text
E : y^2 = x^3 + x + 1
```

For this short Weierstrass curve,

```text
ψ₂ = 2y
ψ₃ = 3x^4 + 6x^2 + 12x - 1.
```

The calculation below is exact in the quotient by

```text
y^2 = x^3 + x + 1,
ψ₃(x) = 0,
ε^2 = 0.
```

So it is not just a floating-point check; the floating-point branch at the end is only a sanity display.

## Choice of 3-torsion point

Let `α` be a root of

```text
ψ₃(x) = 3x^4 + 6x^2 + 12x - 1,
```

and let

```text
β^2 = α^3 + α + 1.
```

Then `P = (α, β)` is a 3-torsion point, provided `β ≠ 0`.  On this example,

```text
resultant(x^3 + x + 1, 3x^4 + 6x^2 + 12x - 1) = -961,
```

so `x^3 + x + 1` and `ψ₃` have no common root.  Hence `β ≠ 0`, equivalently `ψ₂(P) = 2β ≠ 0`; this is the non-2-torsion side condition.

Take the dual deformation

```text
Pε = (α + ε, β + s ε),       ε^2 = 0,
```

where the curve tangent condition gives

```text
s = (3α^2 + 1) / (2β).
```

Then the input tangent coefficient measured by the invariant differential is

```text
coeffε(input) = 1 / ψ₂(P) = 1 / (2β).
```

The target identity is therefore

```text
coeffε(t([3]Pε)) = 3 / (2β),
```

where, in Jacobian/projective coordinates, the local parameter is

```text
t = -X Z / Y.
```

## Projective formulas used

I used the standard short-Weierstrass Jacobian formulas, with `A = 1`, for coordinates satisfying

```text
x = X / Z^2,
y = Y / Z^3.
```

For doubling:

```text
XX   = X1^2
YY   = Y1^2
YYYY = YY^2
ZZ   = Z1^2
S    = 2 ((X1 + YY)^2 - XX - YYYY)
M    = 3 XX + A ZZ^2
T    = M^2 - 2 S
X3   = T
Y3   = M (S - T) - 8 YYYY
Z3   = (Y1 + Z1)^2 - YY - ZZ
```

For addition:

```text
Z1Z1 = Z1^2
Z2Z2 = Z2^2
U1   = X1 Z2Z2
U2   = X2 Z1Z1
S1   = Y1 Z2 Z2Z2
S2   = Y2 Z1 Z1Z1
H    = U2 - U1
I    = (2H)^2
J    = H I
r    = 2(S2 - S1)
V    = U1 I
X3   = r^2 - J - 2V
Y3   = r(V - X3) - 2 S1 J
Z3   = ((Z1 + Z2)^2 - Z1Z1 - Z2Z2) H
```

Then

```text
[3]Pε = addXYZ(Pε, dblXYZ(Pε)).
```

## Exact Sympy script

```python
import sympy as sp

x, y, e = sp.symbols('x y e')
A = sp.Integer(1)
f = x**3 + x + 1
psi3 = 3*x**4 + 6*x**2 + 12*x - 1
s = (3*x**2 + 1) / (2*y)

def dual(expr):
    """Reduce modulo e^2 = 0.  Here denominators do not contain e."""
    expr = sp.expand(expr)
    return sp.expand(expr.coeff(e, 0) + expr.coeff(e, 1)*e)

def dbl(P):
    X1, Y1, Z1 = P
    XX = dual(X1*X1)
    YY = dual(Y1*Y1)
    YYYY = dual(YY*YY)
    ZZ = dual(Z1*Z1)
    S = dual(2*((X1 + YY)**2 - XX - YYYY))
    M = dual(3*XX + A*ZZ*ZZ)
    T = dual(M*M - 2*S)
    X3 = T
    Y3 = dual(M*(S - T) - 8*YYYY)
    Z3 = dual((Y1 + Z1)**2 - YY - ZZ)
    return tuple(map(dual, (X3, Y3, Z3)))

def add(P, Q):
    X1, Y1, Z1 = P
    X2, Y2, Z2 = Q
    Z1Z1 = dual(Z1*Z1)
    Z2Z2 = dual(Z2*Z2)
    U1 = dual(X1*Z2Z2)
    U2 = dual(X2*Z1Z1)
    S1 = dual(Y1*Z2*Z2Z2)
    S2 = dual(Y2*Z1*Z1Z1)
    H = dual(U2 - U1)
    I = dual((2*H)**2)
    J = dual(H*I)
    r = dual(2*(S2 - S1))
    V = dual(U1*I)
    X3 = dual(r*r - J - 2*V)
    Y3 = dual(r*(V - X3) - 2*S1*J)
    Z3 = dual(((Z1 + Z2)**2 - Z1Z1 - Z2Z2)*H)
    return tuple(map(dual, (X3, Y3, Z3)))

def reduce_num_mod_curve_and_psi3(expr):
    """Return numerator remainder modulo y^2=f and psi3=0."""
    num = sp.factor(sp.together(expr).as_numer_denom()[0])
    rem_y = sp.rem(sp.Poly(num, y), sp.Poly(y**2 - f, y)).as_expr()
    rem_x = sp.rem(
        sp.Poly(rem_y, x, domain=sp.QQ.frac_field(y)),
        sp.Poly(psi3, x, domain=sp.QQ.frac_field(y)),
    ).as_expr()
    return sp.factor(rem_x)

P = (x + e, y + s*e, sp.Integer(1))
R = add(P, dbl(P))
X, Y, Z = R

X0, X1 = X.coeff(e, 0), X.coeff(e, 1)
Y0, Y1 = Y.coeff(e, 0), Y.coeff(e, 1)
Z0, Z1 = Z.coeff(e, 0), Z.coeff(e, 1)

# t = -X Z / Y.  Expand the coefficient in the dual ring.
t0 = sp.simplify(-X0*Z0/Y0)
t1 = sp.simplify(-((X0*Z1 + X1*Z0)/Y0 - X0*Z0*Y1/Y0**2))

assert reduce_num_mod_curve_and_psi3(t0) == 0
assert reduce_num_mod_curve_and_psi3(t1 - sp.Rational(3, 1)/(2*y)) == 0

print('resultant(f, psi3) =', sp.factor(sp.resultant(f, psi3, x)))
print('t0 remainder =', reduce_num_mod_curve_and_psi3(t0))
print('t1 - 3/(2y) remainder =', reduce_num_mod_curve_and_psi3(t1 - sp.Rational(3, 1)/(2*y)))
```

Output:

```text
resultant(f, psi3) = -961
t0 remainder = 0
t1 - 3/(2y) remainder = 0
```

More explicitly, before the final reduction modulo `ψ₃`, the numerator of the constant term of `t([3]Pε)` reduces modulo `y^2 = f(x)` to

```text
(3*x^4 + 6*x^2 + 12*x - 1)
  * (x^9 - 12*x^7 - 96*x^6 + 30*x^5 - 24*x^4
     + 84*x^3 + 48*x^2 + 105*x + 72).
```

Thus the zeroth-order term vanishes at a 3-torsion point.

The numerator of

```text
coeffε(t([3]Pε)) - 3/(2y)
```

reduces modulo `y^2 = f(x)` to

```text
-3 * (3*x^4 + 6*x^2 + 12*x - 1)^4
   * (2*x^9 + 27*x^8 - 24*x^7 - 84*x^6 + 276*x^5
      + 42*x^4 + 600*x^3 + 492*x^2 + 138*x + 147).
```

So the coefficient identity is forced by `ψ₃(x) = 0`.

## Numeric branch sanity check

Taking the real root

```text
α ≈ 0.0801139151812333010788271931286
β = sqrt(α^3 + α + 1) ≈ 1.03953263800065059030165707505
s = (3α^2 + 1)/(2β) ≈ 0.490246617065023614668057473736
```

we get

```text
input coefficient  = 1/(2β)
                   ≈ 0.480985379123504802912309710858

output coefficient = coeffε(t([3]Pε))
                   ≈ 1.44295613737051440873692913257

ratio              = output / input
                   = 3.00000000000000000000000000000
```

## Lean-facing takeaway

For the `n = 3` tangent bridge, the CAS identity has exactly the expected shape:

```text
coeffε(t([3]Pε)) - 3 / ψ₂(P)
```

has numerator divisible by `ψ₃(x)` after reducing by the curve equation.  In this concrete short-Weierstrass example the raw projective-formula expansion even produces a `ψ₃^4` factor for the full dual coefficient expression.

This suggests the formal proof should aim for a numerator-divisibility lemma of the form:

```text
curve_equation(P), ψ₃(x(P)) = 0, ψ₂(P) ≠ 0
  ⊢ coeffε(t(addXYZ Pε (dblXYZ Pε))) = 3 / ψ₂(P).
```

Equivalently, in the general odd-`n` bridge, the proof obligation should be set up so that the difference between the output tangent coefficient and `n / ψ₂(P)` is represented by a numerator containing `preΨ'_n`; for `n = 3`, `preΨ'_3 = Ψ₃`, and the CAS check above confirms the expected identity on a concrete nonsingular short curve.

---

# Q378: reformulating bridge-2 without a `FormalGroup` instance

Request: decide whether bridge-2 can be reformulated so that it does not use

```text
TangentO.nsmul₁ = (n : K)
```

from `formalNsmul_coeff_one`.

The proposed replacement is an order-of-vanishing argument:

```text
preΨ'_n(x) = 0,
φ_n(P) ≠ 0,
[n]P = [φ : ω : 0], ω ≠ 0,
x([n]Q) = φ_n(Q) / ψ_n(Q)^2,
```

then infer that `ψ_n` has a simple zero at `P`, hence that `preΨ'_n` has a simple zero at `x(P)`.

## Verdict

This is a good reformulation target, but the proposed chain is not correct as written.

The corrected statement is:

```text
If [n] is unramified at P, [n]P = O, φ_n(P) ≠ 0, and ψ₂(P) ≠ 0,
then preΨ'_n has a simple root at x(P).
```

Then bridge-2 follows by a purely dual-number calculation:

```text
preΨ'_n(x + δ ε) = preΨ'_n(x) + δ * (preΨ'_n)'(x) ε.
```

If `preΨ'_n(x + δ ε) = 0` and `(preΨ'_n)'(x) ≠ 0`, then `δ = 0`.  Since at a non-2-torsion affine point

```text
δ = ψ₂(P) * τ
```

where `τ` is the invariant tangent coefficient of `Pε`, and `ψ₂(P) ≠ 0`, this gives `τ = 0`.

So yes: bridge-2 can be refactored to avoid mentioning `TangentO.nsmul₁` directly, provided the replacement input is a simple-root/separability lemma for `preΨ'_n`.  But no: the projective nonvanishing facts alone do not prove that simple-root lemma.

## Where the proposed argument breaks

The problematic step is this one:

```text
x([n]P) = φ / ψ² has a SIMPLE pole at P.
```

On an elliptic curve, `x` has a double pole at `O`, not a simple pole.  More importantly, from the formula

```text
x([n]Q) = φ_n(Q) / ψ_n(Q)^2
```

and `φ_n(P) ≠ 0`, all we get is

```text
ord_P(x ∘ [n]) = -2 * ord_P(ψ_n).
```

The nonvanishing of `φ_n(P)` only rules out numerator cancellation.  It does not determine `ord_P(ψ_n)`.

To conclude `ord_P(ψ_n) = 1`, one also needs

```text
ord_P(x ∘ [n]) = -2.
```

That equality is exactly the assertion that `[n]` is unramified at `P`: since `x` has pole order `2` at `O`, pullback by an unramified map keeps the pole order `2`.

Equivalently, using the local parameter

```text
t = -X Z / Y,
```

the projective formula gives near `P`

```text
t([n]Q) = -φ_n(Q) ψ_n(Q) / ω_n(Q),
```

so if `φ_n(P)` and `ω_n(P)` are nonzero, then

```text
ord_P(t ∘ [n]) = ord_P(ψ_n).
```

But to know this order is `1`, one again needs `[n]` to be unramified at `P`.  In the old setup, this is supplied by the formal-group coefficient

```text
coeff₁([n]) = (n : K) ≠ 0.
```

Thus the order argument does not eliminate the mathematical content of `formalNsmul_coeff_one`; it only moves that content into a separability or unramifiedness lemma.

## The part that is correct: translating `ψ_n` order to `preΨ'_n` root multiplicity

The proposed step 5→6 is essentially correct under the stated non-2-torsion hypothesis.

At an affine point,

```text
ω_inv = dx / ψ₂,
```

so if `ψ₂(P) ≠ 0`, then `dx` is nonzero at `P`.  Therefore `x - x(P)` is a local parameter at `P`.  Consequently, for any polynomial `F(X)`,

```text
ord_P(F(x)) = multiplicity of x(P) as a root of F.
```

For odd `n`, `ψ_n` is already a polynomial in `x`, so this applies directly with `F = preΨ'_n = Ψ_n`.

For even `n`, the removed `ψ₂` factor is a unit at a non-2-torsion point, so it does not affect the order:

```text
ord_P(ψ_n) = ord_P(preΨ'_n(x)).
```

Hence

```text
ord_P(ψ_n) = 1
  ↔ multiplicity_x(P)(preΨ'_n) = 1
  ↔ (preΨ'_n)'(x(P)) ≠ 0.
```

This is the clean bridge from geometry on the curve to the derivative test in the `x`-polynomial.

## Non-circular replacement theorem

A non-circular refactor should isolate the real replacement for the formal-group input as one of the following.

### Option A: separability/unramifiedness of multiplication

Use a theorem with content like:

```lean
-- schematic, not current mathlib syntax
lemma nsmul_unramified_at_torsion
    (hn : (n : K) ≠ 0) (hP : IsNonsingular P) :
    UnramifiedAt (fun Q => n • Q) P := by
  -- prove independently of bridge-2
```

Then prove the simple-root theorem:

```lean
-- schematic
lemma prePsiPrime_simple_root_of_non2_torsion
    (hn : (n : K) ≠ 0)
    (hψ : ψ_n(P) = 0)
    (hψ₂ : ψ₂(P) ≠ 0)
    (hφ : φ_n(P) ≠ 0)
    (hunram : UnramifiedAt (fun Q => n • Q) P) :
    (Polynomial.derivative (prePsiPrime n)).eval x(P) ≠ 0 := by
  -- 1. projective formula gives ord_P(x ∘ [n]) = -2 * ord_P(ψ_n)
  -- 2. unramified pullback of the double pole of x at O gives ord_P(x ∘ [n]) = -2
  -- 3. conclude ord_P(ψ_n) = 1
  -- 4. non-2-torsion makes x a local coordinate, so preΨ'_n has root multiplicity 1
```

Then bridge-2 is short:

```lean
-- schematic
lemma bridge2_from_simple_prePsiPrime
    (hdual : evalDual (prePsiPrime n) (x + δ * ε) = 0)
    (hsimple : (Polynomial.derivative (prePsiPrime n)).eval x ≠ 0)
    (hψ₂ : ψ₂(P) ≠ 0)
    (hτ : δ = ψ₂(P) * τ) :
    τ = 0 := by
  -- coeffε of hdual gives δ * (preΨ'_n)'(x) = 0
  -- hsimple gives δ = 0
  -- hψ₂ and hτ give τ = 0
```

This avoids any direct reference to `TangentO.nsmul₁`, but it still uses the equivalent separability fact for `[n]`.

### Option B: an algebraic squarefreeness theorem for division polynomials

Instead of proving unramifiedness of `[n]`, prove directly that `preΨ'_n` is squarefree away from the 2-torsion and discriminant factors:

```lean
-- schematic
lemma prePsiPrime_derivative_nonzero_at_root
    (hn : (n : K) ≠ 0)
    (hroot : (prePsiPrime n).eval x = 0)
    (hnot2 : Ψ₂Sq.eval x ≠ 0)
    (hdisc : Δ ≠ 0) :
    (Polynomial.derivative (prePsiPrime n)).eval x ≠ 0 := by
  -- purely polynomial / gcd / Bezout proof, if available
```

This would genuinely avoid formal groups and even avoid local divisor theory, but it is a substantial algebraic theorem.  It is not a consequence of `φ_n(P) ≠ 0` alone.

## Recommended Lean refactor

The cleanest bridge-2 statement should not mention `coeffε(t([n]Pε))` at all.  It should consume a simple-root lemma:

```text
simple_root_preΨ'_n_at_non2_n_torsion
```

and then use only the dual-number identity

```text
F(x + δ ε) = F(x) + δ F'(x) ε.
```

That makes bridge-2 independent of the projective tangent computation.  The dependency graph becomes:

```text
separability of [n] or squarefreeness of preΨ'_n
        ↓
(preΨ'_n)'(x(P)) ≠ 0
        ↓
preΨ'_n(x + δ ε) = 0 ⇒ δ = 0
        ↓
tangent coefficient τ = δ / ψ₂(P) = 0.
```

This is non-circular if the first line is proved independently of bridge-2.  It is circular if the first line is proved by reusing the desired tangent bridge or by silently asserting that `t ∘ [n]` has nonzero linear coefficient.

## Bottom line

The reformulation is viable, but only after replacing the false/missing “simple pole” step with an explicit independent separability or squarefreeness input.

Projective formula plus `φ_n(P) ≠ 0` proves only “no cancellation.”  The fact that the zero of `ψ_n` has order exactly `1` is the separability of multiplication by `n` at `P`, equivalently the nonzero differential of `[n]`.  Avoiding `FormalGroup` is possible, but the proof still has to pay for that fact somewhere.

---

# Q384: CAS check — simple zeros of `ψ₃` on `y² = x³ + 1`

Request: test whether, in the concrete `n = 3` case, a point with

```text
ψ₃(P) = 0,   φ₃(P) ≠ 0
```

indeed has `ψ₃` vanishing simply at `P`, equivalently whether `preΨ'_3 = Ψ₃` has a simple root at `x(P)`.

## Setup

Use the short Weierstrass curve

```text
E : y² = x³ + 1
```

over characteristic `0`.  For this curve,

```text
ψ₂ = 2y
ψ₃ = 3x⁴ + 12x = 3x(x³ + 4)
preΨ'_3 = Ψ₃ = ψ₃.
```

The roots of `ψ₃` are

```text
x = 0,
```

and the three roots satisfying

```text
x³ = -4.
```

At these roots, the curve has

```text
x = 0       ⇒ y² = 1,
x³ = -4    ⇒ y² = -3.
```

Thus `y ≠ 0` at every such point over an algebraic closure, so `ψ₂(P) = 2y ≠ 0`.  Therefore `x - x(P)` is a local parameter at `P`, and the order of vanishing of `ψ₃` as a function on the curve equals the multiplicity of `x(P)` as a root of the univariate polynomial `ψ₃(x)`.

## Exact Sympy check

Here `φ₃` is computed using

```text
φ₃ = x ψ₃² - ψ₄ ψ₂,
ψ₄ = 4y(x⁶ + 20x³ - 8),
ψ₂ = 2y,
y² = x³ + 1.
```

So on the affine curve,

```text
φ₃ = x ψ₃² - 8(x³ + 1)(x⁶ + 20x³ - 8).
```

```python
import sympy as sp

x = sp.symbols('x')
f = x**3 + 1
psi3 = 3*x**4 + 12*x
dpsi3 = sp.diff(psi3, x)

psi4_factor = x**6 + 20*x**3 - 8
phi3 = sp.expand(x*psi3**2 - 8*f*psi4_factor)

def monic_gcd(a, b):
    return sp.Poly(a, x, domain=sp.QQ).gcd(
        sp.Poly(b, x, domain=sp.QQ)
    ).monic().as_expr()

print('psi3 factor =', sp.factor(psi3))
print('dpsi3 factor =', sp.factor(dpsi3))
print('gcd(psi3,dpsi3) monic =', monic_gcd(psi3, dpsi3))
print('gcd(psi3,f) monic =', monic_gcd(psi3, f))
print('phi3 =', sp.factor(phi3))
print('gcd(psi3,phi3) monic =', monic_gcd(psi3, phi3))
print('phi3 mod psi3 =', sp.factor(sp.rem(sp.Poly(phi3,x), sp.Poly(psi3,x)).as_expr()))
print('dpsi3 at x=0 =', dpsi3.subs(x, 0))
print('dpsi3 at x^3=-4 =', sp.expand(dpsi3.subs(x**3, -4)))
print('phi3 at x=0 =', phi3.subs(x, 0))
print('phi3 at x^3=-4 =', sp.rem(sp.Poly(phi3,x), sp.Poly(x**3+4,x)).as_expr())
print('f at x=0 =', f.subs(x, 0))
print('f at x^3=-4 =', sp.rem(sp.Poly(f,x), sp.Poly(x**3+4,x)).as_expr())
```

Output:

```text
psi3 factor = 3*x*(x**3 + 4)
dpsi3 factor = 12*(x + 1)*(x**2 - x + 1)
gcd(psi3,dpsi3) monic = 1
gcd(psi3,f) monic = 1
phi3 = x**9 - 96*x**6 + 48*x**3 + 64
gcd(psi3,phi3) monic = 1
phi3 mod psi3 = 64*(7*x**3 + 1)
dpsi3 at x=0 = 12
dpsi3 at x^3=-4 = -36
phi3 at x=0 = 64
phi3 at x^3=-4 = -1728
f at x=0 = 1
f at x^3=-4 = -3
```

## Interpretation

The CAS check verifies three separate facts in this example.

First,

```text
gcd(ψ₃, ψ₃') = 1.
```

So every root of `ψ₃` is a simple root of the univariate polynomial.  Explicitly,

```text
ψ₃'(0) = 12 ≠ 0,
ψ₃'(α) = -36 ≠ 0  when α³ = -4.
```

Second,

```text
gcd(ψ₃, x³ + 1) = 1.
```

So no root of `ψ₃` is a 2-torsion `x`-coordinate.  Equivalently, at every point above a root of `ψ₃`, `ψ₂ = 2y` is nonzero, and `x` is a valid local coordinate.

Third,

```text
gcd(ψ₃, φ₃) = 1.
```

So `φ₃(P) ≠ 0` at all points with `ψ₃(P)=0`.  More explicitly,

```text
φ₃(0) = 64,
φ₃(α) = -1728  when α³ = -4.
```

Therefore, for every 3-torsion point `P` on `y² = x³ + 1` with `P ≠ O`,

```text
ord_P(ψ₃) = 1,
mult_{x(P)}(preΨ'_3) = 1,
(preΨ'_3)'(x(P)) ≠ 0.
```

Because `ψ₂(P) ≠ 0`, this order on the curve is exactly the univariate root multiplicity in `x`.

## What this does and does not prove

This is a successful numerical/exact CAS verification of the desired tangent-bridge behavior for `n = 3` on the concrete curve `y² = x³ + 1`.

It does **not** prove the general implication

```text
ψ_n(P)=0 and φ_n(P)≠0  ⇒  ord_P(ψ_n)=1.
```

The reason is the same as in Q378: `φ_n(P)≠0` only proves no numerator cancellation in

```text
x([n]Q) = φ_n(Q) / ψ_n(Q)^2.
```

It does not, by itself, prove that the pullback pole order of `x` along `[n]` is exactly `2`.  That exact pole-order statement is separability/unramifiedness of `[n]` at `P`, or equivalently the squarefreeness of the relevant division polynomial away from the excluded factors.

For this curve and `n = 3`, the CAS proves squarefreeness directly by `gcd(ψ₃, ψ₃') = 1`, so the derivative test succeeds without invoking formal groups.

---

# Q389: additive formal group as a first-order tangent model

Request: use the additive formal group as `W.formalGroup` and prove the tangent bridge.

## Verdict

The useful kernel of the idea is correct:

```text
Every one-dimensional formal group law has F(X,Y) = X + Y + terms of total degree ≥ 2,
so its n-series has linear coefficient n.
```

For tangent-space calculations, the higher-order terms are invisible.  Therefore one may use the additive formal group as a **model for the tangent line**.

However, it is not sound to replace the actual Weierstrass formal group law by the additive formal group if later statements use the full formal group law, not just its first-order truncation.  The Weierstrass formal group and the additive formal group have the same tangent law, but they are not definitionally the same formal group.

So the safe refactor is:

```text
W.actualFormalGroup       -- the true Weierstrass formal group, if needed for higher order facts
TangentO(W) ≃+ K          -- the first-order tangent model via t = -X/Y at O
FormalGroup.𝔾ₐ           -- an abstract model whose n-series has linear coefficient n
```

The missing bridge is not an additive formal group axiom.  It is the geometric statement that the curve's chosen local parameter `t = -X/Y` identifies dual-number deformations at `O` with the coefficient field `K`.

Current mathlib already provides the additive formal group as `FormalGroup.𝔾ₐ`; its definition is `X₀ + X₁`, with the associativity proof done by substitution simplification.  Thus a Lean development should normally alias it rather than rebuild it.

## Complete Lean file for the first-order model

This is the complete Lean-side skeleton for the part that really is formal-group-free.  It deliberately models only the tangent line after the local parameter has already been chosen.  The final geometric lemma tying this model to actual projective dual points is stated below as the remaining project-specific obligation.

```lean
import Mathlib.RingTheory.FormalGroup.Basic

noncomputable section

namespace Q389

/-- The additive formal group.  Mathlib already proves the formal-group axioms. -/
abbrev additiveFormalGroup (K : Type*) [CommRing K] : FormalGroup K :=
  FormalGroup.𝔾ₐ (R := K)

variable (K : Type*) [Field K]

/--
The tangent line at `O` after choosing the local coordinate `t = -X/Y`.
This is not the full curve, only its first-order model.
-/
abbrev TangentO : Type _ := K

/--
The bridge from the curve tangent coordinate to the scalar coefficient.
After choosing `t`, this is just the identity additive equivalence.
-/
def tangentBridge (W : Type*) : TangentO K ≃+ K :=
  AddEquiv.refl K

@[simp]
theorem tangentBridge_apply (W : Type*) (τ : TangentO K) :
    tangentBridge (K := K) W τ = τ :=
  rfl

/-- The additive tangent model has scalar `n` as the differential of `[n]`. -/
theorem tangentBridge_nsmul (W : Type*) (n : ℕ) (τ : TangentO K) :
    tangentBridge (K := K) W (n • τ) =
      (n : K) * tangentBridge (K := K) W τ := by
  simp [tangentBridge, TangentO, nsmul_eq_mul]

end Q389
```

If the project has the theorem named exactly as in the prompt, the additive-formal-group coefficient statement should be a one-line wrapper:

```lean
-- project-local theorem, schematic because this name is not in current Mathlib.Basic
example (K : Type*) [Field K] (n : ℕ) :
    formalNsmul_coeff_one (additiveFormalGroup K) n = (n : K) := by
  simpa [additiveFormalGroup] using
    formalNsmul_coeff_one (F := additiveFormalGroup K) n
```

In current mathlib's `FormalGroup.Basic`, `FormalGroup.𝔾ₐ` exists, but the file only gives the basic formal group structure and an additive operation on `FormalGroup.Point`; it even has a TODO for `Zero`, `SMul`, and `Inv` instances on points.  So the exact theorem `formalNsmul_coeff_one` must be project-local or from a later file, not from this basic API.

## The missing project-specific bridge

The actual curve bridge should be isolated as a theorem about the projective local parameter, not about formal groups:

```lean
-- schematic: names depend on the project's curve and dual-number API
lemma tangentCoeff_eq_t_coeff_at_O
    (W : WeierstrassCurve K)
    (Pε : DualPointAtO W K)
    (τ : K)
    (hτ : coeffε ((-Pε.X) / Pε.Y) = τ) :
    Q389.tangentBridge (K := K) W τ = τ := by
  rfl
```

Or, for the multiplication map:

```lean
-- schematic: this is the real tangent bridge to prove from projective formulas
lemma coeff_t_nsmul_at_O
    (W : WeierstrassCurve K) (n : ℕ) (τ : K)
    (hn : (n : K) ≠ 0) :
    coeffε (t ([n] (O + τ ε))) = (n : K) * τ := by
  -- prove by expanding the projective addition/multiplication formula to first order
  -- after this lemma, no full Weierstrass formal group law is needed
  sorry
```

That final `sorry` is the real mathematical content.  It cannot be obtained by merely declaring `W.formalGroup = FormalGroup.𝔾ₐ`; it must say that the curve's group law, expressed in the chosen local parameter `t`, has first-order addition law.

## Bottom line

Use `FormalGroup.𝔾ₐ` as the first-order tangent model, not as the actual Weierstrass formal group.

The 50-line Lean file above gives the additive model and the identity tangent bridge once the local coordinate has been chosen.  The remaining theorem is exactly the coordinate-compatibility lemma:

```text
dual deformation at O with t-coefficient τ  ↔  tangent scalar τ.
```

Once that lemma is proved from the projective formulas, the differential of multiplication is multiplication by `(n : K)`, without needing the full Weierstrass formal group law.
