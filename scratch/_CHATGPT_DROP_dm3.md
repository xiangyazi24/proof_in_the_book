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
