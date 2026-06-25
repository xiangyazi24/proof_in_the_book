# Q420 — CAS verification of `dblXYZ` near `O`

Question: over `K[ε]/(ε²)`, does Mathlib's raw Jacobian `dblXYZ` at a first-order representative near `O` give `d[2]=2`, or does it degenerate to the zero representative?

## Verdict

The CAS check **does not confirm** the proposed zero-representative conclusion as stated.

The computation reveals a coordinate mismatch:

* Mathlib's `Jacobian` coordinates are weighted `(2,3,1)` coordinates with affine interpretation

  ```text
  x_aff = X/Z²,
  y_aff = Y/Z³.
  ```

* The `(2,3,1)`-homogeneous equation is

  ```text
  Y² + a₁XYZ + a₃YZ³ = X³ + a₂X²Z² + a₄XZ⁴ + a₆Z⁶.
  ```

* At `Z=0`, this gives

  ```text
  Y² = X³.
  ```

  Therefore the Mathlib point at infinity is represented by `[1:1:0]` up to weighted scaling, not by `[0:1:0]`.

Consequences:

```text
[εa : 1 : 0]
```

is not a valid first-order Jacobian point near `O` in Mathlib's coordinate system: it violates `Y²=X³` at `Z=0` because `1 ≠ (εa)³ = 0` in dual numbers.

Using the exact Mathlib formulas anyway, the raw output is not `[0:0:0]`; it is

```text
dblXYZ([εa, 1, 0]) = [-8εa, -8, 0].
```

Likewise,

```text
dblXYZ([εa, -1, 0]) = [-8εa, -8, 0].
```

These are not meaningful tangent computations because the inputs are not on the Mathlib Jacobian curve.

With the correct first-order Mathlib Jacobian chart near `O`, namely

```text
Pε = [1 + Aε : 1 + Bε : βε],
```

subject to the curve equation to first order

```text
2B + a₁β - 3A = 0,
```

Mathlib's `dblXYZ` gives

```text
dblZ(Pε) = 2βε,
```

and the Jacobian local parameter

```text
t = -X·Z/Y
```

satisfies

```text
t(Pε)       = -βε,
t(dblXYZ Pε) = -2βε = 2 · t(Pε).
```

So raw `dblXYZ` **does** see `d[2]=2` in the correct Mathlib Jacobian chart, at least for the doubling map at `O`.

The broader design warning remains valid: raw homogeneous/Jacobian formulas are dangerous over dual numbers if the representative is in the wrong chart or if the formula has a nilpotent common factor.  But the specific claim that Mathlib `dblXYZ([εa:1:0])` gives the zero representative is false.

---

## Mathlib formulas used

Mathlib defines

```lean
def negY (P : Fin 3 → R) : R :=
  -P y - W'.a₁ * P x * P z - W'.a₃ * P z ^ 3

def dblZ (P : Fin 3 → R) : R :=
  P z * (P y - W'.negY P)
```

and

```lean
noncomputable def dblX (P : Fin 3 → R) : R :=
  W'.dblU P ^ 2
    - W'.a₁ * W'.dblU P * P z * (P y - W'.negY P)
    - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2
    - 2 * P x * (P y - W'.negY P) ^ 2
```

where

```lean
noncomputable def dblU (P : Fin 3 → R) : R :=
  eval P W'.polynomialX
```

and

```lean
noncomputable def dblY (P : Fin 3 → R) : R :=
  W'.negY ![W'.dblX P, W'.negDblY P, W'.dblZ P]

noncomputable def dblXYZ (P : Fin 3 → R) : Fin 3 → R :=
  ![W'.dblX P, W'.dblY P, W'.dblZ P]
```

The key exact formula for `Z` is therefore:

```text
dblZ(P) = P[2] · (P[1] - negY(P)).
```

---

## CAS script

This script works in `K[ε]/(ε²)`, implements the Mathlib formulas above, and reduces all expressions modulo `ε²=0`.

```python
import sympy as sp

ε, A, B, β, a = sp.symbols('e A B beta a')
a1, a2, a3, a4, a6 = sp.symbols('a1 a2 a3 a4 a6')

mod = sp.Poly(ε**2, ε)

def red(expr):
    return sp.rem(sp.Poly(sp.expand(expr), ε), mod).as_expr()

def negY(X, Y, Z):
    return -Y - a1*X*Z - a3*Z**3

def dblU(X, Y, Z):
    return a1*Y*Z - (3*X**2 + 2*a2*X*Z**2 + a4*Z**4)

def dblZ(X, Y, Z):
    return Z*(Y - negY(X, Y, Z))

def dblX(X, Y, Z):
    U = dblU(X, Y, Z)
    D = Y - negY(X, Y, Z)
    return U**2 - a1*U*Z*D - a2*Z**2*D**2 - 2*X*D**2

def negDblY(X, Y, Z):
    U = dblU(X, Y, Z)
    D = Y - negY(X, Y, Z)
    X2 = dblX(X, Y, Z)
    return -U*(X2 - X*D**2) + Y*D**3

def dblY(X, Y, Z):
    return negY(dblX(X, Y, Z), negDblY(X, Y, Z), dblZ(X, Y, Z))

def dblXYZ(X, Y, Z):
    return tuple(red(c) for c in (dblX(X,Y,Z), dblY(X,Y,Z), dblZ(X,Y,Z)))

def dual_series(expr):
    return sp.series(expr, ε, 0, 2).removeO()

# The two proposed Z=0 representatives.
print('dblXYZ([εa, 1, 0])  =', dblXYZ(ε*a, 1, 0))
print('dblXYZ([εa,-1, 0])  =', dblXYZ(ε*a, -1, 0))

# Correct Mathlib Jacobian near-O chart.
P = (1 + A*ε, 1 + B*ε, β*ε)
X2, Y2, Z2 = dblXYZ(*P)
print('dblXYZ([1+Aε,1+Bε,βε]) =', (X2, Y2, Z2))

# Local parameter in Mathlib Jacobian coordinates.
tP = red(dual_series(-(1 + A*ε)*(β*ε)/(1 + B*ε)))
t2P = red(dual_series(-X2*Z2/Y2))
print('t(P)      =', tP)
print('t(dbl P)  =', t2P)
print('t(dbl P) - 2*t(P) =', red(t2P - 2*tP))

# First-order curve equation for P=[1+Aε,1+Bε,βε].
curve_eq = (1+B*ε)**2 + a1*(1+A*ε)*(1+B*ε)*(β*ε) + a3*(1+B*ε)*(β*ε)**3 \
    - ((1+A*ε)**3 + a2*(1+A*ε)**2*(β*ε)**2 + a4*(1+A*ε)*(β*ε)**4 + a6*(β*ε)**6)
print('curve equation remainder =', red(curve_eq))
```

Output:

```text
dblXYZ([εa, 1, 0])  = (-8*a*e, -8, 0)
dblXYZ([εa,-1, 0])  = (-8*a*e, -8, 0)
dblXYZ([1+Aε,1+Bε,βε]) =
  (1 + e*(28*A - 8*a1*beta - 16*B),
   1 + e*(-54*A + 19*a1*beta + 40*B),
   2*beta*e)
t(P)      = -beta*e
t(dbl P)  = -2*beta*e
t(dbl P) - 2*t(P) = 0
curve equation remainder = e*(-3*A + a1*beta + 2*B)
```

---

## Interpretation

### 1. `[εa:1:0]` is not the right test point

The proposed representative `[εa:1:0]` reduces to `[0:1:0]`, which is the ordinary homogeneous point at infinity, but not the Mathlib Jacobian point at infinity.  In Mathlib Jacobian coordinates, the `Z=0` locus on the curve satisfies `Y²=X³`; the nonsingular point at infinity is represented by `[1:1:0]`.

Therefore the expression

```text
dblXYZ([εa,1,0])
```

is only a raw polynomial evaluation at a non-curve triple.  It does not test the differential of doubling on the curve.

### 2. Raw `dblXYZ` does not return the zero representative on this input

Even as a raw polynomial evaluation, it gives

```text
[-8εa, -8, 0],
```

not `[0,0,0]`.

The earlier calculation that used only

```text
dblZ = Z·(Y-negY)
```

correctly found `dblZ=0`, but `dblX` and `dblY` are not zero unless `X=0` in a stronger sense.  Over dual numbers, `X=εa` still contributes linearly to `dblX`.

### 3. The correct Mathlib Jacobian near-`O` chart verifies `d[2]=2`

Using

```text
Pε = [1+Aε : 1+Bε : βε],
```

and the local parameter

```text
t = -X·Z/Y,
```

the raw Mathlib doubling formulas give

```text
t(dblXYZ(Pε)) = 2 · t(Pε)
```

modulo `ε²`.  This calculation is independent of the curve-equation linear constraint

```text
-3A + a₁β + 2B = 0.
```

Thus the direct doubling calculation **does** prove the expected first-order `d[2]=2` behavior in the correct chart.

### 4. This does not solve general `d[n]=n`

The doubling calculation alone can plausibly prove powers of two by repeated normalized doubling.  It does not prove arbitrary `n`, because one still needs a reliable first-order addition formula for two near-`O` points:

```text
coeffε(t(A ⊕ B)) = coeffε(t(A)) + coeffε(t(B)).
```

Raw `addXYZ` may still suffer from a saturation/common-factor problem over dual numbers when both inputs are near `O`.  That issue is distinct from the corrected `dblXYZ` calculation.

---

## Design conclusion

The conclusion should be revised as follows.

Incorrect:

```text
Mathlib dblXYZ at O necessarily degenerates and cannot see d[2]=2.
```

Correct:

```text
Mathlib dblXYZ sees d[2]=2 in the correct Jacobian near-O chart [1+O(ε):1+O(ε):O(ε)].
```

Still correct:

```text
The full formal group law should not be built by naively evaluating raw homogeneous addXYZ/dblXYZ on arbitrary O-representatives over dual numbers.
```

For the full tangent bridge, the project still needs one of:

```text
1. a normalized local (t,w)-coordinate addition proof;
2. a saturated/renormalized addXYZ-near-O lemma;
3. the invariant-differential/projective identity from Q401;
4. the full W.formalGroup construction.
```

The `w(t)` power-series construction is still the safest canonical route for the full formal group law, but Q420 shows it is **not** necessary merely to verify `d[2]=2` for `dblXYZ`.
