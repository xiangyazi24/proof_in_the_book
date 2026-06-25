# Q434 — `addXYZ` normalization for the formal group law

Question: for

```text
P(t) = [u(t), -u(t)^2, t · u(t)]
```

in Mathlib Jacobian `(2,3,1)` coordinates, with `u(t) ∈ K⟦t⟧` and `u(0)=1`, does

```text
addXYZ(P(t₁), P(t₂)) = [A,B,C]
```

directly give a formal group law by

```text
F = -A·C/B,
```

or does the same `Z=0` degeneracy force a normalization/factorization step?  Also: does Mathlib `addXYZ` compute `P+Q` or `P-Q`?

## Verdict

Mathlib `Jacobian.addXYZ` computes **`P + Q`**, not `P - Q`.

The factor `t₂ - t₁` in `addZ(P(t₁), P(t₂))` is not evidence for `P-Q`.  It is the diagonal/slope-denominator factor of the projective addition formula: raw `addXYZ` is the distinct-points addition formula, and Mathlib explicitly says it returns `![0,0,0]` when the two representatives are equal.

The raw triple `[A,B,C]` does **not** directly give a power-series ratio `F = -A·C/B`, because `B` is not a unit.  At `(t₁,t₂)=(0,0)`, all coordinates vanish.  The correct construction is the **saturated / normalized** one:

```text
D := t₁ - t₂,
A = D² · A',
B = D³ · B',
C = D · C',
F := -A' · C' / B'.
```

Then `B'` is a unit.  In the leading model `u=1`,

```text
A' = 1,
B' = 1,
C' = -(t₁+t₂),
F = t₁+t₂.
```

So the expected formal group linear term is recovered after weighted saturation.

The right Lean target is not raw `F=-A*C/B`; it is:

```lean
-- schematic
D := X₀ - X₁
A' := A / D^2
B' := B / D^3
C' := C / D
F  := -A' * C' * (B')⁻¹
```

with proofs that the divisions are valid in `K⟦t₁,t₂⟧` and that `B'` is a unit.

---

## Mathlib convention: `addXYZ` is `P + Q`

Mathlib's documentation for Jacobian coordinates says the addition formulae are for representatives of `P + Q`, and `addXYZ` is defined as:

```lean
noncomputable def addXYZ (P Q : Fin 3 → R) : Fin 3 → R :=
  ![W'.addX P Q, W'.addY P Q, addZ P Q]
```

with the docstring:

```text
The coordinates of a representative of P + Q for two distinct Jacobian point
representatives P and Q on a Weierstrass curve.
If the representatives of P and Q are equal, then this returns ![0, 0, 0].
```

The `Z` coordinate is exactly:

```lean
def addZ (P Q : Fin 3 → R) : R :=
  P x * Q z ^ 2 - Q x * P z ^ 2
```

Mathlib also proves, when `Z` is nonzero and `x(P)≠x(Q)`, that

```lean
W.addXYZ P Q = addZ P Q • ![affine_addX, affine_addY, 1]
```

where the affine formula uses the usual secant slope.  This is the addition formula, not subtraction.

---

## Direct computation of `addZ`

Let

```text
P₁ = P(t₁) = [u₁, -u₁², t₁u₁],
P₂ = P(t₂) = [u₂, -u₂², t₂u₂].
```

Then Mathlib's `addZ` gives:

```text
C = addZ(P₁,P₂)
  = u₁ · (t₂u₂)² - u₂ · (t₁u₁)²
  = u₁u₂ · (t₂²u₂ - t₁²u₁).
```

Since `u(t)` is a one-variable power series, the two-variable series

```text
g(t₂) - g(t₁),   where g(t) := t²u(t),
```

is divisible by `t₂-t₁` or equivalently by `D=t₁-t₂`.  Its quotient has leading term `-(t₁+t₂)` for `D=t₁-t₂`:

```text
t₂²u₂ - t₁²u₁ = -(t₁-t₂) · (t₁+t₂+O(2)).
```

Therefore:

```text
C = D · C',
C' = -u₁u₂ · (t₁+t₂+O(2)).
```

The residual factor `C'` has the correct leading behavior for the output `Z` coordinate near `O`: it is order `1` and begins with `-(t₁+t₂)` in the `D=t₁-t₂` normalization.

---

## Why the raw denominator `B` is not a unit

At `t₁=t₂=0`,

```text
P(0) = [1,-1,0],
```

which is the Mathlib point at infinity up to weighted scaling by `-1` from `[1,1,0]`.

The raw distinct-points formula is not meant to handle `P=Q`.  Mathlib has:

```lean
lemma addXYZ_self {P : Fin 3 → R} (hP : W'.Equation P) :
    W'.addXYZ P P = ![0, 0, 0]
```

So at `(t₁,t₂)=(0,0)`, raw `addXYZ(P(t₁),P(t₂))` specializes to the zero tuple, and hence

```text
A(0,0)=B(0,0)=C(0,0)=0.
```

In particular:

```text
B is not a unit in K⟦t₁,t₂⟧.
```

Thus the naive expression

```text
F = -A·C/B
```

is not directly a valid `PowerSeries` expression.

The fix is to divide out the common weighted diagonal factor first:

```text
A = D² A',
B = D³ B',
C = D C'.
```

Then

```text
F = -A' C' / B'
```

is valid because `B'` is a unit.

---

## CAS sanity check: leading model `u=1`

To verify the normalization, ignore higher-order terms of `u` and set all curve coefficients to zero in the leading homogeneous part.  This computes the leading term of Mathlib's raw `addXYZ` at `O`.

Use

```text
P₁ = [1, -1, t₁],
P₂ = [1, -1, t₂].
```

Then Mathlib's exact `addX`, `addY`, `addZ` formulas reduce to:

```text
A = (t₁ - t₂)²,
B = (t₁ - t₂)³,
C = -(t₁ - t₂)(t₁ + t₂).
```

So with

```text
D = t₁ - t₂,
```

the saturated coordinates are

```text
A' = A/D² = 1,
B' = B/D³ = 1,
C' = C/D  = -(t₁+t₂).
```

Then the local parameter is

```text
F = -A' C' / B' = t₁ + t₂.
```

This proves the leading term is correct.  The appearance of `t₁-t₂` was the diagonal factor of the raw addition formula; after saturating, the output parameter begins with `t₁+t₂` as required.

A minimal CAS script for this leading check:

```python
import sympy as sp

t1, t2 = sp.symbols('t1 t2')

# leading model: u=1 and a_i=0
P = (1, -1, t1)
Q = (1, -1, t2)

def addZ(P,Q):
    X,Y,Z = P
    U,V,T = Q
    return X*T**2 - U*Z**2

def addX(P,Q):
    X,Y,Z = P
    U,V,T = Q
    return X*U**2*Z**2 - 2*Y*V*Z*T + X**2*U*T**2

def negAddY(P,Q):
    X,Y,Z = P
    U,V,T = Q
    return (-Y*U**3*Z**3 + 2*Y*V**2*Z**3
            - 3*X**2*U*V*Z**2*T
            + 3*X*Y*U**2*Z*T**2
            + X**3*V*T**3 - 2*Y**2*V*T**3)

def negY(X,Y,Z):
    return -Y

def addY(P,Q):
    return negY(addX(P,Q), negAddY(P,Q), addZ(P,Q))

A = sp.factor(addX(P,Q))
B = sp.factor(addY(P,Q))
C = sp.factor(addZ(P,Q))
print(A, B, C)
print(sp.factor(- (A/(t1-t2)**2) * (C/(t1-t2)) / (B/(t1-t2)**3)))
```

Output:

```text
(t1 - t2)**2, (t1 - t2)**3, -(t1 - t2)*(t1 + t2)
t1 + t2
```

---

## What exactly must be proved in Lean

The formal group construction from `addXYZ` should be organized around saturated coordinates.

Let

```text
D := t₁ - t₂,
[A,B,C] := addXYZ(P(t₁), P(t₂)).
```

Prove divisibility in `MvPowerSeries (Fin 2) K`:

```lean
-- schematic
lemma addX_divisible_by_D_sq : ∃ A', A = D^2 * A' := ...
lemma addY_divisible_by_D_cu : ∃ B', B = D^3 * B' := ...
lemma addZ_divisible_by_D    : ∃ C', C = D   * C' := ...
```

Then choose the quotients:

```lean
noncomputable def A' : MvPowerSeries (Fin 2) K := ...
noncomputable def B' : MvPowerSeries (Fin 2) K := ...
noncomputable def C' : MvPowerSeries (Fin 2) K := ...
```

Prove the unit/linear facts:

```lean
lemma B'_constantCoeff : constantCoeff B' = 1 := ...   -- or -1 if D=t₂-t₁
lemma B'_isUnit : IsUnit B' := ...
lemma C'_linear : C' = -(X₀ + X₁) + terms_total_degree_ge_2 := ...
```

Then define:

```lean
noncomputable def F : MvPowerSeries (Fin 2) K :=
  -A' * C' * (B'_unit⁻¹ : MvPowerSeries (Fin 2) K)
```

and prove:

```lean
lemma F_zero_constantCoeff : F.constantCoeff = 0 := ...
lemma F_lin_coeff_X : F.coeff (Finsupp.single 0 1) = 1 := ...
lemma F_lin_coeff_Y : F.coeff (Finsupp.single 1 1) = 1 := ...
```

The associativity proof still needs either:

1. the uniqueness of the saturated local addition solution; or
2. a reduction to the group law on nonsingular Jacobian points; or
3. a separate formal-group associativity argument in `(t,w)` coordinates.

But the immediate normalization issue is exactly the `D`-weighted saturation above.

---

## Answer to the specific questions

### 1. Is raw `B` a unit?

No.

Raw `B = addY(P(t₁),P(t₂))` has constant term zero.  In fact the leading model shows

```text
B = (t₁-t₂)^3 · unit.
```

So `B` is not invertible in `K⟦t₁,t₂⟧`.

The saturated denominator

```text
B' := B / (t₁-t₂)^3
```

is a unit.  Its constant term is `1` if `D=t₁-t₂`, and `-1` if `D=t₂-t₁`.

### 2. What is `B`'s constant term?

```text
B.constantCoeff = 0.
```

This is because raw `addXYZ(P(0),P(0))` is the self-addition case for the distinct-points formula, and Mathlib explicitly returns `![0,0,0]` in that case.

After saturation,

```text
(B / D^3).constantCoeff = ±1,
```

so the normalized denominator is a unit.

### 3. Does `addXYZ` give `P+Q` or `P-Q`?

It gives `P+Q`.

The apparent `t₂-t₁` factor is the diagonal/slope-denominator factor.  It vanishes when `P(t₁)=P(t₂)`, where the distinct-points addition formula must be replaced by doubling.  It is not the formal group output parameter.

After removing the weighted diagonal factor, the local parameter of the saturated sum is

```text
F(t₁,t₂) = t₁ + t₂ + higher-order terms.
```

---

## Bottom line

`addXYZ(P(t₁),P(t₂))` does not directly define the formal group law by `-A*C/B`; raw `B` is not a unit.

But `addXYZ` is still usable after saturation:

```text
[A,B,C] = [D²A', D³B', DC'],   D=t₁-t₂,
F = -A'C'/B'.
```

The exact factor `D=t₁-t₂` is the diagonal factor of the distinct-points addition formula.  Once divided out with weights `(2,3,1)`, the normalized output has the correct formal group linear term `t₁+t₂`.
