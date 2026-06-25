# Q401 — separability of `preΨ'_n` from the invariant-differential identity

Task: verify the proposed identity

```text
-2 · Φ_n(x₀) · (preΨ'_n)'(x₀) · polY(x₀,y₀)
  = n · ψTwoMulQuot(n)(x₀,y₀)
```

at roots of `preΨ'_n`, and assess whether it can close bridge-2 without building `W.formalGroup`.

## Verdict

The proposed identity is **correct in the odd case** with

```text
polY = ψ₂ = 2y + a₁x + a₃.
```

For the even case, the identity as written is missing one extra `ψ₂` factor.  With the usual normalization

```text
preΨ'_n = ψ_n                    if n is odd,
preΨ'_n = ψ_n / ψ₂               if n is even,
```

the corrected root identity is

```text
-2 · Φ_n(x₀) · (preΨ'_n)'(x₀) · ψ₂(P)^(1 + [n even])
  = n · (ψ_{2n} / ψ_n)(P).                         (★)
```

Equivalently:

```text
n odd:
  -2 · Φ_n(x₀) · (preΨ'_n)'(x₀) · ψ₂(P)
    = n · ψTwoMulQuot(n)(P),

n even:
  -2 · Φ_n(x₀) · (preΨ'_n)'(x₀) · ψ₂(P)^2
    = n · ψTwoMulQuot(n)(P).
```

This parity correction is not cosmetic.  For even `n`, `ψTwoMulQuot(n)=ψ_{2n}/ψ_n` is `x`-only on a short Weierstrass curve, while a single factor `ψ₂=2y` changes sign under `y ↦ -y`.  Thus the one-`ψ₂` formula cannot hold for even `n` unless both sides vanish, which is not the torsion case we want.

The corrected identity was CAS-verified exactly for `n=4` and `n=5` on

```text
E : y² = x³ + x + 1.
```

The result is promising: if `(★)` is formalized and if `ψTwoMulQuot(n)(P) ≠ 0`, then `(preΨ'_n)'(x₀) ≠ 0` follows from already-proved adjacent/non-2/nonzero facts.  This gives bridge-2 by the dual-number derivative test, without constructing `W.formalGroup`.

However, `(★)` is itself the invariant-differential/tangent content in algebraic form.  It is not free from `addX/addY/Z` alone unless the projective formula infrastructure is extended to prove the invariant-differential identity for the multiplication formula.

---

## Normalizations used in the CAS check

For a short Weierstrass curve

```text
y² = x³ + A x + B,
ψ₂ = 2y,
Ψ₂Sq = ψ₂² = 4(x³ + A x + B).
```

Use the standard division polynomials:

```text
ψ₁ = 1,
ψ₂ = 2y,
ψ₃ = 3x⁴ + 6Ax² + 12Bx - A²,
ψ₄ = 4y(x⁶ + 5Ax⁴ + 20Bx³ - 5A²x² - 4ABx - 8B² - A³).
```

Define the `x`-polynomial part:

```text
P_n := preΨ'_n := ψ_n              if n odd,
P_n := ψ_n / ψ₂                   if n even.
```

Let

```text
h_n := 1       if n odd,
h_n := ψ₂      if n even,
```

so that

```text
ψ_n = h_n · P_n.
```

The full `φ_n` is

```text
φ_n = x · ψ_n² - ψ_{n+1}ψ_{n-1}.
```

At a root `P_n(x₀)=0`, the value of `φ_n` is the adjacent-product value:

```text
n odd:   φ_n(P) = -ψ₂(P)^2 · P_{n+1}(x₀) · P_{n-1}(x₀),
n even:  φ_n(P) = -P_{n+1}(x₀) · P_{n-1}(x₀).
```

This is the value called `Φ_n(x₀)` below.  If the project defines

```text
Φ_n = x·P_n² - P_{n+1}P_{n-1}·parity,
```

then the parity factor should satisfy:

```text
parity = Ψ₂Sq  for odd n,
parity = 1     for even n.
```

For even `n`, whether the first term is `x·P_n²` or `x·Ψ₂Sq·P_n²` is irrelevant after evaluation at `P_n(x₀)=0`; the full `φ_n` uses `x·Ψ₂Sq·P_n²`.

---

## Why the parity factor appears

The invariant differential is

```text
ω_inv = dx / ψ₂.
```

The multiplication formula gives

```text
x([n]Q) = φ_n(Q) / ψ_n(Q)^2.
```

Let

```text
q_n := ψ_n = h_n · P_n,
Q_n := ψ_{2n}/ψ_n.
```

The identity `ψ_{2n} = ψ₂([n]Q) · ψ_n(Q)^4` gives

```text
ψ₂([n]Q) = ψ_{2n} / q_n^4.
```

Differentiating `x([n]Q)=φ_n/q_n²` and using `[n]^*ω_inv = n·ω_inv` yields the algebraic identity

```text
ψ₂ · (Dφ_n · q_n - 2φ_n · Dq_n) = n · (ψ_{2n}/q_n),          (ID)
```

where `D` is differentiation along the curve.  On a short curve and on the `x`-polynomial part this is ordinary `d/dx`; for a generalized Weierstrass curve, `D(y)` introduces the denominator `ψ₂`, so the final identity should be stated in the project’s cleared-denominator form.

At a root `P_n(x₀)=0`, the term `Dφ_n · q_n` vanishes.  Also

```text
Dq_n(P) = h_n(P) · P_n'(x₀),
```

because the derivative of `h_n` is multiplied by `P_n(x₀)=0`.  Therefore `(ID)` becomes

```text
-2 · ψ₂(P) · φ_n(P) · h_n(P) · P_n'(x₀)
  = n · (ψ_{2n}/ψ_n)(P).
```

Since `h_n=1` for odd `n` and `h_n=ψ₂` for even `n`, this is exactly `(★)`.

---

## CAS verification on `E : y² = x³ + x + 1`

The following script verifies the corrected root identity for `n=4,5`.  It works modulo the curve equation and modulo `P_n(x)=0`.

```python
import sympy as sp

x, y = sp.symbols('x y')
A = sp.Integer(1)
B = sp.Integer(1)
f = x**3 + A*x + B
psi2 = 2*y
psi2sq = 4*f

psi = {
    0: sp.Integer(0),
    1: sp.Integer(1),
    2: 2*y,
    3: 3*x**4 + 6*A*x**2 + 12*B*x - A**2,
    4: 4*y*(x**6 + 5*A*x**4 + 20*B*x**3
             - 5*A**2*x**2 - 4*A*B*x - 8*B**2 - A**3),
}

def reduce_curve(expr):
    expr = sp.expand(expr)
    p = sp.Poly(expr, y, domain=sp.QQ[x])
    return sp.factor(sp.rem(p, sp.Poly(y**2 - f, y, domain=sp.QQ[x])).as_expr())

def get_psi(n):
    if n in psi:
        return psi[n]
    if n % 2 == 1:
        m = (n - 1)//2
        expr = get_psi(m+2)*get_psi(m)**3 - get_psi(m-1)*get_psi(m+1)**3
    else:
        m = n//2
        expr = get_psi(m)*(get_psi(m+2)*get_psi(m-1)**2
                           - get_psi(m-2)*get_psi(m+1)**2)/(2*y)
    psi[n] = reduce_curve(expr)
    return psi[n]

def pre(n):
    if n % 2 == 0:
        return reduce_curve(get_psi(n) / psi2)
    return get_psi(n)

def phi_full(n):
    return reduce_curve(x*get_psi(n)**2 - get_psi(n+1)*get_psi(n-1))

def quotient(n):
    return reduce_curve(get_psi(2*n) / get_psi(n))

def rem_mod_pre(expr, n):
    expr = reduce_curve(expr)
    pn = pre(n)
    poly_y = sp.Poly(expr, y, domain=sp.QQ[x])
    out = 0
    for (k,), coeff in poly_y.terms():
        out += sp.rem(sp.Poly(coeff, x), sp.Poly(pn, x)).as_expr() * y**k
    return sp.factor(sp.expand(out))

for n in [4, 5]:
    pn = pre(n)
    dpn = sp.diff(pn, x)
    Phi = phi_full(n)
    pol_factor = psi2sq if n % 2 == 0 else psi2
    diff = -2*Phi*dpn*pol_factor - n*quotient(n)
    print('n =', n)
    print('pre factor =', sp.factor(pn))
    print('corrected identity remainder =', rem_mod_pre(diff, n))

    # Nonvanishing checks: remove the visible y factor from odd quotient.
    q = quotient(n)
    q_poly = sp.factor(q/y) if q.has(y) else q
    print('gcd(pre, quotient-part) =', sp.Poly(pn, x).gcd(sp.Poly(q_poly, x)).monic().as_expr())
    print('gcd(pre, Phi) =', sp.Poly(pn, x).gcd(sp.Poly(Phi, x)).monic().as_expr())
    print('gcd(pre, psi2sq) =', sp.Poly(pn, x).gcd(sp.Poly(psi2sq, x)).monic().as_expr())
```

Output:

```text
n = 4
pre factor = 2*(x**6 + 5*x**4 + 20*x**3 - 5*x**2 - 4*x - 9)
corrected identity remainder = 0
gcd(pre, quotient-part) = 1
gcd(pre, Phi) = 1
gcd(pre, psi2sq) = 1

n = 5
pre factor = 5*x**12 + 62*x**10 + 380*x**9 - 105*x**8 + 240*x**7 - 540*x**6 - 696*x**5 - 2045*x**4 - 1680*x**3 - 290*x**2 - 740*x - 287
corrected identity remainder = 0
gcd(pre, quotient-part) = 1
gcd(pre, Phi) = 1
gcd(pre, psi2sq) = 1
```

Interpretation:

* For `n=4`, the identity holds with `ψ₂²`, not with a single `ψ₂`.
* For `n=5`, the identity holds with a single `ψ₂`.
* In both cases, the quotient side is nonzero at roots of `P_n`, at least on this concrete curve.
* In both cases, `Φ_n` and `ψ₂` are nonzero at roots of `P_n`, matching the bridge-1 expectations.

---

## Consequence for separability

Assume the corrected identity `(★)` is formalized at a non-2-torsion root of `P_n = preΨ'_n`.

Hypotheses:

```text
P_n(x₀) = 0,
ψ₂(P) ≠ 0,
Φ_n(x₀) ≠ 0,
(n : K) ≠ 0,
ψTwoMulQuot(n)(P) ≠ 0.
```

Then `(★)` gives

```text
(preΨ'_n)'(x₀) ≠ 0.
```

Reason: all factors except `(preΨ'_n)'(x₀)` on the left are nonzero, and the right side is nonzero.

Then bridge-2 follows by the dual-number derivative identity:

```text
P_n(x₀ + δ ε) = P_n(x₀) + δ · P_n'(x₀) ε.
```

If `P_n(x₀+δ ε)=0`, `P_n(x₀)=0`, and `P_n'(x₀)≠0`, then `δ=0`.  Since at a non-2-torsion affine point

```text
δ = ψ₂(P) · τ,
ψ₂(P) ≠ 0,
```

we get `τ=0`.

This is a clean formal route:

```text
corrected invariant-differential identity
        ↓
separability/simple-root of preΨ'_n
        ↓
dual-number derivative test
        ↓
bridge-2.
```

---

## Is `ψTwoMulQuot(n)(P)` necessarily nonzero?

Not from `Φ_n(P)≠0` alone.

But it should be exactly the same nonvanishing as the projective Y/ω component.  On a short Weierstrass curve,

```text
ψ_{2n} = ψ₂([n]P) · ψ_n(P)^4
       = 2ω_n(P) · ψ_n(P),
```

so

```text
ψTwoMulQuot(n)(P) = ψ_{2n}(P)/ψ_n(P) = 2ω_n(P)
```

as the finite quotient at `ψ_n(P)=0`.

Thus `ψTwoMulQuot(n)(P) ≠ 0` is essentially:

```text
ω_n(P) ≠ 0.
```

This should be supplied by the already-proved adjacent nonvanishing plus the Y-coordinate/ω normalization infrastructure.  If the Y-coordinate projective formula is still `6/7` complete, then the missing `1/7` may be exactly what is needed to expose this quotient nonvanishing in Lean.

So the proof should not assume quotient nonzero magically.  It should prove it from the projective Y formula:

```lean
-- schematic
lemma psiTwoMulQuot_ne_zero_at_prePsi_root
    (hroot : prePsiPrime n x = 0)
    (hnot2 : psi2 P ≠ 0)
    (hadj : adjacent_nonvanishing n P)
    (hY : projective_Y_formula_or_omega_normalization n P) :
    psiTwoMulQuot n P ≠ 0 := by
  -- identify psiTwoMulQuot with the finite Y/ω component and use adjacent nonvanishing
```

---

## Lean-facing corrected theorem statements

The exact names must be adapted to the repository, but the theorem should be parity-aware.

### Root identity

```lean
-- schematic
lemma invariantDifferential_root_identity_prePsi
    (W : WeierstrassCurve K) (n : ℕ) (P : AffinePoint W K)
    (hroot : prePsiPrime W n P.x = 0)
    (hnot2 : psi2 W P ≠ 0) :
    -2 * PhiPre W n P.x
        * (Polynomial.derivative (prePsiPrimePoly W n)).eval P.x
        * parityPsi2Factor W n P
      = (n : K) * psiTwoMulQuot W n P := by
  -- derive from the cleared invariant-differential identity
```

where

```lean
-- schematic
parityPsi2Factor W n P =
  if n % 2 = 0 then (psi2 W P)^2 else psi2 W P
```

or, if the project uses an `x`-only square:

```text
if n even: Ψ₂Sq(P.x)
if n odd:  ψ₂(P).
```

### Quotient nonvanishing

```lean
-- schematic
lemma psiTwoMulQuot_ne_zero_at_prePsi_root
    (W : WeierstrassCurve K) (n : ℕ) (P : AffinePoint W K)
    (hroot : prePsiPrime W n P.x = 0)
    (hnot2 : psi2 W P ≠ 0)
    (hadj : no_adjacent_prePsi_zero W n P)
    (hY : omega_normalization_or_projectiveY W n P) :
    psiTwoMulQuot W n P ≠ 0 := by
  -- identify quotient with the finite Y/ω component
```

### Separability from the identity

```lean
-- schematic
lemma prePsiPrime_derivative_ne_zero_at_root
    (W : WeierstrassCurve K) (n : ℕ) (P : AffinePoint W K)
    (hroot : prePsiPrime W n P.x = 0)
    (hnot2 : psi2 W P ≠ 0)
    (hPhi : PhiPre W n P.x ≠ 0)
    (hn : (n : K) ≠ 0)
    (hquot : psiTwoMulQuot W n P ≠ 0)
    (hid : invariantDifferentialRootIdentity W n P) :
    (Polynomial.derivative (prePsiPrimePoly W n)).eval P.x ≠ 0 := by
  intro hder
  -- substitute hder into the identity: LHS = 0
  -- RHS nonzero by hn and hquot
  -- contradiction
```

### Bridge-2 from separability

```lean
-- schematic
lemma bridge2_from_prePsiPrime_separable
    (W : WeierstrassCurve K) (n : ℕ) (P : AffinePoint W K)
    (δ τ : K)
    (hdual : evalDual (prePsiPrimePoly W n) (P.x + δ * ε) = 0)
    (hroot : prePsiPrime W n P.x = 0)
    (hder : (Polynomial.derivative (prePsiPrimePoly W n)).eval P.x ≠ 0)
    (hδ : δ = psi2 W P * τ)
    (hnot2 : psi2 W P ≠ 0) :
    τ = 0 := by
  -- coefficient of ε in hdual gives δ * derivative = 0
  -- hder gives δ=0
  -- hδ and hnot2 give τ=0
```

---

## How to prove the identity from existing projective formula infrastructure

The projective formula infrastructure should be used to prove the algebraic identity, but the proof must include a differential/invariant step.  The following is the clean route.

### Step 1: define full objects

Use full `ψ_n`, not only `preΨ'_n`, for the differential identity.

```text
q_n = ψ_n = h_n · preΨ'_n,
φ_n = x q_n² - ψ_{n+1}ψ_{n-1},
Q_n = ψ_{2n}/q_n.
```

### Step 2: prove the cleared invariant-differential identity

Target:

```text
ψ₂ · (Dφ_n · q_n - 2φ_n · Dq_n) = n · Q_n.       (ID)
```

Here `D` is the curve derivation compatible with `dx/ψ₂`.  In generalized Weierstrass form, use the relation

```text
D(y) = (3x² + 2a₂x + a₄ - a₁y) / ψ₂
```

and clear denominators if necessary.

Possible proof sources:

1. Differentiate the projective multiplication formulas `X_n=φ_n`, `Z_n=ψ_n`, and `Y_n=ω_n`, then compare `dx/ψ₂` before and after multiplication.
2. Prove the identity by induction on `n` using the projective addition formulas and the invariance of `dx/ψ₂` under the addition law.
3. If the project already has `addX`, `addY`, and `Z` identities for the multiplication formula, use them to rewrite the derivative of `x([n]P)` and the finite quotient `Q_n`.

Important: this is the tangent bridge in algebraic form.  It avoids `W.formalGroup`, but it does not avoid proving the differential behavior of multiplication.

### Step 3: specialize `(ID)` at `preΨ'_n=0`

At a root of `P_n=preΨ'_n`, use:

```text
q_n = h_n · P_n = 0,
Dq_n = h_n · P_n'
```

because the derivative of `h_n` is multiplied by `P_n=0`.

This gives:

```text
-2 · ψ₂ · φ_n · h_n · P_n' = n · Q_n.
```

Then rewrite `ψ₂ · h_n` as:

```text
ψ₂       if n odd,
ψ₂²      if n even.
```

Finally rewrite `φ_n(P)` as `Φ_n(P)` using the adjacent/parity formula.

### Step 4: separability and bridge-2

Use nonvanishing:

```text
Φ_n(P) ≠ 0             -- adjacent nonvanishing / no_adjacent_preΨ_zero
ψ₂(P) ≠ 0             -- non-2-torsion
(n : K) ≠ 0           -- hypothesis
Q_n(P) ≠ 0            -- Y/ω quotient nonvanishing
```

to conclude

```text
P_n'(x₀) ≠ 0.
```

Then close bridge-2 by the dual-number derivative test.

---

## Bottom line

The proposed route is viable after a parity correction.

Corrected core identity:

```text
-2 · Φ_n(x₀) · (preΨ'_n)'(x₀) · ψ₂(P)^(1 + [n even])
  = n · ψTwoMulQuot(n)(P).
```

CAS verification:

```text
n=4: verified with ψ₂²; single ψ₂ is wrong.
n=5: verified with ψ₂.
```

If Lean can prove this invariant-differential identity from the projective formula infrastructure and prove `ψTwoMulQuot(n)(P)≠0` from the Y/ω component, then bridge-2 can be closed without constructing `W.formalGroup`.

But this is not a free shortcut: the invariant-differential identity is the tangent bridge encoded as a polynomial identity.  It may be the shortest formal route, especially because it reuses `addX`, `addY`, and `Z`, but it still contains the irreducible first-order content `d[n]| = n`.
