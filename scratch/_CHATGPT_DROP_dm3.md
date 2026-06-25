# Q397 sub-agent prompt — build `W.formalGroup : FormalGroup K`

Use this as a self-contained prompt for a Lean 4 sub-agent.

---

## Mission

You are working in a Lean 4/mathlib formalization of the FLT/Mazur torsion route.  The current blocker is the tangent bridge, which needs the first-order fact

```text
d[n]|_O = (n : K)
```

for a Weierstrass elliptic curve.  One canonical way to supply this is to build the actual Weierstrass formal group

```lean
W.formalGroup : FormalGroup K
```

with the same local parameter used by the projective tangent computation, then use the formal-group theorem that the `n`-series has linear coefficient `(n : K)`.

Your task is to investigate and implement the shortest Lean-feasible construction of `W.formalGroup : FormalGroup K`, or, if the full construction is too large, to leave the project with the smallest compiling intermediate file and a precise list of remaining lemmas.

Do not write prose only.  Produce Lean code, theorem statements, and exact API notes.

---

## Mathematical context

Work with a generalized Weierstrass equation over a field or commutative ring `K`:

```text
E : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆.
```

In homogeneous coordinates:

```text
Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³.
```

The point at infinity is

```text
O = [0 : 1 : 0].
```

Use the standard local parameters at `O`:

```text
t = -x/y,
w = -1/y.
```

Then

```text
x = t / w,
y = -1 / w.
```

Substituting into the affine Weierstrass equation and multiplying by `w³` gives the fixed-point equation

```text
w = t³ + a₁ t w + a₂ t² w + a₃ w² + a₄ t w² + a₆ w³.        (★)
```

The unique solution in `K⟦t⟧` has leading expansion

```text
w(t) = t³ + a₁ t⁴ + (a₁² + a₂) t⁵ + (a₁³ + 2a₁a₂ + a₃) t⁶ + O(t⁷).
```

For the tangent bridge, the crucial local parameter is `t`.  Any formal group law constructed here must use this same `t`.

---

## Current mathlib facts to use/check

Mathlib has a formal group structure in:

```lean
import Mathlib.RingTheory.FormalGroup.Basic
```

The structure currently has this shape:

```lean
structure FormalGroup (R : Type*) [CommRing R] where
  toPowerSeries : MvPowerSeries (Fin 2) R
  zero_constantCoeff : toPowerSeries.constantCoeff = 0
  lin_coeff_X : toPowerSeries.coeff (Finsupp.single 0 1) = 1
  lin_coeff_Y : toPowerSeries.coeff (Finsupp.single 1 1) = 1
  assoc :
    toPowerSeries.subst ![toPowerSeries.subst ![Y₀, Y₁], Y₂]
      = toPowerSeries.subst ![Y₀, toPowerSeries.subst ![Y₁, Y₂]]
```

Mathlib also has the additive formal group:

```lean
FormalGroup.𝔾ₐ (R := K)
```

Do **not** solve this task by setting `W.formalGroup := FormalGroup.𝔾ₐ`.  That is only a first-order tangent model.  The task here is to build or scaffold the actual Weierstrass formal group compatible with `t = -x/y`.

Power series inverse APIs to inspect:

```lean
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Inverse
```

Important warning: `PowerSeries.invOfUnit` applies only to unit power series with nonzero constant term.  It cannot invert `w(t)`, because `w(0)=0` and `w(t)` has order `3`.

---

## Main difficulty

Step 3 of the naive construction is not directly available in `PowerSeries`:

```text
x(t) = t · w(t)⁻¹,
y(t) = -w(t)⁻¹.
```

Since

```text
w(t) = t³ + O(t⁴),
```

`w(t)⁻¹` has a pole of order `3`.  It is not an ordinary power series.  It belongs to a formal Laurent series ring or to a localization/completion where `t` is invertible.

The unit workaround is:

```text
g(t) := w(t) / t³ = 1 + a₁t + ...,
```

or equivalently

```text
u(t) := t³ / w(t) = g(t)⁻¹.
```

Both `g` and `u` are unit power series.  But then

```text
x(t) = t / w(t) = t⁻² · g(t)⁻¹,
y(t) = -1 / w(t) = -t⁻³ · g(t)⁻¹,
```

so negative powers still appear.  Do not try to force these into `PowerSeries K`.

---

## Which approach is shortest?

The shortest Lean-feasible route is probably **not** to build a full formal Laurent series library just to define `x(t)` and `y(t)`.

Preferred route:

```text
Use ordinary `PowerSeries`/`MvPowerSeries` as long as possible.
Define `w(t)` from (★).
Then define the formal group law `F(t₁,t₂)` by cleared-denominator / implicit polynomial identities in the `t,w` coordinates, not by globally constructing Laurent series `x(t), y(t)`.
```

Concretely, avoid ever needing a term of type

```lean
PowerSeries K
```

for `x(t)` or `y(t)`.  Instead, express the addition formula after multiplying by sufficient powers of `w₁`, `w₂`, and `w₃` so that every identity lives in ordinary bivariate/trivariate power series.

Fallback route if the cleared-denominator construction is too large:

```text
Implement `w(t)` and prove its leading coefficients.
Define the desired theorem statements for `F` and the cleared-denominator identities.
Record exactly which Mathlib API is missing.
```

Do not spend time implementing a general Laurent series theory unless Mathlib already has the necessary localization API ready to use.

---

## Required subtasks

### Subtask 0 — repository/API reconnaissance

Before coding, locate the project’s actual names for:

```text
Weierstrass curve structure,
coefficients a₁ a₂ a₃ a₄ a₆,
projective point type,
point at infinity O,
existing formal group or tangent files,
existing PowerSeries helper files.
```

Search for names like:

```text
WeierstrassCurve
EllipticCurve
Jacobian
FormalGroup
PowerSeries
TangentO
formalNsmul_coeff_one
```

If the project already has a local `formalNsmul_coeff_one`, use its exact type.  If not, write the theorem you need as a project-local target.

### Subtask 1 — define the `w(t)` series

Define the unique power series `w : K⟦t⟧` satisfying

```text
w = t³ + a₁ t w + a₂ t² w + a₃ w² + a₄ t w² + a₆ w³.
```

Lean implementation options, in preferred order:

1. Use an existing contraction/fixed-point theorem for `PowerSeries` if Mathlib has one.
2. If not, define coefficients recursively and build the series by extensionality.
3. If coefficient recursion is too heavy, define the first finite approximation and state the full fixed-point theorem as the next lemma.

The coefficient recursion should use the fact that the coefficient of `w` at degree `n` depends only on coefficients of `w` at lower degrees.  The leading terms should be proved:

```lean
-- schematic names/types
lemma coeff_w_0 : coeff K 0 w = 0 := ...
lemma coeff_w_1 : coeff K 1 w = 0 := ...
lemma coeff_w_2 : coeff K 2 w = 0 := ...
lemma coeff_w_3 : coeff K 3 w = 1 := ...
lemma coeff_w_4 : coeff K 4 w = a₁ := ...
lemma coeff_w_5 : coeff K 5 w = a₁^2 + a₂ := ...
```

Also prove or state:

```text
w(t) = t³ · g(t)
```

where `g(0)=1`, hence `g` is a unit power series.

### Subtask 2 — avoid direct inversion of `w`

Do not write:

```lean
(w)⁻¹
```

as an ordinary power series unless you have moved to a formal Laurent series/localized ring.

Instead, define one of:

```text
g(t) = w(t)/t³,        g(0)=1,
u(t) = g(t)⁻¹ = t³/w(t),   u(0)=1.
```

Use `PowerSeries.invOfUnit` only for `g` or `u`, never for `w`.

Expected theorem statements:

```lean
-- schematic
lemma constantCoeff_g : PowerSeries.constantCoeff g = 1 := ...
noncomputable def gUnit : Units (PowerSeries K) := ...
noncomputable def u : PowerSeries K := ↑(gUnit⁻¹)
lemma constantCoeff_u : PowerSeries.constantCoeff u = 1 := ...
```

### Subtask 3 — define `F(t₁,t₂)` without Laurent series

The formal group law must be a bivariate power series:

```lean
noncomputable def W.formalGroupLaw : MvPowerSeries (Fin 2) K := ...
```

The desired mathematical meaning is:

```text
F(t₁,t₂) = t(P(t₁) + P(t₂)),
```

where

```text
P(t) = (x(t), y(t)) = (t/w(t), -1/w(t)).
```

But because `x(t)` and `y(t)` are Laurent series, define `F` through **cleared-denominator equations** in `t,w` coordinates.

Use variables:

```text
t₁, t₂, t₃
w₁ = w(t₁), w₂ = w(t₂), w₃ = w(t₃).
```

Then the graph of addition should be expressed by projective or affine addition formulas after clearing denominators.  The target is to construct a power series `F` such that `t₃ = F(t₁,t₂)` and `w₃ = w(F(t₁,t₂))` satisfy the cleared addition equations.

If this is too ambitious, produce the exact theorem statement:

```lean
-- schematic
noncomputable def formalGroupLawCandidate
    (W : WeierstrassCurve K) : MvPowerSeries (Fin 2) K := ...

lemma formalGroupLawCandidate_zero_constantCoeff :
    formalGroupLawCandidate W |>.constantCoeff = 0 := ...

lemma formalGroupLawCandidate_lin_coeff_X :
    (formalGroupLawCandidate W).coeff (Finsupp.single 0 1) = 1 := ...

lemma formalGroupLawCandidate_lin_coeff_Y :
    (formalGroupLawCandidate W).coeff (Finsupp.single 1 1) = 1 := ...
```

At minimum, prove the first-order expansion:

```text
F(t₁,t₂) = t₁ + t₂ + terms of total degree ≥ 2.
```

This is enough for the tangent bridge, but not enough for the full `FormalGroup` structure unless associativity is also proved.

### Subtask 4 — construct `FormalGroup K`

Once `F : MvPowerSeries (Fin 2) K` is defined, package it as:

```lean
noncomputable def W.formalGroup : FormalGroup K where
  toPowerSeries := F
  zero_constantCoeff := ...
  lin_coeff_X := ...
  lin_coeff_Y := ...
  assoc := ...
```

Associativity should come from one of these routes:

1. Reduce to associativity of the elliptic-curve group law, if the project already has a group law theorem in projective coordinates.
2. Prove equality by coefficient extensionality using the uniqueness of the formal addition solution in `t,w` coordinates.
3. If neither is feasible, state the associativity theorem exactly and leave it as the only remaining major lemma.

Do not try to prove associativity by expanding raw addition formulas indefinitely.

### Subtask 5 — connect to `formalNsmul_coeff_one`

After `W.formalGroup` exists, prove or instantiate the theorem used by the tangent bridge:

```lean
-- schematic, adapt to the project-local name/type
lemma W.formalGroup_nsmul_coeff_one (n : ℕ) :
    formalNsmul_coeff_one W.formalGroup n = (n : K) := by
  simpa using formalNsmul_coeff_one (F := W.formalGroup) n
```

If `formalNsmul_coeff_one` is not in the project, define the intended theorem statement precisely.  The desired mathematical content is:

```text
[n]_F(T) = (n : K) T + O(T²).
```

For the tangent bridge, also state the required parameter-compatibility theorem:

```lean
-- schematic
lemma W.tangent_parameter_matches_formalGroup
    (Pε : DualPointAtO W K) (τ : K)
    (hτ : coeffε (t Pε) = τ) :
    formalGroupParameter W Pε = τ := by
  ...
```

This lemma is mandatory.  A formal group law that uses the wrong parameter does not prove the bridge.

---

## Expected deliverable

Return one of the following.

### Best outcome

A compiling Lean file that defines:

```lean
W.formalGroup : FormalGroup K
```

and proves:

```lean
W.formalGroup_nsmul_coeff_one
W.tangent_parameter_matches_formalGroup
```

or the project’s exact equivalents.

### Acceptable intermediate outcome

A compiling Lean file that defines `w(t)`, proves the fixed-point equation and leading coefficients, defines the unit `g=w/t³` or `u=t³/w`, and states the formal group law construction/associativity lemmas with exact theorem statements.

### Minimum acceptable outcome

A precise report containing:

1. exact Mathlib APIs found for `PowerSeries`, `MvPowerSeries`, inverse/unit, substitution, and coefficient extensionality;
2. the shortest viable route among:
   * full Laurent/localization construction;
   * cleared-denominator implicit construction;
   * coefficient-recursive universal formal group law;
3. the next 3 Lean theorem statements that should be implemented;
4. the single biggest blocker and why.

---

## Do not do these things

* Do not set `W.formalGroup := FormalGroup.𝔾ₐ` and call the task done.
* Do not invert `w(t)` using `PowerSeries.invOfUnit`; `w` is not a unit.
* Do not introduce a general Laurent series library unless Mathlib already has a ready API.
* Do not prove only `lin_coeff_X=1` and `lin_coeff_Y=1` while ignoring associativity, unless you explicitly label the result as a tangent-model lemma rather than `FormalGroup K`.
* Do not use the tangent bridge itself to prove associativity or parameter compatibility; that would be circular.

---

## Final recommendation

The shortest likely route is:

```text
1. Build `w(t)` and `g(t)=w(t)/t³` in ordinary `PowerSeries`.
2. Avoid ordinary definitions of `x(t)` and `y(t)` because they are Laurent series.
3. Define the formal group law by cleared-denominator identities in `t,w` coordinates.
4. Use uniqueness of the cleared-denominator solution to prove associativity.
5. Package the resulting bivariate power series as `FormalGroup K`.
```

If step 3 or 4 is too large, stop after step 1–2 with a compiling file and exact theorem statements.  That would still materially advance the project because it isolates the only real obstruction: constructing the actual addition power series without a Laurent-series detour.
