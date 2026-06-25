# UNDERSTANDING.md draft — FLT/Mazur formalization

Status date: 2026-06-25

Purpose: single maintained understanding document for the current FLT/Mazur formalization route, per the playbook requirement that project state live in one factual document.  This draft consolidates the dm3 session findings and should be adapted into the maintained `UNDERSTANDING.md`.

This document is factual/status-oriented.  It records what is closed, what remains open, what was tried, and which proof obligations should not be confused with each other.

---

## 1. Executive status

### Current target

The active route is the SEAM1/E1 tangent route for the Mazur/FLT torsion layer.

The current critical blocker is **bridge-2**, also called the **tangent bridge**.  It is the step that connects the projective division-polynomial formulas to the first-order tangent behavior of multiplication by `n`.

### Current high-level state

| Component | Status | Notes |
|---|---:|---|
| `Torsion.lean` sorry inventory | 3 remaining | All 3 are classified as **not ours**.  No owned SEAM1/tangent blocker should be counted in these. |
| SEAM1 architecture | Active | E1 tangent route with two bridges. |
| Bridge-1 | CLOSED | Polynomial/EDS side is closed for the current route. |
| Bridge-2 | OPEN | This is the tangent bridge. |
| Projective formula, Z-coordinate | Done | Part of bridge-2 projective-formula side. |
| Projective formula, X-coordinate | Done | Part of bridge-2 projective-formula side. |
| Projective formula, Y-coordinate | 6/7 done | One remaining Y-coordinate subgoal. |
| Tangent bridge itself | Irreducible | It cannot be bypassed by `φ_n(P) ≠ 0` or by declaring the formal group additive.  It needs `d[n]|_O = n` or an equivalent independent statement. |

### Main conclusion

Bridge-2 cannot be reduced to projective nonvanishing alone.  The missing mathematical content is exactly one of the following equivalent first-order/separability facts:

```text
d[n]|_O = (n : K),
```

or

```text
[n] is unramified / separable at the relevant torsion point,
```

or

```text
preΨ'_n is squarefree at the relevant non-2-torsion root.
```

A formal group proof is one way to supply this fact.  A direct tangent calculation or a squarefreeness proof can also supply it, but no explored route eliminates the need for this content.

---

## 2. Torsion.lean sorry inventory

Current inventory for `Torsion.lean`:

```text
remaining sorries: 3
classification: all not-ours
owned sorries: 0
```

Interpretation:

* The 3 remaining sorries should not be treated as current dm3-owned blockers.
* The SEAM1/tangent-bridge work should not add new sorries to `Torsion.lean`.
* Once bridge-2 is closed, the SEAM1 route should not leave any owned sorry in the torsion layer.
* If any of the 3 remaining sorries becomes relevant to the current route, it must be explicitly reclassified before work begins.

---

## 3. SEAM1 architecture

### 3.1 Route

The active architecture is the **E1 tangent route**.

The route uses division-polynomial/projective formulas and a tangent argument at `O` to control deformations of torsion points.  The route has two logical bridges.

### 3.2 Bridge-1

Bridge-1 is closed.

Role of bridge-1:

```text
polynomial / EDS / division-polynomial data
        ↓
root and adjacent-nonvanishing facts needed by the projective formulas
```

Bridge-1 supplies the algebraic input needed by bridge-2.  It is not the current blocker.

Closed ingredients used by bridge-1 include:

* `ω` normalization;
* Ward invariant;
* shifted EDS indexing;
* adjacent nonvanishing;
* the relevant `preΨ'_n` / division-polynomial root setup.

### 3.3 Bridge-2

Bridge-2 is the tangent bridge.

Expected bridge-2 shape:

```text
non-2-torsion point P,
preΨ'_n(x(P) + δε) = 0,
(n : K) ≠ 0
        ↓
input tangent coefficient τ = 0.
```

Equivalent contrapositive:

```text
τ ≠ 0
        ↓
preΨ'_n(x(P) + δε) ≠ 0.
```

Here `δ` is the coefficient of the `x`-coordinate deformation.  At a non-2-torsion affine point,

```text
δ = ψ₂(P) * τ,
```

and `ψ₂(P) ≠ 0`, so `δ = 0` is equivalent to `τ = 0`.

Bridge-2 has two distinguishable parts:

```text
(A) projective-formula side:
    compute coeffε(t([n]Pε)) from the explicit projective formula;

(B) tangent-law side:
    identify coeffε(t([n]Pε)) with (n : K) times the input tangent coefficient.
```

The projective-formula side is mostly mechanical but still has one Y-coordinate proof remaining.  The tangent-law side is irreducible and must be supplied by a formal group, direct first-order projective calculation, separability, or squarefreeness.

---

## 4. Bridge-2 current detailed status

### 4.1 Projective formula side

The projective formula computes `[n]P` in coordinates.  At a point with `ψ_n(P)=0`, the relevant output has `Z=0`, so `[n]P = O` to zeroth order.

Known/target local-parameter expression:

```text
t = -X * Z / Y
```

for the Jacobian/projective coordinate convention used in the projective formula calculations.  Some formal-group notes use `t = -X/Y` at `O`; these two notations must be reconciled with the exact coordinate convention in the Lean files before finalizing bridge-2.

The projective-formula computation aims at the first-order expression

```text
coeffε(t([n]Pε)) = -φ_n(P) * u / ω_n(P)
```

at `ψ_n(P)=0`, where `u` is the first-order coefficient coming from `ψ_n(Pε)` or the relevant projective `Z` deformation, depending on the local notation.

Status:

| Coordinate | Status | Meaning |
|---|---:|---|
| Z | Done | The `ψ_n`/`Z` first-order behavior is available. |
| X | Done | The `φ_n`/`X` zeroth-order behavior is available. |
| Y | 6/7 done | One remaining Y-coordinate algebraic subgoal remains. |

### 4.2 Tangent-law side

Needed tangent-law statement:

```text
coeffε(t([n](O + τ ε))) = (n : K) * τ.
```

This is equivalent to:

```text
d[n]|_O = (n : K).
```

This is the mathematical content of `formalNsmul_coeff_one` if the project has a formal group instance matching the curve's chosen local parameter.

The current status is:

```text
tangent bridge: open / irreducible.
```

It cannot be obtained solely from:

* `φ_n(P) ≠ 0`;
* `ω_n(P) ≠ 0`;
* `[n]P = [φ : ω : 0]`;
* the rational formula `x([n]Q) = φ_n(Q) / ψ_n(Q)^2`;
* the additive formal group unless the curve-local-parameter compatibility is independently proved.

---

## 5. Key identities and closed algebraic ingredients

The following identities/ingredients are recorded as proved/available for the current route.

### 5.1 `ω` normalization

Role:

```text
normalize the Y-coordinate / ω_n term in the projective formula at ψ_n(P)=0.
```

Use:

* needed to identify the projective output `[φ : ω : 0]` correctly;
* needed to show the denominator in the local parameter computation is nonzero;
* feeds into bridge-2 projective-formula side.

Status:

```text
closed.
```

### 5.2 Ward invariant

Role:

```text
provide the recurrence invariant behind the elliptic divisibility sequence behavior.
```

Use:

* supports shifted EDS arguments;
* supports adjacent nonvanishing;
* prevents the torsion-root case from degenerating into adjacent zero cases.

Status:

```text
closed.
```

### 5.3 EDS shifted

Role:

```text
align the indexing of the division-polynomial sequence with the Ward/EDS recurrence.
```

Use:

* lets the project use Ward-style recurrence statements with the project’s `ψ_n` indexing;
* provides the algebraic infrastructure for adjacent nonvanishing.

Status:

```text
closed.
```

### 5.4 Adjacent nonvanishing

Role:

```text
at ψ_n(P)=0, prove the required adjacent terms do not vanish.
```

Use:

* supplies `φ_n(P) ≠ 0` or the equivalent adjacent nonzero condition;
* supplies `ω_n(P) ≠ 0` after normalization;
* ensures the projective output at `ψ_n(P)=0` is really `[φ : ω : 0]` with nonzero finite data.

Status:

```text
closed.
```

### 5.5 Non-2-torsion coordinate fact

At a non-2-torsion affine point,

```text
ψ₂(P) ≠ 0.
```

Then `x - x(P)` is a valid local coordinate, and for a polynomial `F(X)`,

```text
ord_P(F(x)) = multiplicity of x(P) as a root of F.
```

For odd `n`, `ψ_n` is already a polynomial in `x`, so this applies directly to `preΨ'_n = Ψ_n`.

For even `n`, the removed `ψ₂` factor is a unit at a non-2-torsion point, so it does not change order of vanishing:

```text
ord_P(ψ_n) = ord_P(preΨ'_n(x)).
```

Status:

```text
conceptually valid and used in the bridge analysis;
formal Lean status depends on the local file definitions.
```

### 5.6 Dual-number derivative identity

For any polynomial `F`, in dual numbers,

```text
F(x + δ ε) = F(x) + δ * F'(x) ε.
```

Therefore, if

```text
F(x) = 0,
F'(x) ≠ 0,
F(x + δ ε) = 0,
```

then

```text
δ = 0.
```

For bridge-2, take `F = preΨ'_n` and use `δ = ψ₂(P) * τ` with `ψ₂(P) ≠ 0` to conclude `τ=0`.

Status:

```text
available as the clean formal shape for an alternative bridge-2 if a simple-root lemma is supplied.
```

---

## 6. CAS verifications from this session

The CAS checks are sanity evidence and identity discovery aids.  They are not replacements for the general Lean proof.

### 6.1 `n = 2` is vacuous for this bridge

For `n=2`,

```text
preΨ'_2 = 1.
```

Thus the derivative/root test has no roots.  A 2-torsion point has `ψ₂(P)=0`, and `[2]P=O`, but this does not test bridge-2 in the required non-2-torsion setting.

Conclusion:

```text
n=2 is the wrong first test case for bridge-2.
```

### 6.2 `n = 3` tangent coefficient check on `y² = x³ + x + 1`

Curve:

```text
E : y² = x³ + x + 1.
```

For this curve,

```text
ψ₂ = 2y,
ψ₃ = 3x⁴ + 6x² + 12x - 1.
```

At a root `α` of `ψ₃`, with `β² = α³ + α + 1`, the resultant check gives:

```text
resultant(x³ + x + 1, ψ₃) = -961,
```

so `β ≠ 0`, hence `ψ₂(P) ≠ 0`.

Using exact dual-number expansion of the projective formulas for

```text
Pε = (α + ε, β + s ε),
s = (3α² + 1)/(2β),
[3]Pε = addXYZ(Pε, dblXYZ(Pε)),
t = -X * Z / Y,
```

the exact CAS reduction modulo

```text
y² = x³ + x + 1,
ψ₃(x)=0,
ε²=0
```

gives:

```text
t0 remainder = 0,
t1 - 3/(2y) remainder = 0.
```

Therefore:

```text
coeffε(t([3]Pε)) = 3/(2β),
input coefficient = 1/(2β),
ratio = 3.
```

This confirms the expected tangent bridge behavior in the first non-vacuous case.

Extra factorization observed in the CAS output:

```text
numerator(coeffε(t([3]Pε)) - 3/(2y))
```

contains a high power of `ψ₃`; in the concrete computation it produced a `ψ₃^4` factor after reducing by the curve equation.

### 6.3 `n = 3` squarefreeness check on `y² = x³ + 1`

Curve:

```text
E : y² = x³ + 1.
```

For this curve,

```text
ψ₂ = 2y,
ψ₃ = 3x⁴ + 12x = 3x(x³ + 4),
preΨ'_3 = Ψ₃ = ψ₃.
```

Roots of `ψ₃`:

```text
x = 0,
x³ = -4.
```

At these roots:

```text
x = 0    ⇒ y² = 1,
x³ = -4 ⇒ y² = -3.
```

Thus `ψ₂(P) ≠ 0` at every point above a root.

Exact CAS output:

```text
gcd(ψ₃, ψ₃') = 1,
gcd(ψ₃, x³ + 1) = 1,
gcd(ψ₃, φ₃) = 1,
ψ₃'(0) = 12,
ψ₃'(α) = -36 when α³ = -4,
φ₃(0) = 64,
φ₃(α) = -1728 when α³ = -4.
```

Conclusion for this concrete curve:

```text
ord_P(ψ₃) = 1,
mult_{x(P)}(preΨ'_3) = 1,
(preΨ'_3)'(x(P)) ≠ 0.
```

This verifies the derivative/simple-root behavior in the example.  It does not prove the general theorem.

---

## 7. Alternative routes explored and their status

### 7.1 Route: use `n=2` as the simplest test

Status:

```text
failed / vacuous.
```

Reason:

```text
preΨ'_2 = 1.
```

There are no roots of `preΨ'_2`, so the derivative test does not exercise bridge-2.  The 2-torsion calculation verifies a special projective degeneration but not the desired non-2-torsion tangent bridge.

### 7.2 Route: use `φ_n(P) ≠ 0` to prove `ψ_n` has a simple zero

Status:

```text
false as stated / incomplete.
```

What is true:

From

```text
x([n]Q) = φ_n(Q) / ψ_n(Q)^2
```

and `φ_n(P) ≠ 0`, one gets no numerator cancellation:

```text
ord_P(x ∘ [n]) = -2 * ord_P(ψ_n).
```

What is missing:

To conclude `ord_P(ψ_n)=1`, one also needs

```text
ord_P(x ∘ [n]) = -2.
```

That is exactly unramifiedness/separability of `[n]` at `P`, because `x` has a double pole at `O`.

Conclusion:

```text
φ_n(P) ≠ 0 proves no cancellation; it does not prove simple zero.
```

### 7.3 Route: call `φ/ψ²` a simple pole

Status:

```text
incorrect terminology / wrong order.
```

Reason:

`x` has a double pole at `O`, not a simple pole.  The function `φ/ψ²` has pole order `2 * ord_P(ψ)`, assuming `φ(P) ≠ 0`.  Showing this pole order equals `2` is equivalent to showing `ord_P(ψ)=1`, which is the desired separability/simple-root content.

### 7.4 Route: use `deg([n]) = n²` to force pole order 2

Status:

```text
circular unless separability/unramifiedness is already proved.
```

Reason:

The degree statement by itself is global.  The required bridge-2 fact is a local first-order statement at the torsion point.  To use the global degree to control local pole order without multiplicity loss, one needs separability/unramifiedness.  That is the same missing content.

### 7.5 Route: prove bridge-2 purely by simple roots of `preΨ'_n`

Status:

```text
viable if an independent squarefreeness/simple-root lemma is available.
```

Shape:

```text
(preΨ'_n)(x)=0,
(preΨ'_n)'(x) ≠ 0,
(preΨ'_n)(x + δ ε)=0
        ↓
δ=0
        ↓
τ=0 because δ=ψ₂(P)τ and ψ₂(P)≠0.
```

This avoids formal groups in bridge-2 itself.  The cost is proving the simple-root lemma independently.

Possible theorem shape:

```lean
-- schematic
lemma prePsiPrime_derivative_nonzero_at_root
    (hn : (n : K) ≠ 0)
    (hroot : (prePsiPrime n).eval x = 0)
    (hnot2 : Ψ₂Sq.eval x ≠ 0)
    (hdisc : Δ ≠ 0) :
    (Polynomial.derivative (prePsiPrime n)).eval x ≠ 0 := by
  -- squarefreeness / gcd / Bezout proof
```

### 7.6 Route: use the additive formal group as `W.formalGroup`

Status:

```text
valid as a first-order tangent model; invalid as a replacement for the actual Weierstrass formal group if higher-order facts are used.
```

Correct kernel:

Every one-dimensional formal group law satisfies

```text
F(X,Y) = X + Y + terms of total degree ≥ 2.
```

Therefore the `n`-series has linear coefficient `(n : K)` for every formal group law.  The additive formal group `FormalGroup.𝔾ₐ` is a valid first-order model of the tangent line.

Problem:

The curve's actual formal group law is not definitionally the additive formal group.  Replacing `W.formalGroup` by `FormalGroup.𝔾ₐ` loses higher-order information and does not by itself prove that the curve's chosen local parameter is the same parameter used by the additive model.

Remaining required lemma:

```text
the local parameter t at O identifies projective dual deformations with K,
and the curve group law has first-order addition in this parameter.
```

Schematic Lean first-order model:

```lean
import Mathlib.RingTheory.FormalGroup.Basic

noncomputable section

namespace Q389

abbrev additiveFormalGroup (K : Type*) [CommRing K] : FormalGroup K :=
  FormalGroup.𝔾ₐ (R := K)

variable (K : Type*) [Field K]

abbrev TangentO : Type _ := K

def tangentBridge (W : Type*) : TangentO K ≃+ K :=
  AddEquiv.refl K

@[simp]
theorem tangentBridge_apply (W : Type*) (τ : TangentO K) :
    tangentBridge (K := K) W τ = τ :=
  rfl

theorem tangentBridge_nsmul (W : Type*) (n : ℕ) (τ : TangentO K) :
    tangentBridge (K := K) W (n • τ) =
      (n : K) * tangentBridge (K := K) W τ := by
  simp [tangentBridge, TangentO, nsmul_eq_mul]

end Q389
```

This proves only the model fact.  It does not prove the geometric tangent bridge for the curve.

### 7.7 Route: prove the tangent bridge directly from projective addition formulas

Status:

```text
viable and formal-group-free, but it is still the tangent bridge.
```

Target theorem:

```lean
-- schematic
lemma coeff_t_nsmul_at_O
    (W : WeierstrassCurve K) (n : ℕ) (τ : K)
    (hn : (n : K) ≠ 0) :
    coeffε (t ([n] (O + τ ε))) = (n : K) * τ := by
  -- expand projective addition/multiplication to first order
```

This avoids constructing the full Weierstrass formal group.  It does not avoid proving `d[n]|_O=n`; it proves that fact directly.

---

## 8. Key Lean files / components and sorry status

Exact repository paths should be synchronized when this draft is moved into the maintained `UNDERSTANDING.md`.  The table below records the file/component names as referenced in the current session.

| File/component | Role | Current status |
|---|---|---|
| `Torsion.lean` | Top-level torsion/Mazur integration target | 3 sorries remain; all 3 are not-ours; no owned sorry should remain from SEAM1. |
| SEAM1 / E1 tangent route files | Main route architecture | Bridge-1 closed; bridge-2 open. |
| Bridge-1 polynomial/EDS files | Root/EDS/adjacent-nonvanishing side | Closed. |
| `ω` normalization file/component | Normalizes the projective Y/ω term | Closed. |
| Ward invariant file/component | Proves recurrence invariant used by EDS | Closed. |
| shifted EDS file/component | Aligns EDS indexing with division-polynomial indexing | Closed. |
| adjacent nonvanishing file/component | Proves required adjacent terms nonzero at torsion roots | Closed. |
| Projective formula Z component | `Z`/`ψ_n` behavior | Done. |
| Projective formula X component | `X`/`φ_n` behavior | Done. |
| Projective formula Y component | `Y`/`ω_n` behavior | 6/7 done; one subgoal remains. |
| Formal group / tangent-at-O component | Proves or supplies `d[n]|_O = n` | Open; choose actual `W.formalGroup`, direct tangent proof, or squarefreeness route. |
| `scratch/_CHATGPT_DROP_dm3.md` | Scratch consolidation target | This file now contains the UNDERSTANDING.md draft for migration. |

---

## 9. Recommended next work

### 9.1 Finish the projective formula Y-coordinate

Immediate mechanical task:

```text
close the remaining 1/7 Y-coordinate subgoal.
```

Reason:

The projective-formula side of bridge-2 should be completely closed before the final tangent-law bridge is attempted.  Then bridge-2 has a clean separation:

```text
projective algebra done
        +
tangent law / separability fact
        ↓
bridge-2 closed.
```

### 9.2 Choose exactly one bridge-2 tangent-law route

There are three viable routes.  Do not mix them without a dependency reason.

#### Option A: actual `W.formalGroup`

Prove/build the actual Weierstrass formal group associated to the chosen local parameter.

Needed:

```text
W.formalGroup uses the same local parameter t as the projective tangent computation.
formalNsmul_coeff_one gives coeff₁([n]) = (n : K).
```

Pros:

* mathematically canonical;
* gives the clean statement `d[n]|_O=n`;
* reusable for future local computations.

Cons:

* requires actual formal-group construction and parameter compatibility;
* may be heavier than bridge-2 needs.

#### Option B: direct first-order projective tangent proof

Prove the tangent statement directly from projective addition/multiplication formulas.

Target:

```text
coeffε(t([n](O + τ ε))) = (n : K) * τ.
```

Pros:

* avoids full formal group infrastructure;
* directly matches bridge-2;
* likely enough for current torsion route.

Cons:

* still proves the same irreducible tangent content;
* may duplicate formal-group reasoning in ad hoc projective algebra.

#### Option C: squarefreeness of `preΨ'_n`

Prove that relevant roots of `preΨ'_n` are simple away from the 2-torsion/discriminant exclusions.

Target:

```text
(preΨ'_n)(x)=0,
Ψ₂Sq(x)≠0,
(n:K)≠0,
Δ≠0
        ↓
(preΨ'_n)'(x)≠0.
```

Then bridge-2 follows from the dual-number derivative identity.

Pros:

* avoids formal groups and projective tangent calculation for bridge-2;
* conceptually clean once the squarefreeness theorem exists.

Cons:

* squarefreeness is substantial algebra;
* proving it may be as hard as or harder than the formal-group/tangent route;
* must avoid circular use of the tangent bridge or separability.

### 9.3 Preferred immediate path

Recommended order:

1. Close the final Y-coordinate projective-formula subgoal.
2. Decide whether the maintained project wants actual `W.formalGroup` infrastructure.
3. If yes, implement `W.formalGroup` and prove parameter compatibility with `t`.
4. If no, prove the direct first-order theorem `coeff_t_nsmul_at_O` from projective formulas.
5. Use that theorem to close bridge-2.
6. Re-run the `Torsion.lean` sorry inventory and confirm only the 3 not-ours sorries remain.

---

## 10. Non-circular proof obligations to keep separate

The following statements are logically distinct.  Do not use one as if it proved another unless the bridge is explicitly formalized.

### 10.1 Projective no-cancellation

```text
ψ_n(P)=0,
φ_n(P)≠0,
ω_n(P)≠0
```

This proves the projective output is well normalized and that the rational expressions have no numerator cancellation.

It does not prove `ord_P(ψ_n)=1`.

### 10.2 Simple-root / squarefreeness

```text
(preΨ'_n)'(x(P)) ≠ 0
```

This proves bridge-2 quickly by dual numbers.

It must be proved independently, either by squarefreeness or by an unramifiedness theorem.

### 10.3 Tangent differential

```text
d[n]|_O = (n : K)
```

This proves the tangent bridge.

It can come from:

* formal group coefficient theorem;
* direct projective first-order computation;
* separability/unramifiedness plus local-parameter comparison.

### 10.4 Additive formal group model

```text
FormalGroup.𝔾ₐ
```

This models tangent addition after choosing a tangent coordinate.

It does not identify the curve's projective tangent coordinate with that model unless the local parameter bridge is proved.

---

## 11. Minimal theorem targets for the next Lean pass

These names are schematic; adapt to project naming.

### 11.1 Final projective Y subgoal

```lean
-- schematic
lemma projectiveFormula_Y_remaining_subgoal ... :
  ... := by
  -- close the last Y-coordinate algebraic identity
```

### 11.2 Tangent coordinate identification

```lean
-- schematic
lemma tangentCoeff_eq_t_coeff_at_O
    (W : WeierstrassCurve K)
    (Pε : DualPointAtO W K)
    (τ : K)
    (hτ : coeffε (t Pε) = τ) :
    TangentO.coordinate W Pε = τ := by
  -- prove from definition of the chosen local parameter
```

### 11.3 Direct tangent bridge

```lean
-- schematic
lemma coeff_t_nsmul_at_O
    (W : WeierstrassCurve K) (n : ℕ) (τ : K)
    (hn : (n : K) ≠ 0) :
    coeffε (t ([n] (O + τ ε))) = (n : K) * τ := by
  -- direct first-order projective or formal group proof
```

### 11.4 Bridge-2 from tangent bridge

```lean
-- schematic
lemma bridge2_from_tangent_bridge
    (hpre : evalDual (prePsiPrime n) (x + δ * ε) = 0)
    (hproj : coeffε(t([n]Pε)) = projectiveExpression)
    (htan : coeffε(t([n]Pε)) = (n : K) * τ)
    (hn : (n : K) ≠ 0)
    (hδ : δ = ψ₂(P) * τ)
    (hψ₂ : ψ₂(P) ≠ 0) :
    τ = 0 := by
  -- use the established bridge architecture
```

### 11.5 Bridge-2 from simple-root theorem

```lean
-- schematic
lemma bridge2_from_simple_prePsiPrime
    (hdual : evalDual (prePsiPrime n) (x + δ * ε) = 0)
    (hroot : (prePsiPrime n).eval x = 0)
    (hsimple : (Polynomial.derivative (prePsiPrime n)).eval x ≠ 0)
    (hδ : δ = ψ₂(P) * τ)
    (hψ₂ : ψ₂(P) ≠ 0) :
    τ = 0 := by
  -- coeffε of hdual gives δ * (preΨ'_n)'(x) = 0
  -- hsimple gives δ = 0
  -- hψ₂ and hδ give τ = 0
```

---

## 12. Final checkpoint

The current maintained understanding is:

```text
Torsion.lean has 3 remaining sorries, all not-ours.
Bridge-1 is closed.
Bridge-2 is the only real owned mathematical blocker.
The projective formula side is almost closed: Z+X done, Y 6/7.
The tangent bridge is irreducible: it needs d[n]|_O=n or an equivalent independent fact.
```

Do not spend further time trying to derive bridge-2 from `φ_n(P)≠0` alone.  That only proves no cancellation.  The next productive work is either:

```text
finish projective Y and implement W.formalGroup / formalNsmul_coeff_one with parameter compatibility,
```

or

```text
finish projective Y and prove the first-order tangent bridge directly from projective formulas,
```

or

```text
prove squarefreeness/simple-root of preΨ'_n independently and close bridge-2 by dual numbers.
```
