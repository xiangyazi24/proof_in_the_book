# `_CHATGPT_DROP_dm3`: Mathlib status for prime-to-`p` torsion injection under good reduction

Question checked:

> For Mazur torsion, can we use the classical fact that, for an elliptic curve `E/ℚ` with good reduction at `p`, the reduction map
> `E(ℚ) → E(𝔽_p)` is injective on `m`-torsion when `gcd(m,p)=1`?
> In particular, for `p = 2` and odd `m ≥ 3`, full rational `m`-torsion would inject into `E(𝔽₂)`, giving
> `m^2 ≤ #E(𝔽₂) ≤ 5`, contradiction.
>
> Does Mathlib already have the elliptic-curve formal group at a prime? Does it already have this torsion-injectivity theorem? What infrastructure is needed?

## Bottom line

As of the checked `mathlib4` snapshot, I do **not** see a ready-made theorem of the form

```lean
-- schematic, not current Mathlib API
theorem reduction_injective_on_torsion_prime_to_p
    (E : EllipticCurveOverQ) (p m : ℕ)
    (hgood : E.HasGoodReductionAt p) (hcoprime : Nat.Coprime m p) :
    Function.Injective (fun P : E[m](ℚ) => reduce_mod_p P)
```

I also do **not** see an elliptic-curve-specific formal group at a prime, nor the classical result that the kernel of reduction is pro-`p` / has no prime-to-`p` torsion.

What Mathlib does have is a significant amount of adjacent infrastructure:

* generic one-dimensional formal group laws in `Mathlib.RingTheory.FormalGroup.Basic`;
* Weierstrass curve integrality/minimality/reduction over a DVR in `Mathlib.AlgebraicGeometry.EllipticCurve.Reduction`;
* nonsingular Weierstrass points with an abelian group law in affine and Jacobian coordinates;
* group-theory facts about `p`-groups and torsion modules.

So the shortcut is mathematically correct, but it is not currently a one-line Mathlib lookup.  The missing bridge is the reduction map on points plus the formal-group/no-prime-to-`p`-torsion theorem for its kernel.

## What I found in Mathlib

### 1. Generic formal group laws exist, but not the elliptic formal group at `p`

`Mathlib.RingTheory.FormalGroup.Basic` defines

```lean
FormalGroup R
```

as a one-dimensional formal group law over a commutative ring, with fields like `toPowerSeries`, `zero_constantCoeff`, linear coefficients, and associativity.  It also has additive and multiplicative examples, plus a `map` operation on coefficients.

Useful source/documentation links:

* `Mathlib/RingTheory/FormalGroup/Basic.lean`
* docs: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/FormalGroup/Basic.html`

But this is generic formal group-law infrastructure.  I did not find an elliptic-curve formal group constructed from a Weierstrass equation using the usual parameter at the identity, nor a theorem identifying the kernel of reduction of an elliptic curve with the maximal ideal points of that formal group.

### 2. Curve-level reduction over DVRs exists

`Mathlib.AlgebraicGeometry.EllipticCurve.Reduction` defines the main curve-level predicates and constructions:

```lean
WeierstrassCurve.IsIntegral
WeierstrassCurve.IsMinimal
WeierstrassCurve.reduction
WeierstrassCurve.HasGoodReduction
WeierstrassCurve.hasGoodReduction_iff_isElliptic_reduction
```

This is the right starting point for the good-reduction part.  The file explicitly works over fraction fields of discrete valuation rings and defines the reduction of a minimal Weierstrass equation over the residue field.

Useful source/documentation links:

* `Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.lean`
* docs: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Reduction.html`

Important naming note: `IsGoodReduction` is now a deprecated alias; the current name is `HasGoodReduction`.

### 3. Point groups exist, but the existing `map` is not reduction modulo `p`

Mathlib has nonsingular points and group laws, e.g.

```lean
WeierstrassCurve.Affine.Point.instAddCommGroup
WeierstrassCurve.Jacobian.Point.instAddCommGroup
WeierstrassCurve.Jacobian.Point.toAffineAddEquiv
```

In the affine point file there is a point map

```lean
WeierstrassCurve.Affine.Point.map
```

but this is for an algebra homomorphism between field extensions.  It requires an injective field map `F →ₐ[S] K`, so it is not the residue map from a local ring/fraction field to a residue field.  In particular, it does not directly give a homomorphism

```lean
E(ℚ) →+ E(𝔽_p)
```

or

```lean
E(K) →+ Ē(k)
```

for a DVR `R`, fraction field `K`, and residue field `k`.

Useful source/documentation links:

* `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`
* `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.lean`
* docs: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.html`
* docs: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Point.html`

### 4. The group-theory side has useful pieces once the kernel is known to be `p`-primary

`Mathlib.GroupTheory.PGroup` defines

```lean
IsPGroup p G
```

for multiplicative groups and has facts such as

```lean
IsPGroup.iff_orderOf
IsPGroup.orderOf_coprime
IsPGroup.powEquiv
```

These can discharge the abstract group-theory step once the reduction kernel has been represented as a `p`-group or, more likely for elliptic curves, once each finite quotient in the kernel filtration is a `p`-group.

For additive torsion subgroups/modules, `Mathlib.Algebra.Module.Torsion.Basic` has

```lean
Submodule.torsionBy R M a
```

which is a good Lean representation for `m`-torsion in an additive group viewed as a `ℤ`-module:

```lean
Submodule.torsionBy ℤ EPoint (m : ℤ)
```

Useful source/documentation links:

* `Mathlib/GroupTheory/PGroup.lean`
* `Mathlib/Algebra/Module/Torsion/Basic.lean`
* docs: `https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/PGroup.html`

## Infrastructure needed for the classical theorem

Here is the realistic dependency chain for formalizing the desired shortcut.

### A. Arithmetic/local setup for `ℚ` at `p`

For the final Mazur use case, one wants a convenient DVR model for `ℚ` at `p`, probably some localization of `ℤ` at `(p)`:

```lean
R := ℤ localized at the prime ideal (p)
K := FractionRing R      -- or identify with ℚ
k := ResidueField R      -- identify with ZMod p
```

Needed lemmas:

```lean
IsDiscreteValuationRing R
IsFractionRing R ℚ
ResidueField R ≃+* ZMod p
```

For `p = 2`, the residue field identification with `ZMod 2` is needed if the final bound is stated as `#E(𝔽₂) ≤ 5`.

### B. A reduction map on points

One needs an actual group homomorphism, for a minimal integral model with good reduction,

```lean
reduce : W.Point(K) →+ (W.reduction R).Point(k)
```

or a comparable version in Jacobian/projective coordinates.

This is not the same as the current field-extension `Point.map`.  It must be built from integral/projective representatives and the residue map

```lean
residue R : R →+* ResidueField R
```

Likely proof obligations:

1. every `K`-point has a representative with coordinates in `R`, after scaling;
2. at least one coordinate is a unit, so the reduced projective point is not `(0,0,0)`;
3. the reduced point lies on the reduced Weierstrass equation;
4. under good reduction, nonsingularity is preserved;
5. the construction is independent of the chosen representative/scaling;
6. the construction preserves addition.

This is where Jacobian/projective coordinates are probably better than affine coordinates.  Affine coordinates only cover points whose `x,y` coordinates are integral; projective reduction also handles points with denominators and the point at infinity.

### C. The elliptic formal group

Classically, the kernel of reduction is described by the formal group at the identity.  For a Weierstrass equation over a local ring, one introduces a local parameter, for example

```text
t = -x / y
```

near the point at infinity, writes the other local coordinate as a power series in `t`, and obtains the formal group law from addition on the curve.

A Mathlib development would need something like:

```lean
-- schematic
noncomputable def WeierstrassCurve.formalGroup
    (W : WeierstrassCurve R) : FormalGroup R
```

plus the local description of the kernel:

```lean
-- schematic
ker_reduce ≃ maximalIdeal R with group law from W.formalGroup
```

The generic `FormalGroup R` structure can probably be reused, but the elliptic-specific construction and the connection to point reduction appear to be missing.

### D. No prime-to-`p` torsion in the kernel

There are two plausible formalization routes.

#### Route D1: Pro-`p`/filtration route

Build the usual filtration

```text
E₁(K) = ker(E(K) → Ē(k))
Eₙ(K) = points reducing to O modulo 𝔪ⁿ
```

and prove that the quotients are additive groups over the residue field, hence `p`-groups:

```text
Eₙ(K) / Eₙ₊₁(K) ≃ additive group of k
```

Then conclude that the kernel is pro-`p`, so any finite-order element in the kernel has `p`-power order.  The abstract group-theory lemmas around `IsPGroup` should help here, but one may need additive wrappers or additive versions for EC point groups.

#### Route D2: Direct formal-group multiplication route

For this specific theorem, it may be shorter to avoid formalizing a full pro-`p` group.  Prove directly that if `m` is a unit in the local ring, then multiplication by `m` on the formal group is injective on the maximal ideal.

The key formal-power-series fact is:

```text
[m](T) = m*T + higher-order terms.
```

If `m` is prime to `p`, then `m` is a unit in `R`; therefore `[m]` has a compositional inverse as a formal power series, or equivalently preserves the valuation of a nonzero sufficiently small parameter.  Hence `[m](t) = 0` implies `t = 0`.

This route proves exactly what the Hasse shortcut needs:

```lean
-- schematic
lemma ker_reduce_no_torsion_of_isUnit
    (hm : IsUnit (m : R))
    {P : reduce.ker} (hP : m • P = 0) : P = 0
```

Then the injectivity on `m`-torsion is just the group-hom kernel argument:

```lean
-- schematic
lemma reduce_injective_on_torsion
    (hm : IsUnit (m : R)) :
    Function.Injective
      (fun P : Submodule.torsionBy ℤ W.Point (m : ℤ) => reduce P)
```

This direct route may be substantially smaller than developing the full pro-`p` statement.

## The `#E(𝔽₂) ≤ 5` bound does not need Hasse

For the particular `p = 2` endpoint, the upper bound is much easier than the Hasse bound.

Over `𝔽₂`, an affine Weierstrass point is either the point at infinity or a pair `(x,y) : 𝔽₂ × 𝔽₂` satisfying the equation and nonsingularity condition.  There are only four possible affine pairs, so

```text
#E(𝔽₂) ≤ 1 + 2 * 2 = 5.
```

Lean-facing route:

1. use `WeierstrassCurve.Affine.Point` over `ZMod 2`;
2. define an injection into `Option ((ZMod 2) × (ZMod 2))` by sending `0` to `none` and `some x y h` to `some (x,y)`;
3. conclude

```lean
Nat.card W.Point ≤ Nat.card (Option ((ZMod 2) × (ZMod 2))) = 5
```

If the curve is represented in Jacobian coordinates, use `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv` to transfer the cardinality bound to affine points.

So for Q2077, after the reduction-injection theorem is available, the final contradiction can avoid formalizing the full Hasse theorem:

```text
m^2 = #((ZMod m) × (ZMod m))
    ≤ #E(𝔽₂)
    ≤ 5,
```

which contradicts `m ≥ 3`.

## Suggested theorem targets

A clean API would separate the abstract group argument from the elliptic-curve geometry.

### 1. Abstract group lemma

```lean
-- schematic
lemma AddMonoidHom.injective_on_torsion_of_ker_no_torsion
    {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) (m : ℕ)
    (hker : ∀ x : f.ker, m • (x : G) = 0 → x = 0) :
    Function.Injective
      (fun x : Submodule.torsionBy ℤ G (m : ℤ) => f x)
```

This should be easy once the exact representation of `m`-torsion is chosen.

### 2. Kernel has no prime-to-`p` torsion

```lean
-- schematic
lemma WeierstrassCurve.reduce_ker_no_torsion_of_coprime
    (W : WeierstrassCurve K) [W.HasGoodReduction R]
    (m : ℕ) (hm : IsUnit (m : R))
    {P : reduce R W .ker} (hP : m • (P : W.Point) = 0) :
    P = 0
```

For `R = ℤ_(p)`, `IsUnit (m : R)` follows from `Nat.Coprime m p`.

### 3. Prime-to-`p` torsion injects under reduction

```lean
-- schematic
lemma WeierstrassCurve.reduce_injective_on_torsion_of_coprime
    (W : WeierstrassCurve K) [W.HasGoodReduction R]
    (m : ℕ) (hm : IsUnit (m : R)) :
    Function.Injective
      (fun P : Submodule.torsionBy ℤ W.Point (m : ℤ) => reduce R W P)
```

### 4. `𝔽₂` cardinality bound

```lean
-- schematic
lemma WeierstrassCurve.card_points_le_five_over_zmod_two
    (W : WeierstrassCurve (ZMod 2)) [W.IsElliptic] :
    Nat.card W.Point ≤ 5
```

This is probably much smaller than a general Hasse-bound formalization.

## Recommendation for Q2077

Do not count on the prime-to-`p` torsion injection being already available.  The hard missing component is not the final cardinal arithmetic; it is the local reduction/formal-group theorem.

For the specific `p = 2` contradiction, the minimal useful formalization path is:

1. build/obtain the reduction homomorphism at a good prime;
2. prove its kernel has no odd torsion, preferably via the direct formal-group `[m](T)` unit argument;
3. use the elementary `#E(𝔽₂) ≤ 5` bound by counting affine coordinate pairs;
4. finish with `m^2 ≤ 5` and `3 ≤ m` contradiction.

Also note the mathematical hypothesis: the `p = 2` shortcut applies only when the chosen model has good reduction at `2`.  For an arbitrary elliptic curve over `ℚ`, good reduction at `2` is not automatic; the formal statement should keep `hgood : HasGoodReduction` explicit.
