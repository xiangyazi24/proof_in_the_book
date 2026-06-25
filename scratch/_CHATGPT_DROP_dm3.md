# Q416 — design brainstorm: tangent bridge without `W.formalGroup`

Question: can the tangent bridge

```text
coeffε(t([n]Pε)) = (n : K) · coeffε(t(Pε))
```

be proved directly from projective addition/doubling formulas, without constructing the full Weierstrass formal group `W.formalGroup : FormalGroup K`?

Short answer: **yes in principle**, but **not by a naive strong induction using raw homogeneous `addXYZ` on dual-number representatives near `O`**.  The direct route must prove a local/renormalized first-order addition lemma, or equivalently the invariant-differential identity.  That is still the irreducible tangent content, but it can be smaller than a full formal group construction.

---

## 1. Separate the two tangent bridges

There are two related but distinct statements.

### 1.1 Tangent bridge at `O`

For a first-order point near the identity,

```text
Qε = O + τ ε,
```

the desired identity is

```text
coeffε(t([n]Qε)) = (n : K) · τ.              (O-bridge)
```

This is exactly

```text
d[n]|_O = (n : K).
```

### 1.2 Tangent bridge at a finite `n`-torsion point

For a finite point `P` with `[n]P = O`, and a first-order deformation `Pε`, the desired identity is

```text
coeffε(t([n]Pε)) = (n : K) · τ_P(Pε),        (P-bridge)
```

where `τ_P(Pε)` is the tangent coefficient at `P`, measured by the invariant differential.  In affine coordinates at a non-2-torsion point,

```text
τ_P(Pε) = coeffε(x(Pε)) / ψ₂(P),
```

or equivalently

```text
coeffε(x(Pε)) = ψ₂(P) · τ_P(Pε).
```

The finite-point bridge follows from the identity-point bridge only after proving a translation/invariant-differential compatibility statement:

```text
d[n]|_P = d[n]|_O
```

under the standard tangent trivialization by translations.  This is true for a group variety, but in Lean it is another theorem to prove from the group law / projective formulas / invariant differential.

Do not conflate these two bridges.  A raw doubling computation at `O` only addresses the first one.

---

## 2. Coordinate warning: `t = -X/Y` versus `t = -X·Z/Y`

Before implementing any direct proof, fix the coordinate convention.

### Homogeneous projective coordinates

For the usual Weierstrass projective coordinates

```text
[X : Y : Z],       O = [0 : 1 : 0],
```

the affine coordinates are

```text
x = X/Z,
y = Y/Z,
```

and the standard local parameter at `O` is

```text
t = -x/y = -X/Y.
```

A first-order point near `O` can be represented as

```text
A = [ε a : 1 + ε α : ε β],
```

and then

```text
t(A) = -ε a + O(ε²).
```

### Jacobian/projective coordinates

For Jacobian coordinates with affine interpretation

```text
x = X/Z²,
y = Y/Z³,
```

the local parameter is

```text
t = -x/y = -X Z / Y.
```

Then a first-order point near `O` should have `X` and `Y` with nonzero constant terms, e.g.

```text
A = [1 + ε a : 1 + ε α : ε β],
```

so that

```text
t(A) = -ε β + O(ε²).
```

If one instead uses

```text
A = [ε a : 1 + ε α : ε β]
```

with the Jacobian formula `t=-X·Z/Y`, then `t(A)` is order `ε²` and hence zero in dual numbers.  That mixes the two coordinate conventions.

Action item for Lean:

```text
First identify whether the project’s `addXYZ`/`dblXYZ` are homogeneous Weierstrass formulas or Jacobian formulas, and use the corresponding local parameter and normal form for points near O.
```

The earlier projective bridge notes used `t=-X·Z/Y`; the current prompt uses the representative `[εa : 1+εα : εβ]`, which is the natural shape for `t=-X/Y`.  This must be reconciled before any proof is attempted.

---

## 3. What the raw doubling computation proves

Assume the coordinate convention has been fixed.  The suggested doubling calculation is meaningful as a sanity check.

For a first-order point near `O`, the doubling formula often has a nondegenerate first-order `Z` output.  Schematically, for a representative

```text
A = O + ε · v,
```

the raw doubling formula gives

```text
Z(dblXYZ(A)) = 2 · Z(A) + O(ε²)
```

in a Jacobian-style chart, or an equivalent first-order statement for the chosen local parameter.

Thus one can hope to prove a lemma of the form:

```lean
-- schematic
lemma coeff_t_dbl_near_O
    (A : DualPointNearO W K) :
    coeffε (t (dblXYZ A)) = (2 : K) * coeffε (t A) := by
  -- expand dblXYZ to first order in the correct O-chart
```

This proves

```text
d[2]|_O = 2.
```

It also proves powers of two by repeated doubling, assuming each doubled point is normalized back into the same near-`O` chart.

But it does not prove `d[n]|_O=n` for arbitrary `n` unless one also has a first-order addition lemma for two independent near-`O` points.

---

## 4. Why raw `addXYZ` degenerates for two first-order points near `O`

The prompt observes that for two first-order points

```text
A = [εa : 1+εα : εβ],
B = [εb : 1+εγ : εδ],
```

some raw addition formula gives terms like

```text
addZ(A,B) = A[0]·B[2]^2 - B[0]·A[2]^2
          = εa·(εδ)^2 - εb·(εβ)^2
          = 0
```

in `K[ε]/(ε²)`.

This does **not** mean the group sum has zero tangent.  It means the chosen homogeneous formula has a common nilpotent factor and lands in the invalid representative `[0:0:0]` after reduction to dual numbers.

Mathematically, the addition morphism is regular at `(O,O)`, but a particular homogeneous polynomial formula for addition may represent that morphism only after saturation/normalization.  Over a reduced field point this is harmless because one can divide by a nonzero common factor on an open chart.  Over dual numbers, the common factor can be nilpotent, and Lean cannot divide by it.

So the raw formula is hitting the base-locus/normalization problem of projective coordinates over a nonreduced test ring.

Conclusion:

```text
The equality addXYZ(A,B) = [0:0:0] is a coordinate-formula failure, not a group-law fact.
```

This is exactly why the full formal group construction normally changes to local coordinates `t,w` before adding two points near `O`.

---

## 5. The real heart: first-order addition near `O`

The needed direct lemma is:

```text
coeffε(t(A ⊕ B)) = coeffε(t(A)) + coeffε(t(B))
```

for two first-order points near `O`.

Lean-facing statement:

```lean
-- schematic: exact names depend on project APIs
lemma coeff_t_add_near_O
    (W : WeierstrassCurve K)
    (A B : DualPointNearO W K) :
    coeffε (t (addNearO A B)) =
      coeffε (t A) + coeffε (t B) := by
  -- prove in a local O-chart, not by raw unsaturated addXYZ
```

Here `addNearO` should be a normalized/local addition operation near `O`.  It should not be the raw homogeneous polynomial tuple if that tuple can evaluate to `[0:0:0]` on dual points.

Once this lemma exists, the identity-point bridge is easy:

```lean
-- schematic
lemma coeff_t_nsmul_near_O
    (W : WeierstrassCurve K) (n : ℕ)
    (Qε : DualPointNearO W K) :
    coeffε (t (nsmulPoint n Qε)) =
      (n : K) * coeffε (t Qε) := by
  induction n with
  | zero => simp [nsmulPoint, t_O]
  | succ n ih =>
      calc
        coeffε (t (addNearO (nsmulPoint n Qε) Qε))
            = coeffε (t (nsmulPoint n Qε)) + coeffε (t Qε) :=
                coeff_t_add_near_O W _ _
        _ = (n : K) * coeffε (t Qε) + coeffε (t Qε) := by rw [ih]
        _ = ((n + 1 : ℕ) : K) * coeffε (t Qε) := by ring
```

This is much smaller than a full `FormalGroup K` if `coeff_t_add_near_O` can be proved directly.

But `coeff_t_add_near_O` is precisely the linear part of the Weierstrass formal group law.  It is not avoided; it is isolated.

---

## 6. Can strong induction use `dblXYZ` and `addXYZ` directly?

### 6.1 Powers of two

Likely yes, after fixing coordinates and normalization.

A doubling-only induction can prove:

```text
coeffε(t([2^k]Qε)) = (2^k : K) · coeffε(t(Qε)).
```

This uses only `dblXYZ`, provided each output is represented in the same near-`O` chart and the local parameter expression is valid.

### 6.2 General `n` at `O`

Not by raw `addXYZ` on two dual near-`O` inputs.

Any induction using

```text
[n+1]Qε = [n]Qε ⊕ Qε
```

requires adding two near-`O` dual points.  The raw projective formula can lose the first-order information by producing a zero tuple because all coordinates share nilpotent factors.

Possible workarounds:

1. Prove a saturated/renormalized version of `addXYZ` near `O`.
2. Work in local `(t,w)` coordinates and prove the first-order addition lemma directly.
3. Work over a higher-order or two-parameter Artin ring long enough to see the common factor, then prove a normalization theorem.  This is probably harder than option 2.
4. Use the invariant-differential identity instead of near-`O` addition.

### 6.3 General `n` at a finite torsion point

A strong induction along the finite orbit of `P` is possible in principle but not short.

For

```text
[k+1]Pε = [k]Pε ⊕ Pε,
```

the pair `([k]P, P)` may be finite/finite for many `k`, so the usual addition formula may be nondegenerate.  But special cases occur:

* `[k]P = O`;
* `[k]P = P`;
* `[k]P = -P`;
* the sum lands at `O`;
* doubling cases appear when `[k]P=P`.

Handling all of these uniformly is essentially proving differentiability of the group law and translation invariance of the tangent trivialization across the curve.  That is a large local-geometry proof, not a cheap induction.

Thus:

```text
strong induction along finite torsion orbits is possible, but likely longer than either a local tangent-at-O lemma or the invariant-differential identity.
```

---

## 7. Moving from `O` to a finite torsion point

Suppose the identity-point bridge has been proved:

```text
d[n]|_O = (n : K).
```

To apply it at a finite point `P` with `[n]P=O`, one needs translation compatibility.

Mathematically:

```text
[n](P ⊕ Q) = [n]P ⊕ [n]Q = [n]Q
```

when `[n]P=O`.  Therefore, after identifying the tangent at `P` with the tangent at `O` by translation by `-P`,

```text
d[n]|_P = d[n]|_O.
```

Lean-facing theorem:

```lean
-- schematic
lemma tangent_nsmul_at_torsion_from_O
    (W : WeierstrassCurve K) (n : ℕ) (P : Point W K)
    (hP : n • P = O)
    (Pε : DualPointAt W P)
    (τ : K)
    (hτ : invariantTangentCoeff W P Pε = τ)
    (hO : ∀ Qε : DualPointNearO W K,
        coeffε (t (nsmulPoint n Qε)) = (n : K) * coeffε (t Qε)) :
    coeffε (t (nsmulPoint n Pε)) = (n : K) * τ := by
  -- translate Pε to O, use hO, translate back using [n]P=O
```

The missing ingredients are:

```text
translation by P identifies tangent coefficients with the invariant differential;
[n] commutes with translation in the group-law sense;
local parameter t at O is compatible with the translated output near O.
```

This is another way to package the tangent bridge.  It may be easier than `W.formalGroup`, but it is not automatic.

---

## 8. Relation to the Q401 invariant-differential route

The Q401 route tried to prove separability of `preΨ'_n` from the invariant-differential identity

```text
-2 · Φ_n(x₀) · (preΨ'_n)'(x₀) · ψ₂(P)^(1 + [n even])
  = n · ψTwoMulQuot(n)(P).
```

That identity is essentially the finite-point tangent bridge in polynomial form.  It avoids `W.formalGroup`, but it still proves the same first-order fact.

Compared with direct induction on `addXYZ`:

* Q401 uses the existing multiplication/projective formula infrastructure.
* Q401 focuses on a single algebraic identity and a nonvanishing quotient.
* Q401 avoids the raw near-`O` `addXYZ` degeneracy.
* Q401 still needs the Y/ω component to prove `ψTwoMulQuot(n)(P) ≠ 0`.

If the projective formula side already has `Z+X` done and `Y` is `6/7`, Q401 may be the shortest no-`W.formalGroup` route.  Finish the Y/ω identity, then prove the invariant-differential identity or its root specialization.

---

## 9. Recommended direct route without full `W.formalGroup`

There are two viable no-full-formal-group routes.

### Route A: minimal tangent-at-O package

Prove only the first-order addition law in the local `O` chart.

Required lemmas:

```lean
-- schematic
lemma coeff_t_add_near_O
    (A B : DualPointNearO W K) :
    coeffε (t (A ⊕ B)) = coeffε (t A) + coeffε (t B)

lemma coeff_t_neg_near_O
    (A : DualPointNearO W K) :
    coeffε (t (-A)) = - coeffε (t A)

lemma coeff_t_nsmul_near_O
    (n : ℕ) (A : DualPointNearO W K) :
    coeffε (t ([n]A)) = (n : K) * coeffε (t A)
```

Then prove the finite torsion bridge through translation/invariant tangent coefficient:

```lean
-- schematic
lemma coeff_t_nsmul_at_torsion
    (P : Point W K) (hP : [n]P = O) (Pε : DualPointAt W P) :
    coeffε (t ([n]Pε)) = (n : K) * invariantTangentCoeff W P Pε
```

Pros:

* avoids constructing the full `FormalGroup K`;
* proves exactly the needed tangent law;
* conceptually clean.

Cons:

* still requires a local chart or saturated addition formula near `O`;
* still requires translation compatibility for finite `P`;
* raw `addXYZ` over dual numbers is insufficient without normalization.

### Route B: invariant-differential / projective formula identity

Prove the Q401 identity:

```text
ψ₂ · (Dφ_n · ψ_n - 2φ_n · Dψ_n) = n · (ψ_{2n}/ψ_n)
```

then specialize at `preΨ'_n=0` to obtain separability and bridge-2.

Pros:

* reuses `addX`, `addY`, and `Z` projective formula work;
* avoids near-`O` add formula degeneracy;
* directly targets the non-2-torsion finite-point setting.

Cons:

* it is the tangent bridge in algebraic form;
* needs the Y/ω quotient nonvanishing;
* parity handling for even `n` must be correct.

Given the current project state, Route B likely has the highest leverage.

---

## 10. What not to do

Do not try to prove general `d[n]=n` by repeatedly applying raw `addXYZ` to dual points near `O`.  The zero tuple problem is structural.

Do not interpret `[0:0:0]` from a raw formula as a valid projective result.  It indicates that the chosen polynomial representative has lost information over a nonreduced ring.

Do not use a representative with `t=-X·Z/Y` unless the near-`O` normal form has nonzero constant `X` and `Y`.  If the normal form is `[εa : 1+εα : εβ]`, the compatible local parameter is `t=-X/Y`.

Do not assume that `d[n]|_P=d[n]|_O` in Lean without proving translation/invariant-differential compatibility.

---

## 11. Bottom line

The direct tangent bridge without `W.formalGroup` is viable, but the proposed raw `addXYZ` strong induction is not sufficient as stated.

What `dblXYZ` gives:

```text
A direct sanity proof of d[2]|_O = 2,
and probably d[2^k]|_O = 2^k by repeated doubling.
```

What is still needed for all `n`:

```text
coeffε(t(A ⊕ B)) = coeffε(t(A)) + coeffε(t(B))
```

for two first-order points near `O`, proved in a normalized local chart, or an equivalent invariant-differential identity.

The best no-full-formal-group plan is therefore one of:

```text
(1) prove a minimal local tangent addition lemma near O and induct on n;
```

or

```text
(2) prove the Q401 invariant-differential identity from the projective formula infrastructure.
```

Given that the project already has substantial projective formula infrastructure and only the Y/ω component is partially unfinished, the Q401 invariant-differential route is probably shorter than constructing a local near-`O` addition chart from scratch.
