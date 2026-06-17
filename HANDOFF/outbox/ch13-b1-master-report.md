# Ch13 B1 MASTER report — bricks 5, 6, 9 (`ProofsInTheBook/ZinanFFCT27.lean`)

**Status:** compiles clean-3 (0 errors), all main results `#print axioms` =
`[propext, Classical.choice, Quot.sound]`. No `sorry`/`axiom`/`admit`/`native_decide`.
File: `ProofsInTheBook/ZinanFFCT27.lean` (NEW; only file touched). Not committed.

---

## THE BRICK-6 FINDING (most important)

**The design's §6 statement `halpha_of_hbeta_and_positive_axis_joint` is VACUOUS — its hypothesis
set is unsatisfiable.** This is proved rigorously as `design_halpha_hyps_unsatisfiable`:

> `det3 p mid q = 0`, `ShortArc mid q`, `ShortArc mid p`, `hβ ≥ 0`, `0 < sphAngle p mid q` ⟹ `False`.

### Why (mechanism, fully rigorous in Lean)

`sphAngle u v w := angle(tangentTo v u, tangentTo v w)` — the angle **at the middle argument `v`**.
So `sphAngle p mid q` is the angle **at `mid`**. Writing the span decomposition `p = a•mid + b•q`
(from `det3 p mid q = 0` over the independent base `(mid, q)`, via FFCT25's
`lin_indep_span_of_det3_zero`), the tangent of `p` at `mid` is

```
tangentTo mid p = b • tangentTo mid q          (theorem `tangentTo_span`)
```

— a *scalar multiple* of the tangent of `q` at `mid`. With `G := ⟪mid,q⟫` and unit norms:

- `hβ-quantity = ⟪p,q⟫ − ⟪p,mid⟫⟪q,mid⟫ = b·(1 − G²)`, and `1 − G² > 0` strictly (independence),
  so **`hβ ≥ 0 ⟺ b ≥ 0`**.
- `b > 0` ⟹ `tangentTo mid p` is a **positive** multiple of `tangentTo mid q` ⟹ `sphAngle p mid q = 0`
  (Mathlib `angle_smul_left_of_pos` + `angle_self`).
- `b = 0` ⟹ `tangentTo mid p = 0` ⟹ `p = ±mid` ⟹ `¬ ShortArc mid p`.

So `0 < sphAngle p mid q` excludes `b > 0`; `hβ` forces `b ≥ 0`; together `b = 0`, killed by
`ShortArc mid p`. The hypothesis set is contradictory. **The design's joint-positivity hypothesis is
the wrong companion mechanism** (the prompt's suspicion was correct).

### The TRUE companion mechanism

The companion sign is **`a ≥ 0`** (where `hα = a·(1 − G²)`, so `hα ≥ 0 ⟺ a ≥ 0`), and it is a genuine
**convex-position residual** that does NOT come from the opening derivative or from the joint angle at
`mid`. This is independently confirmed by the substrate's own audit
`HANDOFF/design-rounds/ch13-B5-B1-audit.md`:

> "B1 AUDIT: support-zero alone CANNOT give the Gram signs (branch ambiguity — this is why
> StuckAtKData stores them) … + companion sign." / "a > 0 needs `no_repeat_of_positiveJoints`
> (nonadjacent repeated vertex forces an interior flat joint — master, 180-300 lines)".

And by the proven first-corner precedent `SphericalSZ.StuckData`, where **both** Gram signs (`signA`,
`signC`) are carried as raw convex-position fields of `SZOpeningCore`, NOT derived from one derivative.

A further geometric clarification (from `SphericalStuckGeneral`'s own numeric docstring, lines 31-34):
the betweenness at the genuine stuck config is at the **axis** vertex `A⟨n⟩ ∈ span≥0 {A⟨n-1⟩, qstar}`
with **both** coefficients strictly positive — so the `a ≥ 0` sign is real and provable, just by the
no-repeat/positive-joints brick, which is explicitly a LATER wave, not bricks 5/6/9.

### What I delivered for brick 6 (honest, non-vacuous)

- `tangentTo_span`, `one_sub_gram_sq_pos`, `hbeta_eq_bcoef_mul`, `halpha_eq_acoef_mul` — the algebraic
  core (`hβ = b(1−G²)`, `hα = a(1−G²)`, `1−G² > 0`).
- `hbeta_iff_bcoef_nonneg`, `halpha_iff_acoef_nonneg` — the two clean equivalences.
- `halpha_of_acoef_nonneg` — the **satisfiable** companion: derives `hα ≥ 0` from the genuine residual
  `a ≥ 0` (exposed as the named hypothesis `hacoef`). This is the correct interface to thread the
  no-repeat/positive-joints brick into the wrapper.
- `design_halpha_hyps_unsatisfiable` — the finding itself.

**Residual handed to the master:** the single honest input `a ≥ 0` (i.e. `hacoef`), to be supplied by
the no-repeat / positive-joints master brick (NOT in this wave). Everything else in brick 6 is proved.

---

## Bricks proven

| Brick | Theorem | Notes |
|---|---|---|
| 5 | `hbeta_of_axis_edge_binding` | `hβ ≥ 0` from the axis-incident binding edge, assembling FFCT26's `hasDerivAt_mixedSupport` + `deriv_nonpos_of_left_nonneg_zero` + `det3_axis_cross_eq_neg_gram_S2`. Hypothesis `haxis : A ij.2 = openAxis A` makes the cross-axis the edge's 2nd vertex. **Complete.** |
| 6 | (see finding above) | algebraic core + equivalences + satisfiable companion `halpha_of_acoef_nonneg` + the unsatisfiability finding. **Complete modulo the named `a ≥ 0` residual.** |
| 9 | `StuckAtKData_of_axis_edge_binding` | full `StuckAtKData (openArm A δ) B i (n+1)` at the axis-incident cut; index bridge `mixedSupport_eq_sOrient_openArm` (`i,i+1 ≤ n` fixed, tail = `Fin.last`). **Complete.** |

Supporting: `det3_cyc` (cyclic, to feed the span extractor), `mixedSupport_eq_sOrient_openArm`
(the `openArm` index bridge). Two non-vacuity `example`s included (playbook §3.3).

## Verification

```
scp … ZinanFFCT27.lean uisai2:… && ssh uisai2 'lake env lean ProofsInTheBook/ZinanFFCT27.lean'
```
→ 0 errors. `lake build ProofsInTheBook.ZinanFFCT27` → completed (8486 jobs). `#print axioms` on all 6
main results → clean-3 only. Only remaining diagnostics are upstream Mathlib `push_neg` deprecation
notices (advisory, not in scope).

## Interface notes for downstream assembly

- Brick 5's output Gram form is `0 ≤ ⟪p,q⟫ − ⟪p,mid⟫⟪q,mid⟫` with `q = rot (openAxis A) δ tail`,
  matching `StuckAtKData.hβ` (with `mid = A(i+1) = axis`, `q = openArm last`). To feed brick 9, rewrite
  `q` as `(openArm A δ (Fin.last (n+1)) : E3)` via `openArm_last` + `rotS2_coe`.
- Brick 9 instantiates `N := n+1`, cut `(i, n+1)`; `i+1 < n+1` from `hi_axis : i+1 = n`. The tail index
  `n+1 = (Fin.last (n+1)).val` is bridged by a local `Fin.ext` `hlast`.
- The `a ≥ 0` companion residual is exactly the audit's `no_repeat_of_positiveJoints` brick; once
  landed, compose it through `halpha_of_acoef_nonneg` (or directly `halpha_iff_acoef_nonneg`).
