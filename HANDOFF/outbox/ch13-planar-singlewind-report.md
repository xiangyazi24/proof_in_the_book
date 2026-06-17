# Ch13 planar single-wind no-repeat — bricks A + B report

File: `ProofsInTheBook/ZinanFFCT94.lean`
Verified on uisai2 (HEAD 29f399c): **0 errors**, clean-3 axiom prints
(`propext`, `Classical.choice`, `Quot.sound`) for all three guarded theorems.
NOT committed (master commits after independent re-verification).

## What closed

### Brick A — `PlanarLiftedTurnSpan` (data certificate)
Implemented faithfully to the design §Q1 shape, with one necessary correction:
the structure is **`Type`-valued, not `Prop`-valued**. The design wrote
`structure ... : Prop`, but a `Prop`-valued structure cannot carry the data
fields `θ : ℕ → ℝ` and `ρ` (Lean rejects projecting non-proof fields out of a
`Prop`). It is therefore a plain `structure` (data + proofs). Fields:
`in_plane`, `u_perp_h`, `v_perp_h`, `u_unit`, `v_unit`, `uv_perp`, `θ`, `ρ`,
`ρ_pos`, `edge_eq`, `turn_pos`, `turn_lt_pi`, `one_wind`.

Two further adaptations for Lean:
- `edge_eq` is indexed by a **natural** `m` with `hm : m + 1 < N` (instead of
  `i : Fin N` with `i + 1`), so the successor never wraps inside the open chain
  and the telescoping sum over `Finset.Ico` is clean.
- orthonormality is recorded as the three inner products `⟪u,u⟫=1`, `⟪v,v⟫=1`,
  `⟪u,v⟫=0` (more directly usable than `‖u‖=1 ∧ …`).

A half-wind sub-certificate `PlanarLiftedTurnSpanHalf extends PlanarLiftedTurnSpan`
adds `half_wind : θ N - θ 0 < π`.

### Brick B — `planarWeakConvex_strictTurns_halfWind_noNonadjacentRepeat`
**Statement proved (half-wind case):**
```
{N : ℕ} [NeZero N] {Q : Fin N → E3} {h u v : E3}
(cert : PlanarLiftedTurnSpanHalf Q h u v) : PlanarNoNonadjacentRepeat Q
```
where `PlanarNoNonadjacentRepeat Q := ∀ r s, r+2 ≤ s → Q⟨r⟩ ≠ Q⟨s⟩` (the planar
`E3` analogue of `SphericalKernel.NoNonadjacentRepeat`, which is `S2`-typed).

**Proof (complete, no sorry):**
1. `displacement_telescope`: for `r ≤ m`, `Q⟨m⟩ - Q⟨r⟩ = ∑_{i∈[r,m)} ρᵢ·(cos θᵢ•u + sin θᵢ•v)` (induction on `m` via `edge_eq` + `Finset.sum_Ico_succ_top`).
2. A repeat `Q⟨r⟩ = Q⟨s⟩` (`r+2 ≤ s`) makes the displacement vanish.
3. `covector_component`: pairing each lifted direction with the midpoint
   covector `w = cos φ•u + sin φ•v`, `φ = (θ r + θ(s-1))/2`, gives exactly
   `cos(θᵢ - φ)` (orthonormality + `Real.cos_sub` sum-to-product).
4. `inner_sum` pushes the pairing through, so `0 = ∑_{i∈[r,s)} ρᵢ·cos(θᵢ - φ)`.
5. half-wind ⟹ `θ(s-1) - θ r ≤ θ N - θ 0 < π`, so every `θᵢ - φ ∈ (-π/2, π/2)`
   ⟹ `cos(θᵢ - φ) > 0` (`Real.cos_pos_of_mem_Ioo`); with `ρᵢ > 0` the sum is
   strictly positive (`Finset.sum_pos`, nonempty `Ico`). `0 < 0`, contradiction.

`hsupp` (weak convexity) is **not needed** for the half-wind case — the lifted
certificate is self-contained. `theta_strictMono` (from `turn_pos`) supplies the
ordering.

## Honesty / non-vacuity guards

- `witChain_certificate : Nonempty (PlanarLiftedTurnSpanHalf witChain wH wU wV)` —
  an explicit 3-vertex strictly convex corner that turns left by `π/8`
  (`θ m = m·π/8`, `ρ ≡ 1`, total span `2·π/8 = π/4 < π`). The hypothesis set is
  **genuinely satisfiable**; the theorem is not vacuous.
- `halfWind_span_lt_pi` records that any half-wind certificate forces span `< π`.
  The doubled triangle of `ZinanFFCT93` has lifted `θ` running `0 → 4π`, span
  `4π ≥ π`, so it cannot carry a half-wind (nor even a `one_wind`, span `4π ≥ 2π`)
  certificate. The doubled triangle therefore no longer refutes the conclusion.

## Residual (the general `one_wind` < 2π case)

The general `one_wind` case is **stated but not closed**, and importantly it is
**not provable from `turn_pos` + `turn_lt_pi` + `one_wind` + `ρ>0` alone**. The
closed equilateral triangle (`θ : 0, 2π/3, 4π/3`, all turns `2π/3 ∈ (0,π)`,
total turn `2π`) is a positive combination of directions whose lifted angles span
`< 2π` and yet **sums to zero**. Concretely, for any sub-run that genuinely
closes (`∑ ρᵢ dᵢ = 0`), the directions cannot lie in any open semicircle, so the
single-covector telescoping fails for span `∈ [π, 2π)`.

Excluding the closing run in the `[π, 2π)` regime requires the **support
hypothesis `hsupp`** (weak convexity over the whole chain, including the wrap):
the partial sums `S_m = ∑_{i∈[r,m)} ρᵢ dᵢ` trace a convex polygon whose signed
areas `det2(d_r, S_m)` keep a consistent sign, forcing `S_m` into a half-plane
and `≠ 0` until a *full* `≥ 2π` turn closes it — which `one_wind` (`< 2π`)
forbids. This `det2`-monotonicity argument is the genuine remaining content; it
was scoped out tonight in favor of landing the complete, axiom-free half-wind
core. Exact remaining goal:

```
theorem planarWeakConvex_strictTurns_oneWind_noNonadjacentRepeat
    {N : ℕ} [NeZero N] {Q : Fin N → E3} {h u v : E3}
    (hsupp : ∀ i j : Fin N, j ≠ i → j ≠ i + 1 → 0 ≤ det3 (Q i) (Q (i+1)) (Q j))
    (cert : PlanarLiftedTurnSpan Q h u v) :
    PlanarNoNonadjacentRepeat Q
```
to be proved via partial-sum `det2`-sign monotonicity (convex-polygon stays in a
half-plane), splitting the closing run at the index where cumulative turn first
crosses `π`.

## Downstream wiring (not done here, by scope)
Brick C (gnomonic transport) and the WBS single-wind preservation (design §Q4
bricks C–G) are unchanged and still pending; they consume the *one_wind* planar
theorem, so they wait on the residual above. The half-wind core is already enough
for any spherical arm whose gnomonic image has total exterior turn `< π`.

---

## ADDENDUM (re-verification pass, 2026-06-13) — corrected §3.3 adversarial finding

Re-verified the file on uisai2 @ `29f399c`: **0 errors, 0 warnings**, all three
theorems clean-3. The half-wind core, `witChain_certificate`, and the
honesty-guard are intact and faithful. No `sorry`/`admit`/`axiom`/`native_decide`.

One correction to the residual analysis above. The §Residual section (and the
handed-down strategy) assert the `[π,2π)` band closes via a "convex partial-sum
polygon stays in a half-plane / cannot return to the origin" argument once `hsupp`
is added. An adversarial numerical check (200k + 1.5M targeted trials) shows the
convex-non-return argument is, on its own, **insufficient — and the strategy's
specific framing is refuted by a concrete witness:**

- **Single equilateral triangle** (`Q₀,Q₁,Q₂,Q₃=Q₀`, `θ : 0,2π/3,4π/3`): every
  turn `2π/3 ∈ (0,π)`, sub-run span `4π/3 < 2π` (passes `one_wind`), and
  `Q₃=Q₀` is a nonadjacent repeat. Its partial-sum polygon IS a strictly-convex
  closed polygon that DOES return to its vertex `S₀=S₃=0`. So a convex polygon
  *can* return to its own vertex; the convex-non-return / single-bisector route
  cannot exclude the band `span ∈ [π,2π)`.

- The full brick B is nonetheless **TRUE** (0 counterexamples in 200k forward +
  1.5M targeted constructive trials). What excludes the triangle is the **global
  cyclic `hsupp`** acting against the *off-run* vertices: convex closed sub-runs
  with span `∈ [π,2π)` exist abundantly (263k+ found), but none embeds inside a
  globally cyclically-weakly-convex `Fin N` arm without violating `hsupp`. The
  genuine residual is therefore a global-support argument (a self-overlapping
  single-wind arm breaks cyclic weak convexity against vertices outside the
  overlap) — **not** the partial-sum `det2`-monotonicity of the run alone, which
  the triangle defeats.

This corrected obstruction is recorded in the file header comment as a checked
fact. Per the honesty contract, the clean half-wind theorem (which already
excludes both the doubled *and* the single triangle) is the landed deliverable;
the strict-`<2π` band is left as the documented, true-but-global residual rather
than shipping a partial-sum proof the single triangle refutes.
