# Ch13 — `planar_properRepeat_is_fullClosure` — CLOSED (unconditional)

**File:** `ProofsInTheBook/ZinanFFCT101.lean`
**Status:** compiles on uisai2, 0 errors, 0 `sorry`/`admit`/`axiom`/`native_decide`.
**Axioms (both headline theorems):** `[propext, Classical.choice, Quot.sound]` (clean-3).

## What is unconditional

```
theorem planar_properRepeat_is_fullClosure
    {N : ℕ} [NeZero N] {Q : Fin N → E3} {h u v : E3}
    (cert : PlanarLiftedTurnSpan Q h u v)
    (hsupp : ∀ i j : Fin N, 0 ≤ det3 (Q i) (Q (i + 1)) (Q j))
    {r s : ℕ} (hr : r < N) (hs : s < N) (hrs : r + 2 ≤ s)
    (hrep : Q ⟨r, hr⟩ = Q ⟨s, hs⟩) :
    r = 0 ∧ s = N - 1
```
plus the contrapositive `no_proper_repeat` (a proper repeat `0 < r ∨ s < N-1` ⟹ `False`).

This is the EXACT statement requested. The only deviation is the added `[NeZero N]`
instance, which is **forced**: the `hsupp` term `Q (i + 1)` uses `Fin N` cyclic
addition, and `1 : Fin N` does not elaborate without `NeZero N`. The spherical caller
(`FFCT97`, `Fin (n+1)`) always carries `NeZero`, so the lemma is directly usable
downstream with no loss. `det3` is `ProofsInTheBook.SphericalKernel.det3`, the `i+1`
is `Fin`-cyclic — matching `FFCT97.hsupport`'s shape.

## No residue

The statement was validated TRUE numerically first (N=5..7, both proper sub-cases,
exhaustive `(i,j)` support scan: every proper-repeat configuration violates `hsupp`).
No counterexample. The Lean proof is unconditional — no isolated `Prop` residue.

## Architecture (reusable pieces)

* `det3_h_dir_dir` : `det3 h (cos α•u+sin α•v)(cos β•u+sin β•v) = sin(β−α)·det3 h u v`
  (pure `ring` on coordinates after `det3` unfold).
* `triple_reduction_coords` / `triple_reduction` : via `FFCT9.det3_plane_eq`,
  `det3 A B C · ‖h‖² = (a₁b₂−a₂b₁)·κ` for apex differences `B−A = a₁u+b₁v`,
  `C−A = a₂u+b₂v`; sine form when the differences are single scaled lifted directions.
* `kappa_pos` : `κ := det3 h u v > 0`. Nonzero from `FFCT9.det3h_sq` (`κ² = ‖h‖²`,
  orthonormal frame); nonnegative from the first consecutive support
  `det3 (Q0)(Q1)(Q2) ≥ 0` with `sin(θ₁−θ₀) > 0`.
* `closed_subarc_span_ge_pi` : the closed sub-arc (`∑_{[r,s)} ρᵢ dᵢ = 0`) forces
  `θ_{s-1} − θ_r ≥ π`. This is the NEGATION of `FFCT94`'s half-wind covector
  positivity (midpoint covector `φ = (θ_r+θ_{s-1})/2`, `covector_component`,
  `Finset.sum_pos`).
* `sin_neg_of_mem_pi_two_pi` : `sin x < 0` on `(π, 2π)` (`Real.sin_sub_pi`).

## The STEP-3 sign clash (the new content)

Every planar `det3` of three vertices equals `(ρ·ρ·sin Δθ·κ)/‖h‖²` with `κ > 0`.
A proper repeat exposes an external vertex against an INTERIOR edge (both edges
involved are `≤ N−2`, so controlled by `edge_eq`/`θ` — the uncontrolled cyclic
closing edge `(N-1 → 0)` is never used):

* **`s < N−1`** (external `Q_{s+1}`): support at edge `r`, vertex `s+1`. Since
  `Q_r = Q_s`, `Q_{s+1} − Q_r = Q_{s+1} − Q_s = ρ_s d_{θ_s}`, so
  `det3(Q_r, Q_{r+1}, Q_{s+1})·‖h‖² = ρ_r ρ_s sin(θ_s − θ_r)·κ`.
  Strict monotonicity gives `θ_s − θ_r > θ_{s-1} − θ_r ≥ π`; one-wind gives `< 2π`.
  Hence `sin(θ_s − θ_r) < 0`, so the `det3` is `< 0` — contradicting `hsupp ≥ 0`.

* **`0 < r`** (external `Q_{r-1}`): support at edge `s-1`, vertex `r-1`.
  `Q_{r-1} − Q_{s-1} = −ρ_{r-1} d_{θ_{r-1}} + ρ_{s-1} d_{θ_{s-1}}` (two edges; uses
  `triple_reduction_coords` directly), giving the coefficient
  `ρ_{s-1} ρ_{r-1} sin(θ_{s-1} − θ_{r-1})·κ` with `θ_{s-1} − θ_{r-1} ∈ (π, 2π)` —
  same `< 0` clash.

The closing edge `(N-1, 0)` being theta-uncontrolled is exactly why the FFCT99
full-closure repeat (`r=0, s=N-1`) is correctly ALLOWED: there the external vertex
would be `Q_{-1}`/`Q_N`, which do not exist, so no clash is forced.

## Notes

Only cosmetic `push_neg` deprecation warnings remain (the project's Mathlib still
ships `push_neg`; sibling files use it throughout). They are warnings, not errors.
