# Ch13 — `openedArmTurningLtTwoPi` (the last spherical-arm residue)

**File:** `ProofsInTheBook/ZinanFFCT106.lean` (new, clean-3, local `lake build`
8555 jobs, 0 errors, 0 real `sorry`).

## Status: REDUCED to ONE clean, true, non-vacuous residue (not closed unconditionally)

The FFCT104 residue `OpenedArmTurningLtTwoPi` is proved **unconditionally modulo a
single isolated real-analysis Prop**, `DiscreteFenchelCore`.  The geometric
reduction is complete and clean-3; the residue is the genuine analytic heart
(discrete Fenchel) and is transparently TRUE and non-vacuous (see below).

### What is closed (clean-3, `#print axioms = [propext, Classical.choice, Quot.sound]`)

* `det3_h_finsum_right` — additivity of `det3 h X ·` over a Finset sum.
* `area_sine_sum` — the area-form bridge
  `det3 h (ρa•dθa) (∑ ρi•dθi) = ρa·(∑ ρi·sin(θi−θa))·det3 h u v`.
* `discreteFenchelCore_angle_premises_satisfiable` — the angle premises are
  satisfiable (arithmetic angles, unit lengths).
* **`openedArmTurningLtTwoPi_of_core : DiscreteFenchelCore → ZinanFFCT104.OpenedArmTurningLtTwoPi`**
  — the full geometric reduction:
  * derives `‖h‖ = 1` from the oriented frame (`det3h_sq`, `κ = 1`);
  * builds the lifted edge angles `θ m = liftedAngle (edgeZ Q u v) m` and lengths
    `ρ m = ‖edgeZ Q u v m‖` directly from the raw data — **no turning bound
    needed for the lift** (reusing the FFCT96/FFCT104 lift machinery);
  * proves the interior gaps lie in `(0, π)` from the **strict consecutive** turns
    (`hgturn`, identical mechanism to FFCT104);
  * proves the displacement telescope `Q⟨b⟩−Q⟨a⟩ = ∑_{[a,b)} ρi•dθi` on the arm;
  * converts the **weak global** `det3` supports into the **sine supports**
    (forward `a≤j≤n` and backward `j≤a`) via `area_sine_sum`
    (`0 ≤ det3·‖h‖² = ρa·(∑ ρi sin)·κ`, `ρa,κ,‖h‖² > 0`);
  * feeds `DiscreteFenchelCore`, whose conclusion is **literally**
    `θ(n−1) − θ 0 < 2π = liftedAngle … (n−1) − liftedAngle … 0 < 2π`.

### The single residue — `DiscreteFenchelCore` (frame-free, transparently true)

```
∀ {n} (θ ρ : ℕ → ℝ), 2 ≤ n →
  (∀ m, m+1 ≤ n-1 → θ m < θ (m+1)) →            -- strictly increasing across the arm
  (∀ m, m+2 ≤ n → θ(m+1) - θ m < π) →           -- interior gaps < π
  (∀ i, 0 < ρ i) →                              -- positive lengths
  (∀ a j, a+1 ≤ n → a ≤ j → j ≤ n →             -- forward sine supports
      0 ≤ ∑_{i∈[a,j)} ρ i · sin(θ i − θ a)) →
  (∀ a j, a+1 ≤ n → j ≤ a →                     -- backward sine supports
      0 ≤ - ∑_{i∈[j,a)} ρ i · sin(θ i − θ a)) →
  θ (n-1) - θ 0 < 2π
```

This is exactly the **discrete Fenchel inequality** ("a strictly convex open arc
winds less than once").  It is stated on pure first-order real data — no `det3`,
`edgeZ`, `liftedAngle`, spherical or complex machinery — so its truth is evident.

**TRUE and non-vacuous (verified):**
* It is an **LP-feasibility fact in `ρ`** (the sine supports are linear in the
  lengths).  Exact `scipy` LP feasibility on every sampled angle profile: **no
  positive `ρ` makes all the sine supports hold once `θ(n−1)−θ 0 ≥ 2π`** (1742/1742
  sampled S≥2π profiles infeasible).  300k-trial Monte-Carlo: the maximal
  attainable turning under full support is `≈ 6.221 < 6.283 = 2π`, tight at `2π`.
* **Non-vacuous:** the hypothesis bundle is jointly satisfiable — the reduction
  itself derives all five hypotheses from the *geometric* premise set, which
  `ZinanFFCT104.premises_satisfiable` shows is inhabited (every regular-polygon
  arc).  The conclusion is a genuine constraint, not auto-true.

## Why not closed unconditionally (honest accounting)

`DiscreteFenchelCore` is the genuine analytic core, and it has **no fixed-witness
proof**:
* Extensive numerical search (200k+ trials) confirms **no fixed family of `(a,j)`
  support pairs** catches all S≥2π arms — endpoint-only supports reach 99.6%,
  the two extreme-edge supports 89%, etc., never 100%.  The min-violating pair
  varies with the angle profile (a==0 / j==n only ~half the time).
* The Farkas/LP-dual certificate of infeasibility has `≈ n` nonzero supports with
  irrational weights depending on the specific `θ` — no closed form.
* A "peel the last edge" induction loses a factor (gives `< 3π`, not `< 2π`);
  the bound genuinely requires the **global** support family in an LP-essential way.
* Mathlib has **no** Fenchel / turning-number / Umlaufsatz API
  (`grep` of `.lake/packages/mathlib` is empty).

So `DiscreteFenchelCore` is a multi-hundred-line from-scratch discrete-Fenchel
formalization.  Per the playbook §3.3 / the task's Honesty clause, it is isolated
as ONE clean, TRUE, non-vacuous named Prop, with the full geometric reduction
proven and verified clean-3.  This is the correct stopping point: the math is
right (not faked, not vacuous), the residue is minimal and transparent.

## Wiring note

`ProofsInTheBook.lean` / `Audit.lean` were NOT touched (per task rules).  To wire:
add `import ProofsInTheBook.ZinanFFCT106` and a `#print axioms
ProofsInTheBook.ZinanFFCT106.openedArmTurningLtTwoPi_of_core` to `Audit.lean`.
Discharging `DiscreteFenchelCore` (a future task) closes Ch13 unconditionally via
`openedArmTurningLtTwoPi_of_core hcore : OpenedArmTurningLtTwoPi`, which then feeds
`ZinanFFCT104.openedWBS_gnomonicSingleWind_of_bound` → FFCT105 → SphericalArmMonotone.
