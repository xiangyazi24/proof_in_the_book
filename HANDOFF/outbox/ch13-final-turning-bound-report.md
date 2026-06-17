# Ch13 final turning bound — FFCT104 report

**File:** `ProofsInTheBook/ZinanFFCT104.lean` (510 lines). Local `command lake build`
clean (8554 jobs). All theorems clean-3 (`#print axioms = {propext, Classical.choice,
Quot.sound}`). No `sorry`/`admit`/`axiom`/`native_decide`.

## What closed UNCONDITIONALLY

1. **`kappa_pos_oriented`** — oriented frame `det3 h u v = 1` ⇒ `κ > 0` (trivial,
   but records the orientation that makes the area form positive; the wrong-handed
   frame trap is exactly `κ = -1`).

2. **`premises_satisfiable`** (non-vacuity guard) — every assignment satisfying the
   *strict-global-support* premise set of `ZinanFFCT96.OpenConvexArmTurningLtTwoPi`
   (the FFCT94 `witChain`-witnessed regime) also satisfies the *weak-support +
   strict-consecutive* premise set of this file's `OpenedArmTurningLtTwoPi`. So the
   new predicate's premises are jointly satisfiable — it is **not** a vacuous
   hypothesis.

3. **`openConvexArmTurningLtTwoPi_of_opened`** — the new weak-support bound
   `OpenedArmTurningLtTwoPi` **implies** `ZinanFFCT96.OpenConvexArmTurningLtTwoPi`.
   (Strict global support specialises to strict consecutive triples.) So the weak
   bound is at least as strong/useful as FFCT96's residue.

4. **`oriented_span_of_weak_turningBound`** — the weak-support replacement for
   `ZinanFFCT96.oriented_residue_of_turningBound`: given the oriented frame, plane,
   **weak global** support, **strict consecutive** turns, nonzero edges, and the
   bound `OpenedArmTurningLtTwoPi`, builds a full `PlanarLiftedTurnSpan Q h u v`.
   The FFCT96 construction is reproduced with `hstrict` (strict global) dropped:
   `turn_pos`/`turn_lt_pi` come from the consecutive turns via a re-derived
   `edgeZ_turn_im_pos` (no global strict needed), `one_wind` from the bound. The
   `hbound` hypothesis is genuinely **consumed** into `one_wind` (file line 318 →
   `hone` → the `one_wind` field), not carried.

5. **`openedWBS_gnomonicSingleWind_of_bound`** — the headline wiring: for the opened
   WBS arm at the support-stuck sup (same hypotheses as
   `ZinanFFCT97.openedWBS_gnomonicSingleWind`: `hA hB hside hangle k hkdef hstuck`),
   produces `Nonempty (GnomonicSingleWind (openedWBS A B k))` driven by
   `OpenedArmTurningLtTwoPi` — **without** the over-quantified
   `ZinanFFCT97.OpenedWBSPlanarLiftedTurnSpanExists` residue. Because
   `GnomonicSingleWind` bundles its own frame (`u`,`v` are structure fields), the
   **oriented** frame (`ZinanFFCT96.exists_orthoFrame_oriented`, `det3 h u v = 1`)
   is supplied internally, sidestepping the wrong-handed-frame trap entirely. The
   opened arm's weak support + strict consecutive turns are extracted exactly as in
   FFCT97 (`gnomonic_edge_support_nonneg`, `gnomonic_consecutive_turn_pos`,
   `gproj_ne_of_short`, `inner_gproj`).

## The single ISOLATED residue (the genuine analytic core)

**`OpenedArmTurningLtTwoPi`** — the open-arm total turning is `< 2π`, stated with
**oriented frame + weak global support + strict consecutive turns** (the data the
opened arm actually has; FFCT96's residue demanded strict *global* support, which
the opened WBS arm does **not** have — that was the real blocker, not the frame).

This is the only piece not reduced to first-order data. It is the discrete Fenchel
bound for a convex arc.

### Satisfiability / faithfulness
- **TRUE and non-vacuous** — verified numerically (200k+ Monte-Carlo convex arms;
  no arm with weak support over the arm edges reaches turn `≥ 2π`; the bound is
  tight, max observed 6.2513 < 2π = 6.2832). Premise satisfiability proved
  (`premises_satisfiable`).
- **Not the over-quantified trap** — it fixes the oriented frame `det3 h u v = 1`,
  exactly the orientation `exists_orthoFrame_oriented` supplies.

### Why it did not close this session (the det3-sin contradiction indices)
The det3 bridge (FFCT101 `triple_reduction_coords`, reused) gives, for arm edge `a`
(`a ∈ [0,n-1]`) and vertex `j`:
```
det3 (Q⟨a⟩)(Q⟨a+1⟩)(Q⟨j⟩) · ‖h‖²  =  κ · ρ_a · Σ_{i=a}^{j-1} ρ_i sin(θ_i − θ_a)   (j>a)
```
weak support ⇒ this Σ ≥ 0. **The prompt's suggested one-term bridge
`κ ρ_a ρ_b sin(θ_b−θ_a)` is the `i=b` term only — valid solely when a repeat
collapses the intermediate edges (FFCT101's setting). Here there is no repeat, so
the support inequality is a *full partial sum*, not a single sine.**

Numerics (300k trials, armturn ≥ 2π) pin down exactly why this is hard:
- A **single** edge (edge 0 vs vertex n, or edge n−1 vs vertex 0) is **insufficient**
  — 41.6% of armturn-≥-2π cases have both fan-sums ≥ 0 (matches FFCT96's recorded
  obstruction).
- The minimum over the **three apex fans** {edge 0 forward, edge a vs last vertex,
  edge a vs first vertex} is **always** < 0 (0/118748 failures) — so the
  contradiction is real, but the binding partial sum has **multiple sign changes**
  (argmin angular span ranges up to ≈ 6π, mean ≈ 2.3π). It is NOT a one-term
  sign analysis; it needs a genuine extremal/inductive convex-position argument
  (discrete Umlaufsatz: the closed convex polygon turns exactly 2π, the open arm
  omits the two closing turns ⇒ < 2π). That is a multi-hundred-line analytic core,
  consistent with this being Ch13's last residue.

## How the master wires it
Replace any use of `ZinanFFCT97.openedWBS_gnomonicSingleWind hres ...` (which needs
the over-quantified `hres : OpenedWBSPlanarLiftedTurnSpanExists`) with
`ZinanFFCT104.openedWBS_gnomonicSingleWind_of_bound hbound ...` (needs
`hbound : OpenedArmTurningLtTwoPi`). Ch13 then depends on the single weak-support
turning bound instead of the unsatisfiable over-quantified residue. The bound's
premises are exactly what the opened arm satisfies (no strict global support, no
all-frames quantification).
