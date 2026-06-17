# Refutation report: `PlanarOneWindNoRepeat` is FALSE

**File:** `ProofsInTheBook/ZinanFFCT99.lean` (new file; nothing else touched)
**Theorem:** `ProofsInTheBook.ZinanFFCT99.not_planarOneWindNoRepeat : ¬ ProofsInTheBook.ZinanFFCT97.PlanarOneWindNoRepeat`
**Status:** compiles clean on uisai2 — 0 errors, 0 warnings.
**Axioms (`#print axioms`):** `[propext, Classical.choice, Quot.sound]` — clean-3, no `sorryAx`, no `axiom`, no `native_decide`.

## The result

`ZinanFFCT97.PlanarOneWindNoRepeat` claims: every planar lifted-turn certificate
(`PlanarLiftedTurnSpan Q h u v`) with the single-wind bound `θ N − θ 0 < 2π`
forces `PlanarNoNonadjacentRepeat Q` (no vertex revisited at nonadjacent indices
`r + 2 ≤ s`).

This is genuinely FALSE. The refutation is the single equilateral triangle,
traversed once and recorded as a `4`-vertex CLOSED chain `Q₀,Q₁,Q₂,Q₃ = Q₀`.

## The counterexample (N = 4)

Affine plane `⟪h,·⟫ = 1` with `h = e₂ = (0,0,1)`, frame `u = e₀ = (1,0,0)`,
`v = e₁ = (0,1,0)`. Vertices (`triChain : Fin 4 → E3`, all with third coord 1):

- `Q 0 = (0, 0, 1)`
- `Q 1 = (1, 0, 1)`
- `Q 2 = (1/2, √3/2, 1)`
- `Q 3 = (0, 0, 1) = Q 0`

Edge directions: `Q1−Q0 = (1,0,0)` at angle `0`; `Q2−Q1 = (−1/2, √3/2, 0)` at
`2π/3`; `Q3−Q2 = (−1/2, −√3/2, 0)` at `4π/3`. The three unit edges sum to `0`,
so the chain closes (`Q₃ = Q₀`).

### Certificate fields (`triChain_certificate`)

- `θ m = if m ≤ 2 then m·(2π/3) else 4π/3 + (m−2)·(π/6)`, so
  `θ : 0, 2π/3, 4π/3, 3π/2, 5π/3, …`
- `ρ ≡ 1` (unit edges), `ρ_pos` trivial.
- `edge_eq` (m = 0,1,2): discharged with `Real.cos_zero/sin_zero` and the exact
  values `cos(2π/3) = −1/2`, `sin(2π/3) = √3/2`, `cos(4π/3) = −1/2`,
  `sin(4π/3) = −√3/2` — proved as four standalone helper lemmas via
  `Real.cos_pi_sub` / `Real.sin_pi_sub` / `Real.cos_add_pi` / `Real.sin_add_pi`
  reduced to `Real.cos_pi_div_three` / `Real.sin_pi_div_three`. Coordinate
  bookkeeping by `PiLp.{sub,add,smul}_apply` + `simp`/`ring`.
- `in_plane`, frame perp/unit fields: `ZinanFFCT10.innerE3` + `norm_num`.
- `turn_pos`, `turn_lt_pi`: a helper `triθ_gap` proves every consecutive gap is
  `2π/3` (for m = 0,1) or `π/6` (for m ≥ 2), both in `(0, π)`. (The m = 2 case
  is split out: `θ 2` is taken on the `≤ 2` branch while `θ 3` is on the `else`
  branch — both still evaluate to `4π/3` resp. `4π/3 + π/6`.)
- `one_wind`: `θ 4 − θ 0 = 5π/3 − 0 = 5π/3 < 2π` by `nlinarith [Real.pi_pos]`.

### The contradiction (`not_planarOneWindNoRepeat`)

Assume `H : PlanarOneWindNoRepeat`. Feed it the certificate (`NeZero 4`
instance is available) to get `PlanarNoNonadjacentRepeat triChain`. Instantiate
at `r = 0, s = 3` (`0 < 4`, `3 < 4`, `0 + 2 ≤ 3`) to obtain
`triChain ⟨0⟩ ≠ triChain ⟨3⟩`. But both are `(0,0,1)` by definition, so
`triChain ⟨0⟩ = triChain ⟨3⟩` holds by `rfl`. Contradiction. ∎

## Mathematical content (honesty)

This is a true refutation, not a Lean artifact. The "strictly-convex partial-sum
polygon cannot return to its origin" intuition behind `PlanarOneWindNoRepeat` is
simply false in the span band `[π, 2π)`: a convex polygon DOES close on its own
vertex. The single equilateral triangle has total lifted span `4π/3 ∈ [π, 2π)`,
each interior turn `2π/3 < π`, and `Q₃ = Q₀` is a nonadjacent repeat. This is
exactly the obstruction flagged in `ZinanFFCT94`'s header (lines 29–44): the
half-wind sub-case (`< π`) closes by single-covector telescoping, but the full
`< 2π` band needs the GLOBAL cyclic-support hypothesis `hsupp`, which
`PlanarLiftedTurnSpan` alone does not carry. `PlanarOneWindNoRepeat` drops that
hypothesis and is therefore refutable. Downstream, the correct planar input must
be the half-wind certificate or the support-augmented version, not bare
`PlanarLiftedTurnSpan`.

## Verify recipe used

    scp ProofsInTheBook/ZinanFFCT99.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/
    ssh uisai2 'cd ~/repos/proof_in_the_book && export PATH=$HOME/.elan/bin:$PATH && \
      lake build ProofsInTheBook.ZinanFFCT97 >/dev/null 2>&1 && \
      lake env lean ProofsInTheBook/ZinanFFCT99.lean'

Output: only the `#print axioms` line, `[propext, Classical.choice, Quot.sound]`.

File left in place on uisai2 AND written to the Mac path
`/Users/huangx/repos/proof_in_the_book/ProofsInTheBook/ZinanFFCT99.lean`
(byte-identical to the verified copy). Not committed.
