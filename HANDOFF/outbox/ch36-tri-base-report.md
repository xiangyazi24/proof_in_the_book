# Ch36 TRIANGLE SIGNED BASE — report

File: `ProofsInTheBook/ZinanCh36TriBase.lean` (325 lines, 0 sorry/axiom/admit/native_decide).
All three required results compile clean-3 (`#print axioms` = {propext, Classical.choice, Quot.sound}).
Olean built (`lake build ProofsInTheBook.ZinanCh36TriBase` → success, 8526 jobs).

## Deliverables (all UNCONDITIONAL, clean-3)

```
def       triSign (Q : StrictSimplePolygon 3) : ℤ
            := if 0 < orient (Q.q 0) (Q.q 1) (Q.q 2) then 1 else -1
theorem   triSign_unit (Q) : triSign Q = 1 ∨ triSign Q = -1
theorem   triangle_windValuesWithSign (Q : StrictSimplePolygon 3)
            : WindValuesWithSign Q (triSign Q)
```

`triangle_windValuesWithSign` instantiates the master's `ZinanCh36InteriorValue.WindValuesWithSign`
predicate verbatim: `(triSign Q = ±1) ∧ ∀ ρ x, ¬OnBoundary Q x → (∀k, side ρ.r x (Q.q k) ≠ 0)
→ windCross Q ρ x = 0 ∨ windCross Q ρ x = triSign Q`. The two hypotheses are exactly the predicate's
own genericity guards (off-boundary + ray-avoids-vertices) — no hard content smuggled into a
hypothesis, no vacuity.

## Route chosen: UNIFIED pure-arithmetic core (NO interior/exterior split)

The design note suggested "interior ⟹ s, exterior ⟹ 0" with a possible Jordan-exterior-parity
residue. I avoided that entirely. The key observation: at EVERY generic off-boundary point of a
triangle the signed winding is a pure-arithmetic function of

* `s_k := side ρ.r x (q_k)` (the three side coordinates, all ≠ 0 by genericity),
* `O_k := det2 (q_k - x)(q_{k+1} - q_k)` (the three edge crossTau-numerators),
* `O := orient q0 q1 q2 ≠ 0` (noncollinear_consecutive at the middle vertex),

subject to TWO coordinate identities that hold at EVERY point (no barycentric-weight positivity, no
point-in-triangle assumption — proven by coordinate `ring`):

* `triNum_sum`  : `O0 + O1 + O2 = O`
* `triNum_side` : `O1·s0 + O2·s1 + O0·s2 = 0`   (weightless form of the barycentric side identity)

Then `windCross Q ρ x = Σ_k sContrib s_i s_{i+1} O_i`, where
`sContrib a b O' := osign(b-a) · [Span a b ∧ 0 ≤ O'·(b-a)]` (the per-edge `eSign · forward-indicator`;
`osign d := if 0<d then 1 else -1` is exactly `eSign` once the crossDen `s_{next}-s_i` is plugged in).
The core lemma `signed_forward_sum_mem` proves, by a finite real case analysis on the strict signs of
`(s0,s1,s2,O)`, that this sum ∈ {0, osign O}. Geometrically uniform: an exterior ray misses (sum 0)
or enters-and-leaves with opposite eSign (sum 0); an interior ray crosses once with eSign = osign O
(sum osign O). Finally `triSign Q = osign O` by definition, giving the package.

This is the signed analogue of `PolygonTriangleConvex.forward_count_eq_one` (which proved the UNSIGNED
count = 1 for interior points only); here the SIGNED sum is pinned for ALL generic points at once.

Both identities were Monte-Carlo verified (500k random configs, incl. exterior) before formalizing.

## Key lemmas (all clean-3, unconditional)

* `triNum_sum`, `triNum_side` — the two coordinate identities (coordinate `ring`).
* `sContrib_resolve` — signed-indicator resolution (mirrors `indicator_resolve`).
* `signed_forward_sum_mem` — THE arithmetic core (`maxHeartbeats 4000000`; sign case-split + per-edge
  O_k-sign extraction from the forward/backward product bounds, fed to `nlinarith` against the two
  identities). The load-bearing subtlety: an INACTIVE edge whose span IS satisfiable under the current
  signs carries a BACKWARD bound `O_k·Δ_k < 0` (extracted from `¬(Span ∧ forward)` + a sign-built
  span witness) — without it the `windCross ∈ {0,1,-1}` exclusion of `windCross = -triSign` fails.
* `sEdge_eq_sContrib`, `windCross_tri_eq_sContrib_sum` — the bridge from `windCross` (signed edge sum)
  to the `sContrib` form, using `det2_eq_side_diff` (eSign = osign of side difference) and
  `crossTau_nonneg_iff` + `crossTau_mul_crossDen` + `side_next_sub_side` (forward guard in product
  form, exactly as in `crossingNumber'_interior_eq_one`).

## Blocked items

NONE. The brick is complete and unconditional. The kernel bound `windCross_mem_final` was available
but in the end NOT needed — the unified `signed_forward_sum_mem` lands directly in {0, osign O},
which is a subset of {0,1,-1}, so the result is self-contained on the triangle.

## Faithfulness verdict: FAITHFUL

* Statement = the master predicate, instantiated at `s = triSign Q`. No weakening.
* `triSign` definition = the required `if 0 < orient … then 1 else -1`.
* Hypotheses = the predicate's own genericity guards only.
* Non-vacuous: `O ≠ 0` from `noncollinear_consecutive`; identities are unconditional ring facts;
  numerically validated.
