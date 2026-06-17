# Ch13 — `WBSBetaSign` (the far-side `hβ`) via FFCT29's frame-normalization chain at the WBS `-θ` family

**File:** `ProofsInTheBook/ZinanFFCT55.lean` (clean-3, 0 errors).
**Verify:** `scp … uisai2:… && ssh uisai2 'cd ~/repos/proof_in_the_book && ~/.elan/bin/lake env lean
ProofsInTheBook/ZinanFFCT55.lean'` — every `#print axioms` reports only `[propext, Classical.choice,
Quot.sound]`. No `sorry`/`admit`/`axiom`/`native_decide`. (Deps `ZinanFFCT51`/`45`/`29`/`26` oleans built
first on uisai2; the build completed 8508 jobs clean.)

## The honest headline (the sign finding)

The job was to discharge `ZinanFFCT51.WBSBetaSign` (the far-side `hβ` Gram inequality, equivalently the
span coefficient `b ≥ 0`) at the WBS support-stuck binding, by re-instantiating FFCT29's R1–R4
single-rotation derivative chain at FFCT45's `monitoredSupWBS`.

**Result: the chain does NOT discharge `WBSBetaSign`. Re-instantiated at the WBS family, the one-sided
derivative produces the OPPOSITE sign — `b ≤ 0` — because the WBS support member opens by the WIDENING
direction `-θ` (`openedWBS = openTail A K (-(monitoredSupWBS))`, FFCT49), whereas FFCT29's family opens by
`+θ` (`openTail A K θ`, monitored directly).** The extra chain-rule factor from `θ ↦ -θ` flips the
derivative-supplied sign. This is exposed precisely, not faked (honesty contract).

This SHARPENS FFCT51's finding ("`WBSBetaSign` is the genuinely derivative-resistant residue"): the
derivative does not merely fail to read `b ≥ 0`, it reads `b ≤ 0`. The two are compatible only at the flat
corner `b = 0`.

## What lands clean-3

* **§R1/R2 — the constant-binding contradiction (UNCONDITIONAL).** `wbsConstantBinding_false_allRotated`
  / `…_allFixed`: an all-fixed or all-rotated WBS binding triple is impossible (common-rotation invariance
  `sOrient_rotS2` ⟹ the support is `θ`-constant = the original strict support, which cannot vanish). Direct
  re-instantiation of FFCT29's R2 bricks at the angle `-δ*_WBS` (they are free in the angle). So a genuine
  WBS binding triple is **mixed**.

* **§δ*=0 edge (UNCONDITIONAL).** `wbsBinding_delta_zero_false`: when `δ*_WBS = 0` the opened arm IS the
  original `A` (`openTail A K (-0) = A`), so the binding is the ORIGINAL strict support vanishing —
  contradicts `strict_nonincident` directly. (Edge case the spec asked to handle.)

* **§R3 — slot normalization (the `-θ` axis-edge form).** `wbsAxisEdgeSupport A K i j θ :=
  det3 (A i)(A K)(rot (A K)(-θ)(A j))` and `wbsAxisEdgeSupport_eq`: in the axis-edge sub-case
  (`c.i+1 = K`, the FFCT29 dispatch branch where the one-sided derivative reads ONE axis direction), the
  `-θ`-opened support is exactly this single-rotation function (axis `A K` in slot 2, moving point rotated
  by `-θ` in slot 3).

* **§R4 — the one-sided slope with the EXPLICIT ± ledger.** The slot-normalization sign ledger is written
  as lemma-level equalities (never implicit), as the spec requires:
  - `hasDerivAt_rot_neg` — the chain-rule `-1`: `d/dθ (rot (A K)(-θ)(A j)) = -(A K × rot (A K)(-θ)(A j))`.
  - `wbsAxisEdge_deriv_value` — the slot-2 axis contraction `det3 x (A K)(A K × w) = -hβ_form`
    (`det3_axis_cross_eq_neg_gram_S2`) times the chain-rule `-1` MULTIPLY to `+1`:
    `g'(θ) = det3 (A i)(A K)(-(A K × w)) = +hβ_form`.
  - `wbsAxisEdge_hbeta_le_zero` — the one-sided extremum (FFCT26 `deriv_nonpos_of_left_nonneg_zero`,
    `g ≥ 0` on `[0,δ]`, `g(δ)=0`, `δ>0` ⟹ `g'(δ) ≤ 0`) gives `+hβ_form ≤ 0`, i.e. **`b ≤ 0`**.

* **§R4′ — the forced collapse.** `wbsAxisEdge_betaSign_forces_gram_zero`: `WBSBetaSign` (`hβ_form ≥ 0`) +
  the derivative (`hβ_form ≤ 0`) ⟹ `hβ_form = 0`. So at the axis-edge WBS binding, `WBSBetaSign` is
  EQUIVALENT to the flat corner `b = 0` — it is not a derivative output. This is a named, sign-verified
  corner of the same nature as FFCT51's pred-degenerate corner.

## Why `WBSBetaSign` is not delivered (and what the residue actually is)

| | expected (job) | actual (verified) |
|--|----------------|-------------------|
| axis-edge `hβ` sign | `b ≥ 0` from one-sided deriv | deriv gives `b ≤ 0` (`-θ` flips it) |
| general mixed binding | reduce to axis-edge | axis NOT in slot 2 ⟹ contraction is the un-pivoted `det3_cross_expansion` quantity, not the Gram form `hβ` at all |

Two independent obstructions, both faithful to FFCT51's inventory:

1. **The `-θ` sign inversion (axis-edge).** Documented as the "± bookkeeping that killed two designs": the
   widening direction genuinely inverts the derivative sign relative to FFCT29's `+θ` family. The derivative
   forces `b ≤ 0`; `WBSBetaSign` needs `b ≥ 0`. Provided clean-3 as `wbsAxisEdge_hbeta_le_zero` +
   the contrast guard `ffct29_plus_theta_contrast`.

2. **The slot-position obstruction (general mixed).** `WBSBetaSign`'s Gram form pivots on `mid = A'_{i+1}`,
   so the slot-2 axis contraction `det3_axis_cross_eq_neg_gram` produces it ONLY when the rotation axis
   `A K = A'_{i+1}`, i.e. `i+1 = K` (the axis-edge case). For a general mixed binding `i+1 ≠ K`, the
   moving slot is not pivoted on the axis and the Binet contraction is the bare `det3_cross_expansion`
   `⟪x,k⟫⟪y,w⟫ − ⟪x,w⟫⟪y,k⟫`, which is not `hβ`. (FFCT51 §"Why `hβ` genuinely survives".)

So `wbsBetaSign_holds` is NOT provable via the FFCT29 derivative chain, and inventing it would either be
vacuous or false (the derivative refutes the strict form at the axis-edge binding). Per the honesty
contract, the residual is exposed as the genuine sign finding rather than faked. `WBSBetaSign` remains the
sharp residue FFCT51 named; FFCT55 PINS DOWN its mechanism: at the axis-edge binding it is exactly the flat
corner `b = 0`, and the strict `b > 0` (let alone `b ≥ 0` against the derivative's `b ≤ 0`) cannot come from
the one-sided slope. Its genuine source must be the global weak-convexity / near-side pencil (the FFCT31/32
line FFCT51 used for `hα`), or the 2D great-circle brick — NOT this derivative.

## Refutation guards / non-vacuity (playbook §3.3)

* `hasDerivAt_wbsAxisEdgeSupport_guard` — the derivative is a GENUINE `HasDerivAt` (real `-θ` rotation
  derivative), so the one-sided extremum genuinely fires, not a vacuous constant.
* `ffct29_plus_theta_contrast` — the SAME slot-2 contraction with NO chain-rule minus gives `-hβ` (FFCT29's
  `+θ` sign), confirming the `-θ` inversion is real, not a typo.
* `wbsAxisEdgeSupport_eq_guard` — R3 fires on a real axis-edge config (`i ≤ K < j`), not a degenerate rewrite.
* The `hadm` hypothesis (admissibility of `wbsAxisEdgeSupport ≥ 0` on `[0,δ]`) is the SAME real,
  consumer-supplied input FFCT29 uses (`interiorAxisEdge_stuck_betweenness`'s `hadm`); it is satisfiable
  (the WBS closure `supportWBS_sOrient_nonneg` gives the support `≥ 0` at the sup, and the interval form is
  what the assembly threads), NOT an unsatisfiable premise — so the conditional `wbsAxisEdge_hbeta_le_zero`
  is non-vacuous.

## Bottom line

The FFCT29 frame-normalization chain re-instantiates clean-3 at the WBS family (R1/R2 constant-binding
kill, `δ*=0` edge, R3 slot normalization, R4 one-sided slope with the explicit ± ledger), but its honest
output at the WBS **widening** family is **`b ≤ 0`** — the OPPOSITE of `WBSBetaSign`. So `WBSBetaSign`
(`b ≥ 0`) is genuinely NOT a derivative output (it collapses to the flat corner `b = 0` against the
derivative), confirming and sharpening FFCT51's "derivative-resistant residue" finding. The residue stands;
its mechanism is now pinned. No `sorry`/`axiom`/`admit`/`native_decide`; `#print axioms` clean-3 throughout.
