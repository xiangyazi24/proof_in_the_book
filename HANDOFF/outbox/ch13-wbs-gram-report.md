# Ch13 — WBS Gram-sign residue: shrinking `WBSGramSigns` via the FFCT31/32 near-side line

**File:** `ProofsInTheBook/ZinanFFCT51.lean` (330 lines, clean-3, 0 errors).
**Verify:** `lake env lean ProofsInTheBook/ZinanFFCT51.lean` on uisai2 — every `#print axioms` reports
only `[propext, Classical.choice, Quot.sound]`. No `sorry`/`admit`/`axiom`/`native_decide`.
(Deps `ZinanFFCT49`, `ZinanFFCT32` oleans built first; full upstream build is clean-3.)

## What was asked vs. what is honestly deliverable

The job was to discharge (or sharply shrink) FFCT49's `WBSGramSigns` — the **two** Gram inequalities
`hα`, `hβ` of the opened triple `(A' i, A' (i+1), A' j)` at the WBS support-stuck sup — by re-instantiating
the landed frame-normalization / near-side line at the WBS opened arm
`A'_WBS := openedWBS A B k = openTail A (openingAxis k) (-(monitoredSupWBS A B k))`.

After tracing the master's pred-degenerate sketch against FFCT31/32's **actual** lemmas, the honest
verdict is: **the residue shrinks from two opaque Gram signs to one sharp named sign plus one sharp named
corner**, with the companion sign `hα` discharged in-module. The full unconditional kill of the corner
(master step (3)) is NOT achievable in this brick — see the sign verification below.

## The deliverable (clean-3)

**`wbsGramSigns_or_predDegenerate`** (the headline). From
* the geometric surface of `A'_WBS` at the WBS support-stuck sup: `WeakConvexSphArm (openedWBS A B k)`
  (FFCT46 `supportStuckWBS_weakConvex`, unconditional after FFCT47), `NoNonadjacentRepeat`,
  `PositiveJoints`, `JointLe … B`, `StrictConvexSphArm B`;
* the edge short arc `hsa`, the near-pair short arc `hpm`, the binding's vanishing support `hsupp`,
  the ℕ-orientation `i + 2 ≤ j` (the apex short arcs are derived in-module from `edge_short`);
* the **one** sharp residue `WBSBetaSign` (the far-side `hβ` Gram sign, = `WBSGramSigns` conjunct 2),

produces **`ProofsInTheBook.ZinanFFCT49.WBSGramSigns A B k i j … ∨ NearSidePredDegenerate (A'_WBS) i j …`**
— FFCT49's EXACT consumer type on the left.

This re-instantiates FFCT32's `nearSideCoeffNonneg_or_predDegenerate` at the WBS opened arm and assembles
both Gram signs: `hβ` supplied as `WBSBetaSign`, `hα` extracted via FFCT29's `halpha_of_nearSide` from the
`NearSideCoeffNonneg` the near-side witness chain produces.

**`wbsGramSigns_of_hbeta_of_not_predDegenerate`** — the collapsed form: with the corner explicitly
excluded (the input the global 2D-circle / out-of-plane brick would supply), the disjunction becomes the
full `WBSGramSigns`. So FFCT49's two-sign residue is **shrunk to** `WBSBetaSign` + `¬ NearSidePredDegenerate`.

## The honesty-contract sign verification (the master's step (3), checked)

The master's sketch — "in the pred-degenerate corner the succ readout forces `a ≤ 0`, contradicting the
goal `a ≥ 0`, so the corner is impossible" — was sign-checked against FFCT31/32's actual lemmas in
**`predDegenerate_forces_alpha_le_zero`** (clean-3):

* `NearSidePredDegenerate` ⟺ `E_pred := det3 (A'(j-1))(A' j)(A'(i+1)) = 0` (FFCT32);
* the two weak edge supports of `A'_WBS` give `E_pred ≥ 0` (FFCT31 `nearSide_witness_nonneg`) and
  `F := det3 (A' j)(A'(i+1))(A'(j+1)) ≥ 0` (FFCT32 `nearSide_witnessSucc_F_nonneg`);
* `E_pred = 0` + the dichotomy `not_both_witness_zero` (sign-agnostic) force `0 < F`, i.e.
  `E_succ := det3 (A' j)(A'(j+1))(A'(i+1)) < 0` strictly;
* the succ readout `nearSide_a_readout_succ` gives `0 ≤ a · E_succ`, so `E_succ < 0` ⟹ **`a ≤ 0`**.

**Conclusion (the correction to the sketch):** the corner forces `a ≤ 0`, and with `a ≠ 0`
(`nearSide_a_ne_zero`, the no-repeat kill) it forces `a < 0` — i.e. `hα` (`= a ≥ 0`) **genuinely FAILS**
in the corner. The corner is therefore NOT killed by the local readout; it is a real, strictly-smaller
residue that RESISTS local certification (exactly FFCT32's "succ witness has the wrong support-forced
sign" finding). The master's stronger claim ("⟹ contradiction ⟹ corner impossible") would require
refuting the in-plane configuration via the **global 2D great-circle betweenness** (FFCT44/47-class
`coplanar_triple_det3_zero` + circle ordering) — that brick is NOT assembled here, and inventing it would
risk a vacuous or false statement. So the corner is named, not faked.

## Why `hβ` (`WBSBetaSign`) genuinely survives (FFCT28 inventory, confirmed)

For a GENERAL interior WBS binding, `openTail` rotates two-or-three of `c.i, c.i+1, c.j`, so the banked
single-rotation derivative (FFCT26/29 `axisEdgeSupport`, which reads out exactly ONE axis direction) does
**not** apply — FFCT29 discharges `hβ` only in the *axis-edge* sub-case `c.i+1 = K`. The WBS support-stuck
binding is general (not pinned to the axis edge), so `hβ` is the genuinely derivative-resistant sign. It is
the single sharp residue, equivalently the span coefficient `b ≥ 0` over the independent base `(mid, q)`.

## Residue accounting (against FFCT49)

| | FFCT49 `WBSGramSigns` | FFCT51 output |
|--|----------------------|---------------|
| `hα` (near-side) | opaque residue | **discharged** (near-side witness chain, mod corner) |
| `hβ` (far-side) | opaque residue | `WBSBetaSign` (sharp named, multi-rotation `b`-sign) |
| pred-degenerate corner | folded into `WBSGramSigns` | `NearSidePredDegenerate` (sharp named, sign-verified real) |

So the two opaque signs are replaced by **one sharp sign + one sharp corner**, with `hα` assembled.

## Non-vacuity / anti-impostor guards (playbook §3.3)

* `wbsBetaSign_is_gramSigns_snd` / `wbsGramSigns_of_alpha_and_beta` — `WBSBetaSign` is exactly the second
  Gram conjunct and is precisely the data that completes a known `hα` into `WBSGramSigns` (not a
  re-wrapper, not `True`).
* `predDegenerate_corner_is_real` — restates the corner's `a ≤ 0` forcing (a real, failable sign), so the
  corner is load-bearing, neither vacuous nor an over-claimed kill.
* `nearSidePredDegenerate_is_real` — `E_pred = 0` is a genuine determinant constraint (`det3` of axes = 1).

## Threading for the assembly wave

`WeakConvexSphArm (openedWBS A B k)` is `supportStuckWBS_weakConvex hA hB hka hkt hkdef hwrap` (FFCT46).
`NoNonadjacentRepeat`, `PositiveJoints`, `JointLe (openedWBS A B k) B` are the campaign-accepted opened-arm
inputs (the same surface FFCT31/32/48 thread). `WBSBetaSign` and `¬ NearSidePredDegenerate` are the two
inputs the next wave must supply (the multi-rotation far-side derivative / the 2D-circle corner brick).

## Bottom line

`WBSGramSigns` is shrunk, clean-3, to `WBSBetaSign` (one multi-rotation sign) + `¬ NearSidePredDegenerate`
(one sign-verified corner), with `hα` discharged via the re-instantiated FFCT31/32 near-side line. The
master's corner-kill was found to be a corner-RESISTANCE (`a ≤ 0` forced, `hα` fails), correctly named as a
residue rather than faked. No `sorry`/`axiom`/`admit`/`native_decide`; #print axioms clean-3 throughout.
