# Ch13 — the two-sided witness dichotomy for `NearSideWitnessPos` (`ZinanFFCT32.lean`)

Opus Lean worker. New file: `ProofsInTheBook/ZinanFFCT32.lean`. Compiles 0 errors, clean-3 on all 7
main results. No `sorry`/`axiom`/`admit`/`native_decide`. No other file touched. NOT committed.

## The target

`ZinanFFCT31` isolated the last Ch13 sign residue to a single strict determinant sign at an interior
binding of the opened arm `Aδ`: `NearSideWitnessPos := 0 < E_pred`,
`E_pred := det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1))` (the `j-1`-side witness), with a symmetric
`NearSideWitnessSuccPos := 0 < E_succ`, `E_succ := det3 (Aδ j) (Aδ(j+1)) (Aδ(i+1))` (the `j+1` side).
The task: discharge it via the master's two-sided dichotomy.

## What CLOSED (clean-3, unconditional given the binding's geometric surface)

| theorem | content |
|--|--|
| `base_ne_of_shortArc` | the binding-plane base `(Aδ j, Aδ(i+1))` is U2-independent from the edge `ShortArc (Aδ(i+1)) (Aδ j)` |
| `witnessPred_mem_plane` | `E_pred = 0 ⟹ Aδ(j-1) ∈ Π := span {Aδ j, Aδ(i+1)}` (FFCT25 U2 `lin_indep_span_of_det3_zero`) |
| `witnessSucc_mem_plane` | `E_succ = 0 ⟹ Aδ(j+1) ∈ Π` (same U2 after one slot swap) |
| **`not_both_witness_zero`** | **the master's dichotomy core, UNCONDITIONAL** — both witnesses degenerate ⟹ `Aδ(j-1),Aδ j,Aδ(j+1)` coplanar in `Π` ⟹ `det3 = 0` (FFCT22 `coplanar_triple_det3_zero`) ⟹ flat joint at apex `Aδ j` (FFCT22 `far_fold_tail_not_interior`) ⟹ contradicts `PositiveJoints` + non-flat bound |
| `nearSide_witnessSucc_F_nonneg` | the `j+1`-side sign certificate `F := det3 (Aδ j)(Aδ(i+1))(Aδ(j+1)) ≥ 0` from the weak edge support (so `E_succ ≤ 0`) |
| `Esucc_eq_neg_F` | the ring identity `E_succ = −F` |
| **`nearSideWitness_dichotomy`** | **the sign-correct disjunction** `NearSideWitnessPos ∨ 0 < F`, from `E_pred ≥ 0`, `F ≥ 0`, not-both-zero |
| **`nearSideCoeffNonneg_or_predDegenerate`** | **the consumer wrapper** — at every interior binding with `j < n`: `NearSideCoeffNonneg (Aδ i)(Aδ(i+1))(Aδ j)` (closed by FFCT31's pred assembly) ∨ the named residual `NearSidePredDegenerate` |

`#print axioms` on all 7 main results → `[propext, Classical.choice, Quot.sound]` (clean-3).

## The honest sign finding (per the honesty contract — this is the load-bearing result)

The dichotomy CORE (`not_both_witness_zero`) is exactly the master's argument and is fully proven and
clean. But threading it to an UNCONDITIONAL `a ≥ 0` exposed a genuine SIGN obstruction in the master's
"pick whichever side" plan, which I verified as ring identities (and numerically):

* The weak edge supports of the opened arm fix the two witnesses with OPPOSITE sign conventions:
  - edge `(i,i+1)` at `Aδ(j-1)` ⟹ `E_pred ≥ 0` (FFCT31 §2, the sign-correct side);
  - edge `(i,i+1)` at `Aδ(j+1)` ⟹ `−E_succ = F ≥ 0`, i.e. **`E_succ ≤ 0`**.
* FFCT31's coefficient readouts are `0 ≤ a·E_pred` and `0 ≤ a·E_succ`. So:
  - in the branch `0 < E_pred`: `a ≥ 0` ✓ (the consumer's `NearSideCoeffNonneg`);
  - in the branch `0 < F` (`E_succ < 0`): `0 ≤ a·E_succ` forces **`a ≤ 0`** — the WRONG direction.

So the dichotomy disjunction closes `a ≥ 0` ONLY on the pred side. **FFCT31's
`nearSide_a_nonneg_of_witness_succ_pos` (hypothesis `0 < E_succ`) is sign-inconsistent with the weak
support** (`E_succ ≤ 0`): for a genuine convex binding its hypothesis is never met from the arm, and
with `E_succ < 0` the readout gives `a ≤ 0`. The `j+1`-side witness therefore CANNOT certify the
consumer's `a ≥ 0`; the `j+1` assembly closes the boundary case `j = i+2` only vacuously / in the
wrong direction. This is a precise correction to the FFCT31 "both orientations provided" claim.

## The named residual (strictly smaller than `NearSideWitnessPos`)

**`NearSidePredDegenerate A i j := (E_pred = 0)`** — the pred witness degenerates (`Aδ(j-1) ∈ Π`). In
this corner the `j-1` witness is dead and the `j+1` witness has the opposite coefficient sign, so the
LOCAL readout cannot certify `a ≥ 0`. It is exactly the negation of `NearSideWitnessPos` refined to
`E_pred = 0` by the unconditional `E_pred ≥ 0` — strictly smaller than the original residual. Note
`j = i+2` lies entirely inside this corner (then `Aδ(j-1) = Aδ(i+1) = mid`, so `E_pred ≡ 0`): the
boundary case the FFCT31 succ assembly was meant to cover is precisely where the dichotomy stalls.

Closing this corner needs the same global out-of-plane brick the FFCT25 tail-cone / B5-B1 audit
scoped (`HANDOFF/design-rounds/ch13-B5-B1-audit.md`): certifying `Aδ(j+1) ∉ Π` (`0 < E_succ` in the
correct sense, hence both witnesses non-degenerate) from the polygon's STRICT convexity at the
relevant edge, which the weakly-convex opened arm does not supply pointwise.

## Index scope (the `j = n` corner)

The dichotomy needs both neighbours in range: `j-1` (always, `j ≥ i+2 ≥ 2`) and `j+1` (needs `j < n`).
`far_fold_tail_not_interior` likewise needs `j` interior (`j + 1 < n + 1`). So the wrapper carries the
explicit `j < n` side condition. When `j = n` (far vertex is the last index) only the `j-1` witness
exists; that configuration is the axis-edge / last-vertex case the upstream FFCT28
`axis_edge_binding_false_of_positiveJoints` dispatch handles separately, outside this file's algebraic
scope.

## Net for the consumer (FFCT29)

At every interior binding with `j < n`, `nearSideCoeffNonneg_or_predDegenerate` delivers
`NearSideCoeffNonneg ∨ NearSidePredDegenerate` with NO witness-sign hypothesis. FFCT29's
`gramSigns_of_nearSide_axisEdge` consumes the left disjunct unchanged; the right disjunct is the
honest, named, strictly-smaller residual remaining for the global brick. The dichotomy mechanism
itself (`not_both_witness_zero`) is fully formalized and clean — the master's geometric argument is
now in Lean.

## Verification

- `lake env lean ProofsInTheBook/ZinanFFCT32.lean` (uisai2, fresh oleans) → 0 errors.
- `#print axioms` on all 7 main results → clean-3.
- No forbidden tokens (`sorry`/`admit`/`axiom`/`native_decide`) outside the docstring.
- Sign relations independently checked as ring identities (and numerically, `det3` scalar triple form).
