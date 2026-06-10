# Ch13 — `NearSideCoeffNonneg` discharge via WITNESS-READOUT (`ZinanFFCT31.lean`)

Opus Lean worker. New file: `ProofsInTheBook/ZinanFFCT31.lean`. Compiles 0 errors, clean-3 on all
main results. No `sorry`/`axiom`/`admit`/`native_decide`. No other file touched. NOT committed.

## The target

FFCT29 isolated the LAST Ch13 sign residue to
`NearSideCoeffNonneg p mid q := ∀ a b, (p:E3) = a•mid + b•q → 0 ≤ a` — the near-side span coefficient
sign `a ≥ 0` at an interior binding of the OPENED arm `Aδ = openTail A K δ*`, with
`p = Aδ i`, `mid = Aδ (i+1)`, `q = Aδ j`, the binding `sOrient (Aδ i)(Aδ (i+1))(Aδ j) = 0`, and
`hβ ⟹ b ≥ 0` already supplied. FFCT29's `gramSigns_of_nearSide_axisEdge` /
`interiorAxisEdge_stuck_betweenness` consume exactly this predicate.

## What CLOSED (the FFCT24-T1/T2 witness-readout pattern, near-side variant)

The opened arm presents EXACTLY the FFCT24/25 hypothesis surface — `WeakConvexSphArm Aδ` (so every
edge support is `≥ 0`, which IS the admissibility supply of NonIncident supports at `δ*`),
`NoNonadjacentRepeat Aδ`, and the binding span sign. The orientation is the consumer's axis-edge one:
`i + 2 ≤ j`.

| theorem | content |
|--|--|
| `nearSide_a_ne_zero` | **the `a = 0` kill, UNCONDITIONAL** — `a = 0` ⟹ `Aδ i = b•Aδ j`, units force `Aδ i = Aδ j`, a nonadjacent repeat (`NoNonadjacentRepeat`) |
| `nearSide_witness_nonneg` | `E := det3 (Aδ(j-1))(Aδ j)(Aδ(i+1)) ≥ 0` from the weak support of edge `(i,i+1)` at the `j`-side witness `Aδ(j-1)` (`b > 0`) |
| `nearSide_a_readout` | `0 ≤ a·E` from the weak support of edge `(j-1,j)` at `Aδ i` (the `b·q` term drops, `det3 z'' q q = 0`) |
| `nearSide_a_nonneg_of_witness_pos` | **`a ≥ 0`** from `0 ≤ a·E` + the strict residual `0 < E` |
| `nearSide_a_readout_succ` / `nearSide_a_nonneg_of_witness_succ_pos` | the symmetric `j+1`-side readout/sign (covers `j = i+2`, where the `j-1`-side witness `= mid` degenerates) |
| `nearSide_b_pos_of_shortArc` | `b > 0` from `0 ≤ b` + `ShortArc mid p` (`b = 0` ⟹ `p = ±mid`) |
| `nearSideCoeffNonneg_of_witness` | **the assembly**: produces `NearSideCoeffNonneg (Aδ i)(Aδ(i+1))(Aδ j)` in the EXACT FFCT29 shape, from `WeakConvexSphArm`, `NoNonadjacentRepeat`, the `hβ` Gram sign, `ShortArc`s, and the named residual `NearSideWitnessPos` |
| `nearSideCoeffNonneg_of_witness_succ` | the `j+1`-side assembly (boundary `j = i+2`), residual `NearSideWitnessSuccPos` |

`#print axioms` on all main results → `[propext, Classical.choice, Quot.sound]` (clean-3).

## The honest residual (what shrank, where it stopped — per the honesty contract)

The full surface collapsed to a SINGLE strict determinant sign:

* **`NearSideWitnessPos A i j := 0 < det3 (Aδ(j-1)) (Aδ j) (Aδ(i+1))`** (the `j-1` side), and its
  symmetric `NearSideWitnessSuccPos` (the `j+1` side).

This is "the `j`-side witness vertex is non-degenerate (off the binding plane `span {Aδ j, Aδ(i+1)}`)".
It is NOT a sign assumption masquerading as content:

1. **The `a = 0` kill is fully unconditional** — landed first, per the contract.
2. **`E ≥ 0` is derived unconditionally** (`nearSide_witness_nonneg`), from weak convexity alone.
   So the residual is ONLY the strictness `E ≠ 0`, not the sign.
3. **The residual is genuinely load-bearing and genuinely resistant.** `E` is the support of edge
   `(j-1, j)` at vertex `i+1`; when `j > i+2` it is a NonIncident support, so it would be `> 0` for a
   *strictly* convex arm — but at the binding the opened arm is only WEAKLY convex (the binding support
   itself vanished). Its strictness at THIS configuration is exactly the deep degenerate sub-case the
   master attack flagged ("the j-side witness is non-degenerate"); `E = 0` would put `Aδ(j-1)`,
   `Aδ j`, `Aδ(i+1)`, `Aδ i` all coplanar through the origin, which does not reduce to a single
   consecutive flat-joint triple by local algebra (it needs the same global out-of-plane machinery the
   B5-B1 audit scoped — `HANDOFF/design-rounds/ch13-B5-B1-audit.md` line 3).

Both witness orientations (`j-1` and `j+1`) are provided so the consumer can pick whichever side is
non-degenerate; at least one is available for any interior binding (`j-1` needs `j ≥ i+3`, `j+1` needs
`j < n`; the boundary `j = i+2` is exactly the `j+1`-side case and the far-vertex `j = n` is exactly
the `j-1`-side case).

## Orientation note (for the consumer)

`NonIncident` allows `j < i`; FFCT29's axis-edge consumer (`gramSigns_of_nearSide_axisEdge`) supplies
`c.1.1.val ≤ K.val = (c.1.1+1).val` and `K.val < c.1.2.val`, i.e. `i + 1 < j`, hence `i + 2 ≤ j` — the
orientation this file handles. A `j < i` binding would mirror by relabeling (witness on the `i+1`
side); not needed for the axis-edge dispatch FFCT29 routes to.

## Verification

- `lake env lean ProofsInTheBook/ZinanFFCT31.lean` → 0 errors.
- `lake build ProofsInTheBook.ZinanFFCT31` → built (8489 jobs).
- `#print axioms` on all 6 main results → clean-3.
- No forbidden tokens (`sorry`/`admit`/`axiom`/`native_decide`) outside the docstring.

## Next brick (out of this file's scope)

Discharging `NearSideWitnessPos` / `NearSideWitnessSuccPos` (the strict `0 < E`) — the global
out-of-plane non-degeneracy of the `j`-side witness at the binding. This is the same residual class as
the FFCT25 tail-cone / B5-B1 out-of-plane obstruction; the two-step `tail_two_step_refutation`
machinery (FFCT25 U4) is the candidate mechanism. With it threaded, `nearSideCoeffNonneg_of_witness`
becomes unconditional and FFCT29's `interiorAxisEdge_stuck_betweenness` closes Ch13's interior-axis
STUCK→betweenness with no remaining sign hypothesis.
