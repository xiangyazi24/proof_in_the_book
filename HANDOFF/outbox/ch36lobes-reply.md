# Ch36-lobes reply (worker, 2026-06-09)

## STATUS

**Partial — load-bearing bricks banked clean-3; the main theorem
`sameSide_lobes_noninterleave` is NOT closed.** The genuine 2-D Jordan core of the committed
sweep (sub-lemma 4, the moving-ray local constancy) is an irreducible topological residue of
the same difficulty class as the chapter's `RayWindingDichotomy`; it is not cleanly
formalizable from the present substrate without building greenfield arc-restricted ray-parity
local-constancy infrastructure (≈ several hundred lines of 2-D continuity/IVT) or routing
through the dichotomy. Per the prompt's explicit instruction ("IF this corner resists after
honest attempts, STOP and write the obstruction precisely … DO NOT fake, DO NOT add hypotheses
silently"), I banked only what is fully proven and report the obstruction below. **No sorry,
no axiom, no admit, no native_decide anywhere in the file.**

`ProofsInTheBook/ZinanCh36Lobes.lean` (207 lines) compiles on uisai2 with **0 errors, 0
warnings**; **7 theorems**, every one `[propext, Classical.choice, Quot.sound]` (no `sorryAx`,
no `ofReduceBool`/`trustCompiler`). Only the new file was created; nothing else touched.
It imports `ProofsInTheBook.ZinanCh36Theta` directly (NOT the concurrent RayDichotomy file).

## What is proven (all clean-3; `#print axioms` at end of file)

### §A — the abstract 1-D sign-change telescope (the parity heart, polygon-free)
- `aboveInd`, `crossInd` (strict-above indicator; consecutive-pair straddle indicator).
- `crossInd_eq_abs_aboveInd_sub` — per-step atom: a step straddles `t` iff exactly one
  endpoint is above (= |indicator difference|).
- `crossInd_emod_two` — the step's crossing indicator has the parity of the SIGNED
  indicator difference.
- **`sum_crossInd_emod_two`** — THE telescope: along a walk `g 0,…,g m` with no value `= t`,
  `(∑ crossInd t (g k) (g (k+1))) % 2 = (aboveInd t (g m) − aboveInd t (g 0)) % 2`. Proof:
  each step's parity = signed-diff parity (above), and the signed diffs telescope via
  `Finset.sum_range_sub`. This is the exact 1-D / unsigned-parity image of the proven
  `lineCrossing_eSign_sum_zero` per-edge difference. ODD count ⟺ endpoints straddle `t`.

### §B — the along-line coordinate and the crossTau bridge
- `uCoord r x p := ⟪p − x, r⟫`; `uCoord_ray : uCoord r x (x + τ•r) = τ·‖r‖²`.
- `normSq_pos`; **`uCoord_crossPoint`** — a crossing point's `uCoord = crossTau · ‖ρ.r‖²`;
  **`uCoord_crossPoint_lt_iff`** — ordering feet by `crossTau` = ordering by `uCoord`
  (positive scale). This is the design's bridging identity (step 1).

### §C — the lobe structure and the transverse feet-telescope
- `arcPos i k := (i+k) mod n` (cyclic walk position).
- **`UpperLobe`** — the same-side (upper) lobe: `start` (first crossing edge), `len` (walk
  length), `cross_first`/`cross_last` (`SpanCrossesSide` at the two feet edges),
  `interior_pos` (every strictly-interior walk vertex has `side > 0`). Lower mirror is the
  obvious `side < 0` analogue (not yet typed — see below).
- `UpperLobe.vertU k := uCoord ρ.r x (P.q (arcPos start k))`.
- **`UpperLobe.feet_telescope`** — §A specialized: the lobe walk's straddle-count of any
  transverse threshold `t` (avoided by all walk-vertex `uCoord`s) has the parity of the two
  endpoints' `aboveInd` difference. This is exactly sub-lemmas 2/3's parity engine: it gives
  N(r) ODD / N(s) EVEN once instantiated at the foot thresholds.

## The precise obstruction (where the sweep genuinely needs 2-D Jordan content)

The committed design's contradiction is the moving-upward-ray parity invariant
`N(z) = #(A1 ∩ upward vertical ray from z) mod 2`, swept with the base point `z` along A2:
- `N(r)` (A2's foot at `u = τc`) is ODD and `N(s)` (foot at `u = τd`) is EVEN, because the
  vertical line at `u = τc` separates A1's feet `{τa, τb}` while the one at `u = τd` does not
  (here `τa < τc < τb < τd`). **Both parities are clean instances of `feet_telescope` and are
  in-scope** (the §A/§C machinery I banked supplies them).
- The load-bearing residue is **sub-lemma 4: `N` changes parity along A2 only when `z`
  crosses A1** (so `N(r) ≠ N(s)` ⟹ `A2 ∩ A1 ≠ ∅` ⟹ contradiction with
  `EdgeIntersectionCondition`). This is the moving-ray local constancy. It is NOT the
  "both arcs cross V oddly" red herring the prompt's step 5 circles around (that genuinely
  does not contradict); it is the *base-point sweep* invariant, and it IS a true contradiction
  — but its proof is 2-D:
  - the substrate's local-constancy (`openSegmentRegionLocallyConstant_of_sweepNeutral`,
    `regionOf_eventually_eq`, `VertexSweepNeutral`) deforms the base point along a STRAIGHT
    segment with the FULL polygon region (`windCross`/`regionOf`). The sweep needs (i) the
    crossing count restricted to the SUB-ARC A1 (a `Finset` of edges, not the whole boundary),
    (ii) the base point moving along the POLYGONAL path A2 (a concatenation of segments), and
    (iii) the moving-vertical-ray ↔ moving-base equivalence. None of (i)–(iii) is available in
    arc-restricted form; building them is greenfield 2-D continuity/IVT over A1's edges with
    tangency/vertex genericity — the same irreducible Jordan content as the chapter residue
    (`§8` machine-refutations confirm same-side lobe non-interleaving is Jordan-equivalent, not
    a 1-D telescope corollary).
  - The genericity ε-corner the prompt flags (choosing `u0' ∈ (τc, min τb τd)` off the finitely
    many vertex `uCoord`s) is real but SECONDARY — it is dischargeable once (i)–(iii) exist
    (finite bad set ⟹ open free subinterval). It is not the blocker; sub-lemma 4 is.

## Recommendation (for the master's redesign)

Two honest routes, both avoiding new 2-D infrastructure here:
1. **Route through the dichotomy.** Once `ZinanCh36RayDichotomy` lands `RayWindingDichotomy`
   (the concurrent worker), same-side non-interleaving follows from the winding parity along
   the transverse ray directly — the moving-ray invariant `N` is then just `windCross` of a
   transverse `RayDirection`, and sub-lemma 4 becomes the banked windCross local constancy.
   My §A/§B/§C bricks are the consumer-side parity layer for that wiring.
2. **Build arc-restricted ray-parity local constancy** as its own brick
   (`windCross_locally_constant` mirrored onto a `Finset`-of-edges sub-arc + base point on a
   polygonal path), then assemble the sweep. This is the design's literal sub-lemma 4 and is a
   standalone multi-hundred-line task — dispatch it separately; it is not a wiring step.

The 7 banked bricks are exactly the reusable, faithful core either route consumes; none is a
re-wrapper or trivially-true (the telescope and the crossTau bridge are genuine new content).

## VERIFY (run)
```
scp -q ProofsInTheBook/ZinanCh36Lobes.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/ \
 && ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && \
    timeout 1500 lake env lean ProofsInTheBook/ZinanCh36Lobes.lean 2>&1 | head -50'
```
→ 0 errors/warnings; the 7 `#print axioms` lines each report
`[propext, Classical.choice, Quot.sound]`.
