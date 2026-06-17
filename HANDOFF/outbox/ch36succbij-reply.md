# Ch36 SuccBij — two residual geometric items LANDED (reply)

STATUS: NEW file `ProofsInTheBook/ZinanCh36SuccBij.lean` created, compiles clean.
All 9 audited theorems are clean-3 (`{propext, Classical.choice, Quot.sound}`).
No `sorry` / `axiom` / `admit` / `native_decide`. No other edits. 943 lines.

VERIFY: `scp` to uisai2 + `lake env lean ProofsInTheBook/ZinanCh36SuccBij.lean` after
`lake build ProofsInTheBook.ZinanCh36Alternation`. All `#print axioms` clean-3 (no sorryAx).

## Item 1 — boundarySucc injectivity + single-cycle covering (UNCONDITIONAL in `hvert`)

* `boundarySucc_injOn` / `boundarySuccSub_injective` — the `hinj` slot of
  `boundarySucc_cycle_connected` / `fullLineCrossingAlternation_of_geom`. Direct cyclic-distance
  argument (NOT via the list): if `nextCrossing i = nextCrossing j = m` with `i ≠ j`, the
  forward-offset composition `arcPos i (cyclicSteps i j + cyclicSteps j m) = m` plus the two
  `no_crossing_before_next` minimality bounds (`cyclicSteps i m ≤ cyclicSteps i j`,
  `cyclicSteps j m ≤ cyclicSteps j i`) force `cyclicSteps i m = 0`, contradicting positivity.
  `boundarySuccSub_injective` matches `hinj` verbatim.
* `boundarySucc_cover` — the `hcover` slot: the forward orbit of any fixed crossing `i₀` covers
  ALL crossings. Proven NOT from injectivity alone (a permutation can split into cycles) but via
  the `cyclicSteps i₀`-key rank: strong induction on `keyf i₀ w`, a key-predecessor crossing `c`
  (largest crossing key `< key w`, `i₀` qualifies) has `nextCrossing c = w`
  (`nextCrossing_eq_of_keyf_successor`: walk-forward-next = key-order-next, via key composition
  `key (nextCrossing c) = (key c + nextCrossDist c) mod n` + the no-crossing-between gap), so
  `w = succ c` is in the orbit. `boundarySucc_cover` matches `hcover` verbatim.
* `boundarySucc_orbit_covers` (underlying-value form) and
  `boundarySucc_cycle_connected_unconditional` (discharges `boundarySucc_cycle_connected` with NO
  named geometric hyps beyond `hvert`).

## Item 2 — carrier disjointness of distinct same-sign lobes

* `upperLobes_carrier_disjoint` / `lowerLobes_carrier_disjoint` — match the `hdisj` slots of
  `upper_noninterleaving_ascending` / `lower_noninterleaving_ascending` (Brick 1) verbatim:
  `Disjoint (lobeChain (upperLobeOfPos … i …)).carrier (lobeChain (upperLobeOfPos … j …)).carrier`
  for distinct `i ≠ j` with `eSign` both `+1` (resp. `lobeChainL`/`lowerLobeOfNeg`, both `−1`).

  Two layers:
  - **Combinatorial core** `upperLobe_index_disjoint` / `lowerLobe_index_disjoint`: the walk-edge
    index sets are disjoint. In `cyclicSteps a`-offset coordinates the X-offsets are `[0, dA]` and
    the Y-offsets `[β, β+dB]` (β = cyclicSteps a b); the SIGN-FLIP rules out the boundary
    collisions (`b ≠ bsucc a`, `a ≠ bsucc b` since the successor has the opposite sign) and
    `no_crossing_before_next` forces `β > dA` and `β + dB < n`, so the offset intervals are
    disjoint in `[0,n)` ⟹ `arcPos_injOn_lt` gives distinct edge indices.
  - **Geometric layer**: each clipped chain segment ⊆ its polygon edge
    (`lobeChain_seg_subset_edge`; feet meet edges in the OPEN interior via `crossU_mem_Ioo`).
    A shared carrier point gives two DISTINCT polygon edges (index disjointness) meeting; the
    `EdgeIntersectionCondition` adjacency cases reduce to a STRONGER index collision
    (`arcPos a (iX+1) = arcPos b jY`) EXCEPT at the genuinely-last clipped segment, where the
    shared vertex is the post-`bsucc` vertex — on the NEGATIVE side (for `+1` lobes; positive for
    `−1`), contradicting `carrier_side_nonneg` (resp. `carrierL_negside_nonneg`). Nonadjacent
    edges are disjoint outright.

This addresses items 1 and 3-of-the-carrier-part (the named `hinj`/`hcover`/`hdisj` residues) of
`ch36alternation-reply.md`. The remaining geometric residue NOT in this file is the
foot-order-symmetric `¬ TauInterleaves` (the 6 non-ascending interleave configs) — that is the
separate noninterleaving-symmetry item, not touched here.

These are FAITHFUL-UNCONDITIONAL (in `hvert`) discharges of the named hypotheses; nothing smuggled
via `def : Prop` or trivially-true wrappers.
