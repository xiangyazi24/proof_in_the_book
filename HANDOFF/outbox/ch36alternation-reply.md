# Ch36 FINAL wiring — ZinanCh36Alternation.lean (reply)

STATUS: file created, compiles clean, all 9 theorems clean-3
(`{propext, Classical.choice, Quot.sound}`). No sorry/axiom/admit/native_decide.
Only NEW file: `ProofsInTheBook/ZinanCh36Alternation.lean`. No other edits.

## Delivered

- **Brick 1 (partial, ascending).** `upper_noninterleaving_ascending` /
  `lower_noninterleaving_ascending`: wire `upper_lobes_not_interleave` /
  `lower_lobes_not_interleave` into the boundarySucc-foot form. The bridge lemmas
  `lobeLastEdge_upperLobeOfPos` / `lobeLastEdgeL_lowerLobeOfNeg` evaluate
  `lobeLastEdge (upperLobeOfPos a) = boundarySucc a` via `upperLobeOfPos_last` +
  `boundarySucc_eq_nextCrossing`, so the lobe feet match `crossTau a` / `crossTau (boundarySucc a)`.
- **Brick 2 (conditional).** `fullLineCrossingAlternation_of_geom`: instantiate
  `alt_of_twoSide_noncrossing_cycle` at S=LineCrossingEdges, τ=crossTau, σ=eSign, ν=boundarySucc.
  Discharged in-file: hτinj (crossTau_injOn_lineCrossingEdges), hνmem (boundarySucc_mem),
  hpm (eSign_mem), hflip (boundarySucc_sign_flip), L (exists_sorted_enum), and hcycle via
  `boundarySucc_cycle_connected`. Produces the exact `Halt` shape the dichotomy pipeline consumes.
- **Brick 3 (conditional).** `rayWindingDichotomy_of_geom`, `rayCrossingAlternation_of_geom`:
  feed Brick 2 through `rayWindingDichotomy_of_fullLineAlternation` /
  `rayCrossingAlternation_of_fullLineAlternation`. `hvert` kept (required by the pipeline; the
  kernel is FALSE without it — see ZinanCh36Theta §8.2).
- **Brick 3' (unconditional).** `triangle_rayCrossingAlternation_final` (re-export).
- **Brick 4 (chapter bridges).** `windCross_mem_of_rayCrossingAlternation` (UNCONDITIONAL from any
  kernel): windCross ∈ {0,1,-1}. `triangle_windCross_mem` (UNCONDITIONAL, n=3, end-to-end).
  `windCross_mem_of_geom` (conditional, general n).

## Where the chain STOPS and WHY (honest)

The UNCONDITIONAL chain reaches: triangle (n=3) RayCrossingAlternation + windCross∈{-1,0,1}
END-TO-END; and windCross∈{-1,0,1} from ANY supplied kernel, all n.

The GENERAL-n full-line alternation is NOT unconditional. Three geometric residues, all explicitly
left OUT OF SCOPE by the landed substrate (ZinanCh36LobeWiring header + rank-parity design note),
remain and are taken as named hypotheses of the conditional theorems:

1. `hinj` — boundarySucc injective on the crossing subtype (`boundarySuccSub`). Explicit named
   hypothesis of the landed `boundarySucc_cycle_connected`; not proved anywhere.
2. `hcover` — the orbit of one fixed crossing covers ALL crossings (single-cycle). Likewise an
   explicit named hypothesis of `boundarySucc_cycle_connected`.
3. `hposNI` / `hnegNI` — `¬ TauInterleaves` for EVERY same-sign chord pair. The landed
   `upper_lobes_not_interleave` requires the hinter `crossTau Xstart < crossTau Ystart <
   crossTau Xlast < crossTau Ylast`, i.e. BOTH lobes ASCENDING (start foot < last foot). An upper
   chord's left foot need NOT be its start (rank-parity design note: "an upper chord's left
   endpoint need not have a fixed sign"). Brute enumeration of the 4 distinct feet: of the 8
   interleaving configurations only 2 are ascending and discharged by the landed theorem (Brick 1);
   the other 6 need the foot-order-symmetric noninterleaving, which is NOT the landed statement and
   cannot be re-instantiated (no UpperLobe can start at the eSign=-1 foot). Brick 1 closes exactly
   the ascending 2/8.
   ALSO: carrier-disjointness `Disjoint (lobeChain ...).carrier (lobeChain ...).carrier` is itself
   not a landed lemma; it is a hypothesis of Brick 1.

These are genuine residual GEOMETRY (boundary simplicity ⟹ matchings are noncrossing single-cycle),
NOT wiring. They are stated honestly as hypotheses, not smuggled via def:Prop or trivially-true
wrappers. The conditional theorems are FAITHFUL-CONDITIONAL; the triangle + kernel-consumer
theorems are FAITHFUL-UNCONDITIONAL.
