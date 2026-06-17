# Ch36 Arc-Restricted Parity Sweep — DONE (clean-3)

**File:** `ProofsInTheBook/ZinanCh36ArcSweep.lean` (942 lines, only this file created/edited).
**Status:** Compiles with no errors/sorry/axiom/admit/native_decide. All 10 audited results
depend only on `{propext, Classical.choice, Quot.sound}`.
**Verify:** `lake env lean ProofsInTheBook/ZinanCh36ArcSweep.lean` on uisai2 (after building the
`ZinanCh36Lobes` olean upstream — it was missing on uisai2; I built it).

## What is proved (all pinned shapes matched; only indices massaged)

1. **Chain substrate (§1):** `Chain`, `Chain.segA/segB/carrier/Transverse`, `segTau`,
   `SegCrossesRay`, `segCrossInd`, `Chain.rayCount` — verbatim the pinned signatures, adapted
   to the repo's `det2`/`side`/`Span`/`seg`. The side-coordinate half-open convention is reused
   directly from `PolygonSideCrossing` (`side`, `Span`, `span_iff_opp_sign`).

2. **EndpointSafe (§2):** `Chain.first/last/segTauOf` helpers + `Chain.EndpointSafe η z` =
   "first vertex off line OR first-segment tau < 0" ∧ "last vertex off line OR last-segment
   tau < 0".

3. **THE PORT (§3''''):** `Chain.rayCountParity_eventually_eq` — exact pinned statement.
   Proof partitions `Fin m` into `Rest` (generic, both endpoints off line; individually locally
   constant), interior-vertex pairs `Rp ↔ Np = nextSeg '' Rp` (shared vertex on the line; pair
   parity neutralized by the truth table), and the two endpoint events `Re`/`Ne` (excluded by
   `EndpointSafe` → locally backward → constant 0). This mirrors `PolygonWindingExterior`'s
   `windCross_locally_constant_off_boundary` R/N/Rest skeleton, with **ℤ%2** in place of the
   signed sum and `Fin.succ`/`castSucc` adjacency in place of `cyclicNext`.

4. **Transport (§4):** `Chain.rayCountParity_constant_on_segment` — exact pinned statement.
   `IsLocallyConstant` on `Icc 0 1` pulled back along `lineMap`, mirroring
   `windCross_constant_on_ray`.

5. **Cheap extras (§5):** `lineCoord r η x p := det2 (p − x) η / det2 r η` (pinned formula) with
   `lineCoord_on_line` (affine on segments); `side_ray_eta`
   (`side r x (z + t•η) = side r x z + t·det2 r η`, pinned identity); and
   `Chain.rayCount_zero_of_coordMax` (all vertices strictly behind z ⟹ all sides one strict
   sign ⟹ no span ⟹ rayCount = 0).

## The vertex-handoff atom fit — NO mismatch

`span_mod_two_through_vertex` fit the chain pairing **exactly**, as the design predicted: an
interior chain vertex has BOTH incident segments present (`segB i = segA (nextSeg i)` is the
shared side value `s`), so the truth table `[Span a s] + [Span s b] ≡ [Span a b] (mod 2)`
applies verbatim. The only adaptation needed was a 6-line ℤ cast wrapper
(`span_mod_two_through_vertex_int`) since `segCrossInd` is ℤ-valued while the polygon atom is
ℕ-valued; the underlying combinatorial lemma is reused unchanged.

The chain's only genuinely new content over the polygon is the **endpoint handover**: the two
ends of an open chain carry an unpaired incident segment. `EndpointSafe` forces that segment
locally backward (uncounted), so the endpoint vertices are parity-neutral too. This is captured
in `segCrossInd_eventually_eq_endpoint` + the `Re`/`Ne` branches of the assembly.

## Supporting infrastructure built (all clean-3)

- `seg_cross_eq` / `segU` / `segU_mem_Icc` / `onSeg_of_segTau_zero_span` — the standalone raw
  reconstruction layer (chain analogue of `PolygonLocalConstancy.cross_eq`).
- `segTau_shared_eq` — the two incident segments' ray parameters agree at a shared on-line vertex.
- `pair_segCrossInd_eventually_eq` — the interior-vertex pair eventual-parity lemma (chain image
  of `pair_count_eventually_const'`).
- `nextSeg` (total `Nat`-indexed successor map) + `segA_nextSeg` + `nextSeg_injOn`.

## Notes

- Two unused-hypothesis warnings are cosmetic, not vacuity: `hden` in `segU_mem_Icc`/
  `continuous_segTau_base`/`segU_mem_Icc_of_span` (kept for interface symmetry), and `hη` in
  `rayCount_zero_of_coordMax` (the all-sides-positive argument doesn't need the no-flat-segment
  guard; kept to document the intended `Transverse` regime, matching the design).
- Statement faithfulness: `rayCount` is the genuine span+forward-guard sum; the headline is a
  true local-constancy `∀ᶠ` with the three pinned hypotheses, not weakened or vacuous.
