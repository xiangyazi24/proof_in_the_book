# Per-pearl weight aggregation closed — `ProofsInTheBook/BricardAggregate.lean`

**Status: DONE. 0 sorry / 0 axiom / 0 admit / 0 native_decide. Verifies clean on uisai1.
Axioms = core three only.** 633 lines.

I own only the NEW file `ProofsInTheBook/BricardAggregate.lean` (`import
ProofsInTheBook.BricardBalance`). Stayed on `main`; **no commits**; touched nothing else; no
codex/OpenAI tooling; never built locally (kernel-panic rule respected).

> SERVER NOTE: the repo is **not** on uisai2 (only `~/repos/` skeletons there); it lives on
> **uisai1** at `~/repos/proof_in_the_book`. I verified on uisai1. (I synced my local committed
> `BricardBalance.lean` — the `9eff10c`-chain version, byte-identical `WeightedEdgeBalance` Prop to
> uisai1's older variant — so the dependency olean matches the file my module imports.)

## Verification (uisai1)

- `lake env lean ProofsInTheBook/BricardAggregate.lean` → **exit 0, zero output** (no errors, no
  warnings — deprecations and unused-variable lints all cleaned).
- `nohup lake build ProofsInTheBook.BricardAggregate` → **`✔ Built ... (8432 jobs)`** (olean
  generated, integrates into the dependency graph).
- `#print axioms` on the six headline/bridge results → each `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no `ofReduceBool`/`trustCompiler`): `breakCoords_gap_sum_one`,
  `pearlLen_total_on_edgeOcc`, `exists_balanced_pearl_weights`, `exists_srcWeightedEdgeBalance`,
  `weightedEdgeBalance_of_equidecomp`, `regularTet_cube_no_equidecomp_aggregated`.
- `grep` → the only `sorry`/`admit`/`axiom` occurrences are in doc-comment prose; no real ones; no
  `#print axioms` left in the file.

## Item 1 — the pearl-level Pearl-Lemma instantiation (PROVEN, the real content)

The aggregation joint flagged as the sole residue by `opus-bricardbalance-reply.md` is closed.

**(a) Length telescoping — the heart (`breakCoords_gap_sum_one`, PROVEN, no sorry).**
For a raw edge `e ∈ R`, the pearls of `R` sourced on `e` (`pearlsOnSource R e`) tile `[0,1]`: their
`(hi−lo)` gaps sum to `1`. Proof: the breakpoint set `B = breakCoords R e` (`0,1 ∈ B`, `B ⊆ [0,1]`,
`card ≥ 2`) is enumerated by the strictly-monotone `f = B.orderEmbOfFin`; every sourced pearl is
**exactly** a consecutive pair `(f i.castSucc, f i.succ)` (valid-pearl ⇔ consecutive breakpoints,
proved both directions via `range_orderEmbOfFin` + strict monotonicity), giving a bijection
`Fin (card−1) ≃ pearlsOnSource R e`; the gap sum reindexes to `∑_i (f(i+1) − f i)` and telescopes
via `Finset.sum_range_sub` to `f last − f 0 = max'B − min'B = 1 − 0`. Multiplying by `segLen e`:
`pearlLen_sum_on_edge : ∑_{p on e} pearlLen p = segLen e`, and over a piece-edge occurrence
`pearlLen_total_on_edgeOcc : ∑_{p on E.seg} pearlLen p = edgeLen E` (using
`edgeOcc_seg_mem_pieceEdges`: `E.seg ∈ PieceEdges S`).

**(b) The instantiation (`exists_balanced_pearl_weights`, PROVEN, no sorry).**
Index = *all pearls of both solids*: the disjoint union `(Pearls(PieceEdges SP)) ⊕
(Pearls(PieceEdges SQ))` re-indexed by `Fin N`. Real length `len = pearlLen ∘ pearlAt`. One
constraint per P-edge `E`: pair `{indices of P-pearls sourced on E.seg}` with `{indices of Q-pearls
sourced on (edgeOccFwd E).seg}`. The real solution exists because **both sides telescope**:
`∑ pearlLen (P on E.seg) = edgeLen E = edgeLen(edgeOccFwd E) = ∑ pearlLen (Q on (edgeOccFwd E).seg)`,
the middle equality being the proven `edgeOccFwd_edgeLen`. `pearl_lemma` (the abstract Pearl Lemma)
then returns positive integer weights, read off as **two** per-pearl multiplicities `νP`, `νQ`
(everywhere positive; two functions, not one, so the readoff is unambiguous even if a pearl lay in
both canonical sets — `νP` reads the `inl` index, `νQ` the `inr`). The matched per-edge totals are
the source-based `srcWeightOnEdge`.

## Item 2 — `weightedEdgeBalance_of_equidecomp` (the interface instance, PROVEN)

`srcWeightOnEdge` (source-based) → `WeightedEdgeBalance` (the `BricardBalance.lean` interface, which is
**incidence**-based, `weightOnEdge ν P E = ∑_{p incident to E} ν p`). I proved **source ⟹ incidence**
unconditionally (`pearlsOnSource_subset_incident`: a pearl sourced on `E.seg` has `relInterior ⊆
E.seg.carrier = E.carrier`). The converse (no *distinct collinear* raw edge donating an off-source
pearl to `E`'s carrier) is the **one truly resistant joint**, isolated honestly as the named bridge
`EdgeSourceFaithful S` (a finset equality `incident-pearls = source-pearls`, per edge). Under it,
`weightOnEdge = srcWeightOnEdge` (`weightOnEdge_eq_srcWeightOnEdge`), hence the source balance becomes
the interface `WeightedEdgeBalance` (`weightedEdgeBalance_of_srcBalance`). Composed:

`weightedEdgeBalance_of_equidecomp decomp hFP hFQ : ∃ νP νQ, (∀p,0<νP p) ∧ (∀q,0<νQ q) ∧
  WeightedEdgeBalance decomp νP νQ (Pearls(PieceEdges SP)) (Pearls(PieceEdges SQ))`.

## Item 3 — the headline (`regularTet_cube_no_equidecomp_aggregated`, PROVEN)

Composed with `BricardBalance.regularTet_cube_no_equidecomp_sharp`. **The pearl multiplicities and the
weighted edge balance are no longer hypotheses** — they are constructed from the equidecomposition by
the Pearl Lemma. (Named `…_aggregated` to avoid the existing `regularTet_cube_no_equidecomp` in the
same `ProofsInTheBook.Bricard` namespace from `BricardInduce.lean`.)

**Exactly what remains in the headline (the minimal honest hypothesis set):**
1. `Ldata`, `Rdata` — `LocationData` over the canonical pearl sets (the classification layer's
   `PearlSectorModel` certificates);
2. `decomp` — the putative equidecomposition (the object refuted; raw carrier-image data);
3. `hP_arccos`, `hQ_pi2` — the concrete external-angle normalizations `arccos(1/3)` / `π/2`;
4. `hSP : SP.pieces.Nonempty`;
5. `hFP`, `hFQ : EdgeSourceFaithful …` — the **two faithfulness bridges** (collinear-edge
   non-degeneracy of a genuine simplicial decomposition).

So the brief's target "{LocationData/PearlSectorModel + concrete angle normalizations}" is met, plus
the nonempty-solid datum and **the single isolated geometric joint** `EdgeSourceFaithful` (incidence ⇔
source on the canonical pearl sets). That bridge is the one named residue; everything else
(telescoping, Pearl-Lemma instantiation, source⟹incidence, the entire weighted location chain via
`BricardBalance`) is proved unconditionally.

## §3.3 faithfulness / non-vacuity self-audit

- **The telescoping is genuine, not a re-wrapper.** `breakCoords_gap_sum_one` is new mathematics
  (sorted-enumeration bijection + `sum_range_sub`), not a restatement of an existing lemma.
- **VACUOUS-conditional check.** `exists_srcWeightedEdgeBalance` proves `SrcWeightedEdgeBalance` is
  realized **unconditionally** for *any* `decomp`, with everywhere-positive `νP`/`νQ` — the
  Pearl-Lemma aggregation layer is not VACUOUS (`srcWeightedEdgeBalance_nonvacuous`). The bridge
  `EdgeSourceFaithful` is inhabited (`edgeSourceFaithful_of_no_edges`; a genuine `∀ E ∈ allEdgeOccs`,
  not unsatisfiable-by-construction).
- **No hidden weakening.** `srcWeightOnEdge` sums over the *source* relation; the gap to the
  interface's *incidence* relation is named (`EdgeSourceFaithful`) and discharged by an honest finset
  equality, with the easy half (source ⊆ incidence) proved.
- **Two-multiplicity choice documented.** Using `νP`, `νQ` separately (matching `WeightedEdgeBalance
  decomp νP νQ`'s two-multiplicity signature) avoids the unprovable `q ∉ PsetP` that a single `ν`
  would have required — a faithful design choice, not a dodge.
- **Verdict:** **FAITHFUL** for items 1–2 (the telescoping + Pearl-Lemma instantiation +
  source⟹incidence: unconditional, proven); **CONDITIONAL-honest** for the headline (sole isolated
  geometric input = `EdgeSourceFaithful`, the collinear-edge non-degeneracy; plus the classification
  layer's `LocationData`/`PearlSectorModel` and the concrete angle normalizations).

## Wiring note (for whoever updates the import graph / Audit.lean — I did not touch them)

`BricardAggregate.lean` imports `ProofsInTheBook.BricardBalance`. To surface it, add it to the library
root and add `#print axioms ProofsInTheBook.Bricard.regularTet_cube_no_equidecomp_aggregated` (et al.)
to `Audit.lean` (keeping Audit's own import list updated). Verified output is the core three axioms.
