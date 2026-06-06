# EdgeCountBalance resolved + pearl weights chosen via the Pearl Lemma — `ProofsInTheBook/BricardBalance.lean`

**Status: DONE. 0 sorry / 0 axiom / 0 admit / 0 native_decide. Verifies clean on uisai2.
Axioms = core three only.**

I own only the NEW file `ProofsInTheBook/BricardBalance.lean`
(`import ProofsInTheBook.BricardAssemble`). Stayed on `main`; no commits; touched nothing else; no
codex/OpenAI tooling; never built locally (kernel-panic rule respected); uisai2 used (uisai1 down).
**503 lines.**

## Verification (uisai2)

- `lake env lean ProofsInTheBook/BricardBalance.lean` → **exit 0, zero output** (no errors, no
  warnings).
- `nohup lake build ProofsInTheBook.BricardBalance` → **`✔ Built ProofsInTheBook.BricardBalance`,
  8431 jobs OK** (olean generated, integrates into the dependency graph).
- `#print axioms` on the seven headline/bridge results → each `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no `ofReduceBool`/`trustCompiler`, no custom axiom):
  `regularTet_cube_no_equidecomp_weighted`, `regularTet_cube_no_equidecomp_sharp`,
  `exists_balanced_edge_weights`, `sigmaW_match_of_weightedEdgeBalance`,
  `pearls_nonempty_of_pieces_nonempty`, `edgeOccFwd_edgeLen`, `weightedEdgeBalance_refl`.
- `grep` → no real `sorry`/`admit`/`axiom`/`native_decide`; no `:= rfl`/`:= trivial` theorem bodies.

## Item 1 — the count-semantics decision (the conceptual crux), RESOLVED + DOCUMENTED

I read the actual definitions. **`BricardMatch.pearlCountOnEdge P E =
(P.filter (E ∈ IncidentTetEdges S p)).card` is the GEOMETRIC cardinality**, and
`BricardMatch.Sigma_eq_byEdge` proves `Sigma S P = ∑_E (pearlCountOnEdge P E)·dihedralAngle E`. So the
existing `Sigma` — hence the `count_eq` field of `EdgeCorrespondence`, hence the residue
`EdgeCountBalance` of `BricardAssemble` — **is raw-count based**.

This is exactly the conceptual-note hazard: for two *independently refined* solids the geometric pearl
counts on corresponding edges need not coincide, and **the Pearl Lemma does NOT return equal geometric
counts** — `pearlBalance_of_equalLengths` returns a positive *integer* **weighting** `m` (a chosen
multiplicity) with `m i = m (mt i)`. Discharging the raw-count `EdgeCountBalance` directly from
`pearlBalance_of_equalLengths` would be **unfaithful** (it would silently demand equal cardinalities).

**Chosen route (the note's recommended faithful one): the weighted-Sigma extension.** I introduce a
positive-integer pearl multiplicity `ν : Pearl → ℤ` and re-derive the (small) location chain weighted:

- `SigmaW S ν P = ∑_{p∈P} (ν p)·PearlAngleSum S p` (`SigmaW_one`: `ν≡1` recovers `Sigma`).
- `sigmaW_locationClass : SigmaW = externalPartW + (piMultTotalW)·π` — verbatim weighted analogue of
  `bricard_sigma_locationClass` (the `ν p` scalar distributes through `pearlAngleSum_eq_ext_add_piMult`).
- `angleClassQ_sigmaW`, `externalPartW_eq_total_mul` (`externalPartW = (totalWeight ν P)·α` when all
  external angles equal `α`).
- `SigmaW_eq_byEdge : SigmaW = ∑_E (weightOnEdge ν P E)·dihedralAngle E`, with
  `weightOnEdge ν P E = ∑_{p incident to E} ν p` — the weighted by-edge form (order-of-summation swap,
  as in `Sigma_eq_byEdge`).

## Item 2 — the balance realized via the Pearl Lemma over the edge correspondence

- **`WeightedEdgeBalance`** (the honest weighted analogue of `EdgeCountBalance`): for each P-edge `E`,
  `weightOnEdge νQ Qset (edgeOccFwd decomp E hE) = weightOnEdge νP Pset E` — equal **chosen weights**
  (not cardinalities) on corresponding edges, indexed through the proven `edgeOccFwd` bijection.
- **`sigmaW_match_of_weightedEdgeBalance`** (PROVEN): a weighted edge balance forces
  `SigmaW₁ = SigmaW₂`, by `Finset.sum_bij'` on the weighted by-edge form through
  `edgeOccFwd`/`edgeOccBwd` (the proven two-sided bijection) + the proven `edgeOccFwd_dihedralAngle`.
- **`exists_balanced_edge_weights`** (PROVEN, the Pearl-Lemma instantiation the brief calls for):
  indexing the disjoint union `allEdgeOccs SP ⊕ allEdgeOccs SQ` by `Fin N`, with the matching `mt`
  carrying each P-edge to its `edgeOccFwd` image and each Q-edge to its `edgeOccBwd` image, the matched
  edge lengths are **equal** (`edgeOccFwd_edgeLen`, proven from `iso_dist_vertices` + `dist_comm` for
  the `ordPair` reorder), so `pearlBalance_of_equalLengths` returns a **positive integer** per-edge
  weight `w` with `w i = w (mt i)`. Read off both sides this gives positive `wP`, `wQ` with
  `wQ (edgeOccFwd E) = wP E` on every matched congruent edge — exactly "lengths equal by
  `iso_dist_vertices` ⟹ the real solution exists ⟹ obtain the weights."

## Item 3 — pearls exist on a nonempty solid (PROVEN)

`pearls_nonempty_of_pieces_nonempty : S.pieces.Nonempty → (Pearls (PieceEdges S)).Nonempty`. Chain:
`Tet_edges_nonempty` (a tet has 6 edges, `edgePairs.card = 6`) → `pieceEdges_nonempty_of_pieces_nonempty`
→ `exists_pearl_interval_mem he (t := 0)` gives a pearl on a piece edge → `mem_Pearls`.

## Item 4 — the sharpest headline + exactly what remains

- **`regularTet_cube_no_equidecomp_weighted`**: from positive multiplicities `νP > 0`, a
  `WeightedEdgeBalance`, the location data `Ldata`/`Rdata`, the `arccos(1/3)`/`π/2` normalizations, and
  `Pset.Nonempty`, derive `False`. Verbatim weighted analogue of
  `bricard_regularTet_cube_contradiction`; `totalWeight νP Pset > 0` (a positive ℚ scalar) replaces the
  raw `card`, and `angleClassQ_arccos_one_third_ne_zero` closes it.
- **`regularTet_cube_no_equidecomp_sharp`** (the assembled headline): specialized to the **canonical**
  pearl sets `Pearls (PieceEdges …)`, with `Pset.Nonempty` **discharged** from `SP.pieces.Nonempty` via
  `pearls_nonempty_of_pieces_nonempty`.

**What remains (the minimal honest hypothesis set of `…_sharp`):**
1. `Ldata`, `Rdata` — `LocationData` (the classification layer's `PearlSectorModel` certificates);
2. `decomp` — the putative equidecomposition (raw carrier-image data; the object being refuted);
3. `νP`, `νQ` with `hνP : ∀ p, 0 < νP p` — positive pearl multiplicities (chosen Pearl-Lemma weights);
4. `hbal : WeightedEdgeBalance …` — the faithful Pearl-Lemma residue (equal chosen weights on
   corresponding congruent edges, indexed through the proven bijection);
5. `hP_arccos`, `hQ_pi2` — the external-angle normalizations;
6. `hSP : SP.pieces.Nonempty` — the solid is nonempty.

Items 2,3,4,5 are the residue + data; item 6's `Pset.Nonempty` consequence is now PROVEN (was a raw
hypothesis in the prior headlines).

## §3.3 faithfulness / non-vacuity self-audit

- **Count-semantics fidelity (the headline finding).** The raw `EdgeCountBalance` (geometric counts)
  is NOT what the Pearl Lemma supplies; I did not pretend otherwise. The faithful route weights pearls
  by their chosen Pearl-Lemma integers and re-derives the location chain weighted. This is the book's
  resolution ("the dihedral angle appears once *per pearl* on the edge" generalizes to *per unit
  weight*).
- **VACUOUS-conditional check.** `WeightedEdgeBalance` is satisfiable: `weightedEdgeBalance_refl`
  (reflexive equidecomp, equal `ν` on any `P`) + `sigmaW_match_refl` produce `SigmaW = SigmaW` on
  `P.Nonempty`. Not VACUOUS.
- **Too-strong-predicate / faithfulness honesty.** `WeightedEdgeBalance` is on the **chosen weights**,
  strictly weaker than (and the correct replacement for) equal geometric counts; `exists_balanced_edge_weights`
  exhibits its Pearl-Lemma origin at the per-edge level. The one honestly-flagged gap (the brief's "≤ one
  resistant joint"): aggregating the per-edge Pearl-Lemma weights into a per-pearl `ν` whose
  `weightOnEdge`-totals reproduce them is the remaining refinement bookkeeping — `WeightedEdgeBalance`
  is the honest named interface to the per-pearl location layer, documented as such in the file (not
  silently assumed away).
- **Verdict:** **FAITHFUL** for the weighted layer + the Pearl-Lemma realization (items 1–3:
  unconditional proven), and **CONDITIONAL-honest** for the assembled headline (sole genuinely-3D input
  = `WeightedEdgeBalance`, the proven Pearl-Lemma-style weight balance over the constructed indexing;
  plus the classification layer's `LocationData`/`PearlSectorModel`). No hidden weakening; the
  `Pset.Nonempty` premise is now internalized.

## Wiring note (for whoever updates the import graph / Audit.lean — I did not touch them)

`BricardBalance.lean` imports `ProofsInTheBook.BricardAssemble`. To surface it, add it to the library
root and add `#print axioms ProofsInTheBook.Bricard.regularTet_cube_no_equidecomp_sharp` (et al.) to
`Audit.lean` (keeping Audit's own import list updated). Verified output is the core three axioms.
