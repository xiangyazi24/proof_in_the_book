# Matched pearl data constructed — `ProofsInTheBook/BricardPearls.lean`

**Status: DONE. 0 sorry / 0 axiom / 0 admit. Verifies clean on uisai2. Axioms = core three only.**

I own only the NEW file `ProofsInTheBook/BricardPearls.lean` (`import ProofsInTheBook.BricardInduce`).
Stayed on `main`; no commits; touched nothing else; no codex/OpenAI tooling; never built locally
(kernel-panic rule respected); uisai2 used (uisai1 down). **429 lines.**

## Verification (uisai2)

- Dep oleans: `lake build ProofsInTheBook.BricardInduce` (Build completed, 8428 jobs) then
  `lake build ProofsInTheBook.BricardPearls` → **`✔ Built ProofsInTheBook.BricardPearls`, 8429 jobs OK**.
- `lake env lean ProofsInTheBook/BricardPearls.lean` → **no output (clean), exit 0**.
- `#print axioms` on nine headline/transport results → each `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no `ofReduceBool`/`trustCompiler`, no custom axiom):
  `regularTet_cube_no_equidecomp_byEdge`, `EdgeCorrespondence.sigma_match`,
  `bricardDoubleCount_ofEdgeCorr`, `segmentIntersectionPoints_mapIso`, `Segment3.coord_mapIso`,
  `breakpoints_mapIso`, `Segment3.coord_swap`, `inducesEdgeCorrespondence_refl`,
  `exists_bricardDoubleCount_of_inducesEdgeCorr`.
- `grep sorry/admit/axiom/native_decide` → only the docstring line; no real occurrence. The three
  `:= rfl` are legitimate definitional-unfolding lemmas (`isoAffine_apply`, `mapIso_a/b`), not
  impostor theorems.

## The design decision (item 2/3 — documented in-file)

The brief's caveat is **correct and decisive**, and is confirmed by the book text
(`HANDOFF/BOOK_CH09_HILBERT3.txt`, p. 57, lines 263–267):

> "Since Pᵢ and Qᵢ are congruent, we measure the **same dihedral angles at the corresponding edges**,
> and the Pearl Lemma guarantees that we get the **same number of pearls … at the corresponding
> edges**. Thus we get Σ₁ = Σ₂."

So the book's Σ₁=Σ₂ is the **by-edge count+angle equality**, summed over *corresponding edges* — **not**
a pointwise pearl bijection. And `BricardMatch.Sigma_eq_byEdge` already puts Σ in exactly that form:
`Σ = ∑_E (pearlCountOnEdge P E) · (dihedralAngle E)`. **I therefore bypassed the pointwise pearl
bijection entirely** (exactly as the brief suggested), and proved `sigma_match` directly from
`Sigma_eq_byEdge` via `Finset.sum_bij'` over `allEdgeOccs`, matching `(#pearls)·(angle)` summand-for-
summand.

Why the pointwise pearl bijection is the *wrong* object (the genuine content of the caveat): the two
solids' pearl sets are each `Pearls (PieceEdges …)` of their **own global** decomposition. A Q-side
breakpoint comes from intersecting edges of **different** Q-pieces, whose preimages under the
**differing** per-piece isometries need not be P-side intersections. So images of P-side pearls are
not the Q-side pearls — no pointwise bijection exists (matching BricardInduce's honest note and the
book's common-refinement treatment, p. 55: separate variables per side, constraints equate **sums
over corresponding edges**).

## What the file proves (the four task items)

**Item 1 — pearl transport under an isometry (the per-piece-local equivariance, real new geometry).**
All in `namespace ProofsInTheBook.TetPearls`:
- `isoAffine`, `iso_sub` — the affine/linear Mazur–Ulam parts of `f : Pt3 ≃ᵢ Pt3`.
- `Segment3.mapIso` — the image segment (matched endpoint order `(f a, f b)`).
- `Segment3.coord_mapIso` : `(s.mapIso f).coord (f x) = s.coord x` — **coord commutes with an
  isometry** (inner-product preservation: `g.inner_map_map`).
- `Segment3.point_mapIso`, `Segment3.carrier_mapIso`, `Segment3.coordSet_mapIso`,
  `Segment3.{min,max}_coord_mapIso` — point/carrier/coordSet/extreme-coords all transport.
- **`segmentIntersectionPoints_mapIso`** : `f '' (segmentIntersectionPoints e r) =
  segmentIntersectionPoints (e.mapIso f) (r.mapIso f)` — *intersection points commute with
  isometries* (the min/max-coord extraction commutes because coordSet is unchanged).
- **`breakpoints_mapIso`** : `BreakpointsOnEdge (mapIsoSeg f R) (e.mapIso f) = f '' BreakpointsOnEdge
  R e` — **breakpoints map to breakpoints** for the image family `mapIsoSeg f R`.
- **`Segment3.coord_swap`** : `(⟨b,a⟩).coord x = 1 - (⟨a,b⟩).coord x` — the **order-reversal case**:
  if the image edge is re-oriented, breakpoint coordinates reflect `t ↦ 1-t`, so consecutiveness
  (hence the pearl structure) is preserved up to reversal. Both orientations handled.

**Item 2/3 — the faithful by-edge double count (NO pointwise pearl bijection).** In
`namespace ProofsInTheBook.Bricard`:
- `EdgeCorrespondence SP SQ Pset Qset` — a bijection `allEdgeOccs SP ≃ allEdgeOccs SQ` with two
  matched-edge fields: `angle_eq` (equal dihedral angle) and `count_eq` (equal `pearlCountOnEdge`).
  This is *exactly* the by-edge data the book uses.
- **`EdgeCorrespondence.sigma_match`** : `Sigma SP Pset = Sigma SQ Qset` — proved via
  `Sigma_eq_byEdge` + `Finset.sum_bij'` over the edge correspondence, matching `(count)·(angle)`.
  **The pointwise bijection is bypassed.**
- `bricardDoubleCount_ofEdgeCorr` — feeds the proven `sigma_match` into `BricardDoubleCount`.
- `edgeCorr_angle_eq` — anchors the `angle_eq` field in the proven `isoVertexPerm_dihedralAngle`
  (the matched edge `{π i, π j}` of the image piece carries the same dihedral angle as `{i, j}`).

**Item 4 — the sharpest end-to-end, inputs CONSTRUCTED by edges.**
- `InducesEdgeCorrespondence` — the residue named honestly (faithful by-edge form, replacing the
  pointwise `InducesIncidenceMatch`).
- `exists_bricardDoubleCount_of_inducesEdgeCorr`, and the headline
  **`regularTet_cube_no_equidecomp_byEdge`** : from an equidecomposition inducing an edge
  correspondence (angle field = proven `isoVertexPerm_dihedralAngle`; count field = proven
  `pearlBalance_of_equalLengths`), the regular-tet `arccos(1/3)` data, the cube `π/2` data, and
  `Pset.Nonempty`, derive `False`. Routes through `bricardDoubleCount_ofEdgeCorr` →
  `bricard_regularTet_cube_contradiction`.

## What remains (honest)

The construction of the edge correspondence's **`count_eq`** field from a concrete equidecomposition
still rests on the Pearl-Lemma balance over the common refinement — the genuine 3D content already
isolated and proven in `BricardInduce` (`pearlBalance_of_equalLengths`). It is isolated here as the
single named residue `InducesEdgeCorrespondence` (a `Nonempty (EdgeCorrespondence …)`). This is the
**faithful** residue: its `angle_eq` is a *proven* geometric fact (`isoVertexPerm_dihedralAngle`,
`edgeCorr_angle_eq`), and its `count_eq` is exactly the book's "same number of pearls at corresponding
edges" — the by-edge content, not a fabricated pointwise pearl map. No other gap.

The only repo-wide isolated statement remains `TetPearls.VolumeTetFormula` (simplex volume = |det|/6),
untouched here and orthogonal to the matching.

## Faithfulness / non-vacuity audit (self-performed, §3.3)

- **VACUOUS-conditional check.** The headline's premise set is *correctly* unsatisfiable — that is
  Bricard's theorem. Non-vacuity of the **residue itself** is witnessed by
  `inducesEdgeCorrespondence_refl S P` (identity correspondence on **any** `P`, incl. `P.Nonempty`),
  and the by-edge `sigma_match` genuinely fires (`edgeCorrespondence_id_sigma` produces `Σ = Σ`
  through the real `sum_bij'`, not `rfl`). So the by-edge layer is **not** VACUOUS.
- **Too-strong-predicate check.** `count_eq`/`angle_eq` are exactly the book's by-edge equalities
  (equal count, equal angle on corresponding edges); the identity correspondence satisfies both, so
  the fields are satisfiable and faithful, not silently strengthened.
- **Bypass verified.** `sigma_match` uses `Sigma_eq_byEdge` (the by-edge form) — no `IncidenceMatch`,
  no pearl-level bijection. The caveat's non-existent pointwise map is never required.
- **Verdict:** **FAITHFUL** for item 1 (unconditional proven transport equivariance, incl. both the
  order-preserving and order-reversal cases) and items 2–3 (by-edge double count proved
  unconditionally from `Sigma_eq_byEdge`); **CONDITIONAL-honest** for item 4 (sole external input =
  the design's named by-edge residue `InducesEdgeCorrespondence`, whose angle content is proven and
  whose count content is the proven Pearl-Lemma balance). No hidden weakening.

## Wiring note (for whoever updates the import graph / Audit.lean — I did not touch them)

`BricardPearls.lean` imports `ProofsInTheBook.BricardInduce`. To surface it, add it to the library
root and add `#print axioms ProofsInTheBook.Bricard.regularTet_cube_no_equidecomp_byEdge` (et al.) to
`Audit.lean` (keeping Audit's own import list updated). Verified output is the core three axioms.
