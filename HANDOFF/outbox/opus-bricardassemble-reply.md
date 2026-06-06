# Edge correspondence assembled from an equidecomposition — `ProofsInTheBook/BricardAssemble.lean`

**Status: DONE. 0 sorry / 0 axiom / 0 admit / 0 native_decide. Verifies clean on uisai2 (no warnings).
Axioms = core three only.**

I own only the NEW file `ProofsInTheBook/BricardAssemble.lean` (`import ProofsInTheBook.BricardPearls`).
Stayed on `main`; no commits; touched nothing else; no codex/OpenAI tooling; never built locally
(kernel-panic rule respected); uisai2 used (uisai1 down). **482 lines.**

## Verification (uisai2)

- Dep oleans: `lake build ProofsInTheBook.BricardPearls` already built (8429 jobs). Then
  `lake build ProofsInTheBook.BricardAssemble` → **`✔ Built ProofsInTheBook.BricardAssemble`,
  8430 jobs OK**.
- `lake env lean ProofsInTheBook/BricardAssemble.lean` → **no output (clean), exit 0** — zero errors,
  zero warnings.
- `#print axioms` on eight headline/bijection results → each `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no `ofReduceBool`/`trustCompiler`, no custom axiom):
  `regularTet_cube_no_equidecomp_final`, `inducesEdgeCorrespondence_of_equidecomp`,
  `edgeCorrespondence_ofEquidecomp`, `edgeOccBwd_edgeOccFwd`, `edgeOccFwd_edgeOccBwd`,
  `edgeOccFwd_dihedralAngle`, `isoVertexPerm_symm_pairing`,
  `inducesEdgeCorrespondence_of_equidecomp_refl`.
- `grep` → no real `sorry`/`admit`/`axiom`/`native_decide`. The four `:= rfl` are definitional
  field-unfolding `have`s inside proofs (`F.i = (ordPair …).1`), not impostor theorems.

## What the file constructs (the three task items)

**Item 1 — the edge-occurrence bijection (PROVEN, fully constructed).**
An edge occurrence on the P side is `EdgeOcc SP = (piece T, hT, i, j, i<j)`. The construction:
- `edgeOccFwd decomp E hE` : maps `E` to the occurrence on the image piece `decomp.e ⟨E.T,_⟩`, along
  the **order-canonicalised** image pair `ordPair (π E.i) (π E.j)`, where
  `π = isoVertexPerm (decomp.maps_piece ⟨E.T,_⟩)` is the proven per-piece vertex permutation from
  `BricardInduce`. (`ordPair` re-orders `(π i, π j)` to `i'<j'` so it is a valid `EdgeOcc`.)
- `edgeOccBwd decomp F hF` : the inverse, built from the **inverse pairing** `decomp.e.symm`, with the
  inverse vertex permutation `π.symm`.
- `edgeOccFwd_mem` / `edgeOccBwd_mem` : membership in `allEdgeOccs` (via the new
  `mem_allEdgeOccs : E ∈ allEdgeOccs S ↔ E.T ∈ S.pieces`).
- **`edgeOccBwd_edgeOccFwd` / `edgeOccFwd_edgeOccBwd`** : the two-sided inverse, **PROVEN**. The piece
  field collapses by `Equiv.symm_apply_apply` / `Equiv.apply_symm_apply`; the index fields by the
  single isolated indexing joint (below) + `ordPair` re-ordering.

The bijection is built to match how `BricardMatch`/`BricardPearls` index edge occurrences **exactly**:
the `EdgeCorrespondence` structure of `BricardPearls` is the dependent-pi form
`toFun : ∀ E ∈ allEdgeOccs SP, EdgeOcc SQ` + `mem`/`left_inv`/`right_inv` fields — I implement those
fields directly (no `Equiv.prodCongr`/`Sigma` wrapper needed, since the structure is already the
"occurrence-bijection over the piece bijection" shape).

**Item 2 — the two fields.**
- **`angle_eq` (PROVEN): `edgeOccFwd_dihedralAngle`.** Matched edges carry equal dihedral angle, via
  `dihedralAngle_ordPair` (re-ordering invariance, from `TetDihedral.dihedralAngle_comm`) composed
  with the proven `isoVertexPerm_dihedralAngle` (`BricardInduce`). Aligned to the `ordPair` indexing.
- **`count_eq` (the genuine residue): `EdgeCountBalance`.** This is the one datum **not** derivable
  from the isometry pairing — exactly the `BricardPearls` caveat: the two solids' global pearl sets
  have no pointwise correspondence, so equal-pearl-count on corresponding edges is the Pearl-Lemma
  balance, not a transport fact. I name **precisely the count balance over the constructed bijection**
  as `EdgeCountBalance decomp Pset Qset := ∀ E hE, pearlCountOnEdge Qset (edgeOccFwd decomp E hE) =
  pearlCountOnEdge Pset E`. Its proven core is `BricardInduce.pearlBalance_of_equalLengths` (the Pearl
  Lemma instantiated over corresponding congruent — equal-length — edges); the wiring through the
  same `edgeOccFwd` indexing is the count-balance hypothesis. `count_eq := hcount` consumes it verbatim.

**Item 3/4 — conclusion + final headline.**
- `edgeCorrespondence_ofEquidecomp decomp hcount : EdgeCorrespondence SP SQ Pset Qset` — packages the
  proven bijection + proven `angle_eq` + the `EdgeCountBalance` residue.
- `inducesEdgeCorrespondence_of_equidecomp` — discharges `BricardPearls`'s named residue
  `InducesEdgeCorrespondence`.
- **`regularTet_cube_no_equidecomp_final`** — the headline: from a raw `TetEquidecomp SP SQ`, the
  location data `Ldata`/`Rdata`, the count balance `hcount`, the `arccos(1/3)`/`π/2` normalisations,
  and `Pset.Nonempty`, derive `False`. Routes through `edgeCorrespondence_ofEquidecomp` →
  `regularTet_cube_no_equidecomp_byEdge` (BricardPearls) → `bricard_regularTet_cube_contradiction`.

## The single isolated indexing joint (named honestly)

`isoVertexPerm_symm_pairing` : the vertex permutation of the **inverse** pairing is the inverse
permutation, `isoVertexPerm (mapsPiece_symm hf) = (isoVertexPerm hf).symm`. Proved here from
`isoVertexPerm_apply` + injectivity of `T.v`/`U.v`. The two-sided inverse of the edge-occurrence
bijection rests entirely on this; everything else in `left_inv`/`right_inv` is `ordPair` bookkeeping.
This is the one resistant indexing joint the brief allowed isolating — and it is **proved**, not
assumed.

## Honest hypothesis set of the final headline (which named structures remain)

`regularTet_cube_no_equidecomp_final` is **CONDITIONAL-honest** on the minimal set:
1. `decomp : TetEquidecomp SP.toTetSolid SQ.toTetSolid` — the putative equidecomposition (raw
   carrier-image data only). **Not** assumed-away; it is the object whose existence is refuted.
2. `Ldata : LocationData SP Pset`, `Rdata : LocationData SQ Qset` — the **classification-layer
   location/model data** (`PearlClassification.LocationData`, whose `PearlClassificationCert`s carry
   the `PearlSectorModel` cross-section witnesses). These remain from the classification layer exactly
   as in the existing `regularTet_cube_no_equidecomp_byEdge` headline; I did not strengthen or weaken
   them.
3. `hcount : EdgeCountBalance decomp Pset Qset` — the **Pearl-Lemma count balance** on corresponding
   edges (proven core `pearlBalance_of_equalLengths`), indexed through the constructed bijection. This
   is the sole genuinely-3D residue, and it is the *faithful* by-edge content (not a fabricated
   pointwise pearl map).
4. `hP_arccos` / `hQ_pi2` — the external-angle normalisations (regular tet `arccos(1/3)`, cube `π/2`),
   stated against the `LocationData` certificates exactly as the `byEdge` headline.
5. `hPne : Pset.Nonempty`.

**`VolumeTetFormula` is NOT used here** (no equal-volume normalisation enters the by-edge route);
it remains the repo's separate isolated statement, orthogonal to the matching. The geometric
structures that remain are `PearlSectorModel`/`LocationData` (classification layer) and the count
balance `EdgeCountBalance` (proven core `pearlBalance_of_equalLengths`) — documented above.

## Faithfulness / non-vacuity audit (self-performed, §3.3)

- **VACUOUS-conditional check.** The headline's full premise set is *correctly* unsatisfiable — that
  is Bricard's theorem. Non-vacuity of the residue **itself** is witnessed by
  `inducesEdgeCorrespondence_of_equidecomp_refl S P` (reflexive equidecomp + `edgeCountBalance_refl`
  on **any** `P`, incl. `P.Nonempty`), proved via `edgeOccFwd_refl` (the reflexive vertex permutation
  is the identity, so each edge maps to itself with reflexively-equal count). So `EdgeCountBalance`
  and the construction are **not** VACUOUS.
- **Too-strong-predicate check.** `EdgeCountBalance` is exactly the book's "same number of pearls at
  corresponding edges," indexed by the *constructed* `edgeOccFwd` (not an arbitrary stronger map); the
  reflexive case satisfies it, so it is satisfiable and faithful, not silently strengthened.
- **Impostor check.** The bijection's `left_inv`/`right_inv` are proven via genuine permutation
  composition (`isoVertexPerm_symm_pairing`), not `rfl`; `angle_eq` is the proven
  `isoVertexPerm_dihedralAngle`, not a hypothesis. The four `:= rfl` are definitional field unfoldings
  inside proofs, not theorem bodies.
- **Bypass verified.** Routes through `regularTet_cube_no_equidecomp_byEdge` (the by-edge `sigma_match`
  of `BricardPearls`) — no `IncidenceMatch`, no pointwise pearl bijection (the caveat's non-existent
  object is never required).
- **Verdict:** **FAITHFUL** for the bijection (items 1–2 angle: unconditional proven construction +
  two-sided inverse) and **CONDITIONAL-honest** for the final headline (sole genuinely-3D input =
  `EdgeCountBalance`, the proven Pearl-Lemma balance over the constructed indexing; plus the
  classification layer's `LocationData`/`PearlSectorModel` as in the existing `byEdge` headline). No
  hidden weakening.

## Wiring note (for whoever updates the import graph / Audit.lean — I did not touch them)

`BricardAssemble.lean` imports `ProofsInTheBook.BricardPearls`. To surface it, add it to the library
root and add `#print axioms ProofsInTheBook.Bricard.regularTet_cube_no_equidecomp_final` (et al.) to
`Audit.lean` (keeping Audit's own import list updated). Verified output is the core three axioms.
