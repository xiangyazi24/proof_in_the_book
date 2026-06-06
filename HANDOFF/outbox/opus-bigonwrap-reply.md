# Ch35 chord-side bigon WRAP: the FINAL chord-side residue reduced to its irreducible
kernel, with the skip PROVED. New file `ProofsInTheBook/ChordBigonWrap.lean`, RC=0, clean-3.

## TL;DR (honest verdict: NOT an unconditional discharge)

`ChordAnchorInst.lean` reduced the chord-side discharge to `ChordCapData`, whose ONLY
genuinely-geometric field is the bigon WRAP `bigon_close : keptPhi d₂ = d₁`.  This round:

1. **PROVED unconditionally the easy half + the SKIP CERTIFICATE** — the missing
   `M.φ³ dart = dart` fact AND that the filtered rotation at `d₂` genuinely hits the deleted
   chord dart on its first `σ`-step (so the wrap is a real multi-step skip, `firstOutside ≥ 2`).
2. **Reduced the wrap to its irreducible kernel** `ChordBigonWrap` (carrying the wrap equation
   itself + the proved skip certificate + the chord-cap anchors) and built the full discharge
   chain from it: `toChordCapData → correctAnchorTwoCycle_ofWrap → contiguousInterval_ofWrap`.

**The wrap `keptPhi d₂ = d₁` is NOT proved unconditionally, and CANNOT be from
`M.φ³ dart = dart` alone** — see "The mathematical correction" below.  It remains the single
isolated geometric residue, exactly as every prior round, now reduced to its irreducible core.

## The mathematical correction (why the spec's chain is incomplete)

The spec stated: `hNT.inner_tri (face₁ triangle) ⟹ M.φ³ dart = dart ⟹ keptPhi d₂ = d₁`.
The **second implication is false in general**.  Trace it precisely:

* `keptPhi d₂ = sideSigma₁ (sideAlpha₁ d₂) = filteredRotation M.σ keptDel₁ ⟨M.α(M.φ² dart), _⟩`.
* First `σ`-step: `M.σ(M.α(M.φ² dart)) = M.φ³ dart = dart`, the DELETED chord dart — PROVED here
  (`bigonWrap_firstStep_deleted`).  Good: the rotation MUST skip it.
* But `dart`'s own `σ`-successor is `M.σ dart`, which is **NOT** `M.φ dart` (that would force
  `dart = M.α dart`, impossible since `α` is fixed-point-free).  `M.φ dart = M.σ(M.α dart)` is
  the `σ`-successor of `M.α dart`, a dart at a *different* vertex.

So the wrap to `d₁ = M.φ dart` requires that **every** dart strictly between `dart` and
`M.φ dart` in the vertex-`u` rotation `M.σ` is deleted (on side 2 / the outer face).  That is the
discrete planar-embedding (Jordan) datum — which darts of `u`'s rotation are kept by side 1.  It
is determined by `M.φ³ dart = dart` ONLY together with the full `σ`-rotation structure at the
chord endpoint, which the abstract `CombMap` `face₁_isFaceTriangle` (a *face* `φ`-orbit fact)
does not pin.  This is precisely the irreducible content every prior round isolated
(`SidesDisjoint`, `Separates`, `ContiguousInterval`, `tOrbitCard = 2`, `bigon_close`).

## What is PROVED UNCONDITIONALLY (genuinely new content)

* **`phi_cube_dart`** — `M.φ³ dart = dart` (= `data.face₁_isFaceTriangle.2.2`, descending from
  `hNT.inner_tri` on the non-outer face `face₁`).
* **`sigma_alpha_phiSq_dart_eq_dart`** — `M.σ(M.α(M.φ² dart)) = dart` (since `M.σ∘M.α = M.φ`).
* **`bigonWrap_firstStep_deleted`** — the first `σ`-step of the filtered rotation at `d₂` is the
  DELETED chord dart `dart ∈ keptDel₁` (via `dart_mem_keptDel₁`).  The concrete SKIP certificate.
* **`sideSigma₁_sideAlpha₁_firstOutside_ge_two`** — `firstOutside ≥ 2` at `d₂`: the wrap is a
  genuine multi-step skip, never the trivial consecutive step.  Proved from `firstOutside_pos` +
  `firstOutside_notMem` + the skip certificate.

These four are the unconditional substance: they prove the skip mechanism is REAL (non-vacuous)
and pin exactly what the irreducible residue is (where the rotation lands after the skip).

## The single named residue + the discharge chain (built from it)

* **`ChordBigonWrap data hsep`** — the single named geometric residue: the wrap
  `keptPhi d₂ = d₁` (`bigon_wrap`) carried with its UNCONDITIONAL `firstStep_deleted` certificate
  (default-valued to `bigonWrap_firstStep_deleted`, so the wrap is visibly the genuine
  skip-and-wrap, not an abstract pair) + the explicit chord-cap anchors `a₀, a₁` (distinct,
  `σ`-images OUTSIDE the bigon `{d₁, d₂}`) + the rep face + one-fresh indicator.  Non-vacuous
  (`ChordBigonWrap.mk'`).
* **`ChordBigonWrap.toChordCapData`** — supplies `ChordCapData`'s `bigon_close` field from the
  wrap, connecting to `ChordAnchorInst`.
* **`tracePhi_twoCycle_ofWrap`** / **`correctAnchorTwoCycle_ofWrap`** /
  **`face₁_sideTriangle_ofWrap`** / **`contiguousInterval_ofWrap`** — the end-to-end chain from a
  `ChordBigonWrap`, threading to `ChordSideReconstruction → chord_case_recursive →
  nearTriangulation_five_colorable` (all via the proved `ChordAnchorInst` API).
* **`wrap_discharge_eq`** — no-rewrapper certificate: the 2-cycle is COMPUTED from the wrap +
  upstream `keptPhi d₁ = d₂` + anchor-avoidance, and records the unconditional skip certificate.

## §3.3 self-audit (honest, faithful, non-vacuous, not a re-wrapper)

- **NOT an unconditional discharge of `ChordCapData`.**  `ChordBigonWrap` still carries the wrap
  `bigon_wrap` as a field.  The `ContiguousInterval`/headline therefore remain CONDITIONAL on the
  same single geometric residue, with the JordanOracle parameter unchanged.  No overclaim.
- **Not vacuous / not a hidden `False`.**  `firstOutside ≥ 2` is PROVED, so the wrap is a genuine
  non-trivial skip; `ChordBigonWrap.mk'` is the explicit constructor; the wrap + upstream
  `keptPhi d₁ = d₂` is a genuine 2-cycle.  The `firstStep_deleted` field is filled unconditionally.
- **Not a re-wrapper.**  The four unconditional lemmas are new content (the skip mechanics); the
  2-cycle is DERIVED via `chordCap_tracePhi_twoCycle`, not handed in.
- **Anchored to the real darts.**  `face₁Dart₁/₂` = `M.φ dart`, `M.φ² dart`; `phi_cube_dart` and
  the skip certificate are on the ACTUAL chord dart.
- **Headline not regressed.**  No upstream file edited (one-writer rule).
  `nearTriangulation_five_colorable` re-checked: clean-3, no `sorryAx`, UNCHANGED.

## Verification (server uisai1, real olean chain)

- Dependency `lake build ProofsInTheBook.ChordAnchorInst` → Build completed successfully
  (8464 jobs).
- `lake env lean ProofsInTheBook/ChordBigonWrap.lean` → **RC = 0**, zero errors, zero warnings.
  All **9** `#print axioms` results **clean-3 `[propext, Classical.choice, Quot.sound]`**:
  `phi_cube_dart`, `sigma_alpha_phiSq_dart_eq_dart`, `bigonWrap_firstStep_deleted`,
  `sideSigma₁_sideAlpha₁_firstOutside_ge_two`, `tracePhi_twoCycle_ofWrap`,
  `correctAnchorTwoCycle_ofWrap`, `face₁_sideTriangle_ofWrap`, `contiguousInterval_ofWrap`,
  `wrap_discharge_eq`.
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → none in code (docstring only).
- `#print axioms ProofsInTheBook.ThomassenInduction.nearTriangulation_five_colorable`
  → clean-3, no `sorryAx`, UNCHANGED (headline stays CONDITIONAL on the JordanOracle parameter).

## New file (owned, fresh; NOT wired into ProofsInTheBook.lean — one-writer rule)

`ProofsInTheBook/ChordBigonWrap.lean` — imports `ChordAnchorInst`.  9 audited results.
Branch `main`; no commits; no branch switch; no codex/OpenAI tooling; never ran lake/lean on the
Mac (kernel-panic rule observed — verified exclusively on uisai1).

## Precise residue going forward

The Chapter-35 chord-side wall is now EXACTLY `ChordBigonWrap.bigon_wrap` (`keptPhi d₂ = d₁`),
with its first `σ`-step proved to be the deleted chord dart.  The remaining geometric content is:
*after skipping the deleted chord dart, the filtered rotation `M.σ` at the chord endpoint `u`
lands on `M.φ dart`* — i.e. every dart strictly between `dart` and `M.φ dart` in `u`'s
`σ`-rotation is deleted (side-2 / outer).  This is a `filteredRotation` multi-step computation
requiring the vertex-rotation deletion pattern at the chord endpoint, the last genuinely
discrete-planarity (Jordan) datum.  The next attack vector is to obtain a `FilteredRotation.
ContiguousInterval` for the kept side-1 darts of `u`'s `σ`-cycle from the chord-split
separation (`Separates` / the side dart-set structure), then apply
`filteredRotation_iterate_eq_of_contiguous` to compute the two-step wrap.
