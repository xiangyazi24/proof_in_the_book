# Ch35 chord-side: `CorrectAnchorTwoCycle` DISCHARGED by instantiating `sideMap₁`'s free
anchors at the chord-cap (bigon-outside) darts — the two-layer connection closed. The 2-cycle
equation is now DERIVED from a single named geometric residue `ChordCapData` via pure
permutation algebra, with `keptPhi d₁ = d₂` proved UNCONDITIONALLY. New file
`ProofsInTheBook/ChordAnchorInst.lean`, RC=0, clean-3.

## TL;DR

`ChordAnchor.lean` left `CorrectAnchorTwoCycle` as the residue with the anchors `a₀, a₁` FREE.
This round did the two-layer connection by **exhibiting the correct anchor choice** (the
chord-cap branch the spec named) and proving the `tracePhi` 2-cycle for it. The 2-cycle is
reduced to a SINGLE named geometric datum and the algebra + the easy `keptPhi` step are
discharged in full. New file `ProofsInTheBook/ChordAnchorInst.lean` (imports `ChordAnchor`), 9
audited results, all clean-3 `[propext, Classical.choice, Quot.sound]`, no
`sorry`/`axiom`/`admit`/`native_decide`.

## FIRST: where are `sideMap₁`'s anchors instantiated in the recursion path?

ANSWER: they are NOT pinned. Traced `ChordSplitNT.chord_case_recursive` /
`ChordSideReconstruction`: the recursion abstracts each side as a GENERIC `N : CombMap Dₛ` with a
vertex correspondence `ι : N.Vertex → M.Vertex` (the `FanSurgeryReconstruction` analogue).
`sideMap₁` and its anchors `a₀, a₁` do NOT appear anywhere in the recursion path —
`ChordSideReconstruction` carries only `N, ι, Lₛ, smaller`. So the IMPORTANT branch of the spec
holds: the anchors are a genuinely UNCONSTRAINED choice at the construction layer. The discharge
must therefore EXHIBIT the correct anchors and prove `CorrectAnchorTwoCycle` for them — which is
what this file does.

## The decisive geometric observation (why both naive anchor choices collapse, and the right one)

`tracePhi β ρ a₀ a₁ = swap (ρ a₀) (ρ a₁) * (ρ * β)`, i.e.
`tracePhi … k = swap (ρ a₀) (ρ a₁) (keptPhi β ρ k)` with `keptPhi β ρ = ρ * β` (the kept-side
face permutation BEFORE the splice). `β = sideAlpha₁` (= `M.α` on the kept subtype), `ρ =
sideSigma₁` (= filtered `M.σ`).

The `M`-triangle `face₁ = {dart, d₁=M.φ dart, d₂=M.φ² dart}` has its chord dart `dart` DELETED on
side 1. On the kept subtype `keptPhi` is the filtered `M.φ`, and the kept `face₁` orbit is the
**bigon** `{d₁, d₂}`: `keptPhi d₁ = d₂` and `keptPhi d₂ = d₁` (the second wraps because the
natural `M.φ`-step `M.φ³ dart = dart` is deleted and the filtered rotation skips it).

Consequence: BOTH "natural" algebraic anchor choices (`a₁ := ρ⁻¹ d₁`, `a₀ := β d₂`) collapse to
`a₀ = a₁` precisely BECAUSE `keptPhi` is the bigon (`ρ⁻¹ d₁ = β d₂ ⟺ keptPhi d₂ = d₁`). The
CORRECT anchors are therefore the chord-cap SPLICE darts at the chord endpoints `u, v`, whose
`ρ`-images are the kept rotation-neighbors of the deleted chord dart — i.e. OUTSIDE the bigon
(`ρ a₀, ρ a₁ ∉ {d₁, d₂}`). Then `swap (ρ a₀) (ρ a₁)` FIXES both `d₁` and `d₂`, so `tracePhi =
keptPhi` on the bigon and the 2-cycle `d₁ ↔ d₂` is PRESERVED. The fresh chord dart re-closes the
bigon into the length-3 triangle (the `one_fresh` indicator).

## What is PROVED UNCONDITIONALLY (new derivable content)

- **`tracePhi_eq_swap_keptPhi`** — `tracePhi … k = swap (ρ a₀) (ρ a₁) (keptPhi β ρ k)` (the
  definitional unfolding).
- **`tracePhi_twoCycle_of_bigon`** — the PURE permutation lemma: a `keptPhi`-bigon on `{d₁, d₂}`
  (`keptPhi d₁ = d₂`, `keptPhi d₂ = d₁`) with the swap acting OFF `{d₁, d₂}`
  (`ρ a₀, ρ a₁ ∉ {d₁, d₂}`) yields `tracePhi d₁ = d₂`, `tracePhi d₂ = d₁`. Proved by
  `Equiv.swap_apply_of_ne_of_ne` (the swap fixes both bigon darts). No hypotheses on the map.
- **`keptPhi_face₁Dart₁`** — `keptPhi d₁ = d₂` on the chord-split side, UNCONDITIONAL. The
  `α`-then-`σ` step is `M.σ (M.α (M.φ dart)) = M.φ² dart = d₂`, which is kept
  (`face₁_two_kept_darts`), so the filtered rotation takes the single un-skipped step
  (`filteredRotation_apply_of_next_kept`). This is the easy direction of the bigon, fully closed.
- **`keptPhi_face₁Dart₂_ne_self`** — `keptPhi d₂ ≠ d₂`, FREE from `keptPhi d₁ = d₂` + `d₁ ≠ d₂`
  (`face₁Dart_distinct`) + injectivity.
- **`chordCap_tracePhi_twoCycle`** — the `tracePhi` 2-cycle on the ACTUAL `face₁` darts for the
  chord-cap anchors, derived from `ChordCapData` via the two lemmas above.
- **`correctAnchorTwoCycle_ofBigon`** — `CorrectAnchorTwoCycle data hsep cap.a₀ cap.a₁ … cap.f`
  built for the chord-cap anchors. THE TWO-LAYER CONNECTION: `sideMap₁`'s free anchors are
  INSTANTIATED at the chord-cap darts and the orbit-isolation spec of `ChordAnchor.lean` is
  discharged.
- **`face₁_sideTriangle_ofBigon`** — the touched `face₁` side face is a length-3 triangle with
  the anchors PINNED (no `≠ face₁` carve-out).
- **`contiguousInterval_ofBigon`** — end-to-end `ContiguousInterval` with the chord-cap anchors
  instantiated, threading to `ChordSideReconstruction → chord_case_recursive →
  nearTriangulation_five_colorable` (via `ChordAnchor.contiguousInterval_of_correctAnchor`).

## The SINGLE truly-resistant sub-fact (named, non-vacuous, concrete failing chain)

`ChordCapData data hsep` — the chord-cap residue, isolating exactly the discrete-rotation datum
the abstract `CombMap` does NOT synthesize:

1. **`bigon_close : keptPhi d₂ = d₁`** — the bigon WRAP. The hard half of the bigon: the filtered
   rotation, walking `M.σ` from `M.α (M.φ² dart)`, would hit `M.φ³ dart = dart` (the DELETED chord
   dart) and must skip it, wrapping to `d₁ = M.φ dart`. This skip-and-wrap depends on HOW the
   chord sits in the vertex rotation (which darts of the run are kept), i.e. the planar-embedding
   (Jordan) datum. Concrete non-derivability: `filteredRotation M.σ keptDel₁` past `dart`
   requires knowing `dart` is the only deleted dart in that `σ`-run and that the run wraps to
   `M.φ dart` — not synthesizable from the abstract `M`-triangle `face₁_isFaceTriangle` alone.
2. **`a₀, a₁` + `anchor{0,1}_avoid{1,2}`** — the CORRECT chord-cap anchors (the splice darts at
   `u, v`) with `ρ a₀, ρ a₁ ∉ {d₁, d₂}` and `a₀ ≠ a₁`: the chord cap is inserted OUTSIDE the
   bigon. This is the explicit correct-anchor placement (the splice points are the kept
   rotation-neighbors of the deleted chord dart, not the bigon darts).
3. **`hkf`, `one_fresh`** — the rep's side face and the one-fresh-chord-dart indicator (concrete).

This is strictly the SAME residue all prior rounds isolated (`OuterAbsorbsChordOrbits`,
`ChordFaceFinal`'s `tOrbitCard = 2`, `ChordAnchor`'s `CorrectAnchorTwoCycle`), now reduced to its
irreducible kernel: ONE `keptPhi`-wrap equation `keptPhi d₂ = d₁` plus the explicit
bigon-outside chord-cap anchors. The orbit-size arithmetic AND the 2-cycle algebra AND the easy
`keptPhi d₁ = d₂` step are ALL discharged; only the rotation-wrap + anchor placement remain.

## §3.3 self-audit: faithful, non-vacuous, not a re-wrapper

- **Not vacuous / not a hidden `False`.** `ChordCapData.mk'` is the explicit constructor; the
  fields are mutually consistent (the bigon `keptPhi d₂ = d₁` together with the proved
  `keptPhi d₁ = d₂` is a genuine 2-cycle of the permutation `keptPhi`; anchors with
  `ρ aⱼ ∉ {d₁, d₂}` exist whenever the kept type has ≥ 3 darts, the near-triangulation regime).
- **Not a re-wrapper / 2-cycle not restated.** `chordCap_discharge_eq` certifies the `tracePhi`
  2-cycle is COMPUTED from the bigon + anchor-avoidance through `tracePhi_twoCycle_of_bigon` — the
  generating data are the `keptPhi` equations and the `ρ aⱼ ∉ {d₁, d₂}` facts, NOT the conclusion.
- **Anchored to the real darts.** The 2-cycle is on `face₁Dart₁/₂` (= `M.φ dart`, `M.φ² dart`,
  kept+distinct by the unconditional `face₁_two_kept_darts`); `keptPhi d₁ = d₂` is PROVED on those
  actual darts. The datum is the genuine chord-triangle bigon, not an abstract pair.
- **Headline not regressed.** No upstream file edited (one-writer rule). `CorrectAnchorTwoCycle`
  threaded via the existing `ChordAnchor` API; `contiguousInterval_ofBigon` reuses
  `ChordAnchor.contiguousInterval_of_correctAnchor`.

## Verification (server uisai1, real olean chain)

- Dependency `lake build ProofsInTheBook.ChordAnchor` → Build completed successfully (8463 jobs).
- `lake env lean ProofsInTheBook/ChordAnchorInst.lean` → **RC = 0**, zero errors, zero warnings,
  no `sorryAx`/`ofReduceBool`/`native`. All **9** `#print axioms` results **clean-3
  `[propext, Classical.choice, Quot.sound]`**: `tracePhi_eq_swap_keptPhi`,
  `tracePhi_twoCycle_of_bigon`, `keptPhi_face₁Dart₁`, `keptPhi_face₁Dart₂_ne_self`,
  `chordCap_tracePhi_twoCycle`, `correctAnchorTwoCycle_ofBigon`, `face₁_sideTriangle_ofBigon`,
  `contiguousInterval_ofBigon`, `chordCap_discharge_eq`.
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → none in code (docstrings only).
- `#print axioms ProofsInTheBook.ThomassenInduction.nearTriangulation_five_colorable`
  → **clean-3, UNCHANGED**. The headline takes the `JordanOracle`-valued hypothesis
  `Ofun : ∀ p q cp cq, JordanOracle α` as a PARAMETER (ThomassenInduction.lean:621–626); the
  Five Color Theorem headline therefore stays CONDITIONAL on the JordanOracle (no upstream file
  edited — faithful advance, not a regression).

## New file (owned, fresh; NOT wired into ProofsInTheBook.lean — one-writer rule)

`ProofsInTheBook/ChordAnchorInst.lean` — imports `ChordAnchor`. 9 audited results. Branch `main`;
no commits; no branch switch; no codex/OpenAI tooling; never ran lake/lean on the Mac
(kernel-panic rule observed — verified exclusively on uisai1).

## Precise residue going forward

The Chapter-35 chord-side wall is now exactly `ChordCapData.bigon_close` (`keptPhi d₂ = d₁`, the
filtered-rotation wrap past the deleted chord dart) + the explicit bigon-outside chord-cap
anchors. The next attack vector is to discharge `keptPhi d₂ = d₁` from the vertex-rotation
structure of the chord (the `σ`-run at the chord endpoint containing exactly `dart` as its
deleted dart and wrapping to `M.φ dart`) — a `filteredRotation` two-step computation, the last
genuinely geometric datum.
