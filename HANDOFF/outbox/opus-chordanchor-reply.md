# Ch35 chord-side LAST residue: `tOrbitCard = 2` (correct-anchor orbit-isolation) PROVED from
the explicit `tracePhi` 2-cycle on the two ACTUAL kept `face₁` darts — discharging
`SideFaceTriangle(face₁) → InnerFacesSide₁NoCarve → ContiguousInterval`. Headline stays
CONDITIONAL on the JordanOracle parameter (clean-3, UNCHANGED).

## TL;DR (honest, §3.3)

The named residue `tOrbitCard = 2` for the chord-triangle `face₁` orbit is realized and FULLY
FORMALIZED, clean-3, in the new file `ProofsInTheBook/ChordAnchor.lean` (405 lines, 10 audited
results, RC=0, all `[propext, Classical.choice, Quot.sound]`, no
`sorry`/`axiom`/`admit`/`native_decide`).

The crux — **the orbit-size count `tOrbitCard = 2` — is now a THEOREM**, derived from the
explicit `tracePhi` 2-cycle via a pure permutation-algebra lemma. The remaining input is the
`tracePhi`-2-cycle EQUATION itself (`tracePhi (M.φ dart) = M.φ² dart`, `tracePhi (M.φ² dart) =
M.φ dart`) — the chord-cap placement that the abstract `CombMap` provably does not certify.

## What is PROVED UNCONDITIONALLY (the genuinely-new derivable content)

- **`twoCycle_orbit_card`** (pure permutation algebra, no Jordan input): if a permutation `g`
  swaps two distinct points `g k₀ = k₁`, `g k₁ = k₀`, then the cycle-orbit filter of `k₀` is
  EXACTLY `{k₀, k₁}`, so `#{c | g.SameCycle c k₀} = 2`. Proved by showing `{k₀,k₁}` is
  `g`-invariant (the swap nat-iterate stays on the pair) so any same-cycle element lands in it.

- **`tOrbitCard_eq_two_of_tracePhi_swap`**: `tOrbitCard β ρ a₀ a₁ d₁ = 2` from `tracePhi d₁ =
  d₂`, `tracePhi d₂ = d₁`, `d₁ ≠ d₂`. This IS `tOrbitCard = 2` computed directly — `tOrbitCard`
  unfolds to exactly the cycle-orbit filter cardinality that `twoCycle_orbit_card` counts.

- **`face₁Dart₁/face₁Dart₂` + `face₁Dart_distinct`**: the two kept `face₁` darts `M.φ dart`,
  `M.φ² dart` lifted to subtype elements of `{d // d ∉ keptDel₁}`, kept and distinct
  UNCONDITIONALLY via `ChordFaceFinal.face₁_two_kept_darts` (no anchor input). So the abstract
  `k₀, k₁` of the 2-cycle ARE the genuine chord-triangle darts, not an unanchored pair.

- **`correctAnchor_tOrbitCard_two`, `face₁_sideFaceTriangle_of_correctAnchor`,
  `face₁_sideTriangle_ofFace₁Cycle`**: from the `tracePhi` 2-cycle on the ACTUAL `face₁` darts
  + the one-fresh-chord-dart indicator, the touched `face₁` side face is a `SideFaceTriangle`
  (`faceLen = 3`) DIRECTLY (= `tOrbitCard 2 + 1 + 0 = 3` via
  `ChordFaceFinal.sideFaceTriangle_of_count`). NO `≠ face₁` carve-out, NO boundary absorption.

- **`innerFacesSide₁NoCarve_of_classifier` + `contiguousInterval_of_correctAnchor`**: the
  carve-out-free classification `InnerFacesSide₁NoCarve` (splice-untouched faces by the
  inner-triangle route ⊕' the touched `face₁` face by the correct-anchor count) assembles the
  full `ChordSideNT.ContiguousInterval` — the drop-in for the downstream chain
  `→ ChordSideNT.chordSideNearTriangulation → ChordReconClose.ChordSideClassification →
  ChordSideReconstruction → ChordSplitNT.chord_case_recursive → nearTriangulation_five_colorable`.

## The precise residue now (sharpened to a concrete satisfiable EQUATION)

The lone surviving input is the named structure `CorrectAnchorTwoCycle` (Type-valued, carries
the witness darts) — concretely, for the genuine surgery via `correctAnchorTwoCycle_ofFace₁`,
the two `tracePhi` equations

    tracePhi (sideAlpha₁) sideSigma₁ a₀ a₁ (M.φ dart)   = M.φ² dart
    tracePhi (sideAlpha₁) sideSigma₁ a₀ a₁ (M.φ² dart)  = M.φ dart

plus the rep's-face identity and the one-fresh-dart indicator. This is the chord-cap placement:
the cap dart `β aⱼ` IS the chord dart's rotation-neighbor, so the swap re-routes `keptPhi (M.φ²
dart)` back to `M.φ dart`, isolating the 2-dart orbit. It is genuinely the discrete
Jordan–Schoenflies datum the abstract `CombMap` does not synthesize: **the anchors `a₀, a₁` are
universally quantified throughout `PlanarMapChordSplit.sideMap₁`** (PlanarMapChordSplit.lean §8,
lines 683–689: "the side map is well defined for *any* distinct anchors; the *correct* anchors
are what make the outer boundary the arc-plus-fresh chord, which is part of the
separation/classification layer"; ChordSideNT.lean 41–42: "for the arbitrary anchors `sideMap₁`
is defined over, a non-contiguous split would leave a non-triangle"). There is NO construction
in the combinatorial-map layer forcing `a₀, a₁` to the chord-dart neighbors.

This file ADVANCES the residue from a face-SIZE count obligation (`ChordFaceFinal`'s
`tOrbitCard = 2` + one indicator, stated but not computed) to a concrete `tracePhi`-EQUATION:
the orbit-SIZE arithmetic is now fully discharged (`twoCycle_orbit_card`), leaving only the
2-cycle equation, which is the irreducible chord-cap-placement datum.

## §3.3 self-audit: FAITHFUL, non-vacuous, not a re-wrapper

- **Not vacuous / not a disguised `False`.** `CorrectAnchorTwoCycle` is SATISFIABLE: take `β a₁
  = M.φ² dart ∈ {M.φ dart, M.φ² dart}` (one indicator fires), `β a₀ ∉` that orbit (other
  indicator 0) — consistent with `one_fresh = 1` and with the 2-cycle. The
  boundaryorbit-handoff #eval witness (K=Fin 6, ρβ a single 6-cycle) exhibits exactly such a
  real two-orbit split, so the predicate is inhabited, not an unsatisfiable premise.
  `CorrectAnchorTwoCycle.mk'` and `correctAnchorTwoCycle_ofFace₁` are the explicit constructors.
- **Not a re-wrapper / count not restated.** `correctAnchor_discharge_eq` certifies the `2` is
  COMPUTED from the swap equation through `twoCycle_orbit_card`, not handed in. The hypothesis
  is the *generating* 2-cycle `tracePhi d₁ = d₂` (an equation about the actual side `tracePhi`),
  from which `tOrbitCard = 2` is DERIVED — this is the orbit-size arithmetic the prior round
  left open, now a theorem.
- **Anchored to the real darts.** `face₁Dart₁/₂` ARE `M.φ dart`, `M.φ² dart`, kept+distinct by
  the unconditional `face₁_two_kept_darts`; the 2-cycle is on THOSE, so the datum is the genuine
  chord-triangle structure, not an abstract pair.
- **Headline not regressed.** No upstream file edited (one-writer rule). The Type-valued
  structure is used via `⊕'` (PSum) in the classifiers so it threads cleanly.

## Verification (server uisai1, real olean chain)

- Dependency `lake build ProofsInTheBook.ChordFaceFinal` → Build completed successfully (8462
  jobs).
- `lake env lean ProofsInTheBook/ChordAnchor.lean` → **RC = 0**, zero errors, zero warnings, no
  `sorryAx`/`ofReduceBool`/`native`. All **10** `#print axioms` results **clean-3
  `[propext, Classical.choice, Quot.sound]`**: `twoCycle_orbit_card`,
  `tOrbitCard_eq_two_of_tracePhi_swap`, `correctAnchor_tOrbitCard_two`,
  `face₁_sideFaceTriangle_of_correctAnchor`, `innerFacesSide₁NoCarve_of_classifier`,
  `contiguousInterval_of_correctAnchor`, `correctAnchor_discharge_eq`, `face₁Dart_distinct`,
  `correctAnchorTwoCycle_ofFace₁`, `face₁_sideTriangle_ofFace₁Cycle`.
- `grep -nE '\bsorry\b|\badmit\b|native_decide|^axiom '` → none in code (only docstring).
- `#print axioms ProofsInTheBook.ThomassenInduction.nearTriangulation_five_colorable`
  → **clean-3, UNCHANGED** (still parameterized by the `JordanOracle`-valued hypothesis
  `Ofun : ∀ p q cp cq, JordanOracle α`; no upstream file edited — faithful advance, not a
  regression). The Five Color Theorem headline therefore stays CONDITIONAL on the JordanOracle.

## New file (owned, fresh; NOT wired into ProofsInTheBook.lean — one-writer rule)

`ProofsInTheBook/ChordAnchor.lean` — imports `ChordFaceFinal`. 10 audited results. Branch
`main`; no commits; no branch switch; no codex/OpenAI tooling; never ran lake/lean on the Mac
(kernel-panic rule observed — verified exclusively on uisai1).

## The single truly-resistant sub-fact (named, non-vacuous, concrete failing chain)

`CorrectAnchorTwoCycle data hsep a₀ a₁ hne f` — concretely the two `tracePhi` equations above
on the actual `face₁` darts. Concrete non-derivability at the `CombMap` layer: `sideMap₁ hsep
a₀ a₁ hne` (PlanarMapChordSplit.lean:695) is DEFINED for arbitrary distinct `a₀, a₁ : {d // d ∉
keptDel₁}` with NO relation to `dart`; nothing in the combinatorial-map layer constrains the
anchors, so `tracePhi a₀ a₁ (M.φ dart)` is unconstrained for arbitrary anchors — the 2-cycle
holds iff the anchor `β aⱼ` is placed at the chord-dart's rotation-neighbor `M.φ² dart`, which
is the planar-embedding (Jordan) datum. This is the SAME residue isolated by
`ChordBoundaryOrbit.OuterAbsorbsChordOrbits` and `ChordFaceFinal`'s `tOrbitCard = 2` clause,
now reduced to its irreducible kernel: a single 2-cycle equation, with all orbit-size
arithmetic discharged.
