# Ch35 — Unconditional chapter35: autonomous-run doctrine (2026-06-17)

## Main goal (one sentence)
Make `chapter35` UNCONDITIONAL: every near-triangulation is 5-colorable with NO residual
hypotheses, clean-3 ({propext, Classical.choice, Quot.sound}).

## State at run start
- Chord branch CLOSED unconditional (canonicalChordBranchResidualSupplier, 69416e6).
- All three §3.3 vacuities REPAIRED + committed: FIX1 (chordless 3<M.V, 5127f15), FIX2 (chord c₁,
  b9dc3a2), FIX3 (chordless mergedArc ∀, 41b0694).
- Chordless seam DONE (mergedArc + merged-orbit, ZinanCh35MergedArc, 41b0694).
- PHASE C STAGE C-E helpers landed (ZinanCh35DeletedAssembly): deleted_outer_vertices_nodup_M
  (outer_simple core), cleanFaceClass_of_fan_pair_mergedOrbit (cleanFaceClass, non-circular),
  exists_head/terminal_fan_pair.
- REMAINING: (1) φ'-itinerary [e₀..e_k]++oldArc → DeletedSeamData; (2) ChordlessOracle assembly;
  (3) ChordlessOracleResidual; (4) endgame fiveColor_of_residual (Path B, verified).

## Avenues
(a) [PRIMARY] Finish PHASE C straight: itinerary (route b: mergedDarts membership↔SameCycle +
    merged-orbit card + Nodup-perm → faceDartList r₀ ~ mergedDarts) → DeletedSeamData →
    DeletedBoundaryClassification API (boundary_iff via σ-orbit technique, mirror committed side-1
    parent_boundary_to_side_boundary) → ChordlessOracle (ChordlessDeletionSite +
    choose_two_reserved_colors + deleted_thomassenLists) → ChordlessOracleResidual →
    fiveColor_of_residual hNT canonicalChordBranchResidualSupplier (chordlessBranchSupplier_of_residual ·)
    = unconditional chapter35.
(b) [fallback if route-b itinerary stalls after 3 concrete attempts] route-a literal φ'.toList
    equality via cyclic-itinerary lemma; OR strengthen via explicit getElem enumeration.
(c) [fallback if oracle assembly stalls] isolate remaining oracle fields as a named residual
    structure (like the chord side's fuel) + discharge each field; never stop at decomposition.

## Fallbacks / parallel resources
- ChatGPT Pro life/life2 (ask-gpt.py) for hard sub-points (NO effort cap in briefs).
- uisai2 codex (cx2, ISOLATED checkout ~/repos/pbook-ch35-cx2, NEW files only) for INDEPENDENT
  plumbing (ChordlessDeletionSite, choose_two_reserved_colors, fan_w_ne_v0) — one-file-one-writer.
- Mac codex (pbookch35cx) stays on the hard critical path (itinerary → DeletedSeamData → boundary_iff).

## Terminal conditions
- SUCCESS: `chapter35` (or fiveColor_planar_NT) unconditional, clean-3, full build green.
- Per-residual: clean-3 + non-vacuity verified (no carried unsatisfiable premise — the §3.3 trap
  that already bit 3×; verify EVERY new residual is satisfiable before banking).
