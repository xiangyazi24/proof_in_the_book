# Ch13 CLEAN state (2026-06-13, post local-build switch)

## 🎯 Ch13 machine-verified reduced to ONE clean residue: `OpenedArmTurningLtTwoPi`
Full chain LOCAL-BUILD clean-3 (8557 jobs). uisai2 ABANDONED (its olean drift caused all the
file-revert/build-flakiness chaos). BUILD LOCALLY: `cd ~/repos/proof_in_the_book && export PATH="$HOME/.elan/bin:$PATH" && command lake build ProofsInTheBook.ZinanFFCT105` (the shell `lake` fn blocks `build`; use `command lake`).

### Committed chain (branch zinan-overnight, all clean-3, all build locally):
- FFCT100 (a0d4fb2): `spherical_arm_mono_ch13_of_properNoCollision : ProperCrossPieceNoCollisionAtSup → SphericalArmMonotone`. Splits FFCT86 endpoint residue: full-closure r=0&s=n → endpt=sDist(x,x)=0; proper → residue. **WARNING: a linter/sync keeps reverting its full-closure proof (lines 62-67) to a BROKEN `unfold sDist; rw[S2.inner_self]` form. The committed fix uses `unfold sDist sInner` (sInner must be unfolded before S2.inner_self matches). If build fails at FFCT100:66, re-apply: `perl -0pi -e 's/unfold sDist\n      rw \[S2\.inner_self\]/unfold sDist sInner\n      rw [S2.inner_self]/' FFCT100.lean` then build+commit atomically.**
- FFCT101 (23a7c87): `planar_properRepeat_is_fullClosure` — PlanarLiftedTurnSpan + global weak support + repeat(r+2≤s) → r=0∧s=N-1. UNCONDITIONAL, no residue. (det3=κρρsin(θ_s−θ_r); proper repeat → external vertex on interior edge, span∈(π,2π), sin<0, contradicts support≥0.)
- FFCT103 (89972fe): wiring via the OLD over-quantified residue (superseded by FFCT105).
- FFCT104 (7bbcc53): `openedWBS_gnomonicSingleWind_of_bound (hbound : OpenedArmTurningLtTwoPi) : Nonempty (GnomonicSingleWind (openedWBS A B k))`. REPLACED the over-quantified `OpenedWBSPlanarLiftedTurnSpanExists` (FFCT97, unprovable: quantifies all frames, wrong-handed det3<0 breaks turn_pos) with the CLEAN `OpenedArmTurningLtTwoPi`. `oriented_span_of_weak_turningBound` = weak-support variant of FFCT96's oriented_residue (drops strict-GLOBAL, keeps strict-CONSECUTIVE). GnomonicSingleWind bundles its own oriented frame internally.
- FFCT105 (e9a828e): `spherical_arm_mono_ch13_of_turningBound (hbound : OpenedArmTurningLtTwoPi) : SphericalArmMonotone`. **THE LIVE Ch13 reduction.** Re-wires FFCT103 with FFCT104's cert.

### THE LAST RESIDUE — `OpenedArmTurningLtTwoPi` (FFCT104 line ~115):
Oriented frame (det3 h u v=1) + plane + WEAK global support (∀ i j, 0≤det3 Qᵢ Qᵢ₊₁ Qⱼ) + strict
CONSECUTIVE turns (0<det3 at m,m+1,m+2) + nonzero edges ⟹ `liftedAngle(edgeZ Q u v)(n-1) −
liftedAngle(...)(0) < 2π`. TRUE + non-vacuous (FFCT104 premises_satisfiable; 200k MC max 6.25<2π).
NOT strict-global (openedWBS has det3=0 at the WBS stuck contact). Needs discrete-Umlaufsatz:
closed convex polygon turns 2π, open arm omits ≥2 strict closing turns. Single det3-sin
insufficient (weak support = full partial sum Σρ_i sin≥0, multiple sign changes). Existing
machinery: PolygonUmlaufsatz (realTurning=±2π for StrictSimplePolygon), but it's STRICT (the
collinear stuck contact needs a weak adaptation or direct closing-turn argument).

## IN FLIGHT
- Subagent ae95f4731160d5c0c → FFCT106 = `openedArmTurningLtTwoPi_holds : OpenedArmTurningLtTwoPi`.
  Route A: multi-covector partial sums (FFCT101 technique) — "increasing-angle unit vectors
  spanning ≥2π can't keep all prefix-partial-sums in a common half-plane". Route B: Umlaufsatz.
  On completion: pull/commit (local build verify), then `spherical_arm_mono_ch13_of_turningBound
  (openedArmTurningLtTwoPi_holds) : SphericalArmMonotone` = UNCONDITIONAL Ch13 → wire into the
  main Ch13 theorem (check how the book's top-level SphericalArmMonotone / spherical_arm_mono is
  stated and discharge it).

## DISCIPLINES (this session)
- BUILD LOCALLY ONLY (`command lake build`); uisai2 abandoned. Mathlib cache present (was partial,
  now fully built locally — incremental builds fast).
- codex does NOT write files (write-failures) — it advises/audits; I or subagents write. (Xiang.)
- Save-immediately: pull+commit subagent output before anything; verify commit LANDED (git cat-file
  -e HEAD:file) — earlier commits silently failed to persist (phantom b0e7c63).
- Subagents write directly to Mac path + verify via local `command lake build`.
- §3.3: every isolated residue must be TRUE + non-vacuous (FFCT99 refuted a false claim; FFCT104
  fixed an over-quantified one). Hand-audit residues before building on them.
