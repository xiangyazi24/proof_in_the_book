# Ch35 (Five Colour Theorem) — SESSION HANDOFF (2026-06-15)

Branch `zinan-overnight`, all work below COMMITTED + PUSHED. HEAD `be7fbb7`.
Authoritative resume doc. Companion files: `HANDOFF/ch35-residual-worklist.md` (full residual map),
`HANDOFF/ch35-arcsplit-core-refactor.md` (the converged #0 design), `HANDOFF/SATISFIABILITY-AUDIT.md`
(the §3.3 ledger). Memory: `~/.claude/.../memory/project-ch35-vacuity-obstruction.md`.

## 0. TL;DR — what changed this session

The chapter was a **silent vacuity** (`NearTriangulation` provably uninhabited, headline vacuously
true). That is FIXED and the chapter is now sound; the "discrete-Schoenflies arcSplit residue" was a
**phantom** created by the bug. The genuine remaining content is small & combinatorial. Endpoint
`ZinanCh35Final.fiveColor_planar_of_recursionResiduals` is an HONEST conditional on `Ch35RecursionResiduals`.

## 1. LOCKED IN (committed, full build GREEN ~8878 jobs, 0 sorryAx, clean-3)

| Commit | What |
|---|---|
| `7998ab7` | **Vacuity fix**: `BoundaryArcSplit.path{1,2}_internal_iff_proper` `↔`→one-directional `proper→HasInternalVertex`; deleted the now-false `boundaryArcSplit_consecutive_unsatisfiable` + mirror. `NearTriangulation` is inhabitable again. Record: `ZinanCh35VacuityObstruction.lean`. |
| `744364d` | Satisfiability audit over all vacuity-capable chapters — only Ch35 was a real vacuity; Ch13/Ch14 = honest open conditionals (not hidden). `HANDOFF/SATISFIABILITY-AUDIT.md`. |
| `37696e3` | Honest relabeling (Ch13 `realization_rigid` "UNCONDITIONAL"→"given a ConvexPolytopeRealization"; Ch35 "39.5/40"→honest); FFCT57 marked superseded dead scaffolding. |
| `6306080`,`ed95c3f`,`9a04d7d` | **arcSplit core refactor (#0) COMPLETE**: `BoundaryCycle extends BoundaryCycleData`; `BoundaryCycleData.arcSplit_of_nodup` over the core + `toBoundaryCycle` (new `PlanarMapBoundaryArcSplit.lean`); `boundaryCycleOfFace` takes `hnodup` not `arcSplit`; assemblers/OuterTrace/Contiguous cascade fixed. **arcSplit is DERIVED from boundary simplicity, off the residual surface.** |
| `1139110` | **R4a LANDED**: `ZinanCh35Side2Anchors.side₂AnchorsShareFace_canonical` (clean-3) — the side-2 producer that previously had NONE (mechanical port of side-1). |
| `03f000a` | **`outer_v0_darts_consecutive` FULLY PROVEN** (`ZinanCh35OuterV0Consecutive.lean`, clean-3, chordless keystone — needs only `outer_simple`, no chordlessness) + 2 of 4 `MergedOuterArcData` fields. `side outer_simple` algebraic reduction proven (`ZinanCh35SideOuterSimple.lean`), conditional on `OuterTraceInjOn`. |
| `be7fbb7` | §3.3 catch: marked `OrbitProjOnOuterArc` UNSOUND (see §3). |

## 2. THE IMMEDIATE NEXT TARGET — `OuterTraceInjOn` via the orbit↔arc correspondence

**File:** `ProofsInTheBook/ZinanCh35SideOuterSimple.lean`. **Goal:** discharge
`OuterTraceInjOn data hsep a₀ a₁ hne` for the CANONICAL anchors (`side₁Anchor₀/₁`), which then feeds
`side₁_outer_simple_canonical` → the `outer_simple` input of `ZinanCh35Contiguous.contiguousInterval_holds`.

`OuterTraceInjOn` = `∀ x y ∈ (sideMap₁).faceDartList (inr 1), M.tail (proj a₀ a₁ x).1 = M.tail (proj a₀ a₁ y).1 → x = y`.
It is TRUE (⟺ `outer_simple`; the §2 collapse `sideMap₁_tail_eq_iff_M_tail_proj` is proven, and the side
map is a genuine near-triangulation). It is the lone genuine discrete-Jordan residual on the chord side.

**⚠️ DO NOT use `OrbitProjOnOuterArc`** (the dart-level decomposition in the same file). It is UNSOUND:
the orbit root `inr 1` has `proj a₀ a₁ (inr 1) = a₁` (chord anchor), and `a₁.1 ∉ outerCycle.darts` (the
chord is not a boundary edge), so it requires a false containment. `outerTraceInjOn_of_decomposition` is
a vacuity-trap conditional. Marked dead in `be7fbb7`.

**Correct attack — VERTEX level:**
- Orbit darts are `inr 1` + various `inl k` (NOT `inr 0` — that's the inner side of the fresh edge).
- `g x := M.tail (proj a₀ a₁ x).1`: `g(inr 1) = M.tail a₁.1 = v` (canonical anchor tail, proved in
  `ZinanCh35ChordResidue.lean:121`-ish: `M.tail (side₁Anchor₀).1 = u`, `M.tail (side₁Anchor₁).1 = v`);
  `g(inl(β a₁)) = M.head a₁.1 = u`; intermediate `inl k → arc-interior vertices`.
- The orbit's `inl`-darts ARE the boundary side-arc darts → their `.1 ∈ outerCycle.darts` → `M.tail`
  injective among them via `hNT.outer_simple` + `BoundaryCycle.tail_injective_on_darts`. `v`/`u` distinct
  (endpoints), carried once each. So `g` is injective on the orbit.
- **The construction to build:** the orbit ↔ `boundaryArcDartRun` correspondence (the `inl`-darts of
  `(sideMap₁).faceDartList (inr 1)` ↔ the darts of `hNT.boundaryArcDartRun` (the `v→u` boundary arc),
  with `inr 1` for the chord).

**Available machinery (cite/reuse):**
- `ZinanCh35ArcDartRun.lean:285` `boundaryArcDartRun` — the boundary side-arc, darts on `hNT.outerCycle.darts`, length ≥ 2.
- `ChordFaceCount.lean:204-318` — freshMap φ-cycle ↔ `tracePhi` (`faceProj`), `tracePhi`↔`keptPhi`:
  `freshPhi_sameCycle_inl_faceProj`, `tracePhi_sameCycle_faceProj_of_freshPhi_sameCycle`,
  `freshPhi_sameCycle_inl_of_tracePhi_sameCycle`.
- `ChordBoundaryOrbit.lean:199-318` — `tracePhi_reaches_keptPhi_iterate_b0/b1`, `tracePhi_reaches_of_keptPhi_sameCycle_b1`, `sideFace_inl_eq_iff_tracePhi`.
- `ChordReconClose.lean:117-145` — `sideVertexToM₁` (the §2 collapse map; `sideVertexToM₁ ⟦inl x⟧ = M.tail x.1`), and the canonical anchor tail facts.
- `ZinanCh35Contiguous.lean:88-181` — the 3-dart itinerary (`freshMap_phi_inr_one`, `freshMap_phi_inl_b1`, the orbit threads `inr 1 → inl(ρ a₀) → … → inl(β a₁) → inr 1`).
- `proj` def: `ChordSplitEuler.lean:105` (`inl k↦k`, `inr 0↦a₀`, `inr 1↦a₁`); `faceProj`: `ChordFaceCount.lean:161` (`inr↦β a₀/β a₁`). NOTE proj ≠ faceProj on `inr`.

**Orbit membership handle:** `x ∈ φ.toList (inr 1) ↔ φ.SameCycle (inr 1) x ∧ inr 1 ∈ φ.support`
(`Equiv.Perm.mem_toList_iff`); `faceDartList d = φ.toList d`.

## 3. THE REST OF THE UNCONDITIONAL CLOSE (after `OuterTraceInjOn`)

See `HANDOFF/ch35-residual-worklist.md` for the full map. Summary of genuine residuals:
- **R4d-iii / R6d**: side-2 + deleted-map `outer_simple` — MIRROR the `OuterTraceInjOn` argument.
- **R6a `MergedOuterArcData`**: 2 fields done; remaining `arc_run` (cyclic-list arc walk, reuse the
  `Nodup`-cyclic-list tech in `PlanarMapBoundaryArcSplit`) + `exit_jump` (spoke id via
  `PlanarMapFanMergedOrbit.fanTriangle_shared_spoke`). Isolated in `mergedOuterArcData_of_exit`.
- **R3c-i / R4d-i**: side-map `IsSimpleGraph` / `IsSphereMap` (genus-0; producers exist in
  `ChordSideRecon` consuming connectivity/face-count residuals).
- **inner_tri / inner_reps**: `InnerRepsAvoidBoundary` (`ChordBoundaryOrbit:380`), via the face-size route.
- **Thomassen recursion fuel** (R3a/b, R4b/c, R5, R7): pullback lists `Lₛ=L∘ι`, precolored placement,
  reserved colours, deleted lists — concrete recursion data, the driver `thomassen_aux_chordRecursive` is proven.
- **Final integration**: assemble into `ChordRecursionInputSupplier` + `ChordlessOracleResidual`.

## 4. INFRA / DISCIPLINE NOTES
- Build: **uisai2** only (new Tailscale IP `100.75.55.5`, in `~/.ssh/config`; 64 cores, 17T disk).
  Local `lake build` is BLOCKED (kernel-panic hook); `lake env lean <file>` OK for single files whose
  deps are unchanged. After foundation edits, do a full `lake build` on uisai2 (tmux + tee, ~30-60s incremental).
- **Codex is OUT of credits until Jun 18** — use Claude subagents (mechanical adaptation + uisai2 verify) or self.
- ChatGPT channels: **pbook (Pro), pbook2 (xhigh)** — do not cross. `python3 ~/.openclaw/workspace/scripts/ask-gpt.py <ch> "Q"`.
- §3.3 discipline (load-bearing here): verify residual TRUTH before grinding (caught both the universal
  arcSplit vacuity AND the dart-level `OrbitProjOnOuterArc` over-strength this way); independent
  verification of subagent reductions is mandatory; never leave clean-3 conditionals on false premises
  unmarked. The repo's history shows over-claim is the recurring failure mode — label honestly.

---

## ADDENDUM 2026-06-16 — broken HEAD fixed + OuterTraceInjOn REDUCTION landed

**Build state corrected.** HEAD `bb29ffe` did NOT compile: `ZinanCh35SideOuterSimple.lean` had a
syntax error (commit `be7fbb7` left orphan docstring prose outside any comment, before
`def OrbitProjOnOuterArc`). The "full build GREEN ~8878 jobs" claim above was STALE (predated
`be7fbb7`). FIXED + verified (full 8878-job build on uisai2, isolated clone `~/repos/pbook-ch35`,
0 errors, file clean-3) + pushed: commit `6f3058d`.

**Isolated build loop:** `uisai2:~/repos/pbook-ch35` (hardlinked mathlib packages from the main
tree + `lake exe cache get`). Does NOT touch the other session's Ch13 WIP in `~/repos/proof_in_the_book`.
Single-file check: `cd ~/repos/pbook-ch35 && lake env lean ProofsInTheBook/<F>.lean` (deps' oleans built).

**OuterTraceInjOn REDUCTION (commit `55f675d`, clean-3, verified):** new file
`ZinanCh35OuterTraceProof.lean`. `canonical_OuterTraceInjOn_of_arcTrace` proves OuterTraceInjOn
(canonical anchors) from ONE sharply-isolated bridge:

  `CanonicalSide₁OuterArcTrace data hsep A hArcKept` — the ordered orbit↔arc classifier:
  every x ∈ S.faceDartList(inr 1) is `inr 1` OR `inl ⟨A.arcDart i, _⟩`, where
  `A : DartArc M hNT.outerCycle u v` is the **u→v** boundary dart-arc.

Why u→v (NOT the convenience `boundaryArcDartRun v u`): `A.head_last_ne_tail : ∀ i, v ≠ M.tail(A.arcDart i)`
— `v` (carried by root `inr 1`) is not an arc tail, so root↔arc cannot collide. The v→u run's first
tail IS v ⟹ would collide. This is the §3.3-critical orientation fact. `A.tail_nodup` closes arc↔arc.

**REMAINING (the genuine discrete-Jordan bridge — ChatGPT `life` working on it, query
`/tmp/ch35-classifier-q.txt`):**
1. **Prove `CanonicalSide₁OuterArcTrace`** (ordered orbit↔arc trace). Orbit membership via
   `freshFace_sameCycle_iff` (x∈orbit ↔ `tracePhi.SameCycle (β a₁) (faceProj x)`); `inr 0 ∉ orbit`
   for canonical anchors (share-face ⟹ swap splits, `chordOrbits_eq_iff_tracePhi`); the inl-orbit =
   arc via `keptPhi` walking the arc (`hstep: keptPhi(arcDart i)=arcDart(i+1)` from
   `sideAlpha₁_apply_coe` + filteredRotation skip-deleted + arc consecutiveness `head(arc i)=tail(arc i+1)`).
2. **`hArcKept : ∀ i, A.arcDart i ∉ keptDel₁`** = `arcDart i ∈ keptSet₁` (`mem_keptDel₁_iff`) — the
   side-1 arc identification (which boundary arc belongs to side 1).
3. **Orientation / `hhv`** — `chordDart_orientation` (ZinanCh35Aligned): chord dart is u→v OR v→u;
   pin via `normalizedChordSplitData` so the arc terminal = `M.head data.dart` = `M.tail(a₁.1)`
   (`canonicalAnchor₁_tail`). Reduction currently takes `hhv : M.head data.dart = v` as hypothesis.
4. **Wire** `canonical_OuterTraceInjOn_of_arcTrace` → `side₁_outer_simple_canonical` (once 1–3 land).
