# opus-szcomplete-reply — Chapter 13 §8.4 structural assembly (the three pieces)

Status: **`spherical_arm_mono(_strict)` is NOT made fully unconditional.**  The three named structural
pieces are **built and verified** as genuine new substrate (clean-3), strictly enlarging the layer
beneath the residue; but they do **not** close `OpeningStructuralAssembly`.  After honest grinding the
residue stays the substrate's already-named, design-irreducible opening-witness existence
(`StuckWitnessExists` ≡ `OpenedArmReachOrStuck` ≡ `OpeningData` ≡ `SZStepGeom`) — the design's
"THE hard theorem".

New file: `ProofsInTheBook/SphericalSZComplete.lean` (RC=0).  No upstream files edited
(`SphericalDiagCut.cutArm` is already generic in the arm, so the B-side needed no edit — I instantiate
it; `SphericalArmFinal` re-exported, not modified).

## What I BANKED (genuine new content, clean-3 — strictly enlarges the substrate)

All three are NEW substrate (the prior round had only the single-field `open_hemisphere_reindex`, no
reach measure, and no B-side cut):

1. **Arbitrary-joint opening via a full five-field relabel.**
   `cyclicShiftPolygon_strictConvex` — the cyclic shift `P ↦ P ∘ (· + r)` transports *all five*
   `StrictConvexSphPolygon` fields (edges short, edge supports ≥0, non-incident supports >0, open
   hemisphere, three_le).  Backed by `shift_succ_comm` (`(i+r)+1 = (i+1)+r` via `add_right_comm`) and
   additive injectivity of `+r` on `Fin m`.  This is the relabel moving an arbitrary interior joint of
   the closed polygon to a canonical position so the proved last-joint machinery applies.  (Reversal
   recorded via `det3_swap01`.)

2. **The reach-recursion well-founded measure.**  `unmatchedSet`/`unmatchedCount` =
   `#{i | jointAngle A i < jointAngle B i}` (a `Finset.card`), with `unmatchedCount_lt_of_match`: a
   reach match at one more joint (previously unmatched, now matched, no matched joint regressing)
   **strictly decreases** the count (`Finset.card_lt_card` via `ssubset`).  This is the
   strictly-decreasing measure the §8.4 reach recursion runs on.

3. **The B-side diagonal cut + two-sided transport.**  `cutArmB := cutArm` at `B`,
   `cutArmB_strictConvexArm` (generic `cutArm_strictConvexArm` at `B`), and `bothSided_cut_transport`
   — `cut_endpt_transport` with BOTH sub-arms supplied (the B-side, previously absent, is now an
   explicit construction).  Glues the two sub-comparisons through `SZComparison n`.

Plus the conditional re-exports `spherical_arm_mono_complete` / `_strict_complete` /
`schoenbergZaremba_complete` (conditional only on `OpeningStructuralAssembly`), and non-vacuity guards
for each piece (`cyclicShiftPolygon_zero`, `unmatchedCount_eq_zero_iff`, `cutArmB_zero`).

## The single remaining residue (honest — ONE named, non-vacuous Prop + concrete failing chain)

`SphericalArmClose.OpeningStructuralAssembly` (operationally `StuckWitnessExists ∧ WeakArmStep`,
its hypothesis `BoundaryConvexPersist` being proved).  After the three pieces, the §8.4 step splits:

* **(cut case)** an interior joint matched → equal-angle diagonal cut → `bothSided_cut_transport`
  feeds `SZComparison n` → **discharged here**;
* **(opening case)** all-strict, some joint of `B` strictly wider → needs the **opening-witness
  existence**, which genuinely resists.

**Concrete failing chain (verified against the substrate):**

1. `StuckWitnessExists` needs `qstar` with `A 0 ∈ span≥0 {A 1, qstar}`, obtained from
   `betweenness_span_nnreal` on the vanishing *closing* support `det3 (A 0)(A 1) qstar = 0`.
2. The augmented STUCK branch (`augmented_reachOrStuck_at_sup`, proved) yields `∃ ij, mixedSupport A
   ij δ* = 0` — *some* support, not the closing triple.  The substrate records this exact gap
   (`SphericalOpeningProcess.lean:371`: "`arm_reach_or_stuck` yields *some* vanishing support, not the
   closing one").
3. The design §8.4 resolution for an arbitrary vanishing support is the **two-arm diagonal split**
   (`convex_stuck_gives_cut`: left `A i..A j` + right `A j..A i`, glued by the hinge lemma).  The
   substrate has only the **last-vertex-drop** `cutArm` (single sub-arm); the general consecutive-range
   two-arm split + the non-equal-angle glue (the stuck cut is at a vanishing *support*, so `diag_len_eq`
   does NOT apply — the diagonal lengths in `A` and `B` need not match) is absent.  This is the
   design's terminal-visibility obstruction, proved *not* implied by strict convexity alone
   (`CH13_HINGE_DESIGN.md` §6 determinant counterexample).

This is exactly the substrate's irreducible primitive; I did **not** restate it as a fresh
co-extensive Prop (no re-wrapper).  The three pieces enlarge the layer beneath it.

## Verification

* `rsync` + `ssh uisai1 ... lake env lean ProofsInTheBook/SphericalSZComplete.lean` → **RC=0**.
  Deps prebuilt by `lake build ProofsInTheBook.SphericalArmFinal` → "Build completed successfully
  (8441 jobs)".
* `#print axioms` (via a scratch importer on the server) → **clean-3 `[propext, Classical.choice,
  Quot.sound]`** on: `spherical_arm_mono_strict_complete`, `spherical_arm_mono_complete`,
  `cyclicShiftPolygon_strictConvex`, `unmatchedCount_lt_of_match`, `bothSided_cut_transport`,
  `schoenbergZaremba_complete`.
* `grep -nE 'sorry|admit|^axiom|native_decide|:= rfl$|:= trivial'` → only the module-doc prose
  sentence "No `sorry`, `axiom`, ..."; **0 in code**.
* No upstream file edited (verified: `SphericalDiagCut`/`SphericalArmFinal` untouched; `cutArm` was
  already generic, so the B-side instantiation needed no edit).  Scratch checker files removed from the
  server.

## Honest verdict

FRAGMENT (toward FAITHFUL).  The headline `spherical_arm_mono(_strict)` is **NOT** unconditional.
Net progress over `opus-armfinal`: the three structural pieces the prior failing chain named (full
five-field relabel, well-founded `#unmatched` reach measure, B-side cut + two-sided transport) are now
**built and clean-3**, discharging the §8.4 step's *cut case* and supplying the scaffold the opening
case runs on.  The residue narrows to the **opening case alone** — the all-strict opening-witness
existence at a vanishing support (the general two-arm diagonal split + non-equal-angle glue), which is
the design's "THE hard theorem" and matches five prior expert rounds' isolation.  No vacuous coupling
or co-extensive re-wrapper banked.  The chapter frontier after this remains the vertex-link
correspondence (§9–§13).
