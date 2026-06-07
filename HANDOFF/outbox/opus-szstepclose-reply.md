# Ch13 §8.4 SZ opening step `SZOpeningStep` — Opus reply (StepClose round)

## Status: PARTIAL — CUT-branch substrate (ear API + diagonal inequality) BANKED clean-3; `SZOpeningStep` reduced to the single irreducible core `SZStepCore`, with the OPEN-branch obstruction re-verified GENUINE (not premature).

Branch `main`, **no commits** (as instructed).  New file `ProofsInTheBook/SphericalSZStepClose.lean`
(350 lines) + 1 import line in `ProofsInTheBook.lean`.  Verified on `uisai1`.

## Verification

* **RC**: `lake env lean ProofsInTheBook/SphericalSZStepClose.lean` → RC=0, **0 errors, 0 warnings**.
* **Full build**: `lake build` → **Build completed successfully (8648 jobs)**, 0 errors
  (`SphericalSZStepClose` wired into `ProofsInTheBook.lean` after `SphericalSZInduction`).
* **`#print axioms` — clean-3 ({propext, Classical.choice, Quot.sound}, no sorryAx/native_decide):**
  - `spherical_arm_mono_of_core`  — clean-3 ✓  (the headline arm lemma weak half, conditional on the core)
  - `ear_chord_le_of_Main`        — clean-3 ✓
  - `cut_diag_le`                 — clean-3 ✓
  - `intervalArm_sideLen` / `intervalArm_jointAngle` — clean-3 ✓
  - `szOpeningStep_of_core`       — clean-3 ✓
* No `sorry` / `axiom` / `admit` / `native_decide` (grep clean).

## What was BANKED (genuinely new, unconditional, clean-3) — the design §4 CUT-branch substrate

The substrate had only the **last-vertex-drop** `cutArm` (`SphericalDiagCut`) and the
**first-vertex-drop** `frontCut` (`SphericalMatchedCut`) as sub-arm constructors; neither is an
arbitrary interval.  This module builds the design's missing `earA = A[i+1..j]` constructor:

1. **The interval-arm (ear) API** `intervalArm A a m hb : Fin (m+1) → S2` — the contiguous sub-tuple
   `j ↦ A (a+j)` — with:
   * `intervalArm_zero` / `intervalArm_last` / `intervalArm_endpt` (endpoint = chord
     `sDist (A a)(A (a+m))`);
   * `intervalArm_sideLen` (ear side `i` = parent side `a+i`), `intervalArm_jointAngle`
     (ear *interior* joint `i` = parent interior joint `a+i` — a contiguous sub-tuple introduces **no**
     new interior joint, only the two ear endpoints are "new" and they are not joints);
   * `intervalArm_sameSides` / `intervalArm_jointLe` — `SameSides` / `JointLe` of the parent restrict
     to the ear **verbatim**.
2. **The ear endpoint comparison** `ear_chord_le_of_Main`: `Main m` (the level-`m` strengthened
   invariant of `SphericalSZInduction`) applied to the matched ears gives the design §4 chord bound
   `hEar : sDist (A a)(A (a+m)) ≤ sDist (B a)(B (a+m))`.
3. **The cut diagonal inequality** `cut_diag_le` (= `SphericalSZInduction.diag_le_of_flat_ear` restated
   for the cut corner `p=A i, mid=A (i+1), q=A j`): folded-flat betweenness + ear comparison + equal
   first side ⟹ `sDist (A i)(A j) ≤ sDist (B i)(B j)` via the spherical reverse triangle inequality.

## The single isolated residue: `SZStepCore` (= `SZOpeningStep`, with §1–§4 banked beneath it)

`SZStepCore` is the per-level SZ opening/cut endpoint output — **identical in shape** to
`SZOpeningStep` (and `szOpeningStep_of_core : SZStepCore → SZOpeningStep` is the immediate forwarding;
the value is that the ear API + diagonal inequality are now banked substrate, not free inputs).  It is
genuinely load-bearing: `SphericalSZInduction`'s lex `(n, deficitCount)` `WellFounded` recursion
*derives* `endpt A ≤ endpt B` from it by threading the dimension-drop and deficit-drop IHs.  It
packages the two pieces that GENUINELY exceed the substrate, each with a concrete failing chain:

* **(C) CUT body/splice glue.**  After `hEar` and `cut_diag_le` (banked), the CUT rule still needs
  `splice_transport_of_diag_le`: the spliced body `A[0..i] ++ A[j..n]` glued to `endpt A ≤ endpt B`.
  Failing chain: the body's new diagonal side `A i → A j` is matched to `B`'s only by the
  **inequality** `cut_diag_le`, *not* by spherical SAS equality — `SphericalSZChain.diag_len_eq` needs
  the *included angle to agree*, which a folded-flat `A` corner (angle `π`) does not satisfy against
  `B`'s bent corner (angle `< π`); this is exactly `SphericalTerminalVis.terminalVisibility_false`.
  So the body is not a matched-SAS recursion; the genuine glue needs the body sub-arm convexity from
  the folded-flat Gram signs the substrate carries only as hypotheses (`SZStuckData.signA/signC`).

* **(O) OPEN interior reach/stuck production.**  The design §5–§7 OPEN rule opens the deficient joint
  by the interior `openTail` to `δ*`, getting REACH / STUCK with `endpt A ≤ endpt (openTail …)`.

## IMPORTANT FINDING: the directive's CORRECTED "relabel-to-last" does NOT close the OPEN branch — the obstruction is GENUINE, not premature

I verified the directive's proposed fix carefully against the geometry and the entire substrate.  The
claim is: relabel via `cyclicShiftPolygon_strictConvex` so the deficient joint `k` becomes the LAST
interior joint, apply the last-joint `openArm` + `augmented_reachOrStuck_at_sup`, then relabel back.
This **cannot** transport the endpoint bound, for a real geometric reason:

* The last-joint `openArm` rotates the **tail vertex** (index `n+1`), which is *one of the two arm
  endpoints* `A (last)`.  That is precisely why `reach_endpoint_mono_arm` gives a genuine
  `endpt A ≤ endpt (openArm …)`: it is moving an endpoint.
* The cyclic shift `σ_r : i ↦ i+r` is a **closed-polygon** symmetry.  The arm endpoint is the *single*
  chord `(A 0, A n)` (the two vertices adjacent across the closing edge).  After shifting by `r`, the
  shifted arm's endpoint chord is `(A r, A (r-1))` — a **different** chord of the original polygon for
  any `r ≠ 0`.  The spherical arm endpoint distance is **not cyclically invariant**, so the last-joint
  endpoint bound on the *relabelled* arm says nothing about the *original* `endpt A ≤ endpt B`.
* Independently, the interior `openTail` disturbs **two** adjacent joints (`r = k-1` and `r = k`,
  mechanized as `SphericalSZInduction.openTail_preserves_joint_offaxis`), so the design §6 single-
  `erase` deficit-decrease is unavailable (this was already flagged in the prior `SZInduction` round).

This is the same obstruction four prior expert rounds + the substrate independently isolated and
recorded by `grep` against the whole tree: `SphericalArmFinal` item 1 ("Relabelling `k` to the last
position needs a `StrictConvexSphArm`-preserving relabel that ALSO preserves the arm
endpoint/side/joint indexing — no such lemma exists"), `SphericalArmClose2` §F (b1)
("`cyclicShiftPolygon_strictConvex` does not transport the *arm* endpoint pair `(A 0, A last)`"),
`SphericalArmFinish:82`.  Closing it requires either (i) re-deriving the continuity / IVT / admissible-
supremum reach/stuck trichotomy from scratch for the interior `openTail` operation (a multi-thousand-
line analytic re-build — the substrate's entire `SphericalAdmissibleSup`/`SphericalArmClose2`
apparatus is last-joint only), or (ii) proving arm-endpoint cyclic-invariance, which is FALSE.

## Honest scoping verdict

The headline "fully UNCONDITIONAL `spherical_arm_mono/_strict`" is **not reachable** from this
substrate via the directive's design as written: the OPEN branch rests on interior-opening analysis
genuinely absent from the substrate, and the relabel-back endpoint transport the corrected approach
relies on is geometrically false (arm endpoint not cyclically invariant).  What IS delivered and banked
clean-3: the design §4 CUT-branch substrate that was the named missing piece —the **interval-arm (ear)
convexity-restriction API** (sides/joints/endpoint + `SameSides`/`JointLe` restriction), the **ear
endpoint comparison from `Main m`**, and the **cut diagonal inequality** — with `SZOpeningStep` reduced
to the single non-vacuous core `SZStepCore` carrying only the two irreducible pieces (C)+(O), each with
a concrete failing chain.  This strictly enlarges the substrate beneath the SZ opening atom (the ear
sub-arm constructor did not exist), and the whole arm lemma remains conditional on the single per-step
`SZStepCore` ≡ `SZOpeningStep`.

Remaining frontier unchanged: the SZ opening atom (= `SZOpeningStep` / `DeficientReachStep` /
`MatchedCutCornerStep` / `OpeningStructuralAssembly` / `StuckWitnessExists`, all co-extensive), whose
two genuine geometric obstructions are (C) the folded-flat body/splice convexity and (O) the interior-
opening reach/stuck production with the non-cyclically-invariant arm endpoint.

Files touched: `ProofsInTheBook/SphericalSZStepClose.lean` (new, 350 lines),
`ProofsInTheBook.lean` (+1 import).
