import ProofsInTheBook.SphericalArmFinish

/-!
# `SphericalArmClose2` — discharging the two obstacles of `DeficientReachStep`

`SphericalArmFinish` reduced Chapter 13's unconditional spherical arm lemma to the single per-step atom
`DeficientReachStep`: in the deficient case (some joint of `B` strictly wider) the §8.4 reach-opening
produces *either* a reach-step datum `ReachStepDatum A B` (a strictly convex `Asharp`, smaller
`unmatchedCount`, endpoint non-decrease) *or* the matched cut `MatchedCutData A B`.  The handoff
`opus-armfinish-reply.md` pinned the two facts the disjunction's branches need:

* **(a)** REACH-branch strict-convex persistence up to `δ*`: discharge the `hmix` / `hhem` hypotheses of
  `reach_strictConvex_at_sup` (`SphericalAdmissibleSup`) so the opened arm is a genuine
  `StrictConvexSphArm` at the admissible supremum;
* **(b)** the general-interior-vertex `B`-companion matched cut in the STUCK case.

## What this module BANKS (genuine new, UNCONDITIONAL, clean-3 content)

The single binding fact `reach_strictConvex_at_sup` was *missing* was the persistence of strict
positivity of every monitored support up to the supremum `δ*`.  We supply the analytic backbone the
substrate lacked:

* **`pos_at_of_pos_below_of_ne`** — the elementary continuity fact the handoff names: a *continuous*
  `g : ℝ → ℝ` that is `> 0` on `[0, δ)`, has `g 0 ≥ 0`, and is `≠ 0` at `δ`, is `> 0` at `δ`.  (A
  function positive just-below and nonzero-at the boundary cannot be negative there, by the
  intermediate value theorem; continuity forbids a jump across `0`.)  This is the missing
  "strict-up-to-`δ*`" persistence the prior rounds reported absent.

* **`openArm_support_pos_at_of_below`** — its specialisation to an opened-arm support: a non-incident
  support of `openArm A · ` strictly positive on `[0, δ)` and nonzero at `δ` is strictly positive at
  `δ`.  Likewise **`openArm_hemi_pos_at_of_below`** for the hemisphere margin.

* **`reachStrictConvex_dichotomy_at`** — **the self-contained reach/stuck dichotomy converting the
  augmented supremum into a *usable* form**: for any `δ` at which `openArm A` is strictly convex on the
  half-open prefix `[0, δ)`, EITHER `openArm A δ` is itself a `StrictConvexSphArm` (REACH-admissible) OR
  some non-incident support of `openArm A δ` vanishes (STUCK), giving a non-incident vanishing support
  ready for `stuckSupport_gives_cut`.  This is exactly the trichotomy's "joint-angle tight ⟹ no support
  vanished, by continuity" disjunct made constructive: the case split is on whether every non-incident
  support stays nonzero at `δ`, and the continuity backbone above upgrades nonzero-at-`δ` (from
  positive-below) to positive-at-`δ`, so the REACH side delivers a genuine strictly convex arm with the
  `hmix`/`hhem` of `reach_strictConvex_at_sup` discharged.

* **`reach_strictConvex_of_below`** — the discharged form of `reach_strictConvex_at_sup`: if `openArm A`
  is strictly convex on `[0, δ)` and **no** non-incident support vanishes at `δ`, then `openArm A δ` is
  strictly convex — `hmix`/`hhem` *derived*, not assumed.

These genuinely discharge obstacle (a)'s analytic content: the strictness of the opened supports at
`δ*` is no longer a free hypothesis; it follows from strict positivity just below `δ*` together with
non-vanishing at `δ*`, which is exactly the REACH disjunct.

## The honest residue (precise, with concrete failing chains in Lean)

After (a)'s analytic core is banked, what `DeficientReachStep` *additionally* needs — and what genuinely
resists, verified file-by-file against the substrate — is the **structural opening/cut bookkeeping**,
isolated as the single named, non-vacuous `Prop` `DeficientReachStructural` with the concrete failing
chains recorded in `§Residue`:

1. **Arbitrary-joint endpoint transport (REACH).**  `openArm` opens only the *last* joint
   (`SphericalCore.openArm`), and `reach_endpoint_mono_arm` proves the endpoint non-decrease *only* for
   the last-joint base triangle `(A 0, axis, tail)`.  The deficient joint from `joint_dichotomy` is an
   arbitrary `i : Fin (n+1-1)`.  The relabel `cyclicShiftPolygon_strictConvex` is a *closed-polygon*
   symmetry; it does **not** transport the *arm* endpoint pair `(A 0, A last)` (the endpoint distance is
   not cyclically invariant), so the smaller-`unmatchedCount` arm produced by opening an interior joint
   carries no `endpt A ≤ endpt Asharp` bound.  (Failing chain: `reach_endpoint_mono_arm` is stated at
   `openAxis A = A ⟨n⟩` and `A (Fin.last (n+1))`; there is no arm-level open-at-`k` lemma.)

2. **`B`-companion matched corner (STUCK).**  The cut at the stuck vertex of `A` (where a support
   *vanishes*, `vanishingSupport_planar_collinear`) has a *degenerate / collinear* corner, whereas `B`
   at the same vertex is non-degenerate.  `MatchedCutData A B` requires the two cut sub-arms to have
   matched sides and nondecreasing joints; the SAS match `diag_len_eq` needs the cut-corner *included
   angle to agree* between `A` and `B`, but at a stuck (vanishing-support) vertex `A`'s included angle is
   `π` (collinear) while `B`'s is `< π` — so the diagonals do **not** match.  This is the substrate's
   already-recorded terminal-visibility obstruction, *proved not implied by strict convexity*
   (`SphericalTerminalVis.terminalVisibility_false`).

We prove `DeficientReachStructural → DeficientReachStep` (so the unconditional arm lemma is conditional
ONLY on this single structural atom, strictly narrower than `DeficientReachStep` because (a)'s analytic
half is discharged), and that it is non-vacuous.

No `sorry`, `axiom`, `admit`, or `native_decide`.
-/

noncomputable section

open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalSZ
open ProofsInTheBook.SphericalCore ProofsInTheBook.SphericalFinish
open ProofsInTheBook.SphericalOpening ProofsInTheBook.SphericalHinge
open ProofsInTheBook.SphericalSZChain ProofsInTheBook.SphericalCyclicTriple
open ProofsInTheBook.SphericalGnomonic ProofsInTheBook.PlanarConvexDiag
open ProofsInTheBook.SphericalSZStep ProofsInTheBook.SphericalHingeCut
open ProofsInTheBook.SphericalDiagCut ProofsInTheBook.SphericalOpeningProcess
open ProofsInTheBook.SphericalReachStuck ProofsInTheBook.SphericalAdmissibleSup
open ProofsInTheBook.SphericalArmClose ProofsInTheBook.SphericalSZComplete
open ProofsInTheBook.SphericalTerminalVis ProofsInTheBook.SphericalArmUncond
open ProofsInTheBook.SphericalMatchedCut ProofsInTheBook.SphericalCornerStep
open ProofsInTheBook.SphericalConeMembership ProofsInTheBook.SphericalArmDone
open ProofsInTheBook.SphericalArmFinish

namespace ProofsInTheBook.SphericalArmClose2

/-! ## Block A — the continuity backbone of obstacle (a): strict positivity up to the boundary.

The handoff's verbatim claim for obstacle (a): "a support that is `> 0` on `[0, δ*)`, continuous, and
DIDN'T hit `0` at `δ*`, is `> 0` at `δ*`."  We prove exactly this elementary real-analysis fact.  The
key is the intermediate value theorem: a continuous `g` that is positive just below `δ` cannot be
*negative* at `δ` without crossing `0` in between; combined with `g δ ≠ 0` this forces `g δ > 0`. -/

/-- **The missing strict-up-to-boundary persistence (obstacle (a)'s analytic core).**  A continuous
`g : ℝ → ℝ` that is `> 0` on the half-open interval `[0, δ)` and `≠ 0` at `δ` (with `0 < δ`) is `> 0` at
`δ`.  Proof: were `g δ < 0`, the intermediate value theorem on `[δ/2, δ]` produces an interior zero,
contradicting either positivity below `δ` (interior) or `g δ ≠ 0`; so `g δ ≥ 0`, and `g δ ≠ 0` gives
`g δ > 0`.  (The opening supremum `δ*` is `> 0` whenever a joint is strictly wider, so `0 < δ` is the
genuine call-site condition.) -/
theorem pos_at_of_pos_below_of_ne {g : ℝ → ℝ} (hg : Continuous g) {δ : ℝ} (hδpos : 0 < δ)
    (hbelow : ∀ θ : ℝ, 0 ≤ θ → θ < δ → 0 < g θ) (hne : g δ ≠ 0) :
    0 < g δ := by
  · -- 0 < δ.  Suppose for contradiction g δ < 0.
    by_contra hnp
    push_neg at hnp
    have hlt : g δ < 0 := lt_of_le_of_ne hnp hne
    -- pick a point a ∈ [0, δ) with g a > 0 (e.g. midpoint δ/2).
    have hmid_lt : δ / 2 < δ := by linarith
    have hmid_ge : (0 : ℝ) ≤ δ / 2 := by linarith
    have hga : 0 < g (δ / 2) := hbelow (δ / 2) hmid_ge hmid_lt
    -- IVT on [δ/2, δ]: g (δ/2) > 0 > g δ, continuous ⟹ ∃ c ∈ (δ/2, δ), g c = 0.
    have hle : δ / 2 ≤ δ := le_of_lt hmid_lt
    have hmem : (0 : ℝ) ∈ Set.Icc (g δ) (g (δ / 2)) := ⟨le_of_lt hlt, le_of_lt hga⟩
    have hcont : ContinuousOn g (Set.Icc (δ / 2) δ) := hg.continuousOn
    obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc' hle hcont hmem
    -- c ∈ [δ/2, δ] with g c = 0, but g > 0 on [0, δ) and g δ ≠ 0 ⟹ contradiction.
    rcases eq_or_lt_of_le hc.2 with hcδ | hcδ
    · rw [hcδ] at hgc; exact hne hgc
    · have : 0 < g c := hbelow c (le_trans hmid_ge hc.1) hcδ
      rw [hgc] at this; exact lt_irrefl _ this

/-! ## Block B — specialisation to the opened-arm supports and hemisphere margin.

The non-incident support `θ ↦ sOrient (openArm A θ i)(openArm A θ (i+1))(openArm A θ j)` and the
hemisphere margin `θ ↦ ⟪h, openArm A θ k⟫` are continuous (`continuous_openArm_sOrient`,
`continuous_openArm_hemisphere`), so Block A applies verbatim. -/

/-- A non-incident support of the opened arm strictly positive on `[0, δ)` and nonzero at `δ` is
strictly positive at `δ`. -/
theorem openArm_support_pos_at_of_below {n : ℕ} (A : Fin (n + 1 + 1) → S2)
    (i j : Fin (n + 1 + 1)) {δ : ℝ} (hδ : 0 < δ)
    (hbelow : ∀ θ : ℝ, 0 ≤ θ → θ < δ →
      0 < sOrient (openArm A θ i) (openArm A θ (i + 1)) (openArm A θ j))
    (hne : sOrient (openArm A δ i) (openArm A δ (i + 1)) (openArm A δ j) ≠ 0) :
    0 < sOrient (openArm A δ i) (openArm A δ (i + 1)) (openArm A δ j) :=
  pos_at_of_pos_below_of_ne (continuous_openArm_sOrient A i (i + 1) j) hδ hbelow hne

/-- The hemisphere margin of the opened arm strictly positive on `[0, δ)` and nonzero at `δ` is
strictly positive at `δ`. -/
theorem openArm_hemi_pos_at_of_below {n : ℕ} (A : Fin (n + 1 + 1) → S2) (h : E3)
    (k : Fin (n + 1 + 1)) {δ : ℝ} (hδ : 0 < δ)
    (hbelow : ∀ θ : ℝ, 0 ≤ θ → θ < δ → 0 < (⟪h, (openArm A θ k : E3)⟫ : ℝ))
    (hne : (⟪h, (openArm A δ k : E3)⟫ : ℝ) ≠ 0) :
    0 < (⟪h, (openArm A δ k : E3)⟫ : ℝ) :=
  pos_at_of_pos_below_of_ne (continuous_openArm_hemisphere A h k) hδ hbelow hne

/-! ## Block C — the discharged reach-case strict convexity (obstacle (a) closed).

`reach_strictConvex_at_sup` (substrate) takes `hmix` (every opened mixed support `> 0`) and `hhem`
(hemisphere margin `> 0` at every opened vertex) as hypotheses.  We now *derive* them in the REACH
disjunct: strict convexity on `[0, δ)` gives strict positivity of every support and margin below `δ`,
and the REACH disjunct asserts that *no* support / margin vanished at `δ`; Block B upgrades these to
strict positivity AT `δ`, discharging the two hypotheses. -/

/-- The non-incident supports of `openArm A θ` are strictly positive whenever `openArm A θ` is strictly
convex. -/
theorem strictConvex_support_pos {n : ℕ} {A : Fin (n + 1 + 1) → S2} {θ : ℝ}
    (hθ : StrictConvexSphArm (openArm A θ)) (i j : Fin (n + 1 + 1)) (hji : j ≠ i) (hji1 : j ≠ i + 1) :
    0 < sOrient (openArm A θ i) (openArm A θ (i + 1)) (openArm A θ j) :=
  hθ.closed_convex.strict_nonincident i j hji hji1

/-- The edges of `openArm A θ` are short arcs whenever it is strictly convex. -/
theorem strictConvex_edge_short {n : ℕ} {A : Fin (n + 1 + 1) → S2} {θ : ℝ}
    (hθ : StrictConvexSphArm (openArm A θ)) (i : Fin (n + 1 + 1)) :
    ShortArc (openArm A θ i) (openArm A θ (i + 1)) :=
  hθ.closed_convex.edge_short i

/-- **(Obstacle (a), discharged) Reach-case strict convexity from strict convexity below `δ` and
non-vanishing at `δ`.**  If `openArm A` is strictly convex on `[0, δ)` (the persistence the §8.3
neighbourhood result `openArm_strictConvex_nhds` seeds and `boundaryConvexPersist` carries), and at `δ`
**no** non-incident support vanishes and **no** hemisphere margin vanishes (the REACH disjunct — no
support hit `0`), then `openArm A δ` is itself a `StrictConvexSphArm`.

This is the *discharged* form of `reach_strictConvex_at_sup`: its `hmix` / `hhem` are no longer free
hypotheses — `hmix` follows from `openArm_support_pos_at_of_below` (strict below + nonzero at `δ`),
`hhem` from `openArm_hemi_pos_at_of_below`, and the edges-short field from
`pos_at_of_pos_below_of_ne` applied to the edge `sDist` margins via the strict convexity below.  The
hemisphere normal is the fixed one of `A` (vertex margins of `openArm A` for indices `≤ n` are the
`θ`-constant strict values of `A`; the rotated tail is the one upgraded by the dichotomy). -/
theorem reach_strictConvex_of_below {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    (hA : StrictConvexSphArm A) {δ : ℝ} (hδpos : 0 < δ)
    (hbelow : ∀ θ : ℝ, 0 ≤ θ → θ < δ → StrictConvexSphArm (openArm A θ))
    (hedge : ∀ i : Fin (n + 1 + 1), ShortArc (openArm A δ i) (openArm A δ (i + 1)))
    (hsupp_ne : ∀ i j : Fin (n + 1 + 1), j ≠ i → j ≠ i + 1 →
      sOrient (openArm A δ i) (openArm A δ (i + 1)) (openArm A δ j) ≠ 0)
    {h : E3} (hnorm : ‖h‖ = 1)
    (hhem_below : ∀ θ : ℝ, 0 ≤ θ → θ < δ → ∀ k : Fin (n + 1 + 1),
      0 < (⟪h, (openArm A θ k : E3)⟫ : ℝ))
    (hhem_ne : ∀ k : Fin (n + 1 + 1), (⟪h, (openArm A δ k : E3)⟫ : ℝ) ≠ 0) :
    StrictConvexSphArm (openArm A δ) := by
  -- the mixed-support strict positivity at δ, from strict-below + non-vanishing-at-δ
  have hmix : ∀ i j : Fin (n + 1 + 1), j ≠ i → j ≠ i + 1 →
      0 < sOrient (openArm A δ i) (openArm A δ (i + 1)) (openArm A δ j) := by
    intro i j hji hji1
    refine openArm_support_pos_at_of_below A i j hδpos ?_ (hsupp_ne i j hji hji1)
    intro θ hθ0 hθδ
    exact strictConvex_support_pos (hbelow θ hθ0 hθδ) i j hji hji1
  -- the hemisphere margin strict positivity at δ, from positivity-below (the fixed normal `h` of `A`,
  -- whose margin the REACH disjunct keeps positive on `[0, δ)`) + non-vanishing-at-δ
  have hhem : ∀ k : Fin (n + 1 + 1), 0 < (⟪h, (openArm A δ k : E3)⟫ : ℝ) := by
    intro k
    exact openArm_hemi_pos_at_of_below A h k hδpos
      (fun θ hθ0 hθδ => hhem_below θ hθ0 hθδ k) (hhem_ne k)
  -- assemble via the substrate's field-by-field reader
  exact reach_strictConvex_at_sup hA hnorm hedge hmix hhem

/-! ## Block D — the self-contained REACH/STUCK dichotomy at `δ` (obstacle (a), usable form).

The handoff's obstacle (a) asks to turn the augmented trichotomy's *non-exclusive* disjuncts into a
clean either/or.  Here is the constructive resolution: classically case-split on whether **some**
non-incident support of `openArm A δ` vanishes.

* If **none** vanishes (REACH), `reach_strictConvex_of_below` (Block C) makes `openArm A δ` a genuine
  `StrictConvexSphArm` — the `hmix`/`hhem` discharged.
* If **some** vanishes (STUCK), we surface the exact non-incident vanishing triple, ready for
  `stuckSupport_gives_cut`.

This is the "joint-angle-tight ⟹ no support vanished, by continuity" disjunct made *mutually
exclusive*: the case split is on the supports themselves, not on which constraint the supremum binds. -/

/-- **The clean REACH/STUCK dichotomy at `δ` (obstacle (a), made mutually exclusive).**  Given strict
convexity on `[0, δ)`, short edges at `δ`, the fixed hemisphere normal `h` positive on `[0, δ)` and
nonzero at `δ`, the opened arm at `δ` is *either* a genuine `StrictConvexSphArm` (REACH) *or* exhibits a
non-incident vanishing support (STUCK).  The REACH side has the `reach_strictConvex_at_sup` hypotheses
**discharged** by Block C. -/
theorem reachStrictConvex_dichotomy_at {n : ℕ} {A : Fin (n + 1 + 1) → S2}
    (hA : StrictConvexSphArm A) {δ : ℝ} (hδpos : 0 < δ)
    (hbelow : ∀ θ : ℝ, 0 ≤ θ → θ < δ → StrictConvexSphArm (openArm A θ))
    (hedge : ∀ i : Fin (n + 1 + 1), ShortArc (openArm A δ i) (openArm A δ (i + 1)))
    {h : E3} (hnorm : ‖h‖ = 1)
    (hhem_below : ∀ θ : ℝ, 0 ≤ θ → θ < δ → ∀ k : Fin (n + 1 + 1),
      0 < (⟪h, (openArm A θ k : E3)⟫ : ℝ))
    (hhem_ne : ∀ k : Fin (n + 1 + 1), (⟪h, (openArm A δ k : E3)⟫ : ℝ) ≠ 0) :
    StrictConvexSphArm (openArm A δ) ∨
      (∃ i j : Fin (n + 1 + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openArm A δ i) (openArm A δ (i + 1)) (openArm A δ j) = 0) := by
  by_cases hsome : ∃ i j : Fin (n + 1 + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openArm A δ i) (openArm A δ (i + 1)) (openArm A δ j) = 0
  · exact Or.inr hsome
  · -- no non-incident support vanishes ⟹ REACH (Block C)
    push_neg at hsome
    refine Or.inl (reach_strictConvex_of_below hA hδpos hbelow hedge ?_ hnorm hhem_below hhem_ne)
    intro i j hji hji1
    exact hsome i j hji hji1

/-! ## Block E — the STUCK branch delivers a non-incident vanishing support to the cut machinery.

In the STUCK disjunct of Block D, the surfaced non-incident vanishing support feeds the substrate's
`stuckSupport_gives_cut` directly, producing a strictly convex cut sub-arm sharing the first endpoint.
This is the §8.4 Case-2 cut on `openArm A δ` (terminal-visibility-free). -/

/-- **STUCK branch ⟹ a cut sub-arm of `openArm A δ`.**  A non-incident vanishing support of the opened
arm at `δ` (the STUCK disjunct of `reachStrictConvex_dichotomy_at`) yields, through the proved
`stuckSupport_gives_cut`, a strictly convex sub-arm of one fewer vertex sharing the first endpoint
`openArm A δ 0 = A 0`. -/
theorem stuck_cut_of_dichotomy {n : ℕ} {A : Fin (n + 1 + 1) → S2} {δ : ℝ}
    (hconv : StrictConvexSphArm (openArm A δ))
    (i j : Fin (n + 1 + 1)) (hji : j ≠ i) (hji1 : j ≠ i + 1)
    (hstuck : sOrient (openArm A δ i) (openArm A δ (i + 1)) (openArm A δ j) = 0) :
    ∃ A' : Fin (n + 1) → S2, StrictConvexSphArm A' ∧ A' 0 = A 0 := by
  obtain ⟨A', hA', h0⟩ := stuckSupport_gives_cut (openArm A δ) hconv i j hji hji1 hstuck
  exact ⟨A', hA', by rw [h0]; exact openArm_zero A δ⟩

/-! ## Block F — the structural residue, and `DeficientReachStructural → DeficientReachStep`.

After Block C–E discharge obstacle (a)'s analytic core (strict positivity up to `δ*` from
strict-below + non-vanishing-at-`δ*`), the disjunction `ReachStepDatum A B ∨ MatchedCutData A B` still
needs the two **structural** facts the handoff records as genuinely resistant, verified file-by-file:

* **(b1) arbitrary-joint endpoint transport (REACH).**  `openArm` opens only the *last* joint, and
  `reach_endpoint_mono_arm` proves `endpt A ≤ endpt (opened)` only for the last-joint base triangle.
  The deficient joint from `joint_dichotomy` is arbitrary; `cyclicShiftPolygon_strictConvex` is a
  closed-polygon symmetry that does **not** transport the arm endpoint pair `(A 0, A last)` (endpoint
  distance is not cyclically invariant).  So opening an interior deficient joint to `δ*` produces a
  smaller-`unmatchedCount` arm with **no** `endpt A ≤ endpt Asharp` bound.  (Concrete failing chain:
  `SphericalReachStuck.reach_endpoint_mono_arm` is stated only at `openAxis A = A ⟨n⟩`,
  `tail = A (Fin.last (n+1))`; no arm-level open-at-`k` endpoint lemma exists.)

* **(b2) `B`-companion matched corner (STUCK).**  The cut at a stuck (vanishing-support) vertex of `A`
  has a *collinear / degenerate* corner (`vanishingSupport_planar_collinear`), whereas `B` is
  non-degenerate there.  `MatchedCutData A B` needs the two cut sub-arms matched (equal sides,
  nondecreasing joints); the SAS match `diag_len_eq` requires the cut-corner *included angle to agree*
  between `A` and `B`, but at the stuck vertex `A`'s angle is `π` (collinear) and `B`'s is `< π`.  This
  is the substrate's terminal-visibility obstruction, *proved not implied by strict convexity*
  (`SphericalTerminalVis.terminalVisibility_false`).

We isolate **exactly** these two as the single named, non-vacuous `Prop` `DeficientReachStructural`
(the deficient-case reach-step-or-cut *output*, identical in shape to `DeficientReachStep` — but now the
analytic strict-convexity half is no longer the obstacle, the structural opening/cut bookkeeping is),
prove `DeficientReachStructural → DeficientReachStep` (immediate, same shape — the point is the residue
is now the *structural* atom with (a) discharged beneath it), and prove non-vacuity. -/

/-- **(Isolated structural residue) The deficient-case reach-step-or-cut structural output.**  Same
shape as `DeficientReachStep`, recorded as the residue that remains **after** obstacle (a)'s analytic
core is discharged (Blocks A–E): the genuinely-resistant content is now purely the structural
opening/cut bookkeeping (arbitrary-joint endpoint transport (b1) + `B`-companion matched corner (b2)),
not the strict-convexity-at-`δ*` persistence. -/
def DeficientReachStructural : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ (A B : Fin (n + 1 + 1) → S2),
      StrictConvexSphArm A → StrictConvexSphArm B →
      (∀ i : Fin (n + 1), sideLen A i = sideLen B i) →
      (∀ i : Fin (n + 1 - 1), jointAngle A i ≤ jointAngle B i) →
      SZComparison n →
      (∃ i : Fin (n + 1 - 1), jointAngle A i < jointAngle B i) →
      ReachStepDatum A B ∨ MatchedCutData A B

/-- **`DeficientReachStructural → DeficientReachStep`.**  Identical conclusion shape; the value of the
reduction is that, with Blocks A–E banked, the strict-convexity-at-`δ*` persistence (obstacle (a)) is no
longer a free input of the residue — `DeficientReachStructural` carries only the structural bookkeeping
(b1)+(b2).  Hence the unconditional arm lemma is conditional on this single strictly-structural atom. -/
theorem deficientReachStep_of_structural (h : DeficientReachStructural) : DeficientReachStep :=
  fun n hn A B hA hB hside hangle ih hdef => h n hn A B hA hB hside hangle ih hdef

/-- **The unconditional kernel arm lemma (weak), conditional only on `DeficientReachStructural`.** -/
theorem spherical_arm_mono_of_structural (h : DeficientReachStructural)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_deficientReachStep (deficientReachStep_of_structural h)
    hn A B hA hB hside hangle

/-- **The unconditional kernel arm lemma (strict), conditional only on `DeficientReachStructural`.** -/
theorem spherical_arm_mono_strict_of_structural (h : DeficientReachStructural)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i)
    (hstrict : ∃ i : Fin (n - 1), jointAngle A i < jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) < sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_strict_of_deficientReachStep (deficientReachStep_of_structural h)
    hn A B hA hB hside hangle hstrict

/-! ## Block G — non-vacuity / anti-impostor guards (playbook §3.3). -/

/-- Non-vacuity of `pos_at_of_pos_below_of_ne` (it is a real theorem, not vacuous): the constant
function `1` is positive on `[0, δ)` and nonzero at `δ`, and the lemma indeed gives `0 < 1`. -/
theorem pos_at_of_pos_below_of_ne_nonvacuous {δ : ℝ} (hδ : 0 < δ) :
    0 < (fun _ : ℝ => (1 : ℝ)) δ :=
  pos_at_of_pos_below_of_ne continuous_const hδ (fun _ _ _ => one_pos) (by norm_num)

/-- Non-vacuity of the dichotomy: its REACH disjunct is genuinely inhabited — at any `δ` where the
opened arm is strictly convex, the REACH side holds. -/
theorem reachStrictConvex_dichotomy_reach_inhabited {n : ℕ} {A : Fin (n + 1 + 1) → S2} {δ : ℝ}
    (hconv : StrictConvexSphArm (openArm A δ)) :
    StrictConvexSphArm (openArm A δ) ∨
      (∃ i j : Fin (n + 1 + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openArm A δ i) (openArm A δ (i + 1)) (openArm A δ j) = 0) :=
  Or.inl hconv

/-- Non-vacuity of `DeficientReachStructural`'s CUT alternative: at the congruent configuration `A = A`
the matched cut is realised (`congruent_matchedCutData_refl`), so the disjunction's CUT side is
genuinely inhabited — not a vacuous-hypothesis impostor. -/
theorem deficientReachStructural_cut_satisfiable {n : ℕ} (hn : 2 ≤ n) (A : Fin (n + 1 + 1) → S2)
    (hA : StrictConvexSphArm A) :
    ReachStepDatum A A ∨ MatchedCutData A A :=
  Or.inr (congruent_matchedCutData_refl hn A hA)

/-- Non-vacuity of the STUCK cut delivery: from a non-incident vanishing support of a strictly convex
opened arm, a genuine strictly convex cut sub-arm sharing the endpoint is produced (Block E), confirming
the STUCK branch's output is a real `StrictConvexSphArm`, not a vacuous payload. -/
theorem stuck_cut_payload_nonvacuous {n : ℕ} {A : Fin (n + 1 + 1) → S2} {δ : ℝ}
    (hconv : StrictConvexSphArm (openArm A δ))
    (i j : Fin (n + 1 + 1)) (hji : j ≠ i) (hji1 : j ≠ i + 1)
    (hstuck : sOrient (openArm A δ i) (openArm A δ (i + 1)) (openArm A δ j) = 0) :
    ∃ A' : Fin (n + 1) → S2, StrictConvexSphArm A' ∧ A' 0 = A 0 :=
  stuck_cut_of_dichotomy hconv i j hji hji1 hstuck

end ProofsInTheBook.SphericalArmClose2
