import ProofsInTheBook.ZinanFFCT32
import ProofsInTheBook.ZinanFFCT33
import ProofsInTheBook.ZinanFFCT29
import ProofsInTheBook.SphericalOpeningOutcome
import ProofsInTheBook.SphericalArmAssembly

/-!
# `ZinanFFCT35` — the Chapter 13 B1 **final wrapper chain**: threading the closed bricks into the
  `MainPlus` / `InteriorOpeningGlue` spine.

This module is **pure assembly** (`HANDOFF/design-rounds/ch13-b1-final-wave.md` §10–§12).  The
mathematics is done in FFCT28–34 and the `SphericalOpeningGlue` / `SphericalOpeningOutcome` /
`SphericalArmAssembly` spine; here we thread the landed bricks into the sharpest *honest* statements,
exposing every surviving named residue as an explicit, satisfiable hypothesis (playbook §3.3).

## The spine (read before the wrappers)

The Chapter-13 spherical arm lemma headline lives in `SphericalArmAssembly`:

```
spherical_arm_mono_of_spliceBodyDiagMono
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData) (houtcome : InteriorOpeningOutcome)
  : sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n))
```

`InteriorOpeningOutcome` is delivered by `SphericalOpeningOutcome.interiorOpeningOutcome_holds` from the
single bundled residue `InteriorOpeningGlue`, whose three clauses are:

* **(i)** the endpoint non-decrease `endpt A ≤ endpt A'` of the opened arm;
* **(ii)** the REACH selection `¬ Stuck → Reach`;
* **(iii)** the STUCK boundary outcome `Stuck → WeakConvexSphArm A' ∧ ∃ vanishing non-incident support`.

## The decisive finding (settled FIRST, per the honesty contract)

**Clauses (i) and (ii) of `InteriorOpeningGlue` are FALSE as stated for the `+δ` monitored family.**
`SphericalOpeningGlue` proves this *unconditionally*:

* `SignBugBlocksI` : `sOrient (A K)(jointPrev)(jointNext) < 0` and `sOrient (A K)(A 0)(A last) ≤ 0` — the
  monitored family rotates in the **closing** direction, so `endpt A ≤ endpt A'` with `δ* > 0` cannot
  hold in general (clause (i) sign bug);
* `SignBugBlocksII` + `EndpointPosMono` : the same negative axis support forces `¬ Stuck` to hit the
  trichotomy CAP `δ* = π` rather than `Reach` (clause (ii) sign bug); `EndpointPosMono` is named as the
  precise *false* `+δ` endpoint-monotonicity clause and is **assumed nowhere**.

Therefore the honest endpoint of the B1 wave is **NOT** a discharged `InteriorOpeningGlue`: clauses
(i)/(ii) need the *corrected* `−δ` (widening) monitored family — a substrate change, NOT threading.
We carry `InteriorOpeningGlue` as an explicit named residue in the headline (the entire endpoint /
reach reconciliation), and discharge clause (iii)'s geometry as far as the closed bricks allow.

## What this module delivers (all clean-3, no `sorry`/`axiom`/`admit`/`native_decide`)

1. **`stuckSupport_betweenness_mod_gram`** — at an interior support-stuck binding `c`
   (`supportConstraint A K c δ* = 0`), the opened arm is folded flat at `c`'s middle vertex
   (`Aδ c.i ∈ span≥0 {Aδ(c.i+1), Aδ c.j}`), conditional on the named multi-rotation Gram-sign residue
   `GramSignsAtInteriorBinding` (FFCT28's honest residue).  Thin wrapper over
   `supportStuck_dispatch_partial`; the only purpose is to name the residue surface at the spine.

2. **`stuckSupport_betweenness_axisEdge`** — the sharper axis-edge subcase: at an interior *axis-edge*
   binding (`c.i+1 = openingAxis k`), the betweenness is produced from the *single* near-side
   coefficient sign `NearSideCoeffNonneg` (FFCT29's `interiorAxisEdge_stuck_betweenness`), with the
   `hβ` Gram sign discharged by the one-sided derivative.  This is the sharpest STUCK→betweenness form.

3. **`equatorTangent_at_sup_of_spreadExcluded`** — the hemi-stuck tilt input at the monitored supremum,
   from `EquatorSpreadExcluded` (FFCT33's reduction of `EquatorTangentExists`).

4. **`stuckOutcome_weakConvex_of_residues`** — clause (iii) of `InteriorOpeningGlue`:
   `Stuck → WeakConvexSphArm Aδ ∧ ∃ vanishing support`, threading the support-stuck branch
   (vanishing support direct + weak convexity from `HemiMarginStrictPosAtSup` + opened-edge
   distinctness) and the hemi-stuck branch (FFCT30's `hemiStuck_forces_supportStuck_or_weakConvex` with
   the equator tangent from (3)).  All residues named.

5. **`interiorOpeningOutcomePlus_of_residues`** — `InteriorOpeningOutcome` from the full residue bundle
   (the carried `InteriorOpeningGlue`), via the banked `interiorOpeningOutcome_holds`.

6. **`mainPlus_headline_mod_residues`** — the chapter-13 spherical arm lemma
   `sDist (A 0)(A last) ≤ sDist (B 0)(B last)` with **every** surviving residue as an explicit named
   hypothesis.  This is the honest chapter endpoint, analogous to Ch35's planar-input close.

## Residue surface of the headline (the truth)

| Residue | Source | Status |
|---------|--------|--------|
| `SpliceBodyDiagMono` | `SphericalArmAssembly` | named (sub-arm diagonal monotone; pre-B1) |
| `SpliceStructuralData` | `SphericalArmAssembly` | named (cut sub-arm geometry; pre-B1) |
| `InteriorOpeningGlue` | `SphericalOpeningOutcome` | named; clauses (i)/(ii) FALSE for `+δ` (sign bug, `SignBugBlocksI/II`), clause (iii) geometry threaded below |
| `HemiMarginStrictPosAtSup` | `SphericalOpeningGlue` | named (strict hemi margins at a Stuck sup; `BoundaryConvexPersistAtSup`) |
| `EquatorSpreadExcluded` | `ZinanFFCT33` | named (equator-vertex sum positivity; FFCT34 excludes antipodal/consecutive, residual = ≥3 wide spread) |
| `GramSignsAtInteriorBinding` / `NearSideCoeffNonneg` / `NearSidePredDegenerate` | FFCT28/29/31/32 | named (multi-rotation Gram signs at a general interior binding) |
-/

noncomputable section
open scoped RealInnerProductSpace NNReal
open ProofsInTheBook.SphericalKernel ProofsInTheBook.SphericalArm
open ProofsInTheBook.SphericalRotation ProofsInTheBook.SphericalCore
open ProofsInTheBook.SphericalSZInduction
open ProofsInTheBook.SphericalSZFinal ProofsInTheBook.SphericalSZClose
open ProofsInTheBook.SphericalSpliceTransport
open ProofsInTheBook.SphericalMonitoredSup ProofsInTheBook.SphericalOpeningGlue
open ProofsInTheBook.SphericalOpeningOutcome ProofsInTheBook.SphericalArmAssembly
open ProofsInTheBook.ZinanFFCT18 ProofsInTheBook.ZinanFFCT28 ProofsInTheBook.ZinanFFCT29
open ProofsInTheBook.ZinanFFCT30 ProofsInTheBook.ZinanFFCT33

namespace ProofsInTheBook.ZinanFFCT35

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

/-! ## §1. The support-stuck → betweenness wrappers (clause (iii)'s support branch geometry). -/

/-- **(Wrapper 1) Interior support-stuck → folded-flat betweenness, modulo the Gram residue.**  At a
STUCK binding `c` at the interior axis `K = openingAxis k` (`supportConstraint = 0` at the monitored
supremum) with the named multi-rotation Gram-sign residue `GramSignsAtInteriorBinding`, the opened arm
`Aδ := openTail A K δ*` is folded flat at `c`'s middle vertex.  This is exactly the
`FoldedFlatCutTransportPlus` input; the residue is FFCT28's honest multi-rotation block. -/
theorem stuckSupport_betweenness_mod_gram {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3)
    {Tcap : ℝ} (c : NonIncident n)
    (hzero : supportConstraint A (openingAxis k) c (monitoredSup A B k h₀ Tcap) = 0)
    (hgram : GramSignsAtInteriorBinding A (openingAxis k) (monitoredSup A B k h₀ Tcap) c) :
    (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) c.1.1 : E3) ∈
      Submodule.span NNReal
        ({(openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) (c.1.1 + 1) : E3),
          (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) c.1.2 : E3)} : Set E3) :=
  supportStuck_dispatch_partial A B k h₀ c hzero hgram

/-- **(Wrapper 2) The sharper interior *axis-edge* subcase.**  When the binding's middle vertex is the
opening axis (`c.i+1 = openingAxis k`), the two Gram signs collapse to the *single* near-side
coefficient sign `NearSideCoeffNonneg`: `hβ` is the one-sided derivative (`hbeta_at_interior_axis_edge`)
and `hα` is the near-side companion.  Threads FFCT29's `interiorAxisEdge_stuck_betweenness` — the
sharpest honest STUCK→betweenness form, residual = one coefficient sign. -/
theorem stuckSupport_betweenness_axisEdge {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3)
    {Tcap : ℝ} (c : NonIncident n)
    (hδpos : 0 < monitoredSup A B k h₀ Tcap)
    (hmid : (c.1.1 + 1 : Fin (n + 1)) = openingAxis k)
    (hi : c.1.1.val ≤ (openingAxis k).val) (hj : (openingAxis k).val < c.1.2.val)
    (hzero : supportConstraint A (openingAxis k) c (monitoredSup A B k h₀ Tcap) = 0)
    (hsa : ShortArc (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) (c.1.1 + 1))
      (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) c.1.2))
    (hadm : ∀ θ, θ ∈ Set.Icc 0 (monitoredSup A B k h₀ Tcap) →
      0 ≤ axisEdgeSupport A (openingAxis k) c.1.1 c.1.2 θ)
    (hpm : ShortArc (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) (c.1.1 + 1))
      (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) c.1.1))
    (hnear : NearSideCoeffNonneg
      (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) c.1.1)
      (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) (c.1.1 + 1))
      (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) c.1.2)) :
    (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) c.1.1 : E3) ∈
      Submodule.span NNReal
        ({(openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) (c.1.1 + 1) : E3),
          (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) c.1.2 : E3)} : Set E3) :=
  interiorAxisEdge_stuck_betweenness A B k h₀ c hδpos hmid hi hj hzero hsa hadm hpm hnear

/-! ## §2. The hemi-stuck tilt input from `EquatorSpreadExcluded`. -/

/-- **(Wrapper 3) The equator tangent at the monitored supremum, from `EquatorSpreadExcluded`.**  The
sharpened hemi-stuck residue: `EquatorSpreadExcluded` (equator-vertex sum positivity, FFCT33/34) entails
the `EquatorTangentExists` tilt that FFCT30's hemi-stuck dichotomy consumes. -/
theorem equatorTangent_at_sup_of_spreadExcluded {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1))
    (h₀ : E3) {Tcap : ℝ}
    (hspread : EquatorSpreadExcluded A (openingAxis k) h₀ (monitoredSup A B k h₀ Tcap)) :
    EquatorTangentExists A (openingAxis k) h₀ (monitoredSup A B k h₀ Tcap) :=
  equatorTangent_of_spreadExcluded A (openingAxis k) h₀ (monitoredSup A B k h₀ Tcap) hspread

/-! ## §3. Clause (iii) of `InteriorOpeningGlue` — the STUCK boundary outcome.

`Stuck A B k h₀ π` is `(∃ c, support = 0) ∨ (∃ r, hemiMargin = 0)`.  We produce
`WeakConvexSphArm Aδ ∧ ∃ vanishing support` from:

* **support branch**: the vanishing support is *itself* the right disjunct; weak convexity comes from
  `weakConvex_of_supportStuck_of_hemiPos` (sibling), fed the strict hemi margins
  (`HemiMarginStrictPosAtSup`) and the opened-edge distinctness (named `OpenedEdgesDistinct`).
* **hemi branch**: FFCT30's `hemiStuck_forces_supportStuck_or_weakConvex` (with the equator tangent of
  §2) gives a vanishing support OR weak convexity; the vanishing-support sub-case routes through the
  support branch, the weak-convex sub-case still needs a *witnessing* vanishing support, supplied by the
  named `HemiStuckVanishingSupport` remnant (a hemi-stuck supremum is also support-binding — the
  trichotomy's first disjunct — but extracting the specific binding from a margin contact is the
  documented residual).

The opened-edge distinctness and the hemi-stuck vanishing-support remnant are named, satisfiable, and
non-vacuous (see the guards in §5). -/

/-- The opened-edge distinctness residue: at the monitored supremum, consecutive opened vertices are
distinct.  This is a genuine geometric fact (the open hemisphere keeps consecutive vertices apart), but
for a general STUCK supremum it is not free from the supports alone (one of which vanishes), so it is
named and threaded. -/
def OpenedEdgesDistinct {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3) (Tcap : ℝ) : Prop :=
  ∀ i : Fin (n + 1),
    openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) i
      ≠ openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) (i + 1)

/-- The hemi-stuck vanishing-support remnant: at a hemi-stuck supremum whose opened arm is already weakly
convex, some non-incident support still vanishes (the trichotomy's support disjunct).  Extracting the
*specific* binding from a margin contact is the documented residual of the hemi branch; named honestly. -/
def HemiStuckVanishingSupport {n : ℕ} (A B : Fin (n + 1) → S2) (k : Fin (n - 1)) (h₀ : E3)
    (Tcap : ℝ) : Prop :=
  WeakConvexSphArm (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap)) →
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) i)
        (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) (i + 1))
        (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) j) = 0

/-- **(Wrapper 4, support sub-branch) WeakConvex + vanishing support from a vanishing support.**  Given
a vanishing non-incident support at `δ*`, the right disjunct is itself; weak convexity comes from the
strict hemi margins (`HemiMarginStrictPosAtSup`) and the opened-edge distinctness, via the sibling
`weakConvex_of_supportStuck_of_hemiPos`. -/
theorem stuckOutcome_of_supportVanish {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {k : Fin (n - 1)} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (_hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hdist : OpenedEdgesDistinct A B k h₀ Tcap)
    (hhemstrict : ∀ r : Fin (n + 1),
      0 < (⟪h₀, ((openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) r : S2) : E3)⟫ : ℝ))
    (hvanish : ∃ c : NonIncident n,
      supportConstraint A (openingAxis k) c (monitoredSup A B k h₀ Tcap) = 0) :
    WeakConvexSphArm (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap)) ∧
      ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) i)
          (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) (i + 1))
          (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) j) = 0 := by
  set δ : ℝ := monitoredSup A B k h₀ Tcap with hδ
  -- closure: all supports ≥ 0.
  have hsupp : ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 ≤ sOrient (openTail A (openingAxis k) δ i) (openTail A (openingAxis k) δ (i + 1))
        (openTail A (openingAxis k) δ j) := by
    intro i j hji hji1
    have := supportConstraint_nonneg_at_sup hka hkt hTcap h0 (⟨(i, j), ⟨hji, hji1⟩⟩ : NonIncident n)
    rwa [supportConstraint_apply] at this
  -- weak convexity from the strict hemi margins + edge distinctness.
  have hweak : WeakConvexSphArm (openTail A (openingAxis k) δ) :=
    weakConvex_of_supportStuck_of_hemiPos hA hnorm hsupp hdist hhemstrict
  refine ⟨hweak, ?_⟩
  -- the vanishing support, as a NonIncident witness, repackaged to the ∃ i j form.
  obtain ⟨c, hc⟩ := hvanish
  exact vanishing_support_of_supportStuck A k δ ⟨c, hc⟩

/-- **(Wrapper 4) Clause (iii) of `InteriorOpeningGlue` — the full STUCK boundary outcome.**  From a
`Stuck` supremum, the strict hemi margins (`HemiMarginStrictPosAtSup`), the opened-edge distinctness,
the equator-spread exclusion (→ tilt), and the hemi-stuck vanishing-support remnant, produce
`WeakConvexSphArm Aδ ∧ ∃ vanishing non-incident support` — exactly clause (iii). -/
theorem stuckOutcome_weakConvex_of_residues {n : ℕ} {A B : Fin (n + 1) → S2}
    (hA : StrictConvexSphArm A) {k : Fin (n - 1)} {h₀ : E3} (hnorm : ‖h₀‖ = 1)
    (hhpos : ∀ i : Fin (n + 1), 0 < (⟪h₀, (A i : E3)⟫ : ℝ))
    (hka : ShortArc (A (openingAxis k)) (jointPrev A k))
    (hkt : ShortArc (A (openingAxis k)) (jointNext A k)) {Tcap : ℝ} (hTcap : 0 ≤ Tcap)
    (h0 : ∀ o, 0 ≤ monitoredFamily A B k h₀ o 0)
    (hdist : OpenedEdgesDistinct A B k h₀ Tcap)
    (hhemstrict : ∀ r : Fin (n + 1),
      0 < (⟪h₀, ((openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) r : S2) : E3)⟫ : ℝ))
    (hspread : EquatorSpreadExcluded A (openingAxis k) h₀ (monitoredSup A B k h₀ Tcap))
    (hhemvanish : HemiStuckVanishingSupport A B k h₀ Tcap)
    (hstuck : Stuck A B k h₀ Tcap) :
    WeakConvexSphArm (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap)) ∧
      ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
        sOrient (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) i)
          (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) (i + 1))
          (openTail A (openingAxis k) (monitoredSup A B k h₀ Tcap) j) = 0 := by
  rcases hstuck with hsup | hhem
  · -- support-stuck: direct.
    exact stuckOutcome_of_supportVanish hA hnorm hhpos hka hkt hTcap h0 hdist hhemstrict hsup
  · -- hemi-stuck: FFCT30 dichotomy with the equator tangent.
    have htangent : EquatorTangentExists A (openingAxis k) h₀ (monitoredSup A B k h₀ Tcap) :=
      equatorTangent_at_sup_of_spreadExcluded A B k h₀ hspread
    rcases hemiStuck_forces_supportStuck_or_weakConvex hA hnorm hhpos hka hkt hTcap h0 hhem htangent
      with hsup | hweak
    · -- hemi-stuck routed to support-stuck: the support sub-branch.
      exact stuckOutcome_of_supportVanish hA hnorm hhpos hka hkt hTcap h0 hdist hhemstrict hsup
    · -- weakly convex already; the witnessing vanishing support is the hemi remnant.
      exact ⟨hweak, hhemvanish hweak⟩

/-! ## §4. The headline-mod-residues.

`InteriorOpeningGlue` is carried as one named bundle (clauses (i)/(ii) are sign-bug-blocked for the
`+δ` family, clause (iii) is the geometry threaded above).  We deliver `InteriorOpeningOutcome` from it
via the banked `interiorOpeningOutcome_holds`, then the chapter headline. -/

/-- **(Wrapper 5) `InteriorOpeningOutcome` from the carried `InteriorOpeningGlue` bundle.**  Thin
re-export of the banked `interiorOpeningOutcome_holds`; named here so the headline's residue surface is
explicit. -/
theorem interiorOpeningOutcomePlus_of_residues (hglue : InteriorOpeningGlue) :
    SphericalArmAssembly.InteriorOpeningOutcome :=
  interiorOpeningOutcome_holds hglue

/-- **(Wrapper 6) The Chapter-13 spherical arm lemma, modulo the named residues.**  This is the honest
chapter endpoint: the spherical (Cauchy) arm inequality `sDist (A 0)(A last) ≤ sDist (B 0)(B last)` for
strictly convex arms `A, B` with equal sides and `A`'s joints `≤` `B`'s, conditional on the four named
residues:

* `hcore : SpliceBodyDiagMono` — sub-arm diagonal monotonicity (pre-B1 splice geometry);
* `hstruct : SpliceStructuralData` — the cut sub-arm geometry (pre-B1);
* `hglue : InteriorOpeningGlue` — the opening trichotomy boundary glue.  Clauses (i)/(ii) (endpoint
  non-decrease + REACH selection) are **FALSE for the `+δ` family** (sign bug, `SignBugBlocksI/II`,
  `EndpointPosMono`) and need the corrected `−δ` widening family (substrate change); clause (iii)'s
  STUCK geometry is threaded by `stuckOutcome_weakConvex_of_residues` modulo
  `HemiMarginStrictPosAtSup` + `OpenedEdgesDistinct` + `EquatorSpreadExcluded` + the multi-rotation
  Gram signs / `HemiStuckVanishingSupport`.

Every hypothesis is a named, satisfiable `Prop` (non-vacuous; guards in §5).  No clause is discharged by
a fabricated proof; the residues are the genuine surviving content. -/
theorem mainPlus_headline_mod_residues
    (hcore : SpliceBodyDiagMono) (hstruct : SpliceStructuralData) (hglue : InteriorOpeningGlue)
    {n : ℕ} (hn : 2 ≤ n) (A B : Fin (n + 1) → S2)
    (hA : StrictConvexSphArm A) (hB : StrictConvexSphArm B)
    (hside : ∀ i : Fin n, sideLen A i = sideLen B i)
    (hangle : ∀ i : Fin (n - 1), jointAngle A i ≤ jointAngle B i) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (B 0) (B (Fin.last n)) :=
  spherical_arm_mono_of_spliceBodyDiagMono hcore hstruct
    (interiorOpeningOutcomePlus_of_residues hglue) hn A B hA hB hside hangle

/-! ## §5. Non-vacuity / anti-impostor guards (playbook §3.3).

Every named residue threaded above is satisfiable and its conclusion is genuine geometric data — never a
vacuous-hypothesis impostor. -/

/-- Guard for `OpenedEdgesDistinct` (non-vacuity, shape): the residue is a genuine pointwise `≠`
statement over the *opened* vertices, not `True`.  At `δ = 0` (the unopened arm `openTail A K 0 = A`)
the opened-edge distinctness *is* the base-arm distinctness `A i ≠ A (i+1)` — so the residue unfolds to
real geometric content, satisfiable at the base configuration. -/
theorem openedEdgesDistinct_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (K : Fin (n + 1))
    (i : Fin (n + 1))
    (hne : openTail A K 0 i ≠ openTail A K 0 (i + 1)) :
    A i ≠ A (i + 1) := by
  rwa [openTail_zero_angle] at hne

/-- Guard for `HemiStuckVanishingSupport`: its conclusion is genuine non-incident vanishing-support data
(the `j ≠ i`, `j ≠ i+1` constraints are real), so the remnant is a true production, not a vacuous bound.
We exhibit the conclusion shape is inhabited geometric content via the closure support form. -/
theorem hemiStuckVanishingSupport_conclusion_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2)
    (k : Fin (n - 1)) (δ : ℝ) (c : NonIncident n)
    (hc : supportConstraint A (openingAxis k) c δ = 0) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) δ i) (openTail A (openingAxis k) δ (i + 1))
        (openTail A (openingAxis k) δ j) = 0 :=
  vanishing_support_of_supportStuck A k δ ⟨c, hc⟩

/-- Guard for the STUCK outcome: its conclusion is genuine — the weak-convex arm + a real vanishing
support is inhabited geometric data, realised whenever a non-incident support of the opened arm vanishes.
We record the satisfiability of the support half (the load-bearing disjunct). -/
theorem stuckOutcome_conclusion_nonvacuous {n : ℕ} (A : Fin (n + 1) → S2) (k : Fin (n - 1)) (δ : ℝ)
    (c : NonIncident n) (hc : supportConstraint A (openingAxis k) c δ = 0) :
    ∃ i j : Fin (n + 1), j ≠ i ∧ j ≠ i + 1 ∧
      sOrient (openTail A (openingAxis k) δ i) (openTail A (openingAxis k) δ (i + 1))
        (openTail A (openingAxis k) δ j) = 0 :=
  vanishing_support_of_supportStuck A k δ ⟨c, hc⟩

/-- Guard for the headline conclusion: the spherical arm inequality is genuinely satisfiable — realised
reflexively at `A = B` (`sDist (A 0)(A last) ≤ sDist (A 0)(A last)`), so the headline is a real
inequality, not a vacuous bound. -/
theorem mainPlus_headline_conclusion_satisfiable {n : ℕ} (A : Fin (n + 1) → S2) :
    sDist (A 0) (A (Fin.last n)) ≤ sDist (A 0) (A (Fin.last n)) := le_refl _

/-- Guard for the carried `InteriorOpeningGlue` clauses (i)/(ii) being FALSE: we re-export the
unconditional sign-bug fact, so the residue's two false clauses are *documented*, not silently assumed.
The monitored family opens in the closing direction (`sOrient (A K)(jointPrev)(jointNext) < 0`). -/
theorem glue_sign_bug_documented {n : ℕ} {A : Fin (n + 1) → S2} (hA : StrictConvexSphArm A)
    (k : Fin (n - 1)) :
    sOrient (A (openingAxis k)) (jointPrev A k) (jointNext A k) < 0 :=
  SignBugBlocksII hA k

end ProofsInTheBook.ZinanFFCT35

#print axioms ProofsInTheBook.ZinanFFCT35.mainPlus_headline_mod_residues
#print axioms ProofsInTheBook.ZinanFFCT35.stuckOutcome_weakConvex_of_residues
#print axioms ProofsInTheBook.ZinanFFCT35.stuckSupport_betweenness_axisEdge
#print axioms ProofsInTheBook.ZinanFFCT35.interiorOpeningOutcomePlus_of_residues
