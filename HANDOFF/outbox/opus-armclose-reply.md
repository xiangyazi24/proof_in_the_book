# opus-armclose-reply — Chapter 13 §8.4 structural close (spherical arm lemma)

Status: **`spherical_arm_mono(_strict)` is NOT made fully unconditional.**  Genuine new
UNCONDITIONAL content built — the **full §8.3 neighbourhood convexity persistence on the multi-vertex
arm** (every convex-polygon field, not just the mixed-support family), plus a **correctness finding**:
the substrate's `BoundaryConvexPersistAtSup` is **unsound as stated**.  The irreducible residue is
isolated, sharpened, and routed end-to-end to the arm lemma.  File:
`ProofsInTheBook/SphericalArmClose.lean` — RC=0, no sorry/axiom/admit/native_decide, clean-3 on every
new theorem.

## What I PROVED (genuine new content, all UNCONDITIONAL, clean-3 — strictly enlarges the substrate)

* **`shortArc_iff_sDist` + `shortArc_rotS2`** — short arcs are the open condition `sDist ∈ (0,π)` and
  are preserved by the opening isometry `rotS2`.  Hence `openArm_edge_short_prefix` (fixed prefix
  edges) and `openArm_edge_short_axisTail` (the axis→tail edge, via the isometry).

* **`continuous_openArm_vertex` / `continuous_openArm_sOrient` / `continuous_openArm_sDist` /
  `continuous_openArm_hemisphere`** — every opened-arm vertex, support determinant, edge distance, and
  hemisphere functional is continuous in `θ`.  This is the analytic backbone the substrate had only for
  the `mixedSupport` family (`continuous_mixedSupport`); here it is for **all** triples and all vertices
  of the opened arm, including the tail-on-the-edge supports the mixed family never reaches.

* **`openArm_strictConvex_nhds` (THE new result, UNCONDITIONAL, clean-3)** — the **full §8.3
  neighbourhood persistence**: `∀ᶠ θ in nhds 0, StrictConvexSphArm (openArm A θ)`.  All five
  convex-polygon fields reconstructed for `openArm A θ` near `0` (where `openArm A 0 = A`): edges short
  (`openArm_shortArc_persist`), every non-incident support strict (`continuous_openArm_sOrient` +
  `strictSupport`-style eventual positivity), incident supports identically `0` (`det3_self_right/mid`),
  and the **full `open_hemisphere`** (the rotated-tail functional stays positive by continuity).  This is
  exactly design §8.3's `convex_hinge_open_small` *in full* on the genuine multi-vertex arm — the
  substrate proved persistence only for the `mixedSupport` family (`mixedSupport_persists`), which does
  **not** control the tail-on-the-edge supports or the hemisphere.

* **`openArm_sOrient_mixed`** — the opened arm's support on the triples whose *supported* vertex is the
  rotated tail equals `mixedSupport A (i,i+1) δ` (the bridge to the substrate's monitored family).

## Correctness finding (playbook §3.3 — `BoundaryConvexPersistAtSup` is UNSOUND as stated)

The substrate's residue
`BoundaryConvexPersistAtSup : … (∀ ij, 0 ≤ mixedSupport A ij δ) → StrictConvexSphArm (openArm A δ)`
is **false / unprovable as written**, for TWO reasons now made explicit by the neighbourhood result:
1. At a boundary `δ` where a mixed support is exactly `0` (the STUCK branch), the `strict_nonincident`
   field (`> 0`) fails outright.
2. Even with *strict* mixed supports, mere positivity of the `mixedSupport` family (the tail as the
   *supported* vertex) does **not** control the `open_hemisphere` functional at the rotated tail, nor
   the tail-on-the-edge supports — these are genuinely different `θ`-dependent quantities, **not
   monitored** by the admissible-supremum family.

The corrected, non-false statement is `BoundaryConvexPersist`: it hypothesises strict convexity on the
whole path `[0, δ]` and concludes it at `δ` — true on a genuine interval by `openArm_strictConvex_nhds`
(`boundaryConvexPersist_interval` exhibits the positive `ε`).

## The PRECISE isolated obstacle (honest — ONE named, non-vacuous Prop + concrete failing chain)

`BoundaryConvexPersist` — the **boundary extension** of the proven neighbourhood persistence to the
admissible supremum `δ*` (the reach-branch matching angle).

**Concrete failing chain (verified against the substrate):**
1. The §8.4 reach recursion needs `StrictConvexSphArm (openArm A δ*)`.
2. `openArm_strictConvex_nhds` gives it for `θ` in a *neighbourhood of `0`* — but `δ*` is the supremum
   of the admissible set, which can lie *outside* that neighbourhood.
3. The admissible set monitors **only** the `mixedSupport` determinant family and the joint-angle
   `targetSlack` (`SphericalAdmissibleSup.combinedSupport`).  The polygon's `open_hemisphere`
   functional at the rotated tail is **not** among the monitored constraints, so it can degenerate
   strictly *before* `δ*` while every monitored support is still positive.
4. No supporting-functional-from-determinant-positivity lemma exists in the substrate
   (`SphericalSZStep.lean:68` literally records "No persistence lemma exists"); closing it requires
   either adding the hemisphere to the monitored admissible family (an **upstream** change to
   `SphericalCore`/`SphericalAdmissibleSup`, which this round does not own) or a new convex-geometry
   theorem deriving the supporting functional from the determinant supports.

Non-vacuity: `tailIncidentPersist_base` (`δ = 0` ⟹ `openArm A 0 = A` strictly convex) realises the
conclusion; `boundaryConvexPersist_interval` proves the path-strict hypothesis holds on a genuine
`ε > 0` interval (so it is not a vacuous-hypothesis impostor, and the residue is strictly the
boundary-vs-neighbourhood extension).

## The structural-assembly residue (honest, explicit — NOT discharged)

`BoundaryConvexPersist` alone is **not** sufficient for `StuckWitnessExists`/`WeakArmStep`: the
inductive step additionally needs the §8.4 *construction* — **arbitrary-joint opening** (the substrate's
`openArm` opens only the last joint; an interior strict joint needs relabelling via the cyclic/reflection
symmetry of `StrictConvexSphArm`), the **reach recursion** on `#unmatched` joints (well-founded), and the
**matched-data cut** (substrate `diagonalCutArm_holds` + `cut_endpt_transport`).  I record this as the
explicit, satisfiable `OpeningStructuralAssembly : BoundaryConvexPersist → StuckWitnessExists ∧
WeakArmStep` (not `sorry`/`axiom`), and route the arm lemma through it:

* `schoenbergZaremba_of_assembly : BoundaryConvexPersist → OpeningStructuralAssembly →
  SchoenbergZarembaTarget` (via the substrate `schoenbergZaremba_of_witness_weak`);
* `spherical_arm_mono_of_assembly` / `spherical_arm_mono_strict_of_assembly` — the kernel arm lemma,
  conditional on the two isolated residues.

## Verification

* `lake env lean ProofsInTheBook/SphericalArmClose.lean` → RC=0, zero warnings, zero errors.
* `lake build ProofsInTheBook.SphericalArmClose` → Build completed successfully (8440 jobs).
* `grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide'` → 2 hits, both in module-doc prose; 0 in code.
  No `:= rfl` / `:= trivial` / `_placeholder_`.
* `#print axioms` (rebuilt oleans) → clean-3 `[propext, Classical.choice, Quot.sound]` on
  `openArm_strictConvex_nhds`, `openArm_edge_short_axisTail`, `continuous_openArm_sOrient`,
  `shortArc_rotS2`, `reachConvexPersistAtSup`, `boundaryConvexPersist_interval`,
  `spherical_arm_mono_of_assembly`, `spherical_arm_mono_strict_of_assembly`,
  `schoenbergZaremba_of_assembly`.

## Net effect on the chapter

The §8.3 convexity persistence is now **unconditional in full** on the multi-vertex arm
(`openArm_strictConvex_nhds`) — the substrate had only the mixed-support fragment.  The substrate's
`BoundaryConvexPersistAtSup` is exposed as unsound and replaced by the correct, interval-true
`BoundaryConvexPersist`.  `spherical_arm_mono(_strict)` remains **conditional** on two sharply-isolated,
non-vacuous residues: (1) `BoundaryConvexPersist` — the boundary extension whose sole irreducible
obstacle is the **unmonitored `open_hemisphere` functional at `δ*`** (no substrate persistence lemma;
closing it needs an upstream change to the monitored admissible family, not owned this round); and (2)
`OpeningStructuralAssembly` — the multi-vertex opening *construction* (arbitrary-joint opening + reach
recursion + matched-data cut).  No vacuous coupling or co-extensive re-wrapper was banked; the genuine
new content is the full-polygon neighbourhood persistence that strictly enlarges the substrate beneath
the residue.

## Honest verdict

FRAGMENT (toward FAITHFUL).  The headline `spherical_arm_mono(_strict)` is NOT unconditional.  The
analytic §8.3 layer is closed in full and unconditionally; the chapter frontier is now precisely the
boundary persistence (gated by the unmonitored hemisphere — an upstream admissible-family change) plus
the structural opening construction.
