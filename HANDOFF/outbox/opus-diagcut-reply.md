# opus-diagcut-reply — Chapter 13 §8.4 `DiagonalCutArm` construction

Status: **`DiagonalCutArm` is PROVED unconditionally** (the named §8.4 residue the prior round isolated
and left as a stub).  File: `ProofsInTheBook/SphericalDiagCut.lean` — compiles, RC=0, no
sorry/axiom/admit/native_decide, clean-3 axioms.

**Headline target NOT delivered, and CANNOT be delivered from this Prop (verified, not impression):**
`szStepGeom_holds : SZStepGeom` is **not** provable from `DiagonalCutArm`.  The task's premise — that
`DiagonalCutArm` is "the entire remaining residue" and that an assembly skeleton
`DiagonalCutArm + reach + openedJointAngle_surjOn ⇒ SZStepGeom` exists — is **incorrect against the
actual source**.  No such skeleton exists anywhere in the repo (`grep`: `DiagonalCutArm` has exactly
one definition site + one realisability stub + zero consumers), and one cannot exist, for the concrete
reasons below.

## What I PROVED (genuine new content, all clean-3)

The diagonal-cut sub-arm CONSTRUCTION the prior round (`opus-hingecut-reply.md`) flagged as the
missing "Fin re-indexing of the cut sub-family + transport of the four `StrictConvexSphPolygon`
fields", isolated there as `SphericalHingeCut.DiagonalCutArm` with only a payload-realisability stub.
I built it concretely:

* **`cutArm A := A ∘ Fin.castSucc : Fin (n+1) → S2`** — the last-vertex-drop re-indexing, with the
  index-arithmetic lemmas `cutArm_succ_of_ne_last` (non-wrapping cyclic successor), `cutArm_succ_last`
  (the wraparound to `A 0`), `castSucc_succ_eq` (`i.castSucc + 1 = (i+1).castSucc` for `i ≠ last`).
* **`det3_self_left/_mid/_right`** + **`ne_of_sOrient_pos_ac`**, **`not_antipodal_of_sOrient_pos_ac`**
  — a strict support `0 < sOrient a b c` forces `a ≠ c` and `(a:E3) ≠ -(c:E3)`; the analytic content
  certifying a cut diagonal is a `ShortArc`.
* **`shortArc_closing_diag`** — the new closing edge `A ⟨n⟩ → A 0` is a short arc (interior vertex
  exists for `n ≥ 2`, witnessing the diagonal's distinctness/non-antipodality via
  `cut_diagonal_supports`).
* **`cutArm_strictConvexPolygon`** — the load-bearing transport: ALL FOUR convex-polygon fields
  (`edge_short`, `edge_support`, `strict_nonincident`, `open_hemisphere`) carried from `A` (modulus
  `n+2`) to `cutArm A` (modulus `n+1`).  Non-closing edges inherit from `A`'s edges via `Fin.castSucc`
  injectivity; the single closing edge `A ⟨n⟩ → A 0` (the cut diagonal) is handled by
  `shortArc_closing_diag` and `cut_diagonal_supports` via cyclic `sOrient` re-indexing
  (`sOrient_cyclic`).  This is exactly "missing fact 1" of `opus-hingecut-reply.md`.
* **`cutArm_strictConvexArm`** — `cutArm A` is a `StrictConvexSphArm` for `n ≥ 2`.
* **`diagonalCutArm_holds : DiagonalCutArm`** — the named residue, PROVED.  For `n ≥ 2` the witness is
  `cutArm A` (the stuck hypothesis is not even needed — any vertex-deletion of a strictly convex arm
  is strictly convex); for `n = 1` (`A : Fin 3`) the vanishing-non-incident-support hypothesis
  **contradicts** `A`'s own `strict_nonincident` field, so the case is vacuous.

## Why `DiagonalCutArm` does NOT close `SZStepGeom` (the honest, verified residue)

`SZStepGeom` (SphericalSZChain.lean:193) is **definitionally co-extensive with `OpeningData` /
`HingeConvexPosition` / `OpenedArmReachOrStuck`** — the FULL §8.4 single-step inductive opening, as the
prior rounds (`opus-szstep-reply`, `opus-szchain-reply`, `opus-hingecut-reply`) all concluded.  Its
strict branch demands (SphericalOpening.lean:142–150) a **moved tail vertex `qstar`** with
`det3 (A0)(A1) qstar = 0`, the two convex-position Gram signs, the strict opening bound
`endpt A < sDist (A0) qstar`, and the sub-comparison — i.e. the *output of the Rodrigues opening to the
admissible supremum*.  Two concrete obstructions, each verified:

1. **`DiagonalCutArm` produces no `qstar`.**  Its conclusion is only
   `∃ A' : Fin (n+1) → S2, StrictConvexSphArm A' ∧ A' 0 = A 0` — a single re-indexed sub-arm sharing
   the first endpoint, with **no** matched sides, **no** matched joints, **no** second sub-arm, and
   **no** moved tail.  It carries strictly less than even the equal-angle cut transport
   `cut_endpt_transport` needs (which requires endpoint-preserving sub-arms with `∀i, sideLen A' i =
   sideLen B' i`, `endpt A' = endpt A`).
2. **`cutArm` does not even preserve the endpoint.**  `endpt (cutArm A) = sDist (A 0)(A n) ≠
   sDist (A 0)(A (n+1)) = endpt A`, so it cannot feed `cut_endpt_transport` regardless.  An
   endpoint-preserving *interior* cut would still only address the **equal-angle** branch; the
   **all-strict reach** branch (no equal joint) genuinely needs the opening primitive.

## The PRECISE minimal residue (after genuine exhaustion)

The chapter's true remaining frontier for the arm lemma is the **opening primitive**
`SphericalOpening.OpenedArmReachOrStuck` (≡ `OpeningData` ≡ `SphericalSZChain.SZStepGeom`): the
§8.4 Rodrigues-opening-to-admissible-supremum that, in the all-strict case, produces the moved tail
`qstar` with the betweenness determinant + Gram signs + strict opening bound, OR the direct strict
endpoint bound.  Its analytic skeleton is in the substrate (`arm_reach_or_stuck` dichotomy on the mixed
supports, `openedJointAngle_surjOn` IVT, `mixedSupport_persists` neighbourhood persistence, the §8.1
keystone `openedAngle_ge_of_oriented`), but the assembly — convexity persistence *at the supremum
boundary* (not just a neighbourhood), the convex-position sign determination at the tight mixed
constraint, and the IVT last-angle matching under `SZComparison n` — is the genuine multi-hundred-line
core the design calls "THE hard theorem" (§8.4) and which 4+ prior rounds isolated as irreducible.
This is **not** "index bookkeeping"; it is the analytic opening construction.  `DiagonalCutArm` is a
genuine but **strictly weaker** sub-fact than this primitive (it is the convex-position cut substrate,
now proved; the opening that produces `qstar` is separate).

## Verification

* `lake env lean ProofsInTheBook/SphericalDiagCut.lean` → RC=0.
* `lake build ProofsInTheBook.SphericalDiagCut` → Build completed successfully (8436 jobs).
* `grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide'` → 1 hit, inside the module doc comment prose;
  0 in code.
* `#print axioms` (rebuilt oleans) — clean-3 `[propext, Classical.choice, Quot.sound]` on
  `diagonalCutArm_holds`, `cutArm_strictConvexPolygon`, `cutArm_strictConvexArm`.

## Net effect on the chapter

`SphericalHingeCut.DiagonalCutArm` — the §8.4 diagonal-cut sub-arm construction, previously a named
residue with only a realisability stub — is now PROVED (`SphericalDiagCut.diagonalCutArm_holds`), via a
genuine new `Fin`-subfamily re-indexing (`cutArm`) and the full four-field convex-polygon transport
(`cutArm_strictConvexPolygon`).  This discharges the specific named target.  It does **not** make
`spherical_arm_mono(_strict)` unconditional, because `DiagonalCutArm` is — verified against the source —
**not** co-extensive with `SZStepGeom`; the arm lemma's true remaining residue is the opening primitive
`OpenedArmReachOrStuck` (the `qstar`-producing Rodrigues opening), which is genuinely separate convex-
analytic content and is left honestly open.  No vacuous coupling or co-extensive re-wrapper was banked.
