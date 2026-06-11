# Ch13 — discharging / sharply shrinking `WBSCutNormalization` (the FFCT49 bridge residue)

**File:** `ProofsInTheBook/ZinanFFCT52.lean` (632 lines, clean-3, 0 errors).
**Verify:** `lake env lean ProofsInTheBook/ZinanFFCT52.lean` on uisai2 — all 10 `#print axioms` report
only `[propext, Classical.choice, Quot.sound]`. No `sorry`/`admit`/`axiom`/`native_decide`.
(Only edited file. FFCT49's olean was rebuilt first; uisai2 fast-forwarded to `abac5e0`.)

## Target

`ZinanFFCT49.WBSCutNormalization` is a 6-field opaque bundle carried as raw data by the B1→CutReady
bridge.  This module discharges what is genuinely derivable and shrinks the rest to its irreducible core.

## Component 2 — no-repeat distinctness: **FULLY DISCHARGED**

`WBSCutNormalization.hrepeat : openedWBS ⟨i+1⟩ ≠ openedWBS ⟨j⟩` is no longer raw data.

- `distinctNormalized_of_noRepeat` derives it from `NoNonadjacentRepeat (openedWBS)` (the
  campaign-accepted no-repeat surface, FFCT23/25 precedent) + the weak convexity already present at the
  WBS support-stuck sup.  Index arithmetic handled by a **case split**: nonadjacent (`(i+1)+2 ≤ j`) uses
  `NoNonadjacentRepeat`; the adjacent boundary `j = i+2` uses `edge_short` (the consecutive pair is a real
  arm edge ⇒ `ShortArc` ⇒ distinct).
- `hrepeat_of_noRepeat_WBS` instantiates this at the WBS sup; the weak convexity is **unconditional**
  (FFCT47 discharged the wrap residual, so `supportStuckWBS_weakConvex` fires without hypotheses).

## Component 1 — orientation gap: **reversal infrastructure BUILT + normalization proved** (the recommended route)

`SphericalLastCornerStuck` recorded "no reversal-invariance lemma exists" — **built it** (§2):

- `revFin` (Fin reversal, `revFin_involutive`), `revArm`, `revArm_apply`/`revArm_index`.
- `sOrient_revArm_normalized` — the load-bearing det3 sign-tracking: a `b < a` raw triple
  `(P a)(P (a+1))(P b)` reads as the **normalized reversed** triple `(revArm P ⟨n−a−1⟩)(revArm P ⟨n−a⟩)
  (revArm P ⟨n−b⟩)` with value `−sOrient(...)` (slot-1-2 swap, `det3_swap12`); a *vanishing* support stays
  vanishing (`= 0` is sign-free).
- `revArm_sideLen` (sides reverse + `sDist_comm`), `revArm_jointAngle` (joints reverse order, value
  invariant by `sphAngle_comm`), `revArm_openHemisphere`, `revArm_noNonadjacentRepeat`.

`orientationNormalized` (§3) then **closes the orientation gap**: from the raw Fin binding
(`b ≠ a`, `b ≠ a+1`, vanishing support, non-wrap-base `a.val+1 < n+1`) it produces a *normalized* cut
`i+1 < j ≤ n` with matching vanishing support, EITHER on `P` (when `a+1 < b`) OR on `revArm P` (when
`b < a`).  The det3 sign is genuinely calculated, not faked.

Honest scope: `orientationNormalized` takes the non-wrap-base condition `a.val+1 < n+1` (the support edge
`(a,a+1)` is a real interior edge, not the cyclic wrap `(n,0)`).  The wrap-base case `a.val = n` is the
separate cyclic case (flagged).

## Component 3 — interval convexity: **interior restriction DISCHARGED, residue shrunk to the wrap diagonal**

The wrap-edge obstruction is genuine (confirmed: `SphericalSZStepClose` §R — the ear is a *closed*
polygon whose closure adds the **diagonal chord** `A ⟨j⟩ → A ⟨i+1⟩` as a new edge, not a parent edge).

Discharged interior facts (reusable, no residue): `intervalArm_interiorEdgeShort`,
`intervalArm_interiorSupport`, `intervalArm_interiorStrictSupport`, `intervalArm_openHemisphere`.

Residue shrunk: `IntervalWrapData` / `IntervalWrapDataStrict` carry **only** the wrap-diagonal certificates
(the diagonal `ShortArc` + nonneg/strict support based at the diagonal).  Then:
- `weakConvex_intervalArm_of_wrap` : parent weak convexity + wrap data ⇒ `WeakConvexSphArm (intervalArm…)`
- `strictConvex_intervalArm_of_wrap` : parent strict + strict wrap data ⇒ `StrictConvexSphArm (intervalArm…)`
All non-wrap fields (interior edges, interior-base supports incl. wrap-vertex tested, open hemisphere) are
assembled from the parent; the cyclic `i+1` wrap arithmetic is fully handled.

**Small-size honesty (the §4 vacuity check):** `WeakConvexSphArm` requires `two_le : 2 ≤ m`; with
`i+1 < j ≤ n` the ear length `m = j−(i+1) ≥ 1`, and the minimal `j = i+2` gives `m = 1`, which does **not**
typecheck as a convex arm.  So the assemblies stand under `2 ≤ m` (`j ≥ i+3`), and `j = i+2` is the
explicitly-excluded triangle-minimal branch (the consumer `stuckAtK_diag_le` needs the same `two_le`).

## Assembly + verdict

`WBSCutNormalizationShrunk` replaces the 6-field bundle with the irreducible residue: the normalized
support (component 1), the no-repeat surface (component 2 derives `hrepeat`), and the two wrap-diagonal data
(component 3).  `wbsCutNormalization_of_shrunk` reconstructs the **genuine** `ZinanFFCT49.WBSCutNormalization`
from it (hsupp verbatim, hrepeat derived, hAe/hBe via the wrap assemblies).

**Net shrink:** 6 raw fields → {normalized support, no-repeat surface, weak-ear wrap diagonal, strict-ear
wrap diagonal}.  `hrepeat` eliminated entirely (derived); the orientation gap reduced from "supply hij1 +
hsupp as data" to the proved side-choice `orientationNormalized` (with the reversal suite as genuine new
infrastructure); the ear convexity reduced from "full opaque certificate" to the **wrap diagonal alone**.

**Honesty audit (playbook §3.3):** every conditional theorem's hypotheses are satisfiable and non-vacuous.
`WBSCutNormalizationShrunk` fields are mutually consistent (`hm : 2 ≤ j−(i+1)` is compatible with
`hij1 : i+1 < j`, forcing `j ≥ i+3`).  Non-vacuity guards: `wbsCutNormalizationShrunk_orientation`,
`revFin_involutive_nonvacuous`, `orientationNormalized_nonvacuous`, `weakConvex_intervalArm_of_wrap_size`,
`intervalWrapData_wrap_short`.  The residue is NAMED, satisfiable, and strictly smaller; no vacuous
statements, no faked reversal lemma — the reversal suite is real and load-bearing.

Did NOT git commit.
