# opus-windingzero reply — Ch36 `ExteriorWindingZero` residue: sub-step 1 + signed→unsigned + generic local-constancy PROVED; 2′+3′ isolated

**Status: SUBSTANTIAL PROGRESS — sub-step 1 (far-point winding = 0) is fully proved
unconditionally; the signed→unsigned reduction of sub-step 2 is fully proved; the GENERIC
STRATUM of sub-step 2 (`windCross` local-constancy in the base point `x`) is fully proved;
and `ExteriorWindingZero` is reduced to a single named, honestly non-vacuous planar-topology
Prop `WindZeroExterior` (= the wall/vertex strata of sub-step 2 ∪ sub-step 3 connectivity).
0 sorry/axiom/admit/native_decide; all headline results clean-3.**

**File:** `ProofsInTheBook/PolygonWindingZero.lean` (NEW, the only file I own, 473 lines).
**Branch:** `main` (uisai1). No commits, no branch switch. `ProofsInTheBook.lean`/`Audit.lean`
untouched (wiring left for the orchestrator). Only this new file created.
**Server:** uisai1. No codex/OpenAI tooling. NEVER ran lake/lean on the Mac.
**Build dep:** `lake build ProofsInTheBook.PolygonWinding` → *Build completed (8446 jobs)*, RC=0.
**Verification (uisai1):** `lake env lean ProofsInTheBook/PolygonWindingZero.lean` → RC=0, no
warnings; `lake build ProofsInTheBook.PolygonWindingZero` → *Build completed (8447 jobs)*, RC=0.

---

## Honest scope correction (playbook §3.3, no inflation)

The dispatch framed this as "ExteriorWindingZero → OffDiagDisjoint → … → **unconditional**
`artGallery_strict`". On reading the actual import graph this is **overstated** and I report it
straight:

* `OffDiagDisjoint` is **already** derivable, without any winding development, from a
  `CutGeometry`'s `split_region_intersection` field
  (`PolygonContainment.offDiagDisjoint_of_cutGeometry`, re-exported as
  `PolygonCutGeometry.offDiagDisjoint_of_polygon`). The `PolygonWinding` development (and this
  file) is an **alternative, more-honest route** to `OffDiagDisjoint` from the genuine Jordan
  winding fact instead of assuming the full intersection set-identity.
* The unconditional `PolygonTriangleConvex.artGallery_strict` rests on **several other** oracle
  inputs besides `OffDiagDisjoint` (`PolygonGeometryInput`/`CutGeometryOracle`'s
  `split_region_union` + `convexVertex` + transversality, `BaseTriangleFacts`,
  `DiagonalAttachInput M`). Closing `ExteriorWindingZero` **alone does not** make
  `artGallery_strict` unconditional. The assigned concrete target — *prove
  `ExteriorWindingZero`* (the deepest single geometric residue) — is what I attacked.

## What is PROVED (all clean-3, 0 sorry/axiom/admit/native_decide)

**Sub-step 1 — far-point signed winding = 0 (fully unconditional):**
* `not_rawEdgeCrosses_of_same_strictSide`, `rawSignedInd_eq_zero_of_same_strictSide`
* `windRaw_eq_zero_of_all_strictSide` / `windCross_eq_zero_of_all_strictSide` — if every vertex
  is on the *same* strict side of the ray line `x + ℝ·r`, no edge straddles ⇒ every
  `RawEdgeCrosses` false ⇒ `windCross = 0`.
* `perpVec` / `det2_perpVec_pos` / `side_smul_perpVec` / `exists_far_point_all_neg` /
  **`exists_far_point_windCross_zero`** — `side r x v = det2 r v − det2 r x` is affine in `x`;
  the perpendicular `perpVec r = (−r₁, r₀)` has `det2 r perpVec = ‖r‖² > 0`, so along `x = c·perpVec`
  the linear part diverges and pushes every vertex to the strict negative side. Hence **an
  admissible far point with `windCross = 0` exists for every polygon + ray** — the sub-step-1
  existence the standard proof needs, proved from scratch (no Mathlib winding API).

**Sub-step 2 — signed→unsigned reduction (fully proved):**
* `edgeSign` / `rawSignedInd_eq_edgeSign_mul` — the orientation sign of an oriented edge is
  **base-point-independent**: `rawSignedInd r x a b = edgeSign r a b · rawInd r x a b`.
* `windRaw_eq_edgeSign_sum`, `windRaw_eq_of_rawInd_eq`, **`windCross_eq_of_rawInd_eq`** — signed
  winding constancy in `x` follows from *unsigned* per-edge indicator constancy in `x` (the signs
  factor out). This collapses "signed local constancy" to the unsigned story.

**Sub-step 2 — GENERIC stratum (fully proved, the bulk of the local-constancy core):**
* `continuous_pt0`/`continuous_pt1`/`continuous_side_basepoint`/`continuous_rawTau_basepoint` —
  `side r · v` and `rawTau r · a b` are continuous in the *base point* `x` (the `x`-parametrised
  analogue of `PolygonRayIndep.continuous_ds0Of`, which is `t`-parametrised; no such `x`-version
  existed in the repo).
* **`rawInd_eventually_eq_basepoint_generic`** — at a base point `x₀` off the edge line (both
  endpoint sides ≠ 0) with nonzero forward parameter, the unsigned indicator `rawInd r · a b` is
  locally constant in `x` (eventual sign-preservation of the three guards; `Span` decided by the
  sign pattern via `span_iff_opp_sign`).
* **`windCross_eventually_eq_basepoint_generic`** — lifts the per-edge generic constancy to the
  whole **signed** `windCross Q σ ·`: at a base point where *every* edge is in the generic
  stratum, `windCross` is locally constant in `x`. (Finite intersection via `Filter.eventually_all`
  + the signed→unsigned reduction.)

**The residue isolation + reduction (fully proved):**
* `WindZeroExterior Q σ Ext` (named Prop) + **`windZeroExterior_allNegSide`** (anti-vacuity:
  the residue's conclusion is *true* at every far point, so `WindZeroExterior` on the all-negative-
  side witness holds unconditionally — it is satisfiable, not an unsatisfiable-premise strengthening).
* `leftExteriorSide`/`rightExteriorSide` + **`exteriorWindingZero_of_windZeroExterior`** —
  `ExteriorWindingZero g` follows from `WindZeroExterior` on the negative-side (LEFT) and
  positive-side (RIGHT) exterior witnesses, per diagonal.

## The precise remaining residue (one named, non-vacuous Prop: 2′ wall/vertex strata + 3′)

`WindZeroExterior Q σ Ext` — "off the boundary, a base point in the exterior witness `Ext` has
`windCross Q σ x = 0`". With sub-step-1, the signed reduction, and the generic local-constancy
stratum all discharged, the genuine irreducible content of `WindZeroExterior` is exactly:

1. **(2′) wall/vertex strata of local constancy** — `windCross` constancy across the
   *non-generic* base points (some vertex on the ray line `side = 0`, or forward parameter `= 0`),
   i.e. the `x`-parametrised analogue of `PolygonWall`/`PolygonWallGlobal`'s wall-skipping +
   vertex-pairing arguments (`span_mod_two_through_vertex`-style), which I have **not** ported to
   the base-point parametrisation; and
2. **(3′) exterior connectivity** — that a point strictly on the side of the diagonal line away
   from the ear's interior is connected, within the off-boundary exterior of the ear, to a far
   point of sub-step 1 (no boundary crossing).

Concrete failing chain (everything except the residue is PROVED in this file):
```
exists_far_point_windCross_zero            (sub-step 1: far point, windCross = 0)         — PROVED
windCross_eq_of_rawInd_eq                  (signed ⇐ unsigned constancy)                 — PROVED
windCross_eventually_eq_basepoint_generic  (sub-step 2, generic stratum)                 — PROVED
exteriorWindingZero_of_windZeroExterior    (ExteriorWindingZero ⇐ WindZeroExterior)      — PROVED
  └─ WindZeroExterior  =  (2′ wall/vertex local-constancy strata) ∘ (3′ exterior connectivity)
        ← IRREDUCIBLE: the planar winding-zero-outside-a-Jordan-curve transport, base-point
          parametrised; not in Mathlib. Non-vacuous (windZeroExterior_allNegSide).
```

Note the general-ear honesty: a diagonal ear of a *non-convex* simple polygon does **not** lie in
one half-plane of the chord line, so the "convex-ear single-half-plane" shortcut does not apply;
the genuine Jordan transport (2′+3′) is required, confirming the prior round's irreducibility call
— now sharpened, with sub-step 1 and the generic stratum removed from it.

## Verification (playbook §3 acceptance)

* **A (mechanical):** 0 sorry/admit/axiom/native_decide (`grep` clean). The only `:= rfl`/`Iff.rfl`
  uses are genuine defeq characterisations (`hchar : RawEdgeCrosses ↔ Span ∧ 0 ≤ τ`), not
  trivially-true Props. `lake env lean` RC=0 with no warnings; olean built (8447 jobs).
* **`#print axioms` (clean-3, all `[propext, Classical.choice, Quot.sound]`):**
  `exists_far_point_windCross_zero`, `windCross_eq_zero_of_all_strictSide`,
  `windCross_eventually_eq_basepoint_generic`, `windCross_eq_of_rawInd_eq`,
  `exteriorWindingZero_of_windZeroExterior`, `windZeroExterior_allNegSide`,
  `rawInd_eventually_eq_basepoint_generic` — all 7 verified clean-3 (7/7 carry `Classical.choice`,
  none carry `sorryAx`/`ofReduceBool`/`trustCompiler`).
* **B/C (signature/semantic):** `ExteriorWindingZero` / `OffDiagDisjoint` are the existing defs
  (not re-stated). `WindZeroExterior` is non-vacuous (`windZeroExterior_allNegSide` proves its
  conclusion is unconditionally true at far points — co-satisfiable, not a strengthening with an
  unsatisfiable premise). `exteriorWindingZero_of_windZeroExterior` is a GENUINE reduction (uses
  the proved sub-step-1 + signed-reduction machinery), not a re-wrapper.
  **Verdict: FAITHFUL partial discharge** — sub-step 1 + signed-reduction + generic local-constancy
  proved unconditionally; `ExteriorWindingZero` reduced to the minimal base-point Jordan transport
  residue `WindZeroExterior` (2′ non-generic strata + 3′ connectivity).

## Progress map vs the 3-substep spec

| Spec sub-step | Status |
|---|---|
| 1. Far-point signed winding = 0 (+ existence of far point) | **DONE, unconditional** (`exists_far_point_windCross_zero`) |
| 2. Signed local constancy in `x` — reduction to unsigned | **DONE** (`windCross_eq_of_rawInd_eq`) |
| 2. Signed local constancy in `x` — generic stratum | **DONE** (`windCross_eventually_eq_basepoint_generic`) |
| 2. Signed local constancy in `x` — wall/vertex strata | RESIDUE (inside `WindZeroExterior`) |
| 3. Exterior connectivity (far-side point → far point) | RESIDUE (inside `WindZeroExterior`) |
| Conclude `ExteriorWindingZero` | **DONE from `WindZeroExterior`** (`exteriorWindingZero_of_windZeroExterior`) |
| `ExteriorWindingZero → OffDiagDisjoint` | already in `PolygonWinding` (`offDiagDisjoint_of_windingSeparates`) |
| `→ unconditional artGallery_strict` | **NOT closed by this** (other oracle inputs remain; see scope correction) |

## Discipline

No codex/OpenAI tooling. Stayed on `main`, no commits, no branch switch, only created the NEW
file `PolygonWindingZero.lean`. Verified exclusively via rsync + `lake env lean`/`lake build` on
uisai1 (no local build on the Mac). Import graph / `Audit.lean` / `ProofsInTheBook.lean` left for
the orchestrator to wire. tmux build sessions killed; temp axiom-check files removed from the server.
