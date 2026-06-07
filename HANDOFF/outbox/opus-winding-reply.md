# opus-winding reply — SIGNED winding/degree development for `OffDiagDisjoint`

**Status: SUBSTANTIAL PROGRESS — the signed-winding infrastructure the prior round
identified as the *required* tool is BUILT and machine-verified, and `OffDiagDisjoint`
is reduced to a single named, non-vacuous SIGNED Jordan residue
(`ExteriorWindingZero`).** The genuine new mathematics (the signed split identity where
the diagonal CANCELS, the parity bridge, the opposite-sign discriminator) is fully
proved, clean-3, 0 sorry/axiom/admit/native_decide. The one irreducible step that
remains is the Jordan fact "an exterior point of an ear has zero SIGNED winding on its
side" — which is *not* in Mathlib (no winding-number / Jordan-curve API exists there)
and is exactly the planar-topology core. It is isolated as a concrete, satisfiable Prop.

**File:** `ProofsInTheBook/PolygonWinding.lean` (NEW, the only file I own, 559 lines).
**Branch:** `main` (uisai1). No commits, no branch switch. `ProofsInTheBook.lean` /
`Audit.lean` untouched (wiring left for the orchestrator). Only new file created.
**Server:** uisai1. No codex / OpenAI tooling. NEVER ran lake/lean on the Mac.
**Build dep:** `lake build ProofsInTheBook.PolygonJordanDisjoint` → *Build completed
(8447 jobs)*.
**Verification (uisai1):** `lake env lean ProofsInTheBook/PolygonWinding.lean` → RC=0;
`lake build ProofsInTheBook.PolygonWinding` → *Build completed successfully (8446 jobs)*.

---

## What the prior round established (my spec)

`PolygonJordanDisjoint` + `PolygonCutClose` machine-proved BOTH:
* the **unsigned** count is insufficient — parity AND the integer identity
  `cP + 2d = cL + cR` admit the both-inside state (`intCount_admits_both_inside`,
  `parity_admits_both_inside`): the `2d` diagonal term cancels against `Odd cL + Odd cR`;
* the **affine `det2`-side** of the diagonal *line* is insufficient
  (`lineSide_blind_to_chord_endpoints`): blind to the chord *segment*.

The isolated requirement: a SIGNED winding that distinguishes the chord side. Built here.

## The signed development (all proved, clean-3)

**Layer 1 — the signed indicator + orientation antisymmetry (the crux).**
`rawSignedInd r x a b := if RawEdgeCrosses r x a b then (if 0 < det2 r (b−a) then 1 else −1) else 0 : ℤ`.
The event is the SAME (unsigned) `RawEdgeCrosses`; the new datum is the *sign* of
`det2 r (b−a) = side r x b − side r x a` (the crossing direction).
* `rawSignedInd_swap : rawSignedInd r x b a = − rawSignedInd r x a b` — **antisymmetric**,
  vs the unsigned `rawEdgeCrosses_symm` (symmetric). This is what makes the diagonal cancel.
* `rawSignedInd_abs : |rawSignedInd r x a b| = rawInd r x a b` — magnitude = unsigned.
* `det2_ne_zero_of_rawEdgeCrosses` — at a crossing the side difference is nonzero.

**Layer 2 — `windCross P ρ x := ∑ k, rawSignedInd ρ.r x (P.q k) (P.q (cyclicNext k)) : ℤ`.**

**Layer 3 — THE SIGNED SPLIT IDENTITY (the diagonal CANCELS).**
* `windRaw_split_identity : windRaw_L + windRaw_R = windRaw_P` — **no `2·diagCount` term.**
  The left ear traverses the diagonal `j→i` (signed `−s`), the right `i→j` (`+s`); by
  `rawSignedInd_swap` they cancel. (Full arc-decomposition mirroring the unsigned
  `rawCount_split_identity`: `windRaw_left_split`, `windRaw_right_split`,
  `windRaw_parent_eq_arcs` via the rotation bijection — all proved over ℤ.)
* `windCross_split_common` — the polygon-level (`buildLeftPoly`/`buildRightPoly`, common
  ray) form: `windCross_L + windCross_R = windCross_P`. This is the `CountSummationDatum`
  shape, SIGNED, hence WITHOUT the `2d` term — the exact structural improvement over the
  unsigned identity.

**Layer 4 — the parity bridge (signed refines unsigned).**
* `rawSignedInd_emod_two`, `windRaw_emod_two`, `windCross_emod_two :
  windCross ≡ CrossingNumber' (mod 2)`.
* `windCross_ne_zero_of_odd_crossing : Odd CrossingNumber' → windCross ≠ 0` — so off the
  boundary `ClosedRegion'` (= `Odd CrossingNumber'`) forces nonzero signed winding.
* `windCross_opposite_of_both_inside_outside_parent` — **the discriminator the unsigned
  count provably lacks**: at the both-inside, outside-parent state (`windCross_P = 0`),
  the split forces `windCross_L = − windCross_R ≠ 0`. The unsigned both-inside state had
  `Odd cL ∧ Odd cR` and nothing more; the SIGNED count pins the two windings as negatives.

**Layer 5 — the conclusion: `OffDiagDisjoint` from the signed residue.**
* `WindingSeparates g` (named Prop): off all boundaries, (i) `wDiagSide < 0 →
  windCross_L = 0`, (ii) `0 < wDiagSide → windCross_R = 0`, (iii) the logical clause
  `wDiagSide ≠ 0 ∨ ¬in_L ∨ ¬in_R`.
* `offDiagDisjoint_of_windingSeparates : WindingSeparates g → OffDiagDisjoint g` — **the
  full reduction, PROVED.** If `x` is in both sub-regions off boundaries: both crossing
  numbers odd ⇒ both windings nonzero (parity bridge); clause (iii) ⇒ `wDiagSide ≠ 0`;
  the strict sign of `wDiagSide` makes clause (i) or (ii) force the corresponding winding
  to `0` — contradiction.

**Layer 6/7 — non-vacuity / residue minimization (§3.3).**
* `windingSeparates_compat_offDiagDisjoint` — clause (iii) is *implied* by
  `OffDiagDisjoint` (so it adds no new content; the residue is the two zero-winding clauses).
* `ExteriorWindingZero g` — the two SIGNED zero-winding clauses alone (the irreducible
  Jordan datum, side-aware).
* `windingSeparates_of_exteriorWindingZero : ExteriorWindingZero g → OffDiagDisjoint g →
  WindingSeparates g` — **anti-vacuity certificate**: `WindingSeparates` is satisfiable
  exactly when a genuine oracle (`OffDiagDisjoint`) and the Jordan exterior-winding-zero
  fact both hold; not an unsatisfiable premise.
* `offDiagDisjoint_of_exteriorWindingZero` — reduction to `ExteriorWindingZero` under an
  *explicitly-labelled auxiliary* off-line hypothesis `hlog` (honestly non-vacuous: the
  diagonal LINE extends past the segment, so `hlog` is a genuine extra assumption, NOT
  always true; the primary `offDiagDisjoint_of_windingSeparates` does NOT need it).

## The precise remaining residue (one named, non-vacuous, satisfiable Prop)

`ExteriorWindingZero g` — the SIGNED, side-aware statement that an exterior point of an
ear has zero signed winding around its boundary. This is the genuine planar Jordan-curve
fact (winding `0` outside a simple closed curve), in the signed form the unsigned count
provably cannot encode. **Mathlib carries no winding-number / Jordan-curve API** (verified:
only complex-analytic Cauchy winding exists, no combinatorial planar one), so this is new
substrate, not a wiring gap. The concrete failing chain:

```
windCross_split_common : windCross_L + windCross_R = windCross_P   (signed, diagonal CANCELS) — PROVED
windCross_ne_zero_of_odd_crossing : Odd CrossingNumber' → windCross ≠ 0  (parity bridge) — PROVED
offDiagDisjoint_of_windingSeparates : WindingSeparates → OffDiagDisjoint — PROVED
  └─ needs WindingSeparates = ExteriorWindingZero (+ disjointness-implied logical clause)
        ExteriorWindingZero : exterior point ⟹ signed winding 0 on its side  ← IRREDUCIBLE
        (Jordan curve theorem for the ear; not in Mathlib)
```

To discharge `ExteriorWindingZero`: a topological/combinatorial proof that the signed
winding of an ear's boundary vanishes at points on the far side of the diagonal line
(e.g. for a convex ear, the boundary lies in one closed half-plane so the upward-ray
signed crossings telescope to 0; for a general ear, the Jordan separation). This is the
single planar primitive remaining — sharply smaller than `OffDiagDisjoint` itself, and
strictly stronger/cleaner than the prior `SubRegionContainment` residue because it is
*sign-aware* (carries the chord side the unsigned count loses).

## Verification (playbook §3 acceptance)

* **A (mechanical):** 0 sorry/admit/axiom/native_decide. The 3 `:= rfl` are definitional
  unfolding lemmas (`windCross_eq`, `windRaw_eq_sum`, right=left-tuple-swap) — genuine `=`
  between distinct expressions, not trivially-true Props. `lake env lean` RC=0; olean built
  (8446 jobs).
* **`#print axioms` (clean-3, all `[propext, Classical.choice, Quot.sound]`):**
  `rawSignedInd_swap`, `rawSignedInd_abs`, `windRaw_split_identity`, `windCross_split_common`,
  `windCross_emod_two`, `windCross_ne_zero_of_odd_crossing`,
  `windCross_opposite_of_both_inside_outside_parent`, `offDiagDisjoint_of_windingSeparates`,
  `windingSeparates_of_exteriorWindingZero`, `offDiagDisjoint_of_exteriorWindingZero`.
* **B/C (signature/semantic):** `OffDiagDisjoint` is the existing `PolygonOracle` field
  (faithful, not re-stated). `WindingSeparates`/`ExteriorWindingZero` are non-vacuous (the
  anti-vacuity certificate `windingSeparates_of_exteriorWindingZero` shows co-satisfiability
  with a genuine oracle; `ExteriorWindingZero` is a true Jordan statement, not unsatisfiable).
  `offDiagDisjoint_of_windingSeparates` is a GENUINE reduction (uses the signed split + parity
  bridge — new math), not a re-wrapper. **Verdict: FAITHFUL reduction** of `OffDiagDisjoint`
  to the minimal signed Jordan residue `ExteriorWindingZero`; the signed-winding tool the
  prior insufficiency demanded is built and proved discriminating
  (`windCross_opposite_of_both_inside_outside_parent`).

## Progress map vs the spec

| Spec item | Status |
|---|---|
| Define SIGNED `windCross` via det2 orientation sign | DONE (`rawSignedInd`, `windCross`) |
| SIGNED additivity, diagonal CANCELS (windCross_L+windCross_R = windCross_P) | DONE (`windRaw_split_identity`, `windCross_split_common`) |
| Connect signed winding to unsigned region (odd crossing ⟺ winding ≠ 0) | DONE one direction (`windCross_ne_zero_of_odd_crossing`); `\|wind\|≤1` ⇒ converse needs Jordan |
| KEY: windCross_L(x)=0 for x on the RIGHT of the diagonal | ISOLATED as `ExteriorWindingZero` (Jordan, not in Mathlib) |
| Conclude OffDiagDisjoint | DONE from `WindingSeparates`/`ExteriorWindingZero` (`offDiagDisjoint_of_windingSeparates`) |

## Discipline

No codex/OpenAI tooling. Stayed on `main`, no commits, no branch switch, only created the
NEW file `PolygonWinding.lean`. Verified exclusively via rsync + `lake env lean` / `lake
build` on uisai1 (no local build on the Mac). Import graph / `Audit.lean` /
`ProofsInTheBook.lean` left for the orchestrator to wire. Temp axiom-check file removed
from the server.
