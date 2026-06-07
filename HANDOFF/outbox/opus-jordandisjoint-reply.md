# opus-jordandisjoint reply — `OffDiagDisjoint` attacked DIRECTLY (the planar Jordan core)

**Status: HONEST PARTIAL — the direct attack is driven to genuine exhaustion, and the
result is a *sharpened* obstruction + the precisely-pinned irreducible residue.**
Both prescribed direct routes (the crossing-count engine and the det2-side of the
diagonal line) are ground out; this round proves *why each fails as a theorem* (one of
them strictly stronger than any prior negative result), isolates the residue as ONE named
non-vacuous `Prop` faithful to `OffDiagDisjoint`, and records the concrete failing chain
end to end. Clean-3, 0 sorry/axiom/admit/native_decide.

**File:** `ProofsInTheBook/PolygonJordanDisjoint.lean` (NEW, the only file I own, ~270 lines).
**Branch:** `main` (uisai1). No commits, no branch switch, no tracked-file modification
by me (the lone `ProofsInTheBook.lean` diff — `+import …SphericalArmFinish` — was already
in the working tree before this session and is unrelated to polygons; I left it untouched).
**Server:** uisai1. **No codex / OpenAI tooling. NEVER ran lake/lean on the Mac.**
**Build dep:** `lake build ProofsInTheBook.PolygonEarDelete` → *Build completed (8452 jobs)*.
**Verification (uisai1):** `lake env lean ProofsInTheBook/PolygonJordanDisjoint.lean` → **RC=0**;
`lake build ProofsInTheBook.PolygonJordanDisjoint` → *Built (8447/8447)*.

---

## What `OffDiagDisjoint` actually is, and the circularity I confirmed first

`OffDiagDisjoint g` (off all three boundaries) = `¬ (in_L ∧ in_R)`. The "derivations" in
the existing chain are **circular**: `PolygonContainment.offDiagDisjoint_of_cutGeometry`
pulls it out of `CutGeometry.split_region_intersection`, which is populated by
`PolygonOracleClose.cutGeometry_of_data` *from the `ResidualGeometryData.disjoint`/
`.intersection` fields* — i.e. from `OffDiagDisjoint` itself. So at the bottom of the
stack `OffDiagDisjoint` is a genuine **oracle input** (the `disjoint` field), exactly as
the spec said. The direct attack must produce it without that field.

## Route 1 — the crossing-count engine: PROVABLY insufficient (sharpened past prior work)

The substrate's full count datum per off-boundary point is **not** just the parity XOR;
it is the *integer* identity `cP + 2·d = cL + cR` (`crossingNumber'_split_identity_common`,
`d = diagCount`). I verified at arc-level that `cP = aL + aR`, `cL = aL + d`, `cR = aR + d`
(parent edges = both arcs, diagonal counted once per side), so the integer identity is the
sharpest count fact available. The new theorems:

* **`intCount_admits_both_inside (d)`** — for *every* `d`, `∃ cP cL cR`,
  `cP + 2d = cL + cR ∧ Odd cL ∧ Odd cR ∧ Even cP`. Witness `cL = 2d+1, cR = 1, cP = 2`.
  **This is strictly stronger than `PolygonCutClose.parity_admits_both_inside`**: it shows
  the both-inside admissibility is *not* an artefact of forgetting `d` — the genuine
  over-`ℤ` bookkeeping is equally blind, because `2d` cancels against `Odd cL + Odd cR`.
  (`#print axioms` → `[propext]`, the cleanest possible.)
* **`count_engine_admits_both_inside (d)`** — the conjunction of *everything* the count
  machinery delivers (the parity XOR *and* the integer identity) holds at a both-inside
  assignment. So no combination of the substrate's count facts excludes both-inside.
* **`offDiagDisjoint_unprovable_from_count`** — region-level corollary: the off-boundary
  XOR `region_symmDiff_pieces` admits both-inside.

**Verdict (Route 1): the count engine cannot prove `OffDiagDisjoint`, at parity OR integer
granularity — now a theorem, sharper than any prior round.**

## Route 2 — the det2-side of the diagonal *line*: the geometric skeleton, and the exact gap

I re-derived (locally, importing only `PolygonContainment`'s closure) the diagonal-line
side function `lineSide` and its unconditional facts: both endpoints on the line
(`lineSide_left`/`_right`), affineness (`lineSide_lineMap`), and the **chord segment ⊆ line**
(`lineSide_eq_zero_of_mem_seg`). Then the precise obstruction:

* **`lineSide_blind_to_chord_endpoints`** — `lineSide P j i x = - lineSide P i j x`: the
  line-side is the same affine functional up to orientation sign, with zero set the *whole
  infinite line*. It carries **no** datum distinguishing the chord *segment* from its
  complementary segments on the same line. Hence the bridge Route 2 needs —
  *`x ∈ region_L ⟹ x has L's fixed line-side sign`* — **cannot** be a substrate theorem:
  `region_L` is the parity region of a possibly **non-convex** ear whose interior straddles
  the chord's infinite line (a dent reaching across), so it has interior points of *both*
  signs. The only separating datum is membership of the chord *segment*, which the affine
  `det2`-sign does not encode.

**Verdict (Route 2): the det2 line-side routes through the chord *segment* (the Jordan
content), not the line — proved, not asserted.** (This matches `PolygonFinish.
dirComparable_forces_det2_eq` blocking the straight-segment route, now pinned to the
segment-vs-line blindness at point level.)

## The precise minimal residue (ONE named non-vacuous Prop + the failing chain)

* **`ChordSeparates g`** := `OffDiagDisjoint g` — the literal planar Jordan chord
  separation, **definitionally equal** to `OffDiagDisjoint`
  (`chordSeparates_eq_offDiagDisjoint : … = … := rfl`), so it is neither a strengthening
  nor a weakening — the honest irreducible residue.
  * `offDiagDisjoint_of_chordSeparates` / `chordSeparates_of_offDiagDisjoint` — two-way
    reduction.
  * `chordSeparates_nonvacuous` — satisfiable exactly when a `CutGeometry` exists (§3.3
    anti-vacuity), inherited from `offDiagDisjoint_of_cutGeometry`.
  * `chordSeparates_iff_containment_pointwise` — re-confirms, at this file's level, that
    the count engine reduces `OffDiagDisjoint` *exactly* to sub-region containment
    (`PolygonCutClose.offDiag_disjoint_iff_subRegion_containment`) and **no further**.

**The concrete failing chain (recorded in the file header):**
```
  region_symmDiff_pieces      : in_P ↔ (in_L ↔ ¬in_R)        (count, parity) — stops at both-inside
  crossingNumber'_split_identity_common : cP + 2d = cL + cR  (count, integer) — stops at both-inside
        ⟹ intCount_admits_both_inside / count_engine_admits_both_inside
  lineSide                    : = -lineSide (orientation flip) (det2 line-side) — blind to the segment
        ⟹ lineSide_blind_to_chord_endpoints  (no fixed-sign bridge for a non-convex ear)
  ChordSeparates ( = OffDiagDisjoint ) : the irreducible planar Jordan residue
```

## Honest mathematical conclusion

`OffDiagDisjoint` is **not** derivable from the crossing-count engine (proved, over ℤ — the
strongest count datum) nor from the affine diagonal-line side (proved — blind to the chord
endpoints). It is the genuine Jordan separation of a chord: the diagonal *segment* is the
shared boundary of the two ear-domains, and a point inside both would have to cross that
shared boundary — a Jordan-curve-theorem fact for the ear that the substrate does **not**
carry in point-applicable form (the per-point `rawInd`/parity is global-topology-free; the
`det2` sign is segment-blind). A full discharge requires either a Jordan curve theorem for
the ear domain (separation by the chord) or a winding-number development with a probe ray
whose intersection with the chord segment is tracked over ℤ with position information — both
beyond what the leaf substrate exposes. The residue is correctly carried as the `disjoint`
field of `ResidualGeometryData`; this round proves that is *forced*, sharply.

## Verification (playbook §3 acceptance)

* **A (mechanical):** 0 sorry/admit/axiom/native_decide (only `:= rfl` is the faithfulness
  certification `chordSeparates_eq_offDiagDisjoint`, documenting `ChordSeparates =
  OffDiagDisjoint`). `lake env lean …` → RC=0; olean built (8447 jobs).
* **`#print axioms` (clean-3):**
  * `intCount_admits_both_inside` → `[propext]` (cleanest)
  * `count_engine_admits_both_inside` → `[propext, Classical.choice, Quot.sound]`
  * `lineSide_blind_to_chord_endpoints` → `[propext, Classical.choice, Quot.sound]`
  * `lineSide_eq_zero_of_mem_seg` → `[propext, Classical.choice, Quot.sound]`
  * `chordSeparates_nonvacuous` → `[propext, Classical.choice, Quot.sound]`
  * `offDiagDisjoint_of_chordSeparates` → `[propext, Classical.choice, Quot.sound]`
  * `chordSeparates_iff_containment_pointwise` → `[propext, Classical.choice, Quot.sound]`
* **B/C (signature/semantic):** `ChordSeparates` is definitionally `OffDiagDisjoint`
  (faithful, non-vacuous, certified both ways); the negative theorems are non-vacuous
  (they exhibit concrete witnesses, not unsatisfiable premises). **Verdict:
  CONDITIONAL-honest** — `OffDiagDisjoint` remains the irreducible planar Jordan residue
  `ChordSeparates`; the two direct routes are *proved* insufficient (the Route-1 negative
  result is strictly sharper than the prior parity-only one).

## Precise residue (what the next round needs)

`ChordSeparates` ( = `OffDiagDisjoint`, = the `ResidualGeometryData.disjoint`/`.intersection`
fields). To discharge it requires a *genuine Jordan separation* of the chord segment — not
available from per-point ray-parity (segment-blind) or affine `det2`-sign (line, not
segment). The minimal new substrate needed: a winding/degree argument that tracks the
probe ray's signed intersection with the chord *segment* with position (so `d` becomes a
position-aware separating datum), or a Jordan-curve-theorem instance for the ear domain.
This round establishes that *nothing weaker* (no count identity, no affine line-side) can
do it.

## Discipline

No codex/OpenAI tooling. Stayed on `main`, no commits, no branch switch, only created the
NEW file `PolygonJordanDisjoint.lean` (the `ProofsInTheBook.lean` SphericalArmFinish import
was pre-existing, not mine). Verified exclusively via rsync + `lake env lean` / `lake build`
on uisai1 (no local build on the Mac). Import graph / `Audit.lean` / `ProofsInTheBook.lean`
left for the orchestrator to wire.
