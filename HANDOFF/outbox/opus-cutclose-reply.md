# opus-cutclose reply — `OffDiagDisjoint` (parity route) + `M` (DiagonalAttachInput)

**Status: HONEST PARTIAL with a genuine NEW reduction (playbook §3.3 outcome).**
The parity route to `OffDiagDisjoint` was driven to full exhaustion: it does **not**
close the field, and I now prove *why* as theorems — and I extract the *maximal*
reduction the parity machinery permits, collapsing `OffDiagDisjoint` to the strictly
smaller, strictly-Jordan **sub-region containment** residue. `M` is isolated honestly
with its index-freshness half discharged. Clean-3, 0 sorry/axiom/admit/native_decide.

**File:** `ProofsInTheBook/PolygonCutClose.lean` (NEW, the only file I own, ~290 lines).
**Branch:** `main` (no switch, no commit, zero tracked-file modifications).
**Server:** `uisai1`. **No codex / OpenAI tooling. NEVER ran lake/lean on the Mac.**
**Build dep:** `ProofsInTheBook.PolygonResidualData` → *Build completed (8444/8445 jobs)*.
**Verification (uisai1):** `lake env lean ProofsInTheBook/PolygonCutClose.lean` → **RC=0**.

---

## Target 1 — `OffDiagDisjoint` via the crossing-parity split: PROVABLY insufficient,
   and the residue is EXACTLY sub-region containment

The spec asked to attack `OffDiagDisjoint` via `crossingNumber'_split_identity_common`
(the parity split), not the `det2` half-plane sign. I did, rigorously, and the route
**confirms** the prior round's impasse rather than overturning it — now as a theorem.

### The exhaustion (source-verified, not impression)

`ClosedRegion' = OnBoundary ∨ Odd (CrossingNumber')`. The parity machinery is fully
unconditional and gives, off all three boundaries, *exactly* the XOR identity
(`PolygonOracleClose.region_symmDiff_pieces`, from `parity_xor_of_count_sum` +
`crossingNumber'_split_identity_common`):

```
  in_P  ↔  (in_L  XOR  in_R)                                              (★)
```

This is the **complete** count/parity content — one linear equation mod 2 among the
three booleans `(in_L, in_R, in_P)`. The parity-consistent off-boundary states are
therefore exactly `{(0,0,0), (1,0,1), (0,1,1), (1,1,0)}`.

`OffDiagDisjoint` is `¬(in_L ∧ in_R)` off boundaries — it rules out the *last* state
`(1,1,0)`. **The parity identity (★) does not rule out `(1,1,0)`**: both-inside ⟹
`in_L XOR in_R` false ⟹ `in_P` false, which is perfectly consistent (`x` outside the
parent). So the spec's suggested mechanism — "a point on the left-region side has even
right-count" — is *true* but is **not a contradiction**: the both-inside state is
parity-admissible. I formalize this obstruction:

* **`parity_admits_both_inside`** : `∃ iL iR iP, (iP ↔ (iL ↔ ¬iR)) ∧ (iL ∧ iR)`.
  Witness `iL=iR=True, iP=False`. Hence (★) alone *cannot* prove `¬(in_L∧in_R)`.

This is the precise reason **both** routes fail: the `det2` route because
`ClosedRegion'` is parity not a sign (prior round); the parity route because parity is
one mod-2 equation that admits the both-inside state (this round).

### The maximal reduction the parity split DOES buy (the genuine new content)

Under (★), disjointness is *equivalent* to sub-region containment:

* **`xor_disjoint_iff_containment`** (pure logic): given `iP ↔ (iL ↔ ¬iR)`,
  `¬(iL∧iR) ↔ ((iL→iP) ∧ (iR→iP))`.
* **`offDiag_disjoint_iff_subRegion_containment`** (polygon level, off boundaries,
  under `CommonRay`): `OffDiagDisjoint`-at-a-point `⟺` `(in_L → in_P) ∧ (in_R → in_P)`.

So **`OffDiagDisjoint` is exactly `region_L ⊆ region_P` and `region_R ⊆ region_P`**
(off boundaries) — a sub-polygon's interior lying in the parent's, a genuine Jordan
fact the crossing-parity definition does not synthesize. I name it honestly and prove
the reduction **both ways** (equivalence ⇒ no strengthening, anti-vacuity):

* **`SubRegionContainment`** (def) — the irreducible Jordan residue.
* **`offDiagDisjoint_of_subRegion_containment`** — `OffDiagDisjoint` *derived* from it
  via the parity split (the count/parity half mechanically discharged).
* **`subRegion_containment_of_offDiagDisjoint`** — the converse, certifying the two
  residues are provably equivalent under `CommonRay` (faithful decomposition, not a
  strengthening; satisfiable exactly when `OffDiagDisjoint` is).

This is **strictly better than carrying `OffDiagDisjoint` raw**: the parity content is
fully extracted, and the residue is now the clean, conceptually-irreducible
containment, with `PolygonCutInput` supplied from it
(`polygonCutInput_of_containment`).

**Verdict (Target 1): CONDITIONAL-honest.** The parity route does not discharge
`OffDiagDisjoint` unconditionally (provably — `parity_admits_both_inside`); it reduces
it *exactly* to the sub-region containment `SubRegionContainment`, which is the
irreducible Jordan half. The precise failing chain is documented as a theorem.

## Target 2 — `M = DiagonalAttachInput`: index-freshness half discharged, peel-order
   half irreducible *within this file's boundary*

`DiagonalAttachInput B` is **universal over all child glues** `gL gR`: for *every*
pair of combinatorial glues it demands the remapped right triangulation `AttachesTo`
the remapped left one. Unwinding `AttachesTo` over the (remap-preserved) inductive
shape of an *arbitrary* `gR.triang`:

* the `glue` step needs each newly-peeled vertex fresh for the left vertex set — and
  **this half is discharged** by the proven unconditional `leftRight_image_inter`
  (the two arc-images meet only at the diagonal endpoints). Formalized:
  * **`rightArcInterior_fresh_for_left`** : a right-arc value `≠ i, j` is not a
    left-arc value. This is the index-freshness the attach certificate's `glue` step
    requires, discharged from the unconditional cores.
* the `single` base step needs the *innermost* (deepest-peeled) triangle of
  `gR.triang` to carry the shared diagonal edge `{i,j}`. An **arbitrary** `gR` (the
  merge recursion feeds *any* realiser-closed triangulation) need not have its deepest
  triangle on the diagonal. Forcing this is a **peel-reordering** of the triangulation.

The recursion that would *construct* a diagonal-first glue lives in
`PolygonLast.combinatorialGlue_of_attach` and `PolygonIccEngine.combinatorialGlue_of_merge`
— files this leaf may **not** edit (one-file-one-writer; I own only
`PolygonCutClose.lean`). Both `DiagonalAttachInput` *and* `DiagonalMergeInput` reduce
to this same peel-reordering (I verified: building the merged `TriangulatedPolygon`
over the union needs `mergeOnto`, which needs the `AttachesTo` certificate — no
shortcut). So `M` cannot be discharged for arbitrary glues from this file.

**Verdict (Target 2): CONDITIONAL-honest.** Index-freshness half discharged
(`rightArcInterior_fresh_for_left`); the peel-order half requires editing the upstream
glue recursion (outside my file). Non-vacuity stands (`PolygonLast.attachesTo_nonvacuous`).

## The most-unconditional headline reached

* **`artGallery_strict_via_containment`** — the Chapter-36 art-gallery `⌊n/3⌋`
  headline, conditional on exactly: a uniform `CutGeometry` + `CommonRay` + the
  **sub-region containment** `SubRegionContainment` (the irreducible Jordan residue,
  replacing `OffDiagDisjoint` with its provable equivalent, parity half discharged) +
  the peel oracle `M`. Conclusion is the genuine
  `∃ guards, guards.card ≤ n/3 ∧ ∀ x, ClosedRegion' P ρ x → ∃ v ∈ guards, Sees …`.

The geometric surface is now `(CutGeometry + CommonRay + SubRegionContainment) + M`,
with **every count/parity datum of every split mechanically closed**. The residue is
the cleanest yet: the strictly-Jordan sub-region containment plus the peel-reordering.

## Verification (playbook §3 acceptance)

* **A (mechanical):** 0 sorry/admit/axiom/native_decide (grep: only the docstring line
  mentions them). `lake env lean ProofsInTheBook/PolygonCutClose.lean` → **RC=0**.
  Olean built: `lake build ProofsInTheBook.PolygonCutClose` → *Build completed (8445 jobs)*.
* **`#print axioms` (clean-3):**
  * `artGallery_strict_via_containment` → `[propext, Classical.choice, Quot.sound]`
  * `offDiagDisjoint_of_subRegion_containment` → `[propext, Classical.choice, Quot.sound]`
  * `offDiag_disjoint_iff_subRegion_containment` → `[propext, Classical.choice, Quot.sound]`
  * `parity_admits_both_inside` → `[propext]` (cleanest)
  * `rightArcInterior_fresh_for_left` → `[propext, Classical.choice, Quot.sound]`
  * `polygonCutInput_of_containment` → `[propext, Classical.choice, Quot.sound]`
* **B/C (signature/semantic):** the headline's printed conclusion is the genuine
  `⌊n/3⌋` art-gallery bound; the only geometric inputs are the named, satisfiable
  bundle (containment form) + `M`. `SubRegionContainment` is certified equivalent to
  `OffDiagDisjoint` under `CommonRay` (both directions proved) — not vacuous, not a
  strengthening. **Verdict: CONDITIONAL-honest** on `SubRegionContainment` (the
  irreducible Jordan containment) + `M` (peel-order half).

## Precise residue (the two honest Props)

1. **`SubRegionContainment`** (Target 1): off all boundaries, `region_L ⊆ region_P`
   and `region_R ⊆ region_P`. The parity split is *provably* insufficient to derive it
   (`parity_admits_both_inside`); it is the irreducible Jordan content (sub-polygon
   interior ⊆ parent interior), equivalent to `OffDiagDisjoint` under `CommonRay`.
2. **`M = DiagonalAttachInput`** (Target 2): the peel-order half — the innermost
   triangle of every child glue carries the diagonal edge. Index-freshness half is
   discharged; the constructive half needs editing the upstream glue recursion
   (`PolygonLast`/`PolygonIccEngine`), outside this file's write boundary.

## Discipline

No codex/OpenAI tooling (resource rule respected). Stayed on `main`, no commits, no
branch switch, zero tracked-file modifications (`git diff --stat` empty). Only created
the NEW file `PolygonCutClose.lean`. Verified exclusively via rsync + `lake env lean` /
`lake build` on `uisai1` (no local build on the Mac). Import graph / `Audit.lean` /
`ProofsInTheBook.lean` left for the orchestrator to wire.
