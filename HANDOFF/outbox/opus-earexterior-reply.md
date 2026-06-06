# opus-earexterior reply — Chapter-36 `EarInductionInput.earExteriorEven` via the det2-side of the ear chord: the residual ear field is collapsed to ONE named geometric residue (the interior parity-match), with the *entire* surrounding algebra + det2 geometry + ear-triangle simplicity/interior-parity PROVED, and `earExteriorEven` discharged from that residue for EVERY ray by pure (unconditional) split algebra

**Status: the last even-parity Jordan-localization field `earExteriorEven` is reduced to a
single named, non-vacuous, faithful residue `InteriorEarParityMatch` ("an interior ear
point is inside `P` exactly as it is inside its own ear triangle"), and DISCHARGED from it
for every ray with no side / non-degeneracy hypotheses.  From the residue the full
`EarInductionInput` is constructed (`earExteriorEven` supplied, not assumed), making
`PolygonJordan.polygonGeomResidue_of_earInput` input-free in the even field and giving the
Chapter-36 `⌊n/3⌋` headline conditional on exactly this ONE geometric residue + the
remaining cut data + `M`.  Everything else in the ear-exterior step — the exact parity
equivalence, the det2-side same-side geometry, the reversed-chord even pairing, the ear
triangle as a genuine `StrictSimplePolygon 3` (with a self-contained simplicity proof) and
its interior parity — is PROVED unconditionally, clean-3.  The residue itself is the
genuine general-`n` interior-odd Jordan content (no producer in the tree); the concrete
failing chain is pinned below.**

**File:** `ProofsInTheBook/PolygonEarExterior.lean` (FRESH, ~530 lines, the only file I own).
**Branch:** `main` (no switch, no commit; `git status` shows only `?? PolygonEarExterior.lean`).
**No codex / OpenAI tooling.  NEVER ran lake/lean on the Mac.**  Build dep:
`lake build ProofsInTheBook.PolygonJordan` → completed (8450 jobs).

## Verification (uisai1)

* `lake env lean ProofsInTheBook/PolygonEarExterior.lean` → **RC=0, no errors, no warnings**.
* `lake build ProofsInTheBook.PolygonEarExterior` → **"Build completed successfully (8451 jobs)"**, RC=0.
* **Mechanical (A):** 0 `sorry` / `admit` / `native_decide` / `axiom` in the file (only the
  docstring "No `sorry`/…" line and the word "axioms").
* **`#print axioms` (clean-3, ALL):** `earExteriorEven_of_parityMatch`,
  `earExteriorEven_iff_interiorOdd`, `parityMatch_of_convex`, `earTriSegSum_odd_of_valid`,
  `earInductionInput_of_parityMatch`, `isConvexVertex'_all_of_parityMatch`,
  `artGallery_strict_of_parityMatch`, `interiorEar_sameSide_v`, `earTri` →
  all **`[propext, Classical.choice, Quot.sound]`**.  No `sorryAx`, `ofReduceBool`, `native_decide`.

## The decisive structural finding (the exact content of `earExteriorEven`)

The crossing split `PolygonJordan.crossingNumber'_split_ear` is **unconditional for every
ray**: `CrossingNumber' P ρ x = segCross(a→v) + segCross(v→b) + restSum`.  Hence, mod 2,

```
segCross(a→b) + restSum  ≡  CrossingNumber' P ρ x  +  earTriSegSum
```
where `earTriSegSum = segCross(a→v) + segCross(v→b) + segCross(a→b)` is the directed-edge
sum of the ear triangle.  Therefore `earExteriorEven` (= `Even (segCross(a→b)+restSum)`)
holds **iff** `x` has the *same crossing parity* for the whole polygon `P` as for its ear
triangle.  This *parity match* IS the field — it is the textbook "the ear ⊆ the region of
`P`" localization, and (via the det2-side, below) it is equivalent to the interior odd seed
`Odd (CrossingNumber' P ρ x)`.

## What is PROVED here (unconditional, clean-3)

1. **The exact parity equivalence** `earExteriorEven_iff_interiorOdd` (vertex-avoiding ray):
   `Even (segCross a b + restSum) ↔ Odd (CrossingNumber' P ρ x)` — split + the local seed
   `triangle_segCross_sum_eq_one` + the reversal symmetry `segCross_symm`.  The genuine
   det2-side content of the field.

2. **The det2-side geometry of the ear chord** `diagSide_apex_ne_zero`,
   `interiorEar_diagSide_eq`, `interiorEar_sameSide_v`: the chord `(a,b)` lies on
   `{ y | diagSide a b y = 0 }`; the apex `v` is strictly off it (nondegenerate ear); an
   interior ear point `x = w0•a+w1•v+w2•b` has `diagSide x = w1·diagSide v` and so lies in
   the SAME open half-plane as `v` (`0 < diagSide x · diagSide v`).  Exactly "x interior to
   the ear ⟹ x, v on the same side of the chord line."

3. **The reversed-chord even pairing** `segCross_add_rev_even`: `Even (segCross a b +
   segCross b a)` for ANY direction (no off-line hypothesis — the half-open `Span` forces
   the relevant denominator nonzero).

4. **The ear triangle as a genuine `StrictSimplePolygon 3`** `earTri` (+ the self-contained
   `det2` segment-intersection-at-vertex lemma `seg_inter_seg_eq_vertex`): for `orient a v b
   ≠ 0`, `(a,v,b)` is a strict simple polygon (distinctness, consecutive noncollinearity,
   and the 3 cyclically-adjacent edge intersections).  From it,
   **`earTriSegSum_odd_of_valid`**: the ear-triangle directed-edge sum is odd for every ray
   direction valid on the triangle (the PROVED triangle interior count + `segCross_add_rev_even`).

5. **The discharge** `earExteriorEven_of_parityMatch`: the residue gives `earExteriorEven`
   for **every** ray, by *pure split algebra* — no side / non-degeneracy hypotheses, no ray
   transport.  This handles the all-rays quantifier (including vertex-aligned and
   chord-parallel directions) cleanly, because the split is unconditional.

6. **The full bundle** `earInductionInput_of_parityMatch` /
   `isConvexVertex'_all_of_parityMatch` / `artGallery_strict_of_parityMatch`: from the
   residue (+ the standard combinatorial orientation / ear-base diagonal / `n=3` base data
   the existing `EarInductionInput` already carries) the full `EarInductionInput` is built
   with `earExteriorEven` SUPPLIED, hence `polygonGeomResidue_of_earInput` is input-free in
   the even field and the Chapter-36 `⌊n/3⌋` headline is conditional on exactly this one
   residue + cut data + `M`.

## The single residue (named, non-vacuous, faithful)

`InteriorEarParityMatch ear` : for the chosen ear vertex of every polygon (`4 ≤ m`), every
ray `σ`, and a strict-interior ear point `x` off the boundary,
`CrossingNumber' P σ x % 2 = earTriSegSum P σ x (ear P) % 2`.

* **Faithful** (`parityMatch_of_convex`): a *consequence* of `IsConvexVertex'` at the ear
  vertex — an off-boundary interior ear point in the region has odd `CrossingNumber'`, and
  the bare-triple seed makes `earTriSegSum` odd too, so the parities match.  No hidden
  strengthening: the residue is satisfiable exactly when the region-level convex vertex is.
* **Non-vacuous:** gated `4 ≤ m`, with concrete content (the `earTri` interior parity #4 is
  the genuine `n=3` instance), and the constructed bundle carries the ear vertex verbatim
  (`earInductionInput_of_parityMatch_ear`).

## Concrete failing chain (the one place it dead-ends)

By #1, the residue is *logically equivalent* to `Odd (CrossingNumber' P σ x)` for an
interior ear point — the **general-`n` interior-odd seed**.  Producing it unconditionally
needs either (i) building the ear-deleted polygon as a genuine `StrictSimplePolygon (n-1)`
(`PolygonDiagonal.A4CuttingFacts.ear_delete_strict`, which has **no producer** anywhere in
the tree), or (ii) a base-point Jordan separation — but the substrate has **no
translate-the-base-point parity engine**: every parity-transport lemma
(`PolygonRayIndep`/`PolygonWallGlobal`/`PolygonGeneralWall`/`region_ray_independent`) varies
the *ray direction* at fixed `x`, never `x` itself.  The far-exterior even baseline
(`PolygonSeparation.exists_rayDir_crossingNumber'_eq_zero_of_not_mem_hull`) is for a
DIFFERENT point and cannot be transported to `x`.  The chain dead-ends precisely at this one
interior-odd membership for `P`; everything reachable from the ray-crossing substrate (the
split, the local seed, the reversal symmetry, the det2 same-side geometry, the ear-triangle
simplicity + interior parity, and the all-ray discharge) is PROVED above.  This is the same
verdict as the `opus-polygonjordan-reply` handoff and the prior independent analyses, now
pinned to a single parity-match residue with all surrounding algebra discharged.

## Precise residue (one line)

`InteriorEarParityMatch ear : ∀ P σ, 4≤m → ¬OnBoundary P x → (positive bary weights, x = ear
barycenter) → CrossingNumber' P σ x % 2 = earTriSegSum P σ x (ear P) % 2`
— equivalently `Odd (CrossingNumber' P σ x)` for an interior ear point — the general-`n`
interior-odd Jordan seed, the lone irreducible planar primitive of the ear step.

## Discipline

No codex / OpenAI tooling.  Stayed on `main`, no commits, no branch switch, zero
tracked-file modifications.  Created only the FRESH `PolygonEarExterior.lean` (leaf;
nothing imports it).  Verified exclusively via rsync + `lake env lean` / `lake build` /
`#print axioms` on `uisai1` (no local Mac build).  Import-graph / `Audit.lean` /
`ProofsInTheBook.lean` wiring left for the orchestrator.
