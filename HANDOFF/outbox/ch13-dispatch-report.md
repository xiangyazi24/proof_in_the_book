# Ch13 B1 final wave — dispatch report (`ZinanFFCT28.lean`)

Opus worker. New file: `ProofsInTheBook/ZinanFFCT28.lean`. Compiles 0 errors, clean-3 on all 5 main
results. No `sorry`/`axiom`/`admit`/`native_decide`. No other file touched. NOT committed.

## The interiorSupport inventory finding (settled FIRST, per honesty contract)

**There are two NON-interchangeable opening vocabularies, and the design's multi-rotation worry is
REAL.**

| | `openArm A θ` (FFCT26/27) | `openTail A K δ` (Monitored) |
|--|--|--|
| arm type | `Fin (n+1+1) → S2` | `Fin (n+1) → S2` |
| opening | last-joint | interior at `K = openingAxis k` |
| who rotates | **only** `Fin.last (n+1)` (one vertex) | **every** vertex `r` with `r.val > K.val` |
| support fn | `mixedSupport` = single-rotation `det3(Ai)(Aj)(rot k θ tail)` | `interiorSupport`/`supportConstraint` = `sOrient` of three `openTail` vertices |
| rotating args in a support | exactly 1 (the tail) | generally **2 or 3** |

`supportConstraint A K c θ = sOrient (openTail A K θ c.i)(openTail A K θ (c.i+1))(openTail A K θ c.j)`,
and `openTail A K δ r = rotS2 (A K) δ (A r)` for every `K.val < r.val`. So for a general non-incident
binding `(c.i, c.i+1, c.j)`, ANY of the three vertices with value `> K` rotates simultaneously.

**Consequence (the load-bearing finding):** FFCT26's `hasDerivAt_mixedSupport` differentiates exactly
ONE rotating argument (the tail). It does **NOT** apply to a general interior binding. Therefore the
derivative-based `hβ`/`hα` Gram-sign extraction (FFCT27 brick 5, `hbeta_of_axis_edge_binding`) is valid
**only** in the last-joint `openArm` vocabulary. For a general interior `supportConstraint = 0` binding,
the two Gram signs that `StuckAtKData`/`foldedFlat_of_support` require are a **genuine residue** — this
is precisely why the audit called the general normalization a "master". The single-rotation derivative
is not enough; the only FFCT26-compatible case is the axis-edge/tail case where one vertex moves.

File is structured around this answer: close the single-rotation (axis-edge) case fully; expose the
multi-rotation Gram-sign block as a named satisfiable residue.

## What CLOSED (unconditional, clean-3)

1. **`axis_edge_binding_false_of_positiveJoints`** (Brick 1, §3 of design). Axis-incident support
   binding at the last-joint opened arm `openArm A δ` (edge `(i,i+1)`, `i+1=n` the axis, far point =
   opened tail `Fin.last (n+1)`) with the `hβ` Gram sign and `0 < sphAngle (Aδ i)(Aδ (i+1))(Aδ last)`
   (the joint AT the axis apex) ⟹ `False`. Closed by instantiating FFCT27's
   `design_halpha_hyps_unsatisfiable` with `p=Aδ i, mid=Aδ (i+1) (apex), q=Aδ last`. The `sphAngle`
   argument order matches FFCT27 verbatim (angle at the MIDDLE arg = axis apex). `hsupp` is
   definitionally `det3 = 0` so it feeds `hcol` directly. **FAITHFUL** — genuine axis-edge
   impossibility, hypotheses individually satisfiable (FFCT27's own guard), contradiction from the
   conjunction.

2. **`acoef_nonneg_of_axis_edge_binding`** (Brick 2, §4). The `exfalso` companion interface: given the
   brick-1 `False`, the span coefficient `a ≥ 0` is vacuously available via `False.elim`. Honest form —
   does not fabricate a witness sign that would hide the stronger contradiction. (Needed `hi_axis`
   added so the `Fin` bounds elaborate.)

3. **`supportBinding_dispatch`** (Brick 3a, §7). The genuine non-vacuous case split: `c.1.1+1 =
   (openingAxis k).val ∨ ≠`. Exhaustive `em` of a decidable equation; both branches reachable.

4. **`interior_support_betweenness_of_gramSigns`** (Brick 3b, §10 consumer side). The load-bearing
   UNCONDITIONAL wiring: from an interior vanishing support `sOrient (Aδ i)(Aδ (i+1))(Aδ j) = 0`, the
   edge short arc, and the two Gram signs at `Aδ = openTail A K δ`, produce
   `Aδ i ∈ span≥0 {Aδ(i+1), Aδ j}` — the exact `FoldedFlatCutTransportPlus` input. Lands via
   `foldedFlat_of_support`. Takes the Gram signs as inputs (= the residue).

5. **`supportStuck_dispatch_partial`** (Brick 3d, §10 skeleton). From a STUCK binding
   (`supportConstraint A (openingAxis k) c δ* = 0`) + the named residue
   `GramSignsAtInteriorBinding A (openingAxis k) δ* c`, assemble the folded-flat betweenness. Unfolds
   `supportConstraint → sOrient` (`supportConstraint_apply`) and routes through brick 3b. No fold
   geometry faked. **CONDITIONAL-honest** on the multi-rotation Gram-sign residue.

## The named residue (the honest block)

`GramSignsAtInteriorBinding A K δ c : Prop` — a conjunction of the edge short arc and the two Gram
inequalities of the opened triple `(c.i, c.i+1, c.j)` at `openTail A K δ`. This is **exactly** the
input the betweenness consumer needs and **exactly** what the single-rotation derivative cannot supply
for a general interior opening (the inventory finding). It is satisfiable (short arc + two genuine
inner-product inequalities; non-trivial conjunction, not `True`).

## Residues / next bricks (not in this file's scope)

- **Producing `GramSignsAtInteriorBinding` for a general interior binding** — the master normalization.
  Needs either a multi-rotation derivative form (FFCT26's single-rotation `hasDerivAt_mixedSupport` does
  not cover it) or a reduction showing only the axis-edge/tail case can bind at `δ*`. This is the real
  remaining mathematical block.
- Wiring the dispatch into the trichotomy STUCK branch end-to-end (the `Stuck` predicate's first
  disjunct is `∃ c, supportConstraint ... = 0`, directly feeding `supportStuck_dispatch_partial`).
- The non-axis-branch fold-data extraction → `FoldedFlatCutTransportPlus`/`far_fold_..._final`.

## Non-vacuity guards

Every conditional brick carries a playbook §3.3 guard (all compiled): sphAngle-nonneg building block
for Brick 1, the exhaustive `em` for 3a, a genuine flat `span≥0` membership for 3b/3d, and the residue
shape (non-trivial conjunction) for `GramSignsAtInteriorBinding`.

## Verification

- `lake env lean ProofsInTheBook/ZinanFFCT28.lean` → 0 errors.
- `lake build ProofsInTheBook.ZinanFFCT28` → built (8487 jobs).
- `#print axioms` on all 5 main results → `[propext, Classical.choice, Quot.sound]` (clean-3, no
  `sorryAx`/`ofReduceBool`).
