# Ch36 sign-sync worker bricks — report

File: `ProofsInTheBook/ZinanCh36SignSync.lean` (320 lines, **0 errors, clean-3**, no
sorry/axiom/admit/native_decide). Not committed (per instructions).

Bricks delivered: **1, 3, 6, 9**. Brick 8 **SKIPPED** (justified below by inventory answer (c)).

---

## Inventory answers (settled by reading source)

### (a) `windCross` as a sum of `eSign` over `CrossingEdges'`

**No landed `windCross_eq_sum_crossing_eSign`.** But `windCross` *is* derivably such a sum:

- `windCross_eq_sum_sEdge` (PolygonWindingExterior:86): `windCross P ρ z = ∑ i, sEdge P ρ z i`.
- `sEdge_eq_eSign_mul` (PolygonWindingExterior:73): `sEdge P ρ z i = eSign P ρ i * (if EdgeCrossesRay' P ρ z i then 1 else 0)`.
- `eSign P ρ i := edgeSign ρ.r (P.q i) (P.q (cyclicNext i))` (PolygonWindingExterior:69) — **BASE-POINT-INDEPENDENT** (depends only on edge geometry vs ray direction, NOT on the base point `x`).

I packaged this as **`windCross_eq_sum_crossingEdges_eSign`**:
`windCross P ρ x = ∑ i ∈ CrossingEdges' P ρ x, eSign P ρ i` (proved via `windCross_eq_sum_sEdge` +
`Finset.sum_ite_mem`). **Consequence for brick 3:** since `eSign` is base-point-free, the singleton
jump needs **NO shared-eSign hypothesis** — the same function `eSign Q σ` appears at both `x` and
`y`, so the difference telescopes cleanly over the symmetric difference. (The design's worried-about
"sign depends on basepoint" case does not occur.)

### (b) Guard-free local constancy

**YES, exists, guard-free.** `windCross_locally_constant_off_boundary` (PolygonWindingExterior:422):
`∀ᶠ y in nhds x, windCross Q σ y = windCross Q σ x` for `¬ OnBoundary Q x`, with **no vertex
guards**. (Consumed by master bricks 5/11, not directly here, but confirmed for them.)

### (c) `windCross_mem_final` vertex guards — **YES (this is why brick 8 is skipped)**

`windCross_mem_final` (ZinanCh36Interval:513) requires BOTH `hoff : ¬ OnBoundary P x` AND
`hvert : ∀ k, side ρ.r x (P.q k) ≠ 0`. **No guard-free parent bound exists** anywhere in the
winding substrate. Therefore the ray-indexed brick 8 (`rayWindValues_split_offAll`) cannot synthesize
its parent bound at a guard-violating off-all point: the children give `L, R ∈ {0,s}` hence
`P = L+R ∈ {0, s, 2s}`, and excluding `2s` is *exactly* the content `windCross_mem_final` supplies —
which it refuses to do without `hvert`. The only escape (design option iii) is to perturb to a generic
point and transfer back by local constancy on all three polygons. That perturb-to-generic machinery is
the unlanded brick 10/11 territory (only `eventually side ≠ 0` fragments exist, at
PolygonWindingExterior:240; no landed density/off-all-generic lemma). **Per the design's explicit
instruction ("If (iii) needs the unlanded perturb machinery, SKIP brick 8"), brick 8 is skipped and
belongs with bricks 10–11.**

---

## Statements proven (all clean-3)

1. **Brick 1** — `RayWindValuesWithSign P ρ s` (Prop), `RayOrientedWindData` (**Type**-valued
   structure, so `s` is projectable as data — design permits since it's an induction-12 carrier),
   accessors `.sign_unit` / `.values`, and the bridge
   **`WindValuesWithSign.of_raywise`** (guard-free ray-wise ⟹ guard-ful `WindValuesWithSign`, trivial
   weakening: the guard-free package never consults `hvert`).

3. **Brick 3** — `windCross_eq_sum_crossingEdges_eSign` (the sum form, see (a)) +
   **`windCross_ne_of_symmDiff_singleton`**: `symmDiff (CrossingEdges' Q σ x) (CrossingEdges' Q σ y)
   = {e}` ⟹ `windCross Q σ x ≠ windCross Q σ y`. Proof: split each sum into `A∩B` + diff; the two
   diff sets are disjoint with union `{e}`, so exactly one is `{e}` and the other `∅`; the difference
   is `± eSign e = ±1 ≠ 0` (`eSign_mem`).
   **Shape delta:** statement matches the design exactly, but the *promised* extra hypothesis
   ("shared crossing edges have equal eSign") is **NOT NEEDED and NOT added** — because eSign is
   base-point-independent (answer (a)). Brick 5 can consume this unconditionally.

6. **Brick 6** — **`signs_eq_from_split_local`**: exact design signature (renamed the subscript
   identifiers `L₊…` → `Lp/Lm/Rp/Rm/Pp/Pm` because `₊`/`₋` are operator-class tokens Lean rejects in
   identifiers; the *hypothesis names* `hsplitp/hsplitm` likewise). Pure `rcases … <;> omega`.
   **Verified non-vacuous** (brute-forced: 4 satisfying assignments, all with `sL = sR`).
   Note: `omega` closes without using `hLjump` (one jump + the constant-nonzero parent already
   forces it); `hLjump` is kept for the design's symmetric interface (brick 7 supplies it). Benign
   unused-variable warning only.

9. **Brick 9** — `subBoundaryLeft_of_parentOff_is_diag`, `subBoundaryRight_of_parentOff_is_diag`,
   and the combined **`subBoundary_of_parentOff_is_diag`**: parent-off + child-on (either child) ⟹
   `x ∈ openSegment ℝ (P.q i) (P.q j)`. LEFT proved fully via `left_arc_edge_endpoints` /
   `left_diag_edge_endpoints` (arc edge ⟹ parent edge ⟹ `OnBoundary P`, contradiction; diagonal edge
   ⟹ `seg (P.q j) (P.q i)`, endpoints excluded by `vertex_onBoundary` + `mem_openSegment_of_ne_left_right`).
   **RIGHT proved fully too** (not exposed as a hypothesis): the right subpolygon along `(i,j)`
   equals the left subpolygon along `(j,i)` *definitionally* (`rightIndex i j = leftIndex j i`,
   `rightLength i j = leftLength j i`, both `rfl`), so I reuse the left endpoint lemmas with `(j,i)`
   via a `Fin.cast rfl` on the edge index. Both child cases land; no missing right-arc lemma was
   needed.

---

## Skipped

- **Brick 8** (`rayWindValues_split_offAll`): skipped — blocked on the guard-ful parent bound
  (answer (c)); the resolution is the perturb-to-generic machinery of bricks 10–11. Documented in
  the file header and above.

## Shape deltas summary

- Brick 3: dropped the (unnecessary) shared-eSign hypothesis — eSign is base-point-free.
- Brick 6: subscript identifiers renamed (`₊/₋` are illegal in Lean identifiers); statement otherwise verbatim.
- Brick 9: right case fully proven (design allowed exposing it as a hypothesis; the (j,i)-reversal
  defeq made the full proof cheaper than a named hole).

## Axiom audit (from `#print axioms`)

All clean-3 (`propext`, `Classical.choice`, `Quot.sound`); `signs_eq_from_split_local` needs only
`propext`, `Quot.sound`. No `sorryAx`.
