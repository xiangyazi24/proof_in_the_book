# ch36-ray-dichotomy — reply

**Status: GREEN.** New file `ProofsInTheBook/ZinanCh36RayDichotomy.lean` compiles clean on
uisai2 (`lake env lean`) with **zero errors, zero sorry/axiom/admit/native_decide**. All 16
theorems report `#print axioms` = `[propext, Classical.choice, Quot.sound]` (clean-3).

Imports: `ProofsInTheBook.ZinanCh36Theta`, `ProofsInTheBook.PolygonWindingExterior`.
Namespace: `ProofsInTheBook.ZinanCh36Theta` (same opens as the theta file).

## Bricks delivered (all design-pinned statements, none weakened)

1. **`LineCrossingEdges P ρ x := univ.filter (fun i => SpanCrossesSide P ρ x i)`** — the
   full-line span-crossing filter. The predicate is `SpanCrossesSide` verbatim, the exact
   filter of `ZinanCh36Theta.lineCrossing_eSign_sum_zero` (read its statement; reused as-is).
   Helpers: `mem_lineCrossingEdges_iff`, `crossingEdges'_eq_filter_lineCrossing`
   (`CrossingEdges' = LineCrossingEdges.filter (0 ≤ crossTau)` — the forward subset).

2. **`crossTau_injOn_lineCrossingEdges`** — distinct line crossings have distinct `crossTau`
   under `hvert`. Proof is the `crossTau_injOn_crossingEdges` template with the forward guard
   dropped (uses `crossU_mem_Ioo` + `crossPoint_mem_edge` + `EdgeIntersectionCondition`).

3. **`rayWindingDichotomy_of_fullLineAlternation`** — CONDITIONAL on `Halt`, statement
   exactly as specified. Conclusion `∃ s, (s = 1 ∨ s = -1) ∧ ∀ c ≥ 0, ¬OnBoundary → windCross
   ∈ {0, s}`. Proof chain: `windCross_cut_eq_lineFilter_sum` (windCross at cut `c≥0` =
   `eSign`-sum over `LineCrossingEdges.filter (c ≤ τ)`, the forward guard absorbed by `c≥0`)
   → `windCross_cut_eq_listFilter_sum` (= list-sum over `L.filter (c≤τ)`) →
   `filter_suffix_of_sorted` (that list-filter is a `<:+` suffix of the τ-ascending `L`) →
   `isSuffix_sum_mem_of_alt` (the two-value suffix law). The full sum is `0` via
   `fullLine_listSum_zero` (wraps `lineCrossing_eSign_sum_zero`). `s` = last sign of
   `L.map eSign` (`1` if empty).
   - **List lemmas (the requested suffix-sum machinery):** `altSum_eq_getLast` (an alternating
     ±1 list sums to 0 or to its last entry), `alt_drop`/`isPM1_drop`/`getLast?_drop_eq`,
     `suffix_sum_mem_of_alt` (drop form), `isSuffix_sum_mem_of_alt` (`<:+` form),
     `filter_suffix_of_sorted`.

4. **`triangle_rayWindingDichotomy` (n = 3)** — UNCONDITIONAL base case, same conclusion
   shape, NO `Halt` input. Builds the sorted full-line enumeration (`exists_sorted_enum` +
   `crossTau_injOn_lineCrossingEdges`); `lineCrossing_card_le_two` proves `|L| ≤ 2` (nodup
   over `Fin 3` gives `≤ 3`; the ±1 `eSign` sum is `0` so the count is even, ruling out 3 —
   parity-of-sum = parity-of-length lemma inline); `alt_of_len_le_two` makes the ≤2 list
   alternate trivially; then Brick 3 closes it. This **also proves `Halt` is satisfiable for
   n=3** (non-vacuity witness for the conditional brick).

5. **`rayCrossingAlternation_of_fullLineAlternation`** — CONDITIONAL wrapper: obtains `(s, hs,
   H)` from Brick 3 and feeds `ZinanCh36Theta.rayCrossingAlternation_of_ray_dichotomy`.
   Bonus: **`triangle_rayCrossingAlternation`** — the triangle Jordan kernel UNCONDITIONALLY
   (Brick 4 ∘ the reduction), taking only `(Q, ρ, x, hoff, hvert)`.

## Honesty / faithfulness notes

- Bricks 3 and 5 stay HONESTLY conditional on `Halt` (the lobe/matching alternation supply —
  the master's brick — was NOT attempted and is NOT stated as an axiom anywhere).
- `Halt` is not a vacuous premise: it is proved to HOLD for every generic off-boundary point
  of a triangle (Brick 4), so the conditional theorems are operationally non-empty.
- `s = last sign of L (1 if empty)`, matching the brief; the empty case (`L = []`) gives
  winding `0` along the whole forward ray with `s := 1`.

## Deviations
None of substance. Two cosmetic `unused variable` warnings remain on design-pinned interface
hypotheses (`hoff` in `rayWindingDichotomy_of_fullLineAlternation`, kept because the brief
pins it in the statement; `hsum` in `suffix_sum_mem_of_alt`, the precondition of the two-value
law threaded through `isSuffix_sum_mem_of_alt`). Both are correct and intentional; no errors.

## Verify
```
scp -q ProofsInTheBook/ZinanCh36RayDichotomy.lean uisai2:~/repos/proof_in_the_book/ProofsInTheBook/
ssh uisai2 'export PATH=$HOME/.elan/bin:$PATH; cd ~/repos/proof_in_the_book && \
  lake env lean ProofsInTheBook/ZinanCh36RayDichotomy.lean 2>&1 | tail -20'
```
(Deps `ProofsInTheBook.ZinanCh36Theta` etc. already built — `Build completed successfully`.)
