# Ch36 Perturb-wrapper report (bricks 8, 10, 11)

File: `ProofsInTheBook/ZinanCh36Perturb.lean` — compiles, 0 errors, clean-3
(`propext, Classical.choice, Quot.sound`) on all three `#print axioms`. No
`sorry/admit/axiom/native_decide`.

## Deliverables landed

| Brick | Theorem | Status |
|-------|---------|--------|
| 10 | `exists_near_point_off_all_generic` | ✅ off-all + vertex-generic for P, L, R |
| 8 (generic) | `rayWindValues_split_offAll_generic` | ✅ parent value ∈ {0,s} at generic y |
| 8 (general) | `rayWindValues_split_offAll` | ✅ only `hPoff` needed |
| 11 | `rayWindValues_split` | ✅ collapses to a one-liner |

Plus the supporting algebra: `orient_perturb_affine`, `side_perturb_affine`,
`exists_lambda_transverse_edges` (direction selection), `exists_badt_polygon`
(per-polygon bad-t), `exists_eps_segment_in_nhds` (small-t neighbourhood capture).

## hLoff / hRoff: DROPPED ✅

The strengthened brick 10 produces the vertex-genericity guards itself, so brick
8's *general* form `rayWindValues_split_offAll` requires ONLY
`hPoff : ¬ OnBoundary P x`. The child boundaries / child local constancy at `x`
are never consulted: at the perturbed generic point `y` the child values come
directly from the guard-free packages `HVL`/`HVR` (brick 10 gives `¬OnBoundary L y`,
`¬OnBoundary R y`). Consequently brick 11 `rayWindValues_split` collapses with NO
`by_cases` on the child boundaries and does NOT use
`subBoundary_of_parentOff_is_diag` at all (brick 9 input unused by this chain).

## Inventory findings

* **No reusable generic-point selector existed.** The Ch36 files have
  `exists_generic_u0` / `exists_generic_u0L` (`ZinanCh36NonInterleave`) but those
  are tied to lobe-chain vertices along the *ray* line `x + u₀•r`, not a normal
  perturbation off all three polygon boundaries. Brick 10 was built fresh.
* **Reused the `sweepDir` direction family** (`ZinanCh36NonInterleave`):
  `w = sweepDir ρ.r λ = perpVec ρ.r + λ•ρ.r`. Key property
  `det2 ρ.r (sweepDir ρ.r λ) = ‖ρ.r‖² > 0` (`det2_r_sweepDir_pos`, independent of λ)
  makes `w` ALWAYS transverse to the ray, so every vertex-guard line
  `{y | side ρ.r y q = 0}` is hit by `t ↦ x+t•w` in ≤1 `t` for free. The edge
  transversality `det2 (edgeVec) w ≠ 0` is the affine-in-λ root-avoidance via
  `det2_sweepDir_left`. Per-polygon edges of P/L/R are all ρ.r-non-parallel because
  `σL.r = σR.r = ρ.r` are valid `RayDirection`s of L/R (`no_edge_parallel`).
* **Segment→line** via `PolygonTriangleConvex.orient_eq_zero_of_mem_seg`
  (point on `seg a b` ⟹ `orient a b · = 0`); the perturbation makes `orient` and
  `side` affine non-constant in `t`, giving ≤1 bad `t` each. Bad `t`'s collected
  into a `Finset`, dodged inside `Ioo 0 ε` (`Set.Ioo_infinite`).
* Local constancy: `windCross_locally_constant_off_boundary`
  (`PolygonWindingExterior`) supplies the parent neighbourhood `U` for transfer.

## Residuals

NONE. No named residual hypothesis. The general-position direction selection and
per-object ≤1-intersection argument went through in full generality (no
specialization needed), because `sweepDir` reduces both to single affine roots.

## One lint note

Brick 10 (`exists_near_point_off_all_generic`) carries `hPoff : ¬ OnBoundary P x`
in its signature (per the design and so brick 8 can pass it naturally), but the
construction is genuinely INDEPENDENT of `hPoff` — it perturbs off ALL boundaries
regardless of where `x` sits. Hence one `unused variable hPoff` warning. Kept the
hypothesis for API/design parity; it does not affect clean-3 or soundness. (If the
master prefers, `hPoff` can be dropped from brick 10 entirely — strictly stronger —
but brick 8's general form independently needs `hPoff` for `windCross_mem_final` at
the transferred-from point's local-constancy anchor, so it stays available there.)
