# opus-triconvex reply — `TriangleConvexLeaf` discharged UNCONDITIONALLY (hconv done)

**Status: DONE — `triangleConvexLeaf_holds : TriangleConvexLeaf` proved unconditionally
(clean-3, 0 sorry/axiom/admit/native_decide). The `hconv` oracle of
`artGallery_strict_unconditional` is fully discharged. Chapter-36 art-gallery headline is
now conditional on only TWO oracles (`D`, `M`) instead of three.**

**File:** `ProofsInTheBook/PolygonTriangleConvex.lean` (NEW, the only file I own, 590 lines).
**Branch:** `main` (no switch, no commit). **Server:** `uisai1`.
**Build dep:** `ProofsInTheBook.PolygonGeometryData` → *Build completed (8442 jobs)*.
**Verification (uisai1):** `lake env lean ProofsInTheBook/PolygonTriangleConvex.lean` → RC=0
(≈47s); full `lake build ProofsInTheBook.PolygonTriangleConvex` → *Build completed (8443 jobs)*.

## The crossTau-sign lemma — BUILT (the geometric heart, fully algebraic)

The spec's reduction was correct, and I closed it with a fully algebraic (no convex-geometry-
analysis) crossTau-sign argument. The key closed form (verified numerically first, then proved
by `det2` bilinearity):

- **Barycentric side identity** (`barycentric_side_sum`): for `x = w0•q0+w1•q1+w2•q2` with
  `∑w=1`, `∑ w_k·side r x q_k = side r x x = 0`.
- **crossTau numerator = weighted orient** (`crossNum_eq_weight_orient`):
  `det2 (q_i - x) (q_{i+1}-q_i) = w_opp · orient(q0,q1,q2)`, where `w_opp` is the weight of the
  vertex opposite edge `i`. Hence `crossTau_i · crossDen_i = w_opp · O`.
- **Forward-key reduction** (`crossTau_nonneg_iff` + `fwdKey_iff`): `0 ≤ crossTau_i ⟺
  0 ≤ (w_opp O)·crossDen_i ⟺ 0 ≤ O·(s_{i+1}-s_i)` (drop the positive weight; multiply by
  `crossDen²>0`). `crossDen_i = s_{i+1}-s_i` (`side_next_sub_side`).

The crossTau-sign content is then the **pure-arithmetic** `forward_count_eq_one`: for three
nonzero side values that are NOT all one strict sign (forced by the barycentric identity with
positive weights) and `O≠0`, the three cyclic edge indicators (Span ∧ forward) sum to **exactly
1**. Proof: 8-way sign split (2 all-same-sign leaves excluded) × O-sign; each leaf resolved by
`indicator_resolve` + `nlinarith`. This IS "of the two spanning edges exactly one is forward",
because the two spanning edges share the lone-sign vertex and so have opposite-sign `crossDen`s.

## The chain (all unconditional, clean-3)

1. `exists_barycentric_of_mem_closedTri` — weights from `closedTri = convexJoin {a}(seg b c)`.
2. `crossingNumber'_interior_eq_one` — interior point + vertex-avoiding valid ray ⟹
   `CrossingNumber' Q r x = 1` (instantiates `forward_count_eq_one`).
3. `exists_rayDir_side_ne_zero` — a valid `RayDirection` (mkPt 1 t) whose line through `x`
   misses every vertex (avoid finitely many bad slopes), for `x` distinct from all vertices.
4. `not_onBoundary_of_interior` — all-positive-weights ⟹ off boundary, via
   `orient a b x = w_opp·O ≠ 0` (same weighted-orient identity), so `x` is on no edge.
5. `interior_mem_region` — interior ⟹ `ClosedRegion' Q r x` (odd) for `r`, transported to `σ`
   by the already-unconditional `PolygonDegenerateWall.closedRegion'_chain_tri` (ray-independence).
6. `closedTri_subset_region` — dichotomy: a zero-weight point is on an edge (`Or.inl` boundary);
   else strictly interior (step 5). Then `triangleConvexLeaf_holds` unfolds `IsConvexVertex' Q σ
   ⟨1⟩` (cyclicPrev⟨1⟩=⟨0⟩, cyclicNext⟨1⟩=⟨2⟩) to this containment.

## Headline reduction (3 oracles → 2)

`artGallery_strict (D) (M) (P) (ρ)` — the `⌊n/3⌋` guard bound — now consumes only:
- `D : ResidualGeometryData` (the uniform residual geometry), and
- `M : DiagonalAttachInput` (the diagonal-attach peel),
feeding `triangleConvexLeaf_holds` (hconv, NOW unconditional) and
`PolygonDegenerateWall.triangleExteriorEven_unconditional` (already unconditional) into
`PolygonDegenerateWall.artGallery_strict_unconditional`. No `hconv` hypothesis remains.

## Verification (playbook §3 acceptance)

- **A (mechanical):** 0 sorry/admit/axiom/native_decide (grep clean). `lake env lean` RC=0;
  full `lake build` of the module OK.
- **`#print axioms` (clean-3, rebuilt olean):**
  - `triangleConvexLeaf_holds` → `[propext, Classical.choice, Quot.sound]`
  - `artGallery_strict` → `[propext, Classical.choice, Quot.sound]`
  - `crossingNumber'_interior_eq_one`, `closedTri_subset_region` → clean-3.
- **B/C (signature/semantic):** `example : PolygonLeaf.TriangleConvexLeaf := triangleConvexLeaf_holds`
  typechecks — the proved statement is *definitionally* the target oracle `TriangleConvexLeaf`
  (= `∀ Q σ, IsConvexVertex' Q σ ⟨1⟩` = the genuine hull⊆region containment, per
  `base_subset_iff_convexVertex_one`), not a weakened/vacuous re-wrapper. `artGallery_strict`'s
  printed signature has exactly two oracle binders (`D`, `M`) and the genuine `⌊n/3⌋` conclusion.
  Verdict: **FAITHFUL, unconditional.**

## Residue

None for `hconv`. The remaining two Chapter-36 oracles (`D` = half-plane / cut geometry,
`M` = peel-order diagonal-attach) are untouched — they are the genuinely-irreducible
half-plane-separation + peel content the substrate isolates by design.

## Discipline

No codex/OpenAI tooling (resource rule respected). Stayed on `main`, no commits, no branch
switch. Only created the NEW file `PolygonTriangleConvex.lean`. Verified exclusively via
rsync + `lake env lean`/`lake build` on `uisai1` (no local build on the Mac). Numerically
pre-validated the interior-odd claim and the weighted-orient closed form (200k random triangles)
before formalizing.
