# Ch20 Monsky — E2 specification (the single remaining geometric core)

State after `Chapter20Dissection.lean` bricks 1–2:
* **Done in `Chapter20.lean`** (unconditional): valuation extension ℚ→ℝ, Lemma 1
  (rainbow ⟹ `v(doubleArea) ≥ 1`), the abstract Sperner engine
  `exists_trichromatic_of_odd_boundary`, the four-side boundary parity
  `squareBoundaryRGCount_odd_of_side_color_lists` (E5), and the per-side
  `listRGTransitionCount` color lemmas.
* **Done in `Chapter20Dissection.lean`**:
  - `one_le_realTwoAdicValuation_doubleArea_of_trichromatic` (Lemma 1, any order),
  - `not_trichromatic_of_collinear` (≤2 colors per line),
  - `odd_listRGTransitionCount_iff_endpoints` (**E3**, general per-side parity).

The faithful Monsky reduces to the planar-incidence fact below.

## The dissection object

```lean
structure SquareDissection where
  n : ℕ
  vtx : Type
  [vtxFin : Fintype vtx]
  [vtxDec : DecidableEq vtx]
  coord : vtx → ℝ × ℝ
  coord_inj : Function.Injective coord
  tri : Fin n → vtx × vtx × vtx
  nondeg : ∀ i, doubleArea (coord (tri i).1) (coord (tri i).2.1) (coord (tri i).2.2) ≠ 0
  cover : (⋃ i, convexHull ℝ {coord (tri i).1, coord (tri i).2.1, coord (tri i).2.2})
            = Set.Icc (0, 0) (1, 1)
  disjoint_int : ∀ i j, i ≠ j →
    Disjoint (interior (convexHull ℝ {coord (tri i).1, coord (tri i).2.1, coord (tri i).2.2}))
             (interior (convexHull ℝ {coord (tri j).1, coord (tri j).2.1, coord (tri j).2.2}))
  equalArea : ∀ i, realTriangleArea (coord (tri i).1) (coord (tri i).2.1)
                     (coord (tri i).2.2) = ((1 : ℚ) / n : ℚ)
```

`vtx` ranges over *all* triangle corners (T-vertices included), so a side may be
subdivided by other vertices lying in its relative interior.

## Atomic edges

For `i : Fin n` and a side endpoint pair `(p, q)` of `tri i`, the side is
`segment ℝ (coord p) (coord q)`.  The vertices on it, ordered by the affine
parameter `t ∈ [0,1]` with point `= coord p + t • (coord q - coord p)`, give a
chain `p = w₀, w₁, …, w_k = q`.  The **atomic edges of side (p,q)** are
`s(w₀,w₁), …, s(w_{k-1},w_k)`.  `atomicEdges i` concatenates the three sides;
`atomicMult e = ∑ i, (atomicEdges i).count e`.

## E2 — the planar-incidence core (TARGET; everything else reduces to it)

```lean
-- (a) interior atomic edge: even multiplicity; boundary atomic edge: odd (=1).
theorem atomicMult_even_of_interior (D : SquareDissection) (e : Sym2 D.vtx)
    (he : IsAtomicEdge D e) (hint : ¬ OnSquareBoundary D e) :
    Even (atomicMult D e)

theorem atomicMult_eq_one_of_boundary (D : SquareDissection) (e : Sym2 D.vtx)
    (he : IsAtomicEdge D e) (hbd : OnSquareBoundary D e) :
    atomicMult D e = 1

-- (b) the boundary atomic edges, with the 2-adic coloring, form the four square
--     side-chains feeding `squareBoundaryRGCount_odd_of_side_color_lists`.
```

### Proof sketch of (a) — "interior segment borders exactly two triangles"

Fix `e = s(p,q)` atomic, `m` a relative-interior point of `[p,q]`, no vertex on
the open segment.  Pick `ε > 0` smaller than the distance from `m` to every
vertex and to every triangle edge not on the line `L = affineSpan{coord p, coord q}`.

1. **No transversal crossing at `m`.** If a triangle edge not on `L` met the open
   disk `D(m,ε)`, two triangles' interiors would overlap a quadrant ⇒ contradicts
   `disjoint_int`.  Hence every triangle edge meeting `D(m,ε)` lies on `L`, so `L`
   splits `D(m,ε)` into two open half-disks `D⁺, D⁻`, each edge-free.
2. **Each half-disk lies in one triangle interior.** A half-disk is connected,
   edge-free, and (for `m` interior to the square) inside `⋃ closure = S`; every
   point is in some closure but on no edge ⇒ in exactly one interior; "which
   triangle" is locally constant on the connected half-disk ⇒ `D⁺ ⊆ interior(T⁺)`,
   `D⁻ ⊆ interior(T⁻)`, with `T⁺ ≠ T⁻` by disjointness.
3. **`e` is a boundary edge of exactly `{T⁺, T⁻}`.** `coord p..q` near `m` are
   limits of both `interior(T⁺)` and its complement (since `D⁻ ⊆ interior(T⁻)`),
   so on `∂T⁺`; being on `∂` of a triangle and atomic ⇒ `e ⊆` one edge of `T⁺`.
   Same for `T⁻`.  Any third triangle with `e` on its boundary would fill part of
   `D⁺` or `D⁻`, already occupied ⇒ equal to `T⁺` or `T⁻`.  So multiplicity `= 2`.
4. **Boundary case.** If `m ∈ ∂S`, one half-disk is outside `S`; only one triangle,
   multiplicity `= 1`.

Mathlib pieces: `convexHull`/`segment`, `interior_convexHull`-type facts,
`Wbtw`/`Sbtw`, `IsConnected`, `Convex.combo`/half-plane separation,
`volume_convexHull_triangle` (area, used to rule out degenerate overlaps).

This is self-contained convex/affine planar geometry — no algebraic topology.
It is the one heavy brick; everything upstream (valuation, Sperner, parity) and
the wiring (E3 per side ⇒ `hparity`, then `exists_trichromatic_of_odd_boundary`)
is already proved or mechanical.

## Paste-ready atomic definitions (foundational, needed regardless of E2 route)

```lean
open scoped Classical in
/-- A vertex `w` lies on the side `(p,q)` of the dissection. -/
def OnSide (D : SquareDissection) (p q w : D.vtx) : Prop :=
  Wbtw ℝ (D.coord p) (D.coord w) (D.coord q)

/-- The affine parameter of `w` along side `(p,q)`: `coord w = coord p + t•(coord q-coord p)`.
    Used only to order the vertices on a side; well-defined when `coord p ≠ coord q`. -/
noncomputable def sideParam (D : SquareDissection) (p q w : D.vtx) : ℝ :=
  -- first coordinate ratio when the side is non-vertical, else second; robust:
  if (D.coord q).1 ≠ (D.coord p).1
  then ((D.coord w).1 - (D.coord p).1) / ((D.coord q).1 - (D.coord p).1)
  else ((D.coord w).2 - (D.coord p).2) / ((D.coord q).2 - (D.coord p).2)

/-- Vertices strictly between `p` and `q` on the side, ordered by `sideParam`. -/
noncomputable def sideInteriorChain (D : SquareDissection) (p q : D.vtx) : List D.vtx :=
  (Finset.univ.filter (fun w => OnSide D p q w ∧ w ≠ p ∧ w ≠ q)).sort
    (fun w₁ w₂ => sideParam D p q w₁ ≤ sideParam D p q w₂)

/-- Atomic edges along side `(p,q)`: consecutive pairs of `p :: chain ++ [q]`. -/
noncomputable def sideAtomicEdges (D : SquareDissection) (p q : D.vtx) : List (Sym2 D.vtx) :=
  consecutiveEdges (p :: sideInteriorChain D p q ++ [q])

/-- All atomic edges contributed by triangle `i` (its three subdivided sides). -/
noncomputable def triAtomicEdges (D : SquareDissection) (i : Fin D.n) : List (Sym2 D.vtx) :=
  sideAtomicEdges D (D.tri i).1 (D.tri i).2.1 ++
  sideAtomicEdges D (D.tri i).2.1 (D.tri i).2.2 ++
  sideAtomicEdges D (D.tri i).2.2 (D.tri i).1

/-- Multiplicity of an unordered edge across all triangle atomic boundaries. -/
noncomputable def atomicMult (D : SquareDissection) (e : Sym2 D.vtx) : ℕ :=
  ∑ i : Fin D.n, (triAtomicEdges D i).count e

def IsAtomicEdge (D : SquareDissection) (e : Sym2 D.vtx) : Prop :=
  ∃ i, e ∈ triAtomicEdges D i

/-- `e` lies on the boundary of the unit square. -/
def OnSquareBoundary (D : SquareDissection) (e : Sym2 D.vtx) : Prop :=
  Sym2.lift ⟨fun p q => segment ℝ (D.coord p) (D.coord q) ⊆
      frontier (Set.Icc ((0:ℝ),(0:ℝ)) (1,1)), by intro a b; simp [segment_symm]⟩ e
```

The colouring side uses `realTwoAdicColor ∘ D.coord`.  Per-side parity (E3,
already proved) gives `triangleLocalRGCount(corner colours i) ≡
listRGTransitionCount(side colour chain)` mod 2 for each side, because the side
chain is collinear ⇒ ≤2 colours ⇒ `odd_listRGTransitionCount_iff_endpoints`.

## Wiring once E2 holds (mechanical; mirrors `sum_triangleLocalRGCount_*`)

1. `∑ i triangleLocalRGCount(colours i) ≡ ∑ i (RG count of triAtomicEdges i)`  (3×E3).
2. `∑ i (RG count of triAtomicEdges i) = ∑_e atomicMult e · RGind e`           (reindex).
3. `≡ ∑_{e : Odd (atomicMult e)} RGind e`                                       (mod 2).
4. E2 ⇒ odd-mult atomic edges = square-boundary atomic edges; their RG count =
   bottom-side chain RG count = `1` mod 2  (E5, `..._side_color_lists`).
5. Feed `totalRG := ∑ triangleLocalRGCount`, `boundaryRGCount := 1`-parity into
   `exists_trichromatic_of_odd_boundary` ⇒ rainbow triangle ⇒
   `not_real_triangleArea_eq_one_div_odd_of_trichromatic` with `equalArea` ⇒ `False`.
