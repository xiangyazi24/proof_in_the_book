The clean fix is **C, but not weakened all the way to “signChangesFull equal.”** Keep the Euclidean `VertexStar` in the order that makes its convexity predicates true, and weaken `linkOrder` from literal list equality to **equality of the cyclic order up to reversal**. That is the mathematically honest invariant: a cyclic vertex link has no canonical orientation until you choose an orientation convention for `det3`/outward normals. The Cauchy sign-change argument only needs cyclic sign changes, which are invariant under cyclic rotation and reversal.

Do **not** try to force forward `σ` by changing geometry unless you want a larger convention rewrite.

## Why option A is not the best fix

`VertexStar` is already built around a fixed orientation convention:

```lean
turn_support :
  ∀ i j, 0 ≤ det3 (p i - o) (p (i + 1) - o) (p j - o)

turn_strict :
  ∀ i j, j ≠ i → j ≠ i + 1 →
    0 < det3 (p i - o) (p (i + 1) - o) (p j - o)
```

and the spherical link proof transfers this exact raw `det3` sign to `sOrient` of the link directions. fileciteturn103file0L62-L80 fileciteturn103file0L114-L148

So if forward `σ` gives `det = -16` in the tetrahedron, that means your current combinatorial `σ` convention is opposite to the current `det3`/`sOrient` convention at that vertex. This is a **handedness convention mismatch**, not a mathematical failure.

You could flip `det3` globally or swap the first two determinant arguments, but then you are changing the orientation convention used by `VertexStar`, `sOrient`, and every proof depending on them. It does not affect `open_hemi`, but it does ripple through the `VertexStar → StrictConvexSphArm` bridge and the concrete examples. Since reversing the list fixes the issue without touching geometry, option A is unnecessarily invasive.

Geometrically, the phenomenon is expected. In a combinatorial map convention with `φ = σ ∘ α`, the forward vertex rotation often appears clockwise when viewed from the outward side of a convex vertex; the spherical-link CCW order for positive triple products is then the reverse order. Your tetrahedron sign test is good evidence that the reversal is the intended convention for this realization.

## Avoid option B’s `σ⁻¹.toList` route

You do not need to make `σ.toList` itself run backwards.

Mathlib/repo already uses the useful theorem for forward cycle representatives:

```lean
(h.toList_isRotated).map es
```

inside `vertexFlipCountSkipZeros_sameCycle`, proving that two representatives in the same `σ`-orbit give rotated sign lists. fileciteturn101file0L58-L65

But a clean `Perm.toList` theorem saying

```lean
(σ⁻¹).toList x = (σ.toList x).reverse.rotate ...
```

is not something I would rely on. Even if you prove it, the exact rotation offset is annoying:

```text
σ.toList x       = [x, σ x, σ² x, ..., σⁿ⁻¹ x]
σ⁻¹.toList x     = [x, σⁿ⁻¹ x, ..., σ x]
(σ.toList x).reverse = [σⁿ⁻¹ x, ..., σ x, x]
```

so you need a rotate-by-length-minus-one normalization. That is pure bookkeeping pain and does not buy you anything.

If your Euclidean star uses `Fin.rev`, prove the simple local list lemma instead:

```lean
lemma ofFn_fin_rev {n : ℕ} (f : Fin n → α) :
    List.ofFn (fun i : Fin n => f (Fin.rev i))
      = (List.ofFn f).reverse := by
  -- usually by ext/getElem, or induction on n if needed
  ...
```

Then relate the star’s link-sign list to the reverse of the forward `σ` sign list directly.

## Recommended interface change

Replace this field:

```lean
linkOrder : ∀ Q,
  (M.σ.toList (dartRep Q)).map edgeSign =
    (List.ofFn
      (linkDiff (starP Q).vertexLink (linkQcast M starP starQ hnn Q))).map realSignToEdgeSign
```

with a cyclic-order-up-to-reversal relation.

Define:

```lean
def List.DihedralRotated {α : Type*} (l m : List α) : Prop :=
  l ~r m ∨ l.reverse ~r m
```

Then use:

```lean
linkOrder : ∀ Q,
  List.DihedralRotated
    ((M.σ.toList (dartRep Q)).map edgeSign)
    ((List.ofFn
      (linkDiff (starP Q).vertexLink
        (linkQcast M starP starQ hnn Q))).map realSignToEdgeSign)
```

This says: the geometric link order is the same cyclic order as the combinatorial `σ` order, possibly with the opposite orientation. That is not vacuous; it is exactly the orientation ambiguity of an unoriented cyclic link.

If, for your current Euclidean bridge, you know it is always reversed, you can use the stricter field:

```lean
linkOrder_rev : ∀ Q,
  ((M.σ.toList (dartRep Q)).map edgeSign).reverse =
    (List.ofFn
      (linkDiff (starP Q).vertexLink
        (linkQcast M starP starQ hnn Q))).map realSignToEdgeSign
```

This is the smallest patch. The `DihedralRotated` version is the more robust final interface.

## The needed counting lemmas

You already have rotation invariance:

```lean
cyclicFlipCountSkipZeros_of_isRotated :
  l ~r l' →
  cyclicFlipCountSkipZeros l = cyclicFlipCountSkipZeros l'
```

proved in `Ch13Realization`. fileciteturn101file0L51-L56

Add reversal invariance:

```lean
theorem cyclicFlipCount_reverse {α : Type*} [DecidableEq α] (l : List α) :
    cyclicFlipCount l.reverse = cyclicFlipCount l := by
  -- prove once; easiest using `cyclicFlipCount_eq_cyclicSum`
  -- and the fact cyclic adjacent unequal pairs are preserved by reversal.
  ...

theorem filterMap_reverse {α β : Type*} (f : α → Option β) (l : List α) :
    l.reverse.filterMap f = (l.filterMap f).reverse := by
  induction l with
  | nil => simp
  | cons a t =>
      simp [List.filterMap_append, *]
      cases f a <;> simp [*]

theorem cyclicFlipCountSkipZeros_reverse (l : List EdgeSign) :
    cyclicFlipCountSkipZeros l.reverse = cyclicFlipCountSkipZeros l := by
  unfold cyclicFlipCountSkipZeros
  rw [filterMap_reverse]
  exact cyclicFlipCount_reverse _
```

Then:

```lean
theorem cyclicFlipCountSkipZeros_of_dihedralRotated
    {l m : List EdgeSign}
    (h : List.DihedralRotated l m) :
    cyclicFlipCountSkipZeros l = cyclicFlipCountSkipZeros m := by
  rcases h with hrot | hrev
  · exact cyclicFlipCountSkipZeros_of_isRotated hrot
  · calc
      cyclicFlipCountSkipZeros l
          = cyclicFlipCountSkipZeros l.reverse := (cyclicFlipCountSkipZeros_reverse l).symm
      _ = cyclicFlipCountSkipZeros m :=
          cyclicFlipCountSkipZeros_of_isRotated hrev
```

This is the key theorem replacing literal `rw [← R.linkOrder Q]`.

## Patch to `signChangesFull_eq_vertexFlip_rep`

Current proof:

```lean
unfold signChangesFull
rw [cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros]
rw [← R.linkOrder Q]
rfl
```

works only for exact equality. Replace by:

```lean
theorem signChangesFull_eq_vertexFlip_rep (Q : M.Vertex) :
    signChangesFull (R.starP Q).vertexLink (R.linkQ Q)
      = vertexFlipCountSkipZeros M R.edgeSign (R.dartRep Q) := by
  unfold signChangesFull
  rw [cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros]

  let geom :=
    (List.ofFn
      (linkDiff (R.starP Q).vertexLink (R.linkQ Q))).map realSignToEdgeSign
  let comb :=
    (M.σ.toList (R.dartRep Q)).map R.edgeSign

  have hcnt :
      cyclicFlipCountSkipZeros geom = cyclicFlipCountSkipZeros comb := by
    exact (cyclicFlipCountSkipZeros_of_dihedralRotated (R.linkOrder Q)).symm

  change cyclicFlipCountSkipZeros geom = cyclicFlipCountSkipZeros comb
  exact hcnt
```

If you use the stricter reversed field:

```lean
linkOrder_rev :
  ((M.σ.toList (dartRep Q)).map edgeSign).reverse = geom
```

then the proof is even shorter:

```lean
unfold signChangesFull
rw [cyclicFlips_nzSigns_eq_cyclicFlipCountSkipZeros]
rw [← R.linkOrder_rev Q]
rw [cyclicFlipCountSkipZeros_reverse]
rfl
```

Everything after this remains the same: `signChangesFull_eq_vertexFlip` transfers from `dartRep` to an arbitrary dart using `vertexFlipCountSkipZeros_sameCycle`, which already relies only on rotation invariance of `σ.toList`. fileciteturn102file0L20-L41

## Patch to `linkDiff_zero_of_edgeSign_zero`

The current proof uses exact list equality and membership. With `DihedralRotated`, use permutation/membership instead.

Add:

```lean
theorem perm_of_dihedralRotated {α : Type*} {l m : List α}
    (h : List.DihedralRotated l m) : l.Perm m := by
  rcases h with hrot | hrev
  · exact hrot.perm
  · exact (List.reverse_perm l).trans hrev.perm
```

The exact field names may be `List.IsRotated.perm` or you may need to unfold `hrot` as `⟨k, rfl⟩` and use `List.rotate_perm`.

Then in `linkDiff_zero_of_edgeSign_zero`, instead of rewriting the geometric list into the combinatorial list, do:

```lean
let geom :=
  (List.ofFn
    (linkDiff (R.starP Q).vertexLink (R.linkQ Q))).map realSignToEdgeSign

let comb :=
  (M.σ.toList (R.dartRep Q)).map R.edgeSign

have hperm : geom.Perm comb :=
  (perm_of_dihedralRotated (R.linkOrder Q)).symm

have hmem_geom :
    realSignToEdgeSign (linkDiff (R.starP Q).vertexLink (R.linkQ Q) i) ∈ geom := by
  apply List.mem_map.mpr
  exact ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩

have hmem_comb :
    realSignToEdgeSign (linkDiff (R.starP Q).vertexLink (R.linkQ Q) i) ∈ comb :=
  (hperm.mem_iff).mp hmem_geom

have hz :
    realSignToEdgeSign (linkDiff (R.starP Q).vertexLink (R.linkQ Q) i) = EdgeSign.zero := by
  obtain ⟨d, _, hd⟩ := List.mem_map.mp hmem_comb
  rw [← hd, hzero d]

exact (realSignToEdgeSign_eq_zero_iff _).mp hz
```

So the “all edge signs zero ⇒ all link differences zero” endpoint survives the interface change.

## Why this is honest

The current file itself says `linkOrder` is load-bearing because it records that the geometric rotational order matches the combinatorial `σ`-dart order. fileciteturn101file0L77-L81 But “matches” should mean **unoriented cyclic match**, not strict oriented list equality. The Cauchy sign machinery counts cyclic sign changes, and cyclic sign changes are unchanged by reversing the orientation of the cycle.

Weakening to `signChangesFull = vertexFlipCountSkipZeros` directly would be too close to the theorem’s crux; the file explicitly treats that equality as a derived theorem, not a structure field. fileciteturn100file0L24-L35 The relation `DihedralRotated` is still a real order bridge: it says every geometric link edge corresponds to the same combinatorial edge, in cyclic order, allowing only the unavoidable choice of orientation.

## Final recommendation

Use this hierarchy:

1. Keep `vertexStarOfEuclidean` in reversed `σ` order, because that is what satisfies `turn_support/turn_strict` with the current `det3`.
2. Replace strict `linkOrder` list equality by either:
   * `linkOrder_rev` if your bridge always uses reversed `σ`, or
   * `linkOrder : List.DihedralRotated comb geom` for the robust final interface.
3. Add `cyclicFlipCountSkipZeros_reverse` and `cyclicFlipCountSkipZeros_of_dihedralRotated`.
4. Update `signChangesFull_eq_vertexFlip_rep` and `linkDiff_zero_of_edgeSign_zero` as above.
5. Do not use `σ⁻¹.toList` unless you specifically need it elsewhere; it creates unnecessary rotate-offset bookkeeping.

This keeps the bridge non-vacuous, the tetrahedron satisfies it, and the abstract Cauchy proof remains honest: the crux sign-change equality is still derived from a concrete cyclic-order correspondence, not assumed.
