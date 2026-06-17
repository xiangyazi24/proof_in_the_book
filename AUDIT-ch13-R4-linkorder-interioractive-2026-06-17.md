For your current setup, I would solve these two fields by making one design choice explicit:

**Choose `dartRep Q` and the Euclidean star order together.**  
For each vertex, build the star from the reverse of the `σ`-cycle rooted at `dartRep Q`; if the vertex is active, choose `dartRep Q` so that one active dart lands at an **interior** link index, preferably index `1`.

That simultaneously makes `linkOrder` an `Or.inr` proof of `DihedralRotated` and makes `interiorActive` a one-index proof at interior joint `0`.

The current realization layer’s `linkOrder` is the load-bearing field relating the `σ`-ordered edge-sign list to the link-ordered real-sign list. In the fetched version it was strict equality. fileciteturn101file0L142-L149 Your weakened `DihedralRotated` version is the right fix.

---

## 1. `linkOrder`: prove the reverse-rotation branch

Assume you define:

```lean
def DihedralRotated {α : Type*} (l m : List α) : Prop :=
  l ~r m ∨ l.reverse ~r m
```

Then the branch you want is:

```lean
Or.inr : ((M.σ.toList (dartRep Q)).map edgeSign).reverse ~r
  ((List.ofFn (linkDiff (starP Q).vertexLink (linkQcast … Q))).map realSignToEdgeSign)
```

The clean local proof should not try to rewrite `σ.toList` into an inverse-cycle list. Instead, introduce the dart-indexing function actually used by the star:

```lean
starDart Q : Fin ((starP Q).n + 1) → D
```

with two facts:

```lean
-- geometric star order is the reverse cyclic σ-order, up to starting-point rotation
starDart_order :
  ((M.σ.toList (dartRep Q)).map id).reverse ~r
    List.ofFn (starDart Q)

-- per-index value bridge
starDart_value :
  ∀ i,
    edgeSign (starDart Q i)
      =
    realSignToEdgeSign
      (linkDiff (starP Q).vertexLink (linkQcast M starP starQ hnn Q) i)
```

Then `linkOrder` is short.

```lean
lemma linkOrder_of_starDart_order
    (Q : M.Vertex)
    (horder :
      (M.σ.toList (dartRep Q)).reverse ~r List.ofFn (starDart Q))
    (hval :
      ∀ i,
        edgeSign (starDart Q i)
          =
        realSignToEdgeSign
          (linkDiff (starP Q).vertexLink (linkQcast M starP starQ hnn Q) i)) :
    DihedralRotated
      ((M.σ.toList (dartRep Q)).map edgeSign)
      ((List.ofFn
        (linkDiff (starP Q).vertexLink
          (linkQcast M starP starQ hnn Q))).map realSignToEdgeSign) := by
  classical
  right

  -- map `edgeSign` over the reversed σ-list.
  have horderSign :
      ((M.σ.toList (dartRep Q)).reverse.map edgeSign)
        ~r
      (List.ofFn (starDart Q)).map edgeSign :=
    horder.map edgeSign

  -- rewrite left side to reverse of mapped σ-list.
  have hleft :
      ((M.σ.toList (dartRep Q)).map edgeSign).reverse
        =
      (M.σ.toList (dartRep Q)).reverse.map edgeSign := by
    simp [List.map_reverse]

  -- rewrite right side by the per-index bridge.
  have hright :
      (List.ofFn (starDart Q)).map edgeSign
        =
      (List.ofFn
        (linkDiff (starP Q).vertexLink
          (linkQcast M starP starQ hnn Q))).map realSignToEdgeSign := by
    -- Use ext/getElem, or `List.ofFn_eq_map` + extensionality.
    apply List.ext_getElem
    · simp
    · intro k hk₁ hk₂
      simp only [List.getElem_map, List.getElem_ofFn]
      exact hval ⟨k, by simpa using hk₂⟩

  rw [hleft]
  exact horderSign.trans (by simpa [hright] using List.IsRotated.refl _)
```

Depending on your local imports, the final `refl` line may need:

```lean
simpa [hright] using horderSign
```

The important chain is:

```lean
σ-list.reverse ~r List.ofFn starDart
map edgeSign
rewrite RHS by per-index value match
```

### If the star is defined by `Fin.rev`

If you have a forward dart indexing

```lean
forwardDart Q : Fin m → D
```

and

```lean
starDart Q i = forwardDart Q (Fin.rev i)
```

then prove:

```lean
lemma ofFn_fin_rev {n : ℕ} (f : Fin n → α) :
    List.ofFn (fun i : Fin n => f (Fin.rev i)) = (List.ofFn f).reverse := by
  classical
  apply List.ext_getElem
  · simp
  · intro k hk₁ hk₂
    -- left[k] = f (Fin.rev ⟨k,_⟩)
    -- right[k] = f ⟨n - 1 - k,_⟩
    simp only [List.getElem_ofFn, List.getElem_reverse]
    congr
    apply Fin.ext
    simp [Fin.rev]
```

The exact simp proof may vary, but the statement is the right one.

Then combine with the forward order:

```lean
hforward :
  List.ofFn (forwardDart Q) ~r M.σ.toList (dartRep Q)
```

If the starting point differs, this is still enough. Add the standard helper:

```lean
lemma List.IsRotated.reverse {l l' : List α} (h : l ~r l') :
    l.reverse ~r l'.reverse := by
  rcases h with ⟨k, rfl⟩
  -- show `l.reverse ~r (l.rotate k).reverse`
  -- use `(l.rotate k).reverse = l.reverse.rotate (l.length - k % l.length)`
  -- If Mathlib lacks this exact lemma, prove it once from `rotate_eq_drop_append_take`.
  ...
```

Then:

```lean
have hstar :
    List.ofFn (starDart Q) ~r (M.σ.toList (dartRep Q)).reverse := by
  calc
    List.ofFn (starDart Q)
        = (List.ofFn (forwardDart Q)).reverse := ofFn_fin_rev _
    _ ~r (M.σ.toList (dartRep Q)).reverse := hforward.reverse
```

Use `.symm` if you need the opposite direction.

This is exactly “reverse-and-rotated.” Your `DihedralRotated l m := l ~r m ∨ l.reverse ~r m` captures it: `Or.inr` says `m` is a cyclic rotation of `l.reverse`.

### Avoid the `σ⁻¹.toList` route

Do not try to replace `σ.toList` by `(σ⁻¹).toList`. The offset is annoying:

```text
σ.toList x       = [x, σx, σ²x, ..., σⁿ⁻¹x]
σ⁻¹.toList x     = [x, σⁿ⁻¹x, ..., σx]
(σ.toList x).reverse = [σⁿ⁻¹x, ..., σx, x]
```

so there is always a rotate-by-one/length-minus-one bookkeeping theorem. The reverse-rotation relation is the right abstraction.

The repo already uses `List.IsRotated`, `.map`, `.trans`, and `SameCycle.toList_isRotated` for σ-orbit rotation invariance of flip counts. fileciteturn101file0L51-L65

---

## 2. `interiorActive`: do not derive this from `sides_eq + close_eq`

This part is subtle: **an active incident edge can land at closing index `0` or `n` if `dartRep` is arbitrary.** The field

```lean
interiorActive :
  ∀ Q,
    ActiveVertex M edgeSign (dartRep Q) →
      ∃ i : Fin ((starP Q).n - 1),
        jointAngle (starP Q).vertexLink i ≠
        jointAngle (linkQcast M starP starQ hnn Q) i
```

is already singled out in the realization interface as a load-bearing bridge. fileciteturn101file0L128-L136 And the full arm lemma takes this interior witness explicitly; it does not derive it from `sides_eq` and `close_eq`. fileciteturn106file0L129-L141

So the clean proof is **not**:

```lean
active edge differs
→ maybe closing angle differs
→ closing angles are pinned by sides/chord
→ therefore interior differs
```

That middle “closing angles are pinned” statement is generally false for a spherical arm. The closing chord plus edge lengths fixes the endpoint distance, not the two endpoint angles as independent quantities.

The clean proof is:

1. Choose `dartRep Q` so that, if the vertex is active, a selected active dart lands at link index `1`.
2. Link index `1` corresponds to interior joint index `0 : Fin ((starP Q).n - 1)`.
3. Nonzero edge sign at that dart gives nonzero `linkDiff` at link index `1`.
4. `linkDiff_interior` turns that into a nonzero `jointDiff` at interior index `0`.

The repo’s `linkDiff_interior` is exactly the bridge:

```lean
linkDiff A B ⟨i.val + 1, ...⟩ = jointDiff A B i
```

fileciteturn106file0L111-L117

### Adaptive `dartRep`

Let `baseRep Q` be any dart with tail `Q`. Define, noncomputably:

```lean
noncomputable def activeDart? (Q : M.Vertex) :
    Option D :=
  if h : ∃ x : D, M.σ.SameCycle (baseRep Q) x ∧ edgeSign x ≠ EdgeSign.zero
  then some h.choose
  else none
```

Then choose:

```lean
noncomputable def dartRep (Q : M.Vertex) : D :=
  match activeDart? Q with
  | some x => (M.σ ^ 2) x
  | none   => baseRep Q
```

Why `(σ ^ 2) x`? Because your star order is the **reverse** of the forward `σ.toList` order. If the degree is `m = n + 1`, then reverse-index `1` corresponds to forward-index `m - 2`. Starting at `r = σ² x`, the forward index `m - 2` is:

```text
σ^(m-2) (σ² x) = σ^m x = x
```

so the selected active dart `x` lands at star index `1`.

You then want a construction lemma from your star-indexing layer:

```lean
lemma activeDart_at_star_index_one
    {Q : M.Vertex} {x : D}
    (hactiveChoice : activeDart? Q = some x) :
    starDart Q ⟨1, by
      have hn := (starP Q).hn
      omega⟩ = x := by
  -- unfold `dartRep`, `starDart`, `Fin.rev`, and `Perm.toList` getElem theorem
  -- use cycle length = `(starP Q).n + 1`
  ...
```

You do **not** want to reprove this inside `interiorActive`; make it a star-construction lemma.

### `interiorActive` proof skeleton

Assume these local facts:

```lean
-- The selected active dart is placed at link index 1.
active_index_one :
  ActiveVertex M edgeSign (dartRep Q) →
    edgeSign (starDart Q ⟨1, by have := (starP Q).hn; omega⟩) ≠ EdgeSign.zero

-- Per-index bridge from edge sign to link diff.
starDart_value :
  ∀ i,
    edgeSign (starDart Q i)
      =
    realSignToEdgeSign
      (linkDiff (starP Q).vertexLink
        (linkQcast M starP starQ hnn Q) i)
```

Then the field is:

```lean
lemma interiorActive_of_active_index_one
    (Q : M.Vertex)
    (hact : ActiveVertex M edgeSign (dartRep Q)) :
    ∃ i : Fin ((starP Q).n - 1),
      jointAngle (starP Q).vertexLink i ≠
      jointAngle (linkQcast M starP starQ hnn Q) i := by
  classical

  let A := (starP Q).vertexLink
  let B := linkQcast M starP starQ hnn Q
  let one : Fin ((starP Q).n + 1) :=
    ⟨1, by have hn := (starP Q).hn; omega⟩

  have hsign :
      realSignToEdgeSign (linkDiff A B one) ≠ EdgeSign.zero := by
    rw [← starDart_value Q one]
    exact active_index_one Q hact

  have hdiff : linkDiff A B one ≠ 0 := by
    intro h0
    exact hsign ((realSignToEdgeSign_eq_zero_iff _).2 h0)

  let i : Fin ((starP Q).n - 1) :=
    ⟨0, by have hn := (starP Q).hn; omega⟩

  refine ⟨i, ?_⟩

  have hone_eq :
      one = (⟨i.val + 1, by
        have hi := i.isLt
        have hn := (starP Q).hn
        omega⟩ : Fin ((starP Q).n + 1)) := by
    apply Fin.ext
    simp [one, i]

  have hjointDiff : jointDiff A B i ≠ 0 := by
    have h := hdiff
    rw [hone_eq, linkDiff_interior A B i] at h
    exact h

  -- `jointDiff A B i = jointAngle B i - jointAngle A i`
  unfold jointDiff at hjointDiff
  intro hEq
  apply hjointDiff
  rw [hEq]
  ring
```

If `ring` does not close the last line, use:

```lean
linarith
```

or:

```lean
simp [sub_eq_zero, hEq]
```

depending on the exact `jointDiff` definition.

### Deriving `active_index_one`

This is where adaptive `dartRep` pays off.

```lean
lemma active_index_one
    (Q : M.Vertex)
    (hact : ActiveVertex M edgeSign (dartRep Q)) :
    edgeSign (starDart Q ⟨1, by have hn := (starP Q).hn; omega⟩) ≠ EdgeSign.zero := by
  classical

  -- From active at `dartRep Q`, get existence of a nonzero sign in the vertex σ-cycle.
  rcases hact with ⟨x, hxcycle, hxnonzero⟩

  -- This makes the `activeDart?` branch nonempty.
  have hNonempty :
      ∃ y : D, M.σ.SameCycle (baseRep Q) y ∧ edgeSign y ≠ EdgeSign.zero := by
    refine ⟨x, ?_, hxnonzero⟩
    -- `baseRep Q` and `dartRep Q` have the same tail / same σ-cycle,
    -- then compose with `hxcycle`.
    exact (sameCycle_baseRep_dartRep Q).trans hxcycle

  -- Let `x₀` be the chosen active dart.
  -- Since `activeDart?` chooses from `hNonempty`, obtain selected nonzero.
  unfold activeDart? at *
  simp [hNonempty] at *
  -- after simplification, `activeDart? Q = some hNonempty.choose`;
  -- use `activeDart_at_star_index_one`.
  have hidx := activeDart_at_star_index_one Q ...
  rw [hidx]
  exact hNonempty.choose_spec.2
```

The exact simplification depends on how you define `activeDart?`. The important invariant is:

```lean
if active, star index 1 is a chosen nonzero edge-sign dart.
```

Make that a lemma of the representative/star construction.

---

## 3. Do not use endpoint pinning unless you prove a real theorem

You asked whether the differing index can be shown interior because “boundary/closing angles are pinned equal by `sides_eq + close_eq`.”

I would not use that. In the current formal architecture, the full link has `n+1` link angles, while the arm has only `n-1` interior joints; the two angles at `0` and `n` are explicitly the hidden closing-edge angles. fileciteturn106file0L8-L19 The full-arm theorem still takes an explicit interior activity witness. fileciteturn106file0L129-L141

So unless you prove a separate strong geometric theorem:

```lean
linkDiff A B 0 = 0 ∧ linkDiff A B (Fin.last n) = 0
```

from your particular realization data, do not try to route through endpoint equality. It is not a consequence of the current `sides_eq` and `close_eq` fields alone.

---

## 4. Recommended final field-support package

For each vertex `Q`, expose the following from your Euclidean star construction:

```lean
starDart : Fin ((starP Q).n + 1) → D

starDart_order :
  ((M.σ.toList (dartRep Q)).reverse) ~r List.ofFn (starDart Q)

starDart_value :
  ∀ i,
    edgeSign (starDart Q i)
      =
    realSignToEdgeSign
      (linkDiff (starP Q).vertexLink
        (linkQcast M starP starQ hnn Q) i)

active_index_one :
  ActiveVertex M edgeSign (dartRep Q) →
    edgeSign (starDart Q ⟨1, by have hn := (starP Q).hn; omega⟩) ≠ EdgeSign.zero
```

Then:

* `linkOrder` is `Or.inr`, by `starDart_order.map edgeSign` plus `starDart_value`.
* `interiorActive` is `⟨0, ...⟩`, by `active_index_one`, `realSignToEdgeSign_eq_zero_iff`, and `linkDiff_interior`.

This is the least painful and most honest route: the cyclic/reversal issue is confined to the order bridge, and the interior-active issue is solved by representative choice rather than an untrue endpoint-angle pinning claim.
