# ANSWER_36_01_agy — Ch36 Art Gallery Tier 1

## Recommended Tier 1

The Art Gallery theorem (Chvátal 1975, simplified by Fisk): a simple polygon
with n vertices can be guarded by at most ⌊n/3⌋ guards. The book's proof:
triangulate, 3-color, take the smallest color class.

You already have `exists_small_guard_color_class` proving the conclusion
given a 3-colored triangulation. Tier 1 wraps this with a structure for
the geometric input:

```lean
/-- Witness for the Art Gallery theorem: a triangulation of a simple polygon
where every triangle is 3-colored (each vertex assigned one of 3 colors,
each triangle has all 3 colors). -/
structure ArtGalleryWitness (n : ℕ) where
  /-- Vertex set of the polygon. -/
  vertices : Finset (Fin n)
  /-- Triangles in the triangulation. -/
  triangles : Finset (Fin n × Fin n × Fin n)
  /-- 3-coloring of vertices. -/
  color : Fin n → Fin 3
  /-- Every triangle uses all 3 colors. -/
  triangles_three_colored :
    ∀ t ∈ triangles, ∀ c : Fin 3, ∃ v ∈ ({t.1, t.2.1, t.2.2} : Finset (Fin n)), color v = c

/-- Chapter 36 (Art Gallery theorem, Tier 1 conditional):
Given a triangulation 3-coloring witness, a guard set of size ≤ n/3 exists
covering all triangles. Tier 2 (construct the triangulation + 3-coloring
from any simple polygon via ear-cutting + chromatic recursion) is deferred. -/
theorem chapter36 {n : ℕ} (w : ArtGalleryWitness n) :
    ∃ guards : Finset (Fin n),
      guards.card ≤ w.vertices.card / 3 ∧
      ∀ t ∈ w.triangles,
        ∃ v ∈ ({t.1, t.2.1, t.2.2} : Finset (Fin n)), v ∈ guards := by
  -- Apply the existing exists_small_guard_color_class with this witness.
  exact exists_small_guard_color_class w.vertices w.triangles w.color
    w.triangles_three_colored
```

(Adjust the `exists_small_guard_color_class` argument names/order to match
your file's exact signature.)

## Notes

- The chapter result IS Chvátal's bound. The Tier 1 hypothesis (triangulation
  + 3-coloring) is exactly what Fisk's proof reduces to. Tier 2 = "any simple
  polygon admits a triangulation, and any triangulation admits a 3-coloring"
  (the ear-cutting argument + 3-chromatic of planar triangulation).
- `Fin 3` represents red/green/blue.
- The guard set is "the smallest color class" (chosen inside `exists_small_guard_color_class`).

## Variant: if you want a more polished signature

```lean
theorem chapter36 {n : ℕ} (w : ArtGalleryWitness n) :
    ∃ guards : Finset (Fin n),
      guards ⊆ w.vertices ∧
      guards.card ≤ w.vertices.card / 3 ∧
      ∀ t ∈ w.triangles, ∃ v ∈ guards, v ∈ ({t.1, t.2.1, t.2.2} : Finset (Fin n))
```

Adjust depending on what `exists_small_guard_color_class` returns.

## Build + commit

~30 LOC including structure. Should build clean — both pieces (the structure
+ the wrapping) are trivial wiring.

Tier 2 docstring TODO: "Construct ArtGalleryWitness from any simple polygon
via Mathlib's triangulation (or build ear-cutting from scratch), then 3-color
the resulting planar triangulation (each ear-cut preserves 3-colorability)."

Go.
