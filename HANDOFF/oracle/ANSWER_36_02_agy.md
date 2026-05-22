# ANSWER_36_02_agy — Combinatorial triangulation skeleton for Ch36

## Yes, inductive `TriangulatedPolygon` is the right call.

Build the structure by induction on # of triangles. Each step adds one triangle
glued along exactly one edge. This bypasses planar geometry entirely and
gives ear-cutting + 3-coloring for free.

## Recommended skeleton

```lean
/-- A triangle on three distinct vertices of `Fin n`. -/
structure AbsTriangle (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  hab : a ≠ b
  hbc : b ≠ c
  hac : a ≠ c

/-- The (undirected) edges of an abstract triangle, as a finset of unordered
pairs. -/
def AbsTriangle.edges {n : ℕ} (T : AbsTriangle n) : Finset (Sym2 (Fin n)) :=
  {s(T.a, T.b), s(T.b, T.c), s(T.a, T.c)}

/-- A combinatorial triangulation: inductively, either a single triangle, or
an existing triangulation with one new triangle glued along exactly one edge.
The "new" vertex of the added triangle is fresh (not already used by the
existing triangulation), so adjacency is unambiguous. -/
inductive TriangulatedPolygon (n : ℕ) : Finset (AbsTriangle n) → Prop
  | single (T : AbsTriangle n) :
      TriangulatedPolygon n {T}
  | glue {S : Finset (AbsTriangle n)} (h : TriangulatedPolygon n S)
      (T : AbsTriangle n)
      (newVertex : Fin n)
      (hT_new : newVertex ∈ ({T.a, T.b, T.c} : Finset (Fin n)))
      (hShared : ∃ T' ∈ S, ∃ e ∈ T.edges, e ∈ T'.edges ∧ newVertex ∉ e)
      (hFresh : ∀ T' ∈ S, newVertex ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n))) :
      TriangulatedPolygon n (insert T S)
```

The key invariant baked in by `hFresh`: each new triangle introduces exactly
one **new** vertex, so when we add `T` we can 3-color it based on the two
already-colored shared-edge vertices.

## Main theorems to prove

```lean
/-- Vertices of a triangulation. -/
def TriangulatedPolygon.vertices {n : ℕ} {S : Finset (AbsTriangle n)} :
    TriangulatedPolygon n S → Finset (Fin n)
  | .single T => {T.a, T.b, T.c}
  | .glue h T v _ _ _ => insert v h.vertices

/-- Main: every combinatorial triangulation has a proper 3-coloring. -/
theorem TriangulatedPolygon.exists_3coloring {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ c : Fin n → Fin 3,
      ∀ T ∈ S, c T.a ≠ c T.b ∧ c T.b ≠ c T.c ∧ c T.a ≠ c T.c := by
  induction h with
  | single T =>
      -- Color T.a := 0, T.b := 1, T.c := 2.
      refine ⟨fun v => if v = T.a then 0 else if v = T.b then 1 else 2, ?_⟩
      intro T' hT'
      simp at hT'
      subst hT'
      refine ⟨?_, ?_, ?_⟩ <;> · simp [T.hab, T.hbc, T.hac]; decide
  | glue h_ind T v hT_new hShared hFresh ih =>
      -- Extract c from ih; for new vertex v, pick the color
      -- different from the two shared-edge endpoints. Since they have
      -- 2 distinct colors (the shared edge was colored properly),
      -- exactly one of {0,1,2} remains.
      obtain ⟨c, hc⟩ := ih
      -- Find the shared edge and its color pair, extend c at v.
      sorry  -- ~30 LOC: define c' := if · = v then chooseColor else c ·
```

## Ear-cutting lemma (the heart)

```lean
/-- Any TriangulatedPolygon with ≥ 2 triangles has a triangle with a
"free" vertex (degree 1 in the triangulation, i.e., the ear). -/
theorem TriangulatedPolygon.exists_ear {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) (hS : S.card ≥ 2) :
    ∃ T ∈ S, ∃ v ∈ ({T.a, T.b, T.c} : Finset (Fin n)),
      ∀ T' ∈ S, T' ≠ T → v ∉ ({T'.a, T'.b, T'.c} : Finset (Fin n)) := by
  -- Directly: induction. In `.glue h T v _ _ hFresh _`, the new vertex `v`
  -- is in `T` only (by `hFresh`). So `T` is the ear, `v` is its free vertex.
  cases h with
  | single _ => exact absurd hS (by simp)
  | glue h_ind T newV _ _ hFresh =>
      refine ⟨T, by simp, newV, ?_, ?_⟩
      · sorry  -- newV ∈ {T.a, T.b, T.c} from hT_new
      · intro T' hT' hne
        simp at hT'
        rcases hT' with rfl | hT'S
        · exact absurd rfl hne
        · exact hFresh T' hT'S
```

## Chapter36 Tier 2 statement to aim for

```lean
theorem chapter36_artgallery_combinatorial {n : ℕ} {S : Finset (AbsTriangle n)}
    (h : TriangulatedPolygon n S) :
    ∃ guards : Finset (Fin n), guards.card ≤ n / 3 ∧
      ∀ T ∈ S, ∃ v ∈ guards,
        v ∈ ({T.a, T.b, T.c} : Finset (Fin n)) := by
  -- 3-color, then pick the smallest color class.
  obtain ⟨c, hc⟩ := h.exists_3coloring
  -- The smallest of three classes has size ≤ ⌊n/3⌋.
  sorry  -- ~40 LOC
```

## Pragmatic scope estimate

- `AbsTriangle` + `edges`: ~20 LOC
- `TriangulatedPolygon` inductive: ~15 LOC
- `exists_3coloring`: ~50 LOC (the `glue` case has fiddly "pick remaining
  color" logic)
- `exists_ear`: ~25 LOC
- `chapter36_artgallery_combinatorial`: ~40 LOC
- **Total**: ~150 LOC, end-to-end, no Mathlib gaps.

This replaces the `ArtGalleryWitness` hypothesis with a `TriangulatedPolygon`
input that is itself a real combinatorial object (no Prop-witness magic).
The chapter statement becomes "if you have a combinatorial triangulation,
then ⌊n/3⌋ guards suffice", which is the heart of the Fisk argument with
the geometry abstracted away.

## Things to NOT do

- Do NOT add `IsTriangulation` as a Prop hypothesis taking the 3-coloring
  as input. That's a Tier 1 dodge.
- Do NOT use `axiom`. The whole point is to construct this inductively.
- Do NOT prove the "ear exists" geometrically. Use the inductive
  definition's `hFresh` directly.

Go. Aim to ship `exists_3coloring` first as the centerpiece; everything
else hangs off it.
