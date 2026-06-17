[intro]
I’ll verify the exact landed boundary and chord-cycle APIs first, then make the architecture call. The key thing I’m checking is whether `BoundaryArcSplit` carries indices/darts or only vertex/edge lists.

I found the important boundary-layer fact: `BoundaryArcSplit` does **not** store positions into `outerCycle.darts`; it stores two `BoundaryPath`s, and each `BoundaryPath` has vertex and edge lists only. The dart-level recovery has to go through `BoundaryCycle.darts`/`DartArc`, not through `data.arc.path₂` directly.

[answer]
## 1. Incidence layer: not recoverable from `data.arc` alone

`BoundaryArcSplit` does **not** store positions or darts. It stores:

```lean
path₁ : BoundaryPath M u v
path₂ : BoundaryPath M v u
```

and `BoundaryPath` stores only:

```lean
vertices : List M.Vertex
edges    : List (Sym2 M.Vertex)
```

plus start/end/simple fields. There is no `Fin` index into `hNT.outerCycle.darts`, no dart list, and no proof that a listed edge is represented by a specific dart in `outerCycle.darts`. filecite
vertices : List M.Vertex
edges : List (Sym2 M.Vertex)
```

with `consecutive_phi`, `consecutive_vertex`, and `arcSplit`. fileciteturn30file0L121-L155

So:

```text
data.arc.path₂.internalVertices
```

can tell you a vertex `w` is internally listed on the abstract opposite boundary path, but it cannot tell you:

```lean
∃ d₋ d₊ : D,
  d₋ ∈ hNT.outerCycle.darts ∧
  d₊ ∈ hNT.outerCycle.darts ∧
  M.head d₋ = w ∧
  M.tail d₊ = w ∧
  ...
```

That missing bridge is real.

---

## 2. Recoverable route, if you add an index/dart arc certificate

The repo already has the right low-level tool: `DartArc`.

`DartArc` is explicitly the dart-level analogue of `BoundaryPath`: it stores

```lean
len : ℕ
arcDart : Fin len → D
boundary : ∀ i, arcDart i ∈ C.darts
chain : ...
tail_first : ...
head_last : ...
tail_nodup : ...
head_last_ne_tail : ...
```

so it gives exactly the darts that `BoundaryPath` lacks.  arc directly from the `BoundaryCycle.darts` list using start position `p` and length `k`:

```lean
def boundaryDartArc
    (C : BoundaryCycle M f) (hC : C.VertexNodup)
    (p k : ℕ) (hk : 1 ≤ k) (hpk : p + k < C.darts.length)
    (hp : p < C.darts.length) :
    DartArc M C
      (M.tail (C.darts.get ⟨p, hp⟩))
      (M.tail (C.darts.get ⟨p + k, hpk⟩))
```

This is explicitly described as a contiguous slice of `C.darts`, not a `BoundaryPath` extraction. citeturn31file0L138ArcSplit
    (M : CombMap D) (C : BoundaryCycle M f)
    (u v : M.Vertex) : Type u where
  p₁ k₁ : ℕ
  p₂ k₂ : ℕ
  hp₁ : p₁ < C.darts.length
  hp₂ : p₂ < C.darts.length
  hk₁ : 2 ≤ k₁
  hk₂ : 2 ≤ k₂
  hpk₁ : p₁ + k₁ < C.darts.length
  hpk₂ : p₂ + k₂ < C.darts.length

  arc₁D : DartArc M C u v
  arc₂D : DartArc M C v u

  arc₁_eq :
    arc₁D =
      boundaryDartArc C C_vertex_nodup p₁ k₁ (by omega) hpk₁ hp₁
  arc₂_eq :
    arc₂D =
      boundaryDartArc C C_vertex_nodup p₂ k₂ (by omega) hpk₂ hp₂

  path₁_vertices_eq :
    data.arc.path₁.vertices =
      (List.ofFn (fun i : Fin arc₁D.len => M.tail (arc₁D.arcDart i)))
        ++ [v]
  path₂_vertices_eq :
    data.arc.path₂.vertices =
      (List.ofFn (fun i : Fin arc₂D.len => M.tail (arc₂D.arcDart i)))
        ++ [u]
```

Then the two missing path2 incidence facts become straightforward workers:

```lean
theorem path₂_internal_has_boundary_darts
    (split : BoundaryDartArcSplit M hNT.outerCycle u v)
    {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices) :
    ∃ i : Fin split.arc₂D.len,
      M.tail (split.arc₂D.arcDart i) = w ∧
      split.arc₂D.arcDart i ∈ hNT.outerCycle.darts
```

and the stronger two-neighbor version:

```lean
theorem path₂_internal_has_two_boundary_star_darts
    (split : BoundaryDartArcSplit M hNT.outerCycle u v)
    {w : M.Vertex}
    (hw : w ∈ data.arc.path₂.internalVertices) :
    ∃ i : Fin split.arc₂D.len,
      ∃ hprev hnext,
        M.head (split.arc₂D.arcDart ⟨i.1 - 1, hprev⟩) = w ∧
        M.tail (split.arc₂D.arcDart i) = w ∧
        split.arc₂D.arcDart ⟨i.1 - 1, hprev⟩ ∈ hNT.outerCycle.darts ∧
        split.arc₂D.arcDart i ∈ hNT.outerCycle.darts
```

But without such an index/dart certificate, `data.arc.path₂` is too weak.

---

## 3. C-arc identification

The generic `SimplePrimalCycle` structure is in `PlanarMapCutCap.lean`. It stores:

```lean
len : ℕ
len_ge : 3 ≤ len
dart : Fin len → D
tail_inj : Function.Injective (fun i => M.tail (dart i))
consecutive : ...
```

and also defines `dartSet` and `edgeSet`. citeturn61file0L4 a chord dart oriented `v → u`, the cycle is `chord :: arc`, and its `SimplePrimalCycle` fields are proved from `DartArc.chain`, `DartArc.tail_nodup`, and the internal-vertex length bound. citeturn62 named `chordCycleData` through the connector search; the name may be in a newer file not indexed by the connector or under a different spelling. But the concrete constructor route I can verify is:

```text
BoundaryCycle.darts
  → DartArc.boundaryDartArc
  → chord :: arc
  → SimplePrimalCycle
```

Therefore the right C-identification lemma should be stated against the concrete `DartArc`-built cycle:

```lean
theorem chordArcCycle_edgeSet_eq
    (A : DartArc M hNT.outerCycle u v)
    (chord : D)
    (hch_tail : M.tail chord = v)
    (hch_head : M.head chord = u)
    (C : SimplePrimalCycle M) -- built as chord :: A.arcDart
    :
    C.edgeSet =
      ({M.dartEdge chord} ∪
        (Finset.univ.image (fun i : Fin A.len => M.dartEdge (A.arcDart i))))
```

and the path1 identification:

```lean
theorem chordArcCycle_edges_eq_chord_union_path₁
    (split : BoundaryDartArcSplit M hNT.outerCycle u v)
    (C : SimplePrimalCycle M) -- built from split.arc₁D
    :
    C.edgeSet =
      ({s(u,v)} ∪ split.path₁_edgeFinset)
```

where

```lean
split.path₁_edgeFinset =
  Finset.univ.image (fun i : Fin split.arc₁D.len =>
    M.dartEdge (split.arc₁D.arcDart i))
```

If the current `jordan_simple_cycle2_unconditional` is instantiated with an abstract boundary run not tied to `data.arc.path₁`, the cleanest technical route is to **re-instantiate** it with the concrete `DartArc.boundaryDartArc` path1 cycle. That is better than trying to prove an arbitrary abstract C equals the path1 C.

---

## 4. Architecture call

I recommend route 3: add `OppArcStarSeed` and `edge_core` to the planar input class.

Reason: route 1/2 is recoverable only after adding a new dart-indexed boundary split and proving it agrees with `data.arc.path₁/path₂`. That is not 150–300 lines. It is a new boundary-incidence layer:

```text
BoundaryArcSplit vertex paths
↔ positions in BoundaryCycle.darts
↔ DartArc path1/path2
↔ concrete SimplePrimalCycle C
↔ path2 internal vertices off C
↔ star darts and bank seeds
```

That is likely 500–1000 lines if done honestly, because the current `BoundaryArcSplit` intentionally omitted the dart/index data.

The repo already treats `arcSplit`, `outer_simple`, `outer_len`, and `inner_reps` as planar inputs at the side-boundary layer. Adding the final vertex/edge-star confinement inputs is architecturally consistent and honest.

Use this final input bundle:

```lean
structure Side₁ConfinementInput
    (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (C : SimplePrimalCycle M) : Prop where

  /-- The cycle used by the Jordan engine is the chord plus the side-1 boundary arc. -/
  C_edgeSet :
    C.edgeSet =
      ({s(u,v)} : Finset (Sym2 M.Vertex)) ∪ path₁BoundaryEdgeSet data

  /-- Opposite-arc internal vertices are off the cycle and have a face₂-bank
      star seed with a cut-free rotation walk. -/
  oppArcStarSeed :
    ∀ {w : M.Vertex},
      w ∈ data.arc.path₂.internalVertices →
        ∃ d : StarDart M w,
          DualReachableAvoidingCycle M C data.face₂ (starFace w d) ∧
          CutFreeStarWalkToBoundaryBank M C w d

  /-- Ambient edges between sideRegion₁ vertices are represented in the side-1 carve,
      except for the chord seam. -/
  edge_core :
    ∀ {e : D},
      M.tail e ∈ sideRegion₁ data →
      M.head e ∈ sideRegion₁ data →
        ((e ∉ data.keptDel₁ ∧ M.α e ∉ data.keptDel₁) ∨
          M.dartEdge e = s(u,v))
```

If you want the absolutely minimal final bundle, omit `C_edgeSet` and make the two operational fields self-contained:

```lean
structure Side₁SchoenfliesConfinementInput
    (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) : Prop where

  oppArcStarSeed :
    ∀ {w : M.Vertex},
      w ∈ data.arc.path₂.internalVertices →
        w ∉ sideRegion₁ data

  edge_core :
    ∀ {e : D},
      M.tail e ∈ sideRegion₁ data →
      M.head e ∈ sideRegion₁ data →
        ((e ∉ data.keptDel₁ ∧ M.α e ∉ data.keptDel₁) ∨
          M.dartEdge e = s(u,v))
```

This latter shape is the most useful for closing Ch35 now.

---

## 5. Final closing lemmas from the bundle

### `homit`

```lean
theorem homit_of_confinementInput
    (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (H : Side₁SchoenfliesConfinementInput data hsep) :
    ∃ w : M.Vertex, w ∉ sideRegion₁ data := by
  obtain ⟨w, hw_listed, hw_ne_start, hw_ne_end⟩ :=
    data.arc.path₂.exists_internal_vertex data.arc₂_internal
  -- Need convert `hw_listed` to `w ∈ data.arc.path₂.internalVertices`
  exact ⟨w, H.oppArcStarSeed hw_internal⟩
```

`ChordSplitData` carries both `arc₁_internal` and `arc₂_internal`; these are the nonempty internal-vertex facts. citeturn42file0L4-L4

### `hreflect`

```lean
theorem hreflect_of_confinementInput
    (data : hNT.ChordSplitData u v)
    (hsep : data.Separates)
    (a₀ a₁ : {d : D // d ∉ data.keptDel₁})
    (hne : a₀ ≠ a₁)
    (H : Side₁SchoenfliesConfinementInput data hsep) :
    ∀ ⦃x y : (data.sideMap₁ hsep a₀ a₁ hne).Vertex⦄,
      M.toSimpleGraph.Adj
        (sideVertexToM₁ data hsep a₀ a₁ hne x)
        (sideVertexToM₁ data hsep a₀ a₁ hne y) →
      (data.sideMap₁ hsep a₀ a₁ hne).toSimpleGraph.Adj x y := by
  intro x y hAdj
  -- choose ambient dart e witnessing hAdj
  -- sideVertexToM₁_mem gives both endpoints in sideRegion₁
  -- apply H.edge_core
  -- kept case: use Sum.inl ⟨e, he⟩
  -- chord case: use Sum.inr 0 or Sum.inr 1
```

This exactly supplies the `ι_adj_reflect` field expected by `ChordSideResidue`.

---

## 6. Ordered bricks for recommended route

### Brick 1 — define final input bundle  
**Worker, 20–40 lines**

```lean
structure Side₁SchoenfliesConfinementInput
    (data : hNT.ChordSplitData u v)
    (hsep : data.Separates) : Prop where
  oppArcStarSeed :
    ∀ {w : M.Vertex},
      w ∈ data.arc.path₂.internalVertices →
        w ∉ sideRegion₁ data
  edge_core :
    ∀ {e : D},
      M.tail e ∈ sideRegion₁ data →
      M.head e ∈ sideRegion₁ data →
        ((e ∉ data.keptDel₁ ∧ M.α e ∉ data.keptDel₁) ∨
          M.dartEdge e = s(u,v))
```

### Brick 2 — `homit` from input  
**Worker, 20–50 lines**

Use `data.arc₂_internal` and `BoundaryPath.exists_internal_vertex`.

### Brick 3 — side adjacency from kept dart  
**Worker, 50–90 lines**

```lean
lemma side_adj_of_kept_edge
    (he : e ∉ data.keptDel₁)
    (hae : M.α e ∉ data.keptDel₁) :
    S.toSimpleGraph.Adj
      (S.dartVertex (Sum.inl ⟨e, he⟩))
      (S.dartVertex (S.α (Sum.inl ⟨e, he⟩)))
```

plus endpoint identification through `sideVertexToM₁`.

### Brick 4 — side adjacency from chord case  
**Worker, 50–100 lines**

Use `Sum.inr 0`/`Sum.inr 1` and the canonical anchor endpoint equations.

### Brick 5 — `hreflect` from `edge_core`  
**Master, 100–160 lines**

Choose the ambient dart from `M.toSimpleGraph.Adj`, apply `edge_core`, dispatch kept/chord cases.

### Brick 6 — final `ChordSideResidue` close  
**Master, 20–40 lines**

Plug:

```lean
hreflect_of_confinementInput
homit_of_confinementInput
```

into `chordSideResidue₁_partial`.

---

## 7. If you later want to recover the input instead of assuming it

Add a separate file:

```lean
ZinanCh35BoundaryIncidence.lean
```

with:

1. `BoundaryDartArcSplit`
2. `path₂_internal_has_boundary_darts`
3. concrete `C = chord :: path₁DartArc`
4. `C.edgeSet = chord ∪ path₁.edges`
5. `path₂_internal_off_C`
6. `OppArcStarSeed`
7. `edge_core`

That is a future full-discharge path, but it is not the shortest honest route to finish the current Ch35 chain.

---

## 8. Degenerate audit

* **`w` adjacent to `u` or `v`**: allowed only if it is still internal to `path₂`; internality gives `w ≠ u` and `w ≠ v`, so it is not a chord endpoint.
* **`w` shared by both arcs**: excluded by `BoundaryArcSplit.internally_disjoint`; but since current `BoundaryPath` has no darts, this only works at vertex-list level.
* **outer length 3**: valid. Then each arc has minimal internal structure; the input still handles it.
* **chord endpoints adjacent on old boundary**: excluded by `data.chord.not_boundary_edge`.
* **C arc mismatch**: this is the dangerous case. If C was built from an abstract arc not identified with `data.arc.path₁`, do not derive `OppArcStarSeed`; either reinstantiate C with `DartArc.boundaryDartArc`, or assume `OppArcStarSeed` in the final input bundle.
* **boundary darts at a path2-internal vertex**: not derivable from `data.arc` alone. This is precisely why the input bundle is the honest final architectural layer.
