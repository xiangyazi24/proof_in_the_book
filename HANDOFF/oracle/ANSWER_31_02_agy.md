# ANSWER_31_02_agy — IsTree + Inverses blueprint

## The one supporting lemma you need first

Before any of the three, prove this:

```lean
/-- Leaf characterization: `v` is a leaf of `T` iff `v` is NOT in the image
of `pruferEncode T`. This is the central combinatorial fact behind Prüfer codes. -/
theorem pruferEncode_image_eq_nonleaves
    (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    Finset.image (pruferEncode n hn T) Finset.univ =
      (Finset.univ : Finset (Fin n)).filter (fun v => ¬ T.1.degree v = 1) := by
  -- More precisely: count(v in encode(T)) = deg_T(v) - 1.
  -- Proof: by induction on n.
  --   - Base n = 2: encode = empty, all vertices have degree 1, image is ∅.
  --   - Step: encode T = neighbor :: encode(T \ {leaf}). The neighbor contributes one
  --     extra count for itself; the recursive call gives count = deg_{T \ leaf}(v) - 1
  --     for v ≠ leaf. Combine: deg_T(neighbor) = deg_{T\leaf}(neighbor) + 1, leaves of
  --     T are leaves of T\leaf plus possibly the neighbor (if its T-degree was 2).
  sorry -- ~50 lines, the most important supporting lemma
```

Or in the more useful form for the inverses:

```lean
theorem mem_pruferEncode_image_iff
    (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) (v : Fin n) :
    (∃ i, pruferEncode n hn T i = v) ↔ T.1.degree v ≥ 2 := by
  sorry
```

This is the **bridge** between the algorithmic encoding and the structural tree property.
Without it, every inverse step has to recompute the leaf-set, which makes the proof
exponentially uglier. Spend 50 lines here; everything downstream becomes mechanical.

## Lemma 1: `pruferDecodeIsTree`

Strategy: avoid `SimpleGraph.IsTree` directly. Instead prove the three parts:
**|E| = n - 1**, **acyclic**, **connected** — and combine via Mathlib's
`SimpleGraph.IsTree.mk` (or equivalent characterization in your Mathlib snapshot).

```lean
/-- Invariant maintained by the decode loop. -/
structure DecodeInvariant (n : ℕ) (i : ℕ) (state : Finset (Fin n) × Finset (Sym2 (Fin n))) :
    Prop where
  available_card : state.1.card = n - i
  edges_card : state.2.card = i
  -- "Forest" part: the graph (Fin n, state.2) is acyclic
  acyclic : (SimpleGraph.fromEdgeSet (state.2 : Set (Sym2 (Fin n)))).IsAcyclic
  -- "Component count" part: this graph has exactly n - i connected components
  components : (SimpleGraph.fromEdgeSet (state.2 : Set _)).ConnectedComponent.card = n - i
  -- Each removed vertex (not in available) has degree exactly 1 in the current graph
  removed_are_leaves :
    ∀ v : Fin n, v ∉ state.1 → (SimpleGraph.fromEdgeSet (state.2 : Set _)).degree v = 1
```

The induction:

```lean
lemma decodeInvariant_step (n hn s i) (h : DecodeInvariant n i (pruferDecodeStep n hn s i)) :
    DecodeInvariant n (i + 1) (pruferDecodeStep n hn s (i + 1)) := by
  -- Step i+1 picks v = min(available \ future) and adds edge {v, s[i]}.
  -- Verify each invariant component is preserved.
  -- available_card: removed one vertex, so |.| decreases by 1.
  -- edges_card: added one edge.
  -- acyclic: the new edge {v, s[i]} doesn't create a cycle because v had degree 0
  --   (it's in available_i, so it's not in "removed", so its edges so far come only from
  --   the empty contribution — actually need to be careful: are the previous removed
  --   leaves attached to v? No — by `removed_are_leaves`, removed vertices have degree 1
  --   pointing to s[j]'s, not to v. And v itself has no edge in state_i.edges since it's
  --   available. So adding {v, s[i]} can't make a cycle.)
  -- components: merging two components into one (or v's singleton with s[i]'s component).
  -- removed_are_leaves: v is newly removed with degree 1 (the new edge). Others unchanged.
  sorry
```

Then:

```lean
theorem pruferDecodeIsTree (n hn s) :
    (SimpleGraph.fromEdgeSet (pruferDecodeEdges n hn s : Set _)).IsTree := by
  -- After n - 2 loop iterations, available has size 2 and edges has size n - 2.
  -- Apply decodeInvariant_step (n-2) times via induction.
  -- Then add the final edge between the 2 remaining available vertices:
  --   - acyclic preserved (same argument)
  --   - components: 2 - 1 = 1 (single tree)
  --   - |E| = n - 1
  -- Convert "n-1 edges + acyclic + connected on n vertices" to IsTree.
  sorry
```

**Key Mathlib API to use** (if exact names differ in your snapshot, grep):
- `SimpleGraph.IsAcyclic` ; `SimpleGraph.IsTree`
- `SimpleGraph.fromEdgeSet`
- `SimpleGraph.ConnectedComponent`
- `SimpleGraph.degree`

If `IsAcyclic` is hard to invoke directly, use the equivalent: "no `Walk.IsCycle`" or
"every edge is a bridge". Or take the unique-path characterization.

## Lemma 2: `pruferDecode_pruferEncode T = T`

Strong induction on `m := n - 2`.

```lean
theorem pruferDecode_pruferEncode (n hn T) :
    pruferDecode n hn (pruferEncode n hn T) = T := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  induction m with
  | zero =>
    -- n = 2. encode T = empty. decode empty = the tree with single edge between
    -- the 2 elements of Fin 2. Since T has 2 vertices and is a tree, it has exactly
    -- 1 edge between them. So they coincide.
    apply LabeledTree.ext  -- or whatever extensionality lemma you have on LabeledTree
    -- show the underlying SimpleGraphs are equal
    sorry  -- finite case, mostly Decidable stuff
  | succ m ih =>
    -- n = m + 3. Let s = pruferEncode (m+3) hn T.
    -- Step 0 of decode: picks v₀ = min(Fin (m+3) \ futureSymbols₀).
    -- futureSymbols₀ = image of s as Finset.
    -- By the supporting lemma `mem_pruferEncode_image_iff`:
    --   v ∈ image(s) ⟺ deg_T(v) ≥ 2
    -- So Fin (m+3) \ image(s) = leaves of T.
    -- min over leaves = smallestTreeLeaf T = the v₀ that encode picked first.
    --
    -- After step 0: decode has added edge {v₀, s[0]} = {smallestLeaf, smallestNeighbor}
    --                = the same first edge encode peeled off.
    --
    -- Now the inductive hypothesis on T \ {v₀} (which has m + 2 vertices) gives:
    --   decode(encode(T \ v₀)) = T \ v₀
    -- And encode(T) = s[0] :: encode(T \ v₀) by definition of pruferEncodeAux.
    -- And decode (s[0] :: rest) after step 0 = (single-edge {v₀, s[0]}) ∪ decode(rest on Fin n)
    --
    -- But decode(rest on Fin n) needs decoding with `available = Fin n \ {v₀}` and
    -- code = rest. This is exactly decode(rest viewed in Fin (n-1)) plus a re-index.
    -- The re-index goes via `finSuccAboveEquivCompl v₀`.
    --
    -- Apply ih, then push the equality through.
    sorry  -- ~100 lines
```

The hard step is the re-index from `Fin (n-1)` ↔ `Fin n \ {v₀}` for the decode-on-smaller-set
to match decode-on-bigger-set-with-v₀-already-removed. Your existing `finSuccAboveEquivCompl`
gives the equiv; you'll need a lemma:

```lean
lemma pruferDecodeAux_eq_extend (n hn) (v : Fin n) (s' : pruferCodeSpace (n - 1)) :
    let s : pruferCodeSpace n := (s' indexed back via finSuccAboveEquivCompl v)
    pruferDecodeStep n hn s 1 = -- one step past the initial v removal
      { available := state with v removed
        edges := initial edge {v, ?} :: extend (pruferDecodeStep (n-1) _ s' 0) }
  sorry
```

This bridge-lemma is the technical heart. ~80 lines.

## Lemma 3: `pruferEncode_pruferDecode s = s`

Symmetric to Lemma 2. The induction:

- Base: empty code, n = 2. encode(decode(empty)) = encode(unique tree on 2 vertices) = empty.
- Step: 
  - Decode s, getting tree T'.
  - Show smallestLeaf(T') = "the min of (Fin n \ futureSymbols₀)" by construction.
  - So pruferEncode T' at position 0 = neighbor of smallestLeaf(T') in T'.
  - The neighbor of smallestLeaf(T') in T' = s[0] (since decode added that exact edge).
  - So (pruferEncode T') 0 = s 0. ✓
  - For positions ≥ 1: apply IH on T' \ smallestLeaf(T') = decode(s[1..]) (by the bridge lemma).

The proof structure is the **mirror image** of Lemma 2, with similar 80-100 lines of bridge.

## Practical advice

1. **Do Lemma 1 (IsTree) LAST**, not first. The inverses don't depend on IsTree formally —
   they just need decode to produce the right edge set. Once you have both inverses, you
   know decode(encode(T)) = T, hence decode produces valid trees on encoded-codes; for
   the OTHER direction (decode on arbitrary codes producing trees), you DO need IsTree
   separately because `pruferDecode` typed `pruferCodeSpace n → LabeledTree n` requires it.

   Wait — actually `pruferDecode` is typed as returning `LabeledTree`, so you need IsTree
   to even define `pruferDecode`. OK do it first.

2. **Order**: support lemma `mem_pruferEncode_image_iff` → `pruferDecodeIsTree` →
   `pruferDecode_pruferEncode` → `pruferEncode_pruferDecode`. Each builds on prior.

3. **Mathlib `IsTree` characterization**: the cleanest fully-classical statement is
   "connected + |edges| = n - 1" or "for every pair of vertices, unique path". Use
   whichever Mathlib already provides as an iff. If both are missing, "acyclic +
   connected" together imply tree.

4. **`decodeInvariant_step`**: the proof is mechanical case-bashing on graph operations,
   but it's the kind of thing that gets ugly fast. **If you find yourself writing more
   than 200 lines for this single induction step, file a follow-up question with the
   specific stuck point.** I can give targeted help if I know exactly which sub-claim
   (acyclic preservation? component count?) is fighting you.

5. **For LabeledTree.ext or equivalent**: it likely doesn't exist; you'll need to prove
   tree equality by showing underlying SimpleGraphs are equal, then use
   `SimpleGraph.ext` / `SimpleGraph.adj_injective` / etc.

## Honest scope check

- Support lemma: ~50 lines
- IsTree (with invariant): ~150 lines  
- Inverse #1 (decode ∘ encode): ~120 lines
- Inverse #2 (encode ∘ decode): ~100 lines (easier given #1)
- Equiv + wire chapter31: ~20 lines

Total ~440 lines. Within my earlier 300-600 estimate, on the high end.

**Don't sorry any of it. If you hit > 200 lines on a single sub-lemma, file Q03_agy with
the specific block.** Mid-block bridge lemmas are fine to file as separate questions; the
whole inverse is too coarse to ask about.

Go.
