# ANSWER_31_01_agy — Prüfer encode/decode blueprint

## Good news from rereading your file

Ch31 already has the **encode infrastructure** built. You don't need to invent a new
representation; just compose what's there:

```
smallestTreeLeaf            -- the smallest leaf v of T
smallestTreeLeafNeighbor    -- its unique neighbor (the code symbol)
isTree_delete_smallestTreeLeaf  -- T \ {v} is still a tree
deleteSmallestLeafTreeSucc       -- packages the smaller LabeledTree
finSuccAboveEquivCompl      -- canonical Fin m ≃ (Fin (m+1) \ {leaf})
```

These let you write encode as a clean `Nat.rec` on the iteration count. **Don't roll a
custom edge-set state type** — every primitive you need is already there with the right
invariants.

Decode is the harder side. It needs a separate state-tracking representation.

## 1. `pruferEncode` definition

The cleanest framing: index by `m + 2` so the recursion bottoms out at "tree on 2 vertices".

```lean
noncomputable def pruferEncodeAux :
    ∀ (m : ℕ), LabeledTree (m + 2) → (Fin m → Fin (m + 2))
  | 0,   _ => fun i => Fin.elim0 i
  | m+1, T => fun i =>
    -- Strategy: compute the code symbol at index 0 (= smallestTreeLeafNeighbor),
    -- then recurse on the deleted tree (which has m + 2 vertices), mapping its
    -- Fin (m + 2) labels back to Fin (m + 3) via finSuccAboveEquivCompl.
    if h : i.val = 0 then
      smallestTreeLeafNeighbor (m + 3) (by omega) T
    else
      let leaf := smallestTreeLeaf (m + 3) (by omega) T
      let T' := deleteSmallestLeafTreeSucc (m + 2) (by omega) (m + 3) (by omega) T
      -- T' : LabeledTree (m + 2), recursion index i-1 : Fin m
      let symbol_in_smaller : Fin (m + 2) :=
        pruferEncodeAux m T' ⟨i.val - 1, by omega⟩
      -- Map back to Fin (m + 3) via the leaf-exclusion equiv
      (finSuccAboveEquivCompl leaf).symm symbol_in_smaller |>.val
```

Then:

```lean
noncomputable def pruferEncode (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) : pruferCodeSpace n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  exact pruferEncodeAux m T
```

(Cast the `Fin (n-2)` index in `pruferCodeSpace` to `Fin m` after the `rfl`.)

**Critical**: check `deleteSmallestLeafTreeSucc`'s exact signature. It likely returns a tree
on `Fin (m + 2)` via the equiv, but the precise index manipulation depends on whether it
gives you a `LabeledTree (m + 2)` directly or wrapped in an equiv. If wrapped, you compose
with the equiv to map the recursive result back. My pseudocode above conflates the two —
adjust based on what's actually in the file.

## 2. `pruferDecode` definition

This is the painful one because there's no analogous "delete leaf" reduction on
`pruferCodeSpace`. The decode algorithm needs explicit state:

```
state = (available : Finset (Fin n), edges_built : Finset (Sym2 (Fin n)))
```

The cleanest functional version: at each step, compute the "next leaf" as
`(available \ futureCodeSymbols).min'`, add the edge `(leaf, code[i])`, remove `leaf`
from `available`, advance.

```lean
def futureCodeSymbols (n : ℕ) (s : Fin (n - 2) → Fin n) (i : ℕ) : Finset (Fin n) :=
  Finset.image s ((Finset.range (n - 2)).filter (fun j => i ≤ j) |>.attach |>.map ⟨..., ...⟩)
  -- simplification: { s j | j ∈ [i, n-2) } as a Finset

-- Decode iteration: at step i, available has size n - i.
def pruferDecodeAux (n : ℕ) (s : Fin (n - 2) → Fin n) :
    ∀ (i : ℕ), i ≤ n - 2 → Finset (Fin n) →  -- available so far
      Finset (Sym2 (Fin n))                  -- edges built so far
  | 0, _, available => ∅
  | i+1, hi, available =>
    let prev := pruferDecodeAux n s i (by omega) available
    let absent := available \ futureCodeSymbols n s i
    let nextLeaf := absent.min' (by ... -- nonempty when |available| > 2)
    insert s⟨i, by omega⟩ ... prev  -- add edge {nextLeaf, s[i]}
```

After `i = n - 2`, the remaining `available` has exactly 2 elements; add their edge to close.

Convert the final edge set to a `LabeledTree n` via:
```lean
SimpleGraph.fromEdgeSet edges    -- get a simple graph
-- then prove IsTree: connected + no cycle (use induction on length / Cayley count parity)
```

The "prove `IsTree`" step is itself ~50 lines because `SimpleGraph.IsTree` requires
connectivity + acyclicity, both of which need a structural argument over the decode
construction.

**Suggestion**: define decode in two stages:
- (a) `pruferDecodeEdges : pruferCodeSpace n → Finset (Sym2 (Fin n))` (pure data)
- (b) `pruferDecodeIsTree : ∀ s, IsTree (SimpleGraph.fromEdgeSet (pruferDecodeEdges s))`
- (c) `pruferDecode := fun s => ⟨SimpleGraph.fromEdgeSet (pruferDecodeEdges s), pruferDecodeIsTree s⟩`

This separates "what" (data) from "why it's a tree" (proof).

## 3. The two inverse proofs

**`pruferDecode_pruferEncode` (encode then decode = original tree)**:

Strong induction on `n` (or `m = n - 2`).

Key invariant: after the first encode step, the smallest leaf `v` is removed and its
neighbor `c₀ := s[0]` becomes the first code symbol. So in `decode(s)`, the first edge
added must be `{v', c₀}` where `v'` is the smallest "non-future" available vertex.

The matching claim: `v = v'`. This is true iff `v` (the smallest leaf of T) is exactly
`available \ futureSymbols` minimized. The encoding's smallest-leaf choice gives
`v` = min vertex that is **not used as a symbol later**. Decode picks the same v by the
same criterion. So step 0 matches.

After step 0, recurse on `T \ {v}` and `s[1..]`.

Proof skeleton:
```lean
theorem pruferDecode_pruferEncode (n : ℕ) (hn : 2 ≤ n) (T : LabeledTree n) :
    pruferDecode n hn (pruferEncode n hn T) = T := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  induction m with
  | zero =>
    -- n = 2, code is empty, both sides give the unique tree on 2 vertices
    apply LabeledTree.ext  -- (you may need to define this; ext on the underlying graph)
    sorry  -- finite case, ~10 lines
  | succ m ih =>
    -- show step 0 matches: smallestTreeLeaf T = (decode_state \ future).min'
    -- then apply ih to T \ {smallestTreeLeaf T} and (encode T).drop 1
    sorry
```

**`pruferEncode_pruferDecode` (decode then encode = original code)**:

Symmetric. Key invariant: after decoding step 0, the smallest leaf of the just-constructed
tree IS the chosen `nextLeaf`, AND its neighbor in the tree IS `s[0]`. So the encode's
first symbol matches `s[0]`.

```lean
theorem pruferEncode_pruferDecode (n : ℕ) (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    pruferEncode n hn (pruferDecode n hn s) = s := by
  -- symmetric to above; the "step 0 matches" lemma is the harder direction
  sorry
```

## 4. Wiring into `chapter31`

Once both inverses are proved:

```lean
noncomputable def pruferEquiv (n : ℕ) (hn : 2 ≤ n) :
    LabeledTree n ≃ pruferCodeSpace n where
  toFun := pruferEncode n hn
  invFun := pruferDecode n hn
  left_inv := pruferDecode_pruferEncode n hn
  right_inv := pruferEncode_pruferDecode n hn

-- Cayley count
theorem cayley_count (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := by
  rw [Fintype.card_congr (pruferEquiv n hn)]
  -- Fintype.card (Fin (n-2) → Fin n) = n^(n-2)
  simp [pruferCodeSpace, Fintype.card_fun]

theorem chapter31 (n : ℕ) (hn : 2 ≤ n) :
    Fintype.card (LabeledTree n) = n ^ (n - 2) := cayley_count n hn
```

Replace any existing `supplied equivalence` in the current `chapter31` with `pruferEquiv`.

## Honest scope warning

This is a **300-600 line task** done carefully. The hardest individual subproblems:

1. **Step 0 lemma**: "smallest leaf of T = (available \ future).min'" requires understanding
   the relationship between `smallestTreeLeaf` and the encoding's symbol structure. ~80 lines.

2. **Recursive structure compatibility**: when you recurse `pruferEncodeAux` after deleting
   the leaf, you need to relate `pruferDecodeAux` on the smaller code to the larger tree.
   The `finSuccAboveEquivCompl` re-mapping is the index gymnastics that gets ugly.
   ~100 lines.

3. **`pruferDecodeIsTree`**: proving the decoded edge set is acyclic + connected. Induction
   over the decode iteration count, maintaining "current_edges form a forest with
   `available.card - i` components" as invariant. ~100 lines.

If you hit walls beyond "this lemma is fiddly" — e.g., you find that
`deleteSmallestLeafTreeSucc`'s output doesn't compose cleanly with the recursion shape —
file a follow-up question with the specific elaboration error rather than struggling.

## Implementation order suggestion

Do these in sequence and remote-build at each step:

1. Implement `pruferEncodeAux` + a sanity check `(pruferEncode T : Fin (n-2) → Fin n).injective` ?
   Actually injectivity won't hold — instead verify `pruferEncode T 0 = smallestTreeLeafNeighbor T`.
2. Implement `pruferDecodeEdges` + sanity check on edge count = n - 1.
3. Implement `pruferDecodeIsTree` and `pruferDecode`.
4. Prove `pruferDecode_pruferEncode`. Hardest single step.
5. Prove `pruferEncode_pruferDecode`. Easier given step 4 (symmetric structure).
6. Define `pruferEquiv` and wire `chapter31`.

If step 4 takes you more than 200 lines or 3 stuck-build cycles, ask. Don't sorry it.

Go.
