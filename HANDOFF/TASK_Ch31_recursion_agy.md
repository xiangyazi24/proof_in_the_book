# TASK Ch31: structural recursion (THE blocker)

This is the hardest remaining piece for Ch31 Tier 2. Two parts: shiftedCode
definition + the delete-leaf-tree lemma.

## Background

We have:
- `pruferDecode_degree`, `pruferDecode_isLeaf_iff`, `smallestTreeLeaf_pruferDecode`
- `smallestTreeLeafNeighbor_pruferDecode = s_0`
- `pruferEncode_pruferDecode_zero` (position 0 of round-trip)

We want eventually: `Function.LeftInverse (pruferEncode hn) (pruferDecode hn)`
i.e., `pruferEncode hn (pruferDecode hn s) = s` for all s.

This requires showing positions 1..n-3 also agree, which needs structural
induction on the tree size. The key lemma:

```lean
theorem deleteSmallestLeaf_pruferDecode {n : ℕ} (hn : 3 ≤ n) (s : pruferCodeSpace n) :
    deleteSmallestLeafTreeSucc (n - 1) (by omega) (pruferDecode (by omega) s) =
    pruferDecode (by omega : 2 ≤ n - 1) (shiftedCode hn s)
```

where `shiftedCode hn s : pruferCodeSpace (n - 1)`.

## Part 1: Define `shiftedCode`

Append to `scratch_ch31_inverse.lean` (or use scratch_ch31_recursion.lean if you prefer a separate file).

```lean
/-- nextLeaf_0: the smallest tree-leaf of the decoded tree (= smallest Prüfer-leaf). -/
noncomputable def nextLeaf0 {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) : Fin n :=
  smallestTreeLeaf n hn (pruferDecode hn s)

/-- nextLeaf_0 doesn't appear in s anywhere. Immediate from pruferDecode_isLeaf_iff. -/
theorem nextLeaf0_not_in_image {n : ℕ} (hn : 2 ≤ n) (s : pruferCodeSpace n) :
    ∀ j : Fin (n - 2), s j ≠ nextLeaf0 hn s := by
  have h_leaf : nextLeaf0 hn s ∈ treeLeaves (pruferDecode hn s) :=
    smallestTreeLeaf_mem_leaves n hn _
  rw [pruferDecode_isLeaf_iff n hn s] at h_leaf
  exact h_leaf

/-- The shifted code: drop position 0, lift values through `(finSuccAboveEquivCompl nextLeaf0).symm`. -/
noncomputable def shiftedCode {n : ℕ} (hn : 3 ≤ n) (s : pruferCodeSpace n) :
    pruferCodeSpace (n - 1) := by
  intro j'
  classical
  -- Subgoal: produce Fin (n-1).
  -- For j : Fin (n-2) with j.val = j'.val + 1, value s j ≠ nextLeaf_0, so it
  -- lives in {v : Fin n // v ∈ ({nextLeaf_0}ᶜ : Set (Fin n))}. Apply
  -- (finSuccAboveEquivCompl nextLeaf_0).symm to get Fin (n-1).
  --
  -- Note: finSuccAboveEquivCompl is over Fin (m+1) where m+1 = n, so m = n-1.
  -- The .symm gives Fin (n-1).
  have h2le : 2 ≤ n := by omega
  let nL : Fin n := nextLeaf0 h2le s
  have hj_lt : j'.val + 1 < n - 2 + 1 := by have := j'.isLt; omega
  let j : Fin (n - 2) := ⟨j'.val + 1, by have := j'.isLt; omega⟩
  have hNe : s j ≠ nL := nextLeaf0_not_in_image h2le s j
  have hMem : (s j : Fin n) ∈ ({nL}ᶜ : Set (Fin n)) := by simp [hNe]
  -- Cast nL : Fin n to Fin (n-1+1) (defeq when n ≥ 1).
  have hn_eq : n - 1 + 1 = n := by omega
  let nL' : Fin (n - 1 + 1) := hn_eq ▸ nL
  have hMem' : (hn_eq ▸ s j : Fin (n - 1 + 1)) ∈ ({nL'}ᶜ : Set (Fin (n - 1 + 1))) := by
    sorry  -- transport hMem through hn_eq
  let lifted : {v : Fin (n - 1 + 1) // v ∈ ({nL'}ᶜ : Set (Fin (n - 1 + 1)))} :=
    ⟨hn_eq ▸ s j, hMem'⟩
  exact (finSuccAboveEquivCompl nL').symm lifted
```

The dependent-type transport `hn_eq ▸` is the painful part. Alternative: keep
nL : Fin (n-1+1) from the start by working in that index world.

Cleaner alternative: parameterize n as m+2 so we have `n - 1 = m + 1`:

```lean
noncomputable def shiftedCode_v2 {m : ℕ} (hm : 1 ≤ m) (s : pruferCodeSpace (m + 2)) :
    pruferCodeSpace (m + 1) := by
  intro j'  -- j' : Fin ((m+1) - 2) = Fin (m - 1)
  classical
  have h2le : 2 ≤ m + 2 := by omega
  let nL : Fin (m + 2) := nextLeaf0 h2le s
  have hj_lt : j'.val + 1 < (m + 2) - 2 := by have := j'.isLt; omega
  let j : Fin ((m + 2) - 2) := ⟨j'.val + 1, hj_lt⟩
  have hNe : s j ≠ nL := nextLeaf0_not_in_image h2le s j
  have hMem : (s j : Fin (m + 2)) ∈ ({nL}ᶜ : Set (Fin (m + 2))) := by simp [hNe]
  -- finSuccAboveEquivCompl on Fin (m+2) with leaf gives Fin (m+1) ≃ {v // ...}.
  let lifted : {v : Fin (m + 2) // v ∈ ({nL}ᶜ : Set (Fin (m + 2)))} := ⟨s j, hMem⟩
  exact (finSuccAboveEquivCompl nL).symm lifted
```

This avoids the `n - 1 + 1 = n` transport because `m + 2 - 1 = m + 1` is by `rfl`.

## Part 2: the structural lemma

```lean
theorem deleteSmallestLeaf_pruferDecode_v2 {m : ℕ} (hm : 1 ≤ m)
    (s : pruferCodeSpace (m + 2)) :
    deleteSmallestLeafTreeSucc (m + 1) (by omega) (pruferDecode (by omega) s) =
    pruferDecode (by omega : 2 ≤ m + 1) (shiftedCode_v2 hm s)
```

**Proof strategy**: ext on LabeledTree (compare underlying graphs as
SimpleGraph). Two graphs equal iff Adj relation matches. The LHS deletes
nextLeaf_0 and re-indexes; the RHS decodes the shifted code.

For each pair (a, b) of vertices in Fin (m+1):
- a' := finSuccAboveEquivCompl nL a : {v // v ∈ {nL}ᶜ}
- b' := finSuccAboveEquivCompl nL b : {v // v ∈ {nL}ᶜ}
- LHS.Adj a b ⟺ (pruferDecode s).1.Adj a'.1 b'.1 (since deleteSmallestLeafTreeSucc induces on the complement)
- RHS.Adj a b ⟺ s(a, b) ∈ pruferDecodeEdges hn' (shiftedCode_v2 hm s)

Show these are equivalent: an edge in the lifted complement maps to an edge in
the shifted decode and vice versa.

This requires careful induction on the decode steps, matching state.2 at each m
between the two trees.

**Scope estimate**: 200-400 LOC. This is HARD.

## Constraints

- 0 sorry, 0 axiom required in final.
- Build remotely.
- File oracle questions if blocked on Lean-specific issues (dependent typing,
  ▸ transport, ext-based graph equality).

## What to NOT do

- Don't introduce axioms or sorry's that we'd need to discharge later. The goal
  is end-to-end Tier 2.
- Don't simplify by adding hypotheses (Prop) to the conclusion. That's Tier 1
  dodging.
- Don't reformulate the chapter result statement to avoid this lemma. The
  chapter goal (cardinality of LabeledTree = n^(n-2)) genuinely needs the
  round-trip.

## Go

Start with shiftedCode_v2 (Part 1). Get it building. Then attempt Part 2.

If Part 2 hits >50 LOC without progress, file an oracle Q with the exact
sub-goal blocking you.
