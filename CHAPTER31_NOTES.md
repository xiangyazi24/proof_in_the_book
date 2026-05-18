# Chapter 31 / Book Chapter 30: Cayley's Formula Notes

Date: 2026-05-18

## Source checked

Primary source in this repository:

- `proofs_in_the_book.pdf`, book Chapter 30, "Cayley's formula for the number of trees", pp. 201-206 in the book pagination.

The repository file is `ProofsInTheBook/Chapter31.lean`, but the PDF chapter is numbered Chapter 30. The mismatch comes from repository chapter numbering, not from the mathematical topic.

## What the book actually does

The chapter states Cayley's formula:

```text
There are n^(n-2) different labeled trees on n vertices.
```

It first mentions the classical Prüfer-code bijection, but the book does not develop it. Instead it outlines or proves four approaches:

1. Joyal's bijection between functions `N -> N` and trees with two distinguished vertices.
2. Kirchhoff's matrix-tree theorem.
3. Riordan-Rényi recursion for forests `T_{n,k}`.
4. Pitman's double-counting proof for rooted forests.

The most book-faithful formalization would probably be Joyal or Pitman, not Prüfer.

## Current Lean state

The old external premise was:

```lean
hCayley : Fintype.card (LabeledTree n) ≤ n ^ (n - 2)
```

This has been localized into a single internal target:

```lean
theorem cayley_upper_bound (n : ℕ) (_hn : 2 ≤ n) :
    Fintype.card (LabeledTree n) ≤ n ^ (n - 2) := by
  sorry
```

The public theorem now has no external `hCayley` parameter:

```lean
theorem prufer_encoding_exists (n : ℕ) (hn : 2 ≤ n) :
    ∃ encode : LabeledTree n → pruferCodeSpace n,
      Function.Injective encode
```

So the remaining gap is concentrated in `cayley_upper_bound`.

## Mathlib API found

Useful graph/tree lemmas:

```lean
SimpleGraph.IsTree.card_edgeFinset
SimpleGraph.isTree_iff_connected_and_card
SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial
SimpleGraph.Connected.induce_compl_singleton_of_degree_eq_one
SimpleGraph.card_edgeFinset_deleteIncidenceSet
SimpleGraph.degree_eq_one_iff_existsUnique_adj
```

These support a Prüfer-style deletion proof if we choose that route.

Useful absence:

- No ready-made Cayley formula found in Mathlib.
- No ready-made matrix-tree theorem counting spanning trees found, only Laplacian infrastructure.
- No Prüfer sequence formalization found.

## Route assessment

### Prüfer route

Pros:

- Matches existing `pruferCodeSpace` setup.
- Mathlib has leaf-existence and leaf-deletion connectivity lemmas.
- Directly proves the needed injection.

Cons:

- Requires formal recursive deletion of vertices while relabeling from a subtype back to `Fin (n-1)`.
- Injectivity proof is nontrivial: need reconstruct deleted leaves from the code or prove the usual degree-occurrence invariant.

### Joyal route

Pros:

- Book-featured and elegant.
- Avoids recursive leaf deletion.
- Counts `n^n = n^2 * T_n`, then derives `T_n = n^(n-2)` for positive `n`.

Cons:

- Requires formalizing functional digraph components and unique directed cycles for an arbitrary function `Fin n -> Fin n`.
- Needs a clean representation of doubly-rooted trees and a quotient-free bijection.

### Pitman route

Pros:

- Book's final proof, very combinatorial.
- Gives forest generalization.

Cons:

- Requires rooted forest structures, containment of directed forests, and refining sequences.
- Likely more infrastructure than Ch31 currently has.

## Current recommendation

Start with the Prüfer route because the file already defines `pruferCodeSpace`, and Mathlib has the exact graph lemmas needed for leaves. If relabeling deleted vertex subtypes becomes too expensive, switch to Joyal's route with a bespoke functional-digraph representation.

## Immediate subgoals

1. Define the smallest leaf of a labeled tree.
2. Prove degree-one gives a unique neighbor.
3. Define the one-step deletion graph on `{v}ᶜ` and show it is a tree.
4. Decide whether to relabel `{v}ᶜ` to `Fin (n-1)` or run the encoding over a shrinking finite set represented as a `Finset (Fin n)`.
5. Prove an injective encoding into `Fin (n-2) -> Fin n`.

