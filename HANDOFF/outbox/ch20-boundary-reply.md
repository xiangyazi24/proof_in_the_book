# Ch20 boundary reply

## Status

I did not close `oddAtomicRG_card_odd`.

`ProofsInTheBook/Chapter20E2Boundary.lean` was created and currently verifies with:

```bash
PATH=$HOME/.elan/bin:$PATH lake env lean ProofsInTheBook/Chapter20E2Boundary.lean
```

It contains no `sorry`/`axiom`, but the final target theorem is not stated yet because the remaining
boundary-incidence lemma is not available and is not a consequence of just the two E2 multiplicity
statements.

## Proved in the new file

- `odd_atomicMult_iff_isAtomic_boundary`:

```lean
Odd (atomicMult D e) ↔ IsAtomicEdge D e ∧ OnSquareBoundary D e
```

using `atomicMult_even_of_interior` / `atomicMult_eq_one_of_boundary`.

- Corner extraction from the cover using extreme points:

```lean
exists_square_corners :
  ∃ c00 c10 c11 c01 : D.vtx,
    D.coord c00 = (0, 0) ∧ D.coord c10 = (1, 0) ∧
    D.coord c11 = (1, 1) ∧ D.coord c01 = (0, 1)
```

- Local replacements for engine helper lemmas missing from the current imported `.olean`:
  `mem_sideInteriorChain_iff_local`, side-chain nodup/endpoints lemmas, sideParam specification,
  sorted-chain no-between lemma, and square-side disjointness/nodup.

- Four-side color/count bridge:

```lean
squareBoundarySideAtomicList_RG_odd
```

proves the RG count of the corner-to-corner square side chain is odd.

- Conditional final bridge:

```lean
atomicBoundaryRG_card_odd_of_squareBoundaryEdgeList
```

If one supplies

```lean
∀ e, IsAtomicEdge D e ∧ OnSquareBoundary D e ↔
  e ∈ (squareBoundaryEdgeList
    (sideInteriorChain D c00 c10)
    (sideInteriorChain D c10 c11)
    (sideInteriorChain D c11 c01)
    (sideInteriorChain D c01 c00)
    c00 c10 c11 c01).toFinset
```

then the requested odd cardinality follows.

## Blocker

The missing lemma is the actual boundary extraction:

```lean
IsAtomicEdge D e ∧ OnSquareBoundary D e ↔
  e ∈ four square sideAtomicEdges
```

This requires proving that the global D-vertices on each square side form the atomic boundary
chain: every corner-to-corner consecutive side segment is contributed by a triangle side, and every
atomic boundary segment from a triangle side is consecutive in the corresponding square side chain.
That proof needs a cover/frontier argument plus the sideParam no-between machinery; it is not
provided by the two E2 multiplicity theorems alone.

I did not edit `Chapter20DissectionEngine.lean` or any existing Lean source.

## Round 3 update

Closed `oddAtomicRG_card_odd` in `ProofsInTheBook/Chapter20E2Boundary.lean`.

Added the missing decomposition:

- L2 local form: `not_mem_interior_triHull_of_mem_frontier_unitSquare`.
- Global no-between/midpoint parameter machinery for square side chains.
- Generic extraction: `isAtomic_of_mem_squareSideAtomicEdges`.
- Four concrete square-side reverse lemmas.
- Bidirectional extraction:

```lean
atomicBoundary_iff_squareBoundaryEdgeList_of_square_corners
```

Final theorem:

```lean
theorem oddAtomicRG_card_odd :
    Odd (Finset.univ.filter fun e : Sym2 D.vtx =>
      edgeRGIndicator (realTwoAdicColor ∘ D.coord) e = 1 ∧
        Odd (atomicMult D e)).card
```

Verification:

```bash
~/.elan/bin/lake env lean ProofsInTheBook/Chapter20E2Boundary.lean
grep -n "sorry\|axiom" ProofsInTheBook/Chapter20E2Boundary.lean
```

The Lean check exits 0. The grep finds no `sorry`/`axiom` in this file.
