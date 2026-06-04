I am implementing the Lindström-Gessel-Viennot Lemma (Chapter 30). The user suggested defining paths with `Vertex := ℤ × ℤ` and `Step` as North or East.

1. What is the best Lean 4 type definition for these paths? `List (ℤ × ℤ)` with a `Chain Step` property, or something else? (Since we need to split paths at their first intersection and concatenate the tails, `List` seems easiest).

2. For the `BadInvolutionCertificate`, we need to find the *first* intersection (lexicographically smallest pair of paths `(i, j)`, then their first common vertex) and swap tails to define an `Equiv`. Finding the first intersection using `Finset.min` requires decidability. What's the cleanest way to define this tail-swap `Equiv` in Lean 4 without getting bogged down in dependent type decidability hell? Could you provide a concrete skeleton for the lattice path type and the involution definition?
