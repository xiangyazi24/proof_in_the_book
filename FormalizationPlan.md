# Formalization Plan (Proofs from THE BOOK)

This repository tracks a full Lean formalization of the 40 chapters of
*Proofs from THE BOOK* (Fourth Edition), with the long-run target being
non-trivial, theorem-accurate Lean statements and proofs.

## Scope

- 40 chapter modules: `ProofsInTheBook/Chapter01.lean` to `ProofsInTheBook/Chapter40.lean`.
- Main proof driver: `ProofsInTheBook.lean`.
- Communication: webapp-assisted proof completion via `dm-codex`, with strict task batching.

## Chapter index

1. Six proofs of the infinity of primes
2. Bertrand's postulate
3. Binomial coefficients are (almost) never powers
4. Representing numbers as sums of two squares
5. The law of quadratic reciprocity
6. Every finite division ring is a field
7. Some irrational numbers
8. Three times pi^2 / 6
9. Hilbert's third problem: decomposing polyhedra
10. Lines in the plane and decompositions of graphs
11. The slope problem
12. Three applications of Euler's formula
13. Cauchy's rigidity theorem
14. Touching simplices
15. Every large point set has an obtuse angle
16. Borsuk's conjecture
17. Sets, functions, and the continuum hypothesis
18. In praise of inequalities
19. The fundamental theorem of algebra
20. One square and an odd number of triangles
21. A theorem of Pólya on polynomials
22. On a lemma of Littlewood and Offord
23. Cotangent and the Herglotz trick
24. Buffon's needle problem
25. Pigeon-hole and double counting
26. Tiling rectangles
27. Three famous theorems on finite sets
28. Shuffling cards
29. Lattice paths and determinants
30. Cayley's formula for the number of trees
31. Identities versus bijections
32. Completing Latin squares
33. The Dinitz problem
34. Five-coloring plane graphs
35. How to guard a museum
36. Turan's graph theorem
37. Communicating without errors
38. The chromatic number of Kneser graphs
39. Of friends and politicians
40. Probability makes counting (sometimes) easy

## Execution policy

- Mechanical skeletoning (module layout, theorem declarations, imports) is completed locally.
- Hard proofs are assigned to webapp in bounded batches.
- Each webapp round must be explicit: file, theorem name, missing proof goal, and intended proof shape.
- Returned proof text is pasted directly and checked in the corresponding chapter file.

## Acceptance policy

- A chapter is complete only when:
  1. `bash scripts/goal check <chapter>` reports 0 remaining `sorry`.
  2. The chapter theorems are not placeholder-only (`: True`) unless that is the real statement.
  3. The file is type-correct in local context.
  4. The completion is recorded in one commit and traced in `WebappTasks.md` + `Changelog.md`.

## Data artifacts

- `FormalizationPlan.md`: high-level human planning record.
- `GOALS.md`: `/goal` long-run workflow specification.
- `WebappTasks.md`: per-round webapp request log.
- `COMMUNICATION_PROTOCOL.md`: bridge channel and API contract.
- `scripts/goal`: scheduling, task extraction, check and progress state.
