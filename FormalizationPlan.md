# Formalization Plan (Proofs from THE BOOK)

This repository now tracks a chapter-by-chapter mechanical skeleton for Lean formalization.

## Scope
- 40 chapters of *Proofs from THE BOOK* (Fourth Edition)
- Mechanical task: module and theorem placeholders are created.
- Hard proofs are delegated to the webapp.

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
21. A theorem of Polya on polynomials
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

## Convention for each chapter file
- Keep theorem name `chapterNN : True` as a temporary mechanical marker.
- Replace `sorry` with full formalization proof by chapter.

## Suggested workflow with webapp
- Assign one chapter per webapp run.
- Ask webapp to replace `sorry` in `ProofsInTheBook/ChapterXX.lean` with complete proof objects.
- Keep this file updated whenever a chapter is completed.
