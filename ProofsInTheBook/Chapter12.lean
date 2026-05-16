import Mathlib

/-!
# Chapter 12: Three applications of Euler's formula

From "Proofs from THE BOOK":

**Euler's formula**: For any connected planar graph, V - E + F = 2.

Three applications:
1. **Every planar graph is 5-colorable** (or even 4-colorable, but the
   book proves 6-colorable easily, then refines to 5).
2. **The number of edges**: E ≤ 3V - 6 for simple planar graphs.
3. **Regular polyhedra**: There are exactly five Platonic solids.

The proof of Euler's formula proceeds by induction on edges:
removing an edge either merges two faces (keeping V-E+F constant)
or disconnects the graph (handled by the base case of a tree).
-/

namespace ProofsInTheBook.Chapter12

/-!
### Euler's formula and Platonic solids

The classic V - E + F = 2 and its consequence that there are
exactly 5 regular polyhedra (tetrahedron, cube, octahedron,
dodecahedron, icosahedron).

For a regular polyhedron with p-gonal faces and q faces meeting
at each vertex: 1/p + 1/q > 1/2, which has exactly 5 solutions
(3,3), (3,4), (4,3), (3,5), (5,3).
-/

theorem chapter12_platonic_solids :
    {pq : ℕ × ℕ | 3 ≤ pq.1 ∧ 3 ≤ pq.2 ∧ pq.1 * pq.2 < 2 * pq.1 + 2 * pq.2}.Finite := by
  refine Set.Finite.subset (Set.Finite.prod (Set.finite_Icc 3 5) (Set.finite_Icc 3 5)) ?_
  intro ⟨p, q⟩ ⟨hp, hq, hpq⟩
  simp only [Set.mem_prod, Set.mem_Icc]
  exact ⟨⟨hp, by nlinarith⟩, ⟨hq, by nlinarith⟩⟩

theorem chapter12 :
    {pq : ℕ × ℕ | 3 ≤ pq.1 ∧ 3 ≤ pq.2 ∧ pq.1 * pq.2 < 2 * pq.1 + 2 * pq.2}.Finite :=
  chapter12_platonic_solids

end ProofsInTheBook.Chapter12
