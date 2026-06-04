import Mathlib
import ProofsInTheBook.PlanarMap

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

open ProofsInTheBook.PlanarMap in
/-- **Chapter 12 — the Platonic solids, derived from Euler's formula.**
For any connected genus-zero combinatorial map (`IsSphereMap`, i.e. `V - E + F = 2`) that is
regular — every face a `p`-gon (`p ≥ 3`) and every vertex of degree `q` (`q ≥ 3`) — the pair
`(p, q)` is one of exactly five: `(3,3)`, `(3,4)`, `(4,3)`, `(3,5)`, `(5,3)`. The constraint
`1/p + 1/q > 1/2` is *derived from* Euler's formula (`CombMap.platonic_constraint`), not assumed;
hence there are exactly five Platonic solids. The set form is `chapter12_platonic_solids`. -/
theorem chapter12 {D : Type*} [Fintype D] [DecidableEq D] (M : CombMap D)
    (hsphere : M.IsSphereMap) {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hE : 0 < M.E)
    (hF : M.FaceRegular p) (hV : M.VertexRegular q) :
    (p = 3 ∧ q = 3) ∨ (p = 3 ∧ q = 4) ∨ (p = 4 ∧ q = 3) ∨
      (p = 3 ∧ q = 5) ∨ (p = 5 ∧ q = 3) :=
  CombMap.platonic_pairs M hsphere hp hq hE hF hV

end ProofsInTheBook.Chapter12
