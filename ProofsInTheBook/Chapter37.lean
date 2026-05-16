import Mathlib

/-!
# Chapter 37: Turán's graph theorem

From "Proofs from THE BOOK":

**Turán's theorem**: The maximum number of edges in a K_{r+1}-free
graph on n vertices is achieved uniquely by the Turán graph T(n,r),
the complete r-partite graph with parts as equal as possible.

The book presents two proofs:
1. Turán's original proof by induction on n.
2. Zykov's symmetrization argument: replacing a vertex with a copy
   of a non-adjacent vertex can only increase the edge count
   while preserving K_{r+1}-freeness.
-/

namespace ProofsInTheBook.Chapter37

open SimpleGraph

/-!
### Turán's theorem: the Turán graph is extremal

The Turán graph T(n,r) is the unique K_{r+1}-free graph on n = Fin n
vertices with the maximum number of edges.
-/

theorem chapter37_turan (n r : ℕ) (hr : 0 < r) :
    (turanGraph n r).IsTuranMaximal r :=
  isTuranMaximal_turanGraph hr

theorem chapter37 (n r : ℕ) (hr : 0 < r) :
    (turanGraph n r).IsTuranMaximal r :=
  chapter37_turan n r hr

end ProofsInTheBook.Chapter37
