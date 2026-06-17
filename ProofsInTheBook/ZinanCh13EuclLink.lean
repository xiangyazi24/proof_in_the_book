import ProofsInTheBook.ZinanCh13Euclidean
import ProofsInTheBook.Ch13Realization
import ProofsInTheBook.Ch13VertexStar

/-!
# Chapter 13 Euclidean vertex-link bridge frontier

This file records the exact extra local certificate needed to turn a b1
`TriangulatedEuclideanPolyhedron` into the `VertexStar` input consumed by the
Cauchy spherical-link core.

The b1 Euclidean structure deliberately contains face planes, triangular faces,
edge nondegeneracy, and convex supporting halfspaces, but it does not contain the
vertex-link cyclic-order theorem or the strict vertex-link convexity theorem.
Those are the b3 bridge.  Once supplied as the local certificate below, the
assembly into `VertexStar` is direct and contains no further geometric content.
-/

noncomputable section

open scoped Classical RealInnerProductSpace
open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.TetPearls
open ProofsInTheBook.Ch13Euclidean
open ProofsInTheBook.Ch13VertexStar

namespace ProofsInTheBook.Ch13EuclLink

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D}

/--
The local Euclidean link certificate at one combinatorial vertex.

`dart` is the chosen cyclic list of incident darts, in the intended `σ` order.
The last four fields are exactly the raw `VertexStar` predicates for the edge
vectors `pos (head dart i) - pos v`.
-/
structure EuclideanVertexStarCertificate
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex) where
  /-- There are `n + 1` incident darts in the local link. -/
  n : ℕ
  /-- At least three incident darts. -/
  hn : 2 ≤ n
  /-- Incident darts in cyclic order. -/
  dart : Fin (n + 1) → D
  /-- Every chosen dart starts at the vertex. -/
  dart_tail : ∀ i, M.tail (dart i) = v
  /-- The chosen order is the `σ`-successor order. -/
  sigma_next : ∀ i, M.σ (dart i) = dart (i + 1)
  /-- The chosen darts exhaust the vertex orbit. -/
  complete : ∀ d, M.tail d = v → ∃ i, dart i = d
  /-- The raw link directions lie in an open hemisphere. -/
  open_hemi :
    ∃ h : E3, ‖h‖ = 1 ∧
      ∀ i : Fin (n + 1),
        0 < inner ℝ h (P.pos (M.head (dart i)) - P.pos v)
  /-- Every oriented local edge weakly supports the whole raw link. -/
  turn_support :
    ∀ i j : Fin (n + 1),
      0 ≤ ProofsInTheBook.SphericalKernel.det3
        (P.pos (M.head (dart i)) - P.pos v)
        (P.pos (M.head (dart (i + 1))) - P.pos v)
        (P.pos (M.head (dart j)) - P.pos v)
  /-- Non-incident raw directions lie strictly on the supported side. -/
  turn_strict :
    ∀ i j : Fin (n + 1), j ≠ i → j ≠ i + 1 →
      0 < ProofsInTheBook.SphericalKernel.det3
        (P.pos (M.head (dart i)) - P.pos v)
        (P.pos (M.head (dart (i + 1))) - P.pos v)
        (P.pos (M.head (dart j)) - P.pos v)

namespace EuclideanVertexStarCertificate

variable {P : TriangulatedEuclideanPolyhedron M} {v : M.Vertex}
variable (C : EuclideanVertexStarCertificate P v)

/-- Edge nondegeneracy from b1 gives the `VertexStar.apex_ne` field. -/
theorem apex_ne (i : Fin (C.n + 1)) :
    P.pos (M.head (C.dart i)) ≠ P.pos v := by
  intro h
  exact P.edge_nondegenerate (C.dart i) (by
    rw [C.dart_tail i, h])

end EuclideanVertexStarCertificate

/--
Assemble a `VertexStar` from the exact Euclidean local certificate.

This theorem is intentionally certificate-parametric: the present b1 interface
does not yet prove the open-hemisphere and strict cyclic-turn fields from the
global supporting-halfspace data.
-/
def vertexStarOfEuclidean_of_certificate
    (P : TriangulatedEuclideanPolyhedron M) (v : M.Vertex)
    (C : EuclideanVertexStarCertificate P v) : VertexStar where
  n := C.n
  hn := C.hn
  o := P.pos v
  p := fun i => P.pos (M.head (C.dart i))
  apex_ne := C.apex_ne
  open_hemi := C.open_hemi
  turn_support := C.turn_support
  turn_strict := C.turn_strict

end ProofsInTheBook.Ch13EuclLink

#print axioms ProofsInTheBook.Ch13EuclLink.vertexStarOfEuclidean_of_certificate
