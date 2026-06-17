import ProofsInTheBook.Ch13VertexStar

/-!
# `Ch13LinkSides` — Cauchy rigidity, layer D, Step 3: congruent faces ⟹ equal link sides.

The `equal_sides` field that `Chapter13.CauchyArmOpeningObstruction` needs is supplied here, DERIVED
from Bridge A (`sideLen_vertexLink`): the side lengths of a vertex link are exactly the face angles at
the apex, so two vertex stars with the same number of edges and equal corresponding face angles have
equal link side lengths.  (Face congruence ⟹ equal face angles is the Mathlib `Congruent`/angle-
preservation step folded in at assembly time; here we isolate the link side equality.)
-/

namespace ProofsInTheBook.Ch13VertexStar

open scoped RealInnerProductSpace
open ProofsInTheBook.SphericalKernel

/-- **Equal face angles ⟹ equal link side lengths.**  Two vertex stars `S`, `T` with the same edge
count and matching corresponding face angles at the apex have, by Bridge A, equal link side lengths.
This is the `equal_sides` input of the Cauchy arm obstruction, derived (not posited). -/
theorem sideLen_vertexLink_eq_of_faceAngle_eq
    (S T : VertexStar) (hnT : T.n = S.n)
    (hface : ∀ i : Fin S.n,
      EuclideanGeometry.angle (S.p i.castSucc) S.o (S.p i.succ)
        = EuclideanGeometry.angle (T.p (i.cast hnT.symm).castSucc) T.o (T.p (i.cast hnT.symm).succ)) :
    ∀ i : Fin S.n,
      sideLen S.vertexLink i = sideLen T.vertexLink (i.cast hnT.symm) := by
  intro i
  rw [S.sideLen_vertexLink, T.sideLen_vertexLink, hface i]

end ProofsInTheBook.Ch13VertexStar
