import ProofsInTheBook.Ch13MarkedSphere
import ProofsInTheBook.Chapter13

/-!
# `Ch13CauchyAssembly` — the faithful Cauchy-rigidity assembly skeleton.

ChatGPT's adversarial audit showed the old `Chapter13.CauchyRigidityCertificate` (Euler/`3F=2E`/double-count
as fields) is UNFAITHFUL — it combines the active subgraph (for the per-vertex `≥4`) with a triangulation
(for `≤2` per face and `3F=2E`), two incompatible graphs. The faithful replacement (ChatGPT's Q5) is this
two-layer split:

* a **geometric** structure `CauchyMarkedTriangulatedSphere` carrying a triangulated-sphere `CombMap`, an
  edge signing, and the GENUINE per-active-vertex arm data (`vertexArm`, `≥4` from real spherical links via
  `Ch13ArmVertexFull.cauchyArmVertexFull_of_links`) plus the bridge `signChanges = vertexFlipCountSkipZeros`;
* one **combinatorial** theorem `cauchy_marked_sphere_low_active_vertex` (∃ ACTIVE vertex with ≤2 flips on a
  triangulated sphere) — its STRICT core is PROVEN
  (`Ch13MarkedSphere.strict_signed_triangulated_sphere_not_all_ge_four`), the with-zeros reduction is the
  isolated residual (`Ch13MarkedReduction`, in progress).

The contradiction is then ~10 lines (this file). NO `faceSigns`/`double_count`/`euler_formula`/`3F=2E`
fields — that was the §3.3 trap.
-/

namespace ProofsInTheBook.Ch13CauchyAssembly

open ProofsInTheBook.PlanarMap ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.Ch13MarkedSphere
open ProofsInTheBook.Chapter13

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- **The faithful geometric input** for Cauchy rigidity (ChatGPT's Q5 replacement for the unfaithful
`CauchyRigidityCertificate`).  A triangulated-sphere combinatorial map with a ±/0 edge signing, carrying
the GENUINE per-active-vertex arm data: at each active vertex the spherical-link `CauchyArmVertex` (whose
`four_le_signChanges` ≥4 is real), bridged to the skip-zeros σ-cycle count.  It does NOT carry any
Euler/`3F=2E`/face-count field — those live inside the combinatorial lemma. -/
structure CauchyMarkedTriangulatedSphere (M : CombMap D) where
  /-- The surface is a triangulated sphere. -/
  isSphere : M.IsSphereMap
  triangleFaces : M.FaceRegular 3
  /-- The dihedral-difference signing (±/0). -/
  edgeSign : D → EdgeSign
  /-- The signing is edge-invariant (`α`-stable): both darts of an edge carry the same sign. -/
  edgeSign_inv : ∀ d, edgeSign (M.α d) = edgeSign d
  /-- The GENUINE vertex-link arm datum at each active vertex (from real spherical links). -/
  vertexArm : ∀ d, ActiveVertex M edgeSign d → CauchyArmVertex
  /-- The bridge: the arm-datum's sign-change count is exactly the skip-zeros σ-cycle count at the vertex
  (the geometric σ-order = the link rotational order). -/
  vertexArm_signChanges_eq :
    ∀ d (hd : ActiveVertex M edgeSign d),
      (vertexArm d hd).signChanges = vertexFlipCountSkipZeros M edgeSign d

/-- **The faithful Cauchy contradiction.**  Given the geometric input and the (separately proven)
combinatorial lemma — every nonzero ±/0 signing of a triangulated sphere has an ACTIVE vertex with ≤2
skip-zeros sign changes — every edge sign is zero (no dihedral angle differs ⟹ the polyhedra are
congruent).  The genuine `≥4` (from real links) collides with the combinatorial `≤2`. -/
theorem cauchy_no_nonzero_edgeSign {M : CombMap D}
    (C : CauchyMarkedTriangulatedSphere M)
    (hcomb : M.IsSphereMap → M.FaceRegular 3 →
      (∃ d, C.edgeSign d ≠ EdgeSign.zero) →
      ∃ d, ActiveVertex M C.edgeSign d ∧ vertexFlipCountSkipZeros M C.edgeSign d ≤ 2) :
    ∀ d, C.edgeSign d = EdgeSign.zero := by
  by_contra hnot
  push_neg at hnot
  obtain ⟨d₀, hd₀⟩ := hnot
  obtain ⟨d, hdActive, hdLow⟩ := hcomb C.isSphere C.triangleFaces ⟨d₀, hd₀⟩
  have hdFour : 4 ≤ vertexFlipCountSkipZeros M C.edgeSign d := by
    rw [← C.vertexArm_signChanges_eq d hdActive]
    exact CauchyArmVertex.four_le_signChanges (C.vertexArm d hdActive)
  omega

end ProofsInTheBook.Ch13CauchyAssembly
