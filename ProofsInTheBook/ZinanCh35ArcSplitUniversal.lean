import ProofsInTheBook.PlanarMapBoundaryArcSplit

/-!
# Chapter 35 — universal arc-split at the `BoundaryCycle` level (thin wrapper)

The substantive proof now lives over the orbit-algebraic **core** in
`PlanarMapBoundaryArcSplit.lean` (`BoundaryCycleData.arcSplit_of_nodup`), so that the `arcSplit`
field of a `BoundaryCycle` is derivable from `VertexNodup` without the
`boundaryCycleOfFace ↔ arcSplit` self-reference (see `HANDOFF/ch35-arcsplit-core-refactor.md`).

This file re-exports it at the full-`BoundaryCycle` level for convenience: given a `BoundaryCycle`
whose vertex list is simple, every distinct boundary-vertex pair has its `BoundaryArcSplit`.  Proves
`arcSplit` was never genuine Jordan data — it is a free consequence of boundary simplicity.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedVariables false

namespace ProofsInTheBook.ZinanCh35ArcSplitUniversal

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D} {f : M.Face}

/-- **The universal arc-split from `VertexNodup`** (full-`BoundaryCycle` wrapper over the core
`BoundaryCycleData.arcSplit_of_nodup`).  For any two distinct listed boundary vertices `u, v`
(no adjacency restriction), `VertexNodup` yields a `BoundaryArcSplit M C.vertices C.edges u v`. -/
noncomputable def arcSplit_of_nodup (C : BoundaryCycle M f) (hC : C.VertexNodup)
    {u v : M.Vertex} (hne : u ≠ v)
    (hu : C.IsBoundaryVertex u) (hv : C.IsBoundaryVertex v) :
    BoundaryArcSplit M C.vertices C.edges u v :=
  C.toBoundaryCycleData.arcSplit_of_nodup hC hne hu hv

end ProofsInTheBook.ZinanCh35ArcSplitUniversal

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.ZinanCh35ArcSplitUniversal.arcSplit_of_nodup
