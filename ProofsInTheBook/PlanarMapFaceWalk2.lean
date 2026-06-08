import ProofsInTheBook.PlanarMapFaceWalk
import ProofsInTheBook.PlanarMapCutCapConn

/-!
# The cut-and-cap face count core — fourth pass (decisive adversarial audit)

This file is the fourth and decisive pass on the Chapter 35 Jordan face count.  Its
mandate was to **prove** the isolated Prop left open by the previous three passes,

  `FaceChainClosureCount C : numCycles (C.phiLift * C.faceCorr) = M.F + 2`,

(equivalently `(C.cutCapMap).F = M.F + 2`) and then to assemble everything
downstream.

## DECISIVE FINDING: the unconditional target is FALSE

The fourth pass establishes — by **explicit, numerically verified counterexample**
— that `FaceChainClosureCount` is **not a theorem about an arbitrary
`SimplePrimalCycle`**.  It is false in general.  No fake proof is committed; per the
repo's discipline (and §3.3 adversarial-faithfulness audit), a false target is
reported as false rather than forced.

### The exact orbit count

Because `(C.cutCapMap).φ = C.phiLift * C.faceCorr` is a *proved* algebraic identity
(`cutCapPhi_eq_phiLift_mul`, `PlanarMapCutCapF.lean`), the open quantity is exactly
the face count of the concrete cut map:

  `numCycles (C.phiLift * C.faceCorr) = numCycles ((C.cutCapMap).φ) = (C.cutCapMap).F`.

The cut-and-cap surgery has the **proved** counts `V' = V + k`
(`cutCapMap_V`) and `E' = E + k` (`CutCapSurgery.edge_count`).  Hence

  `χ' = V' - E' + F' = (V + k) - (E + k) + F' = (V - E + F') = (2 - F) + F'`

using `V - E = 2 - F` from `χ(M) = 2`.  The surgery is, per connected component, an
orientable genus-`0` planar map, so `χ' = 2 · (number of components of C.cutCapMap)`.
Therefore

  `F' = F + 2·(number of components of C.cutCapMap) - 2`,    (★)

i.e.

  **`numCycles (C.phiLift * C.faceCorr) = M.F + 2·c - 2`** where `c` is the number of
  `dartStep`-components of `C.cutCapMap`.

The target `F' = F + 2` holds **iff `c = 2`**.  It is *not* a σ/φ-level fact: it is
exactly the statement that the cut produces **exactly two** components — which is the
two-sided Jordan-separation content, the very thing `connected_of_dual_path` /
`DualPathSeparation` carry.

### The verified counterexamples (computed orbit-by-orbit, matching every proved
`cutCapPhi_*` action lemma in `PlanarMapCutCapFCore.lean`)

| map (sphere, χ=2)            | V E F | components `c` | F' (actual) | F+2 | F+2c-2 |
|------------------------------|-------|----------------|-------------|-----|--------|
| triangle on 3 vertices, k=3  | 3 3 2 |       4        |     **8**   |  4  |   8    |
| tetrahedron, cut 0→1→2→0     | 4 6 4 |       4        |    **10**   |  6  |  10    |
| triangular bipyramid, equator| 5 9 6 |       2        |     **8**   |  8  |   8    |

The "`k = 3` sphere-triangle" anchor that the previous passes cited as `F' = 4` is
in fact `F' = 8` (its cut map shatters into `c = 4` components: the three `+`-caps
each become φ'-fixed points because `σ(dart i)` is itself a bank-start `p_j`, so
`φ'(capP i) = capP i`; the `−`-caps form one 3-cycle; the forward cycle darts
`inl(dart i)` are the three FCore singletons; and the reverse darts form one
3-cycle).  Concretely `(C.cutCapMap).φ` has the 8 orbits

  `{inl0} {inl2} {inl4}` (the three FCore `inl(dart i)` singletons),
  `{inl1, inl5, inl3}` (the reverse-dart face), `{cP0} {cP1} {cP2}` (three capped
  singletons), `{cM0, cM1, cM2}` (one capped 3-cycle).

This matches the previously-proved action lemmas exactly — the previous passes never
evaluated the *global* orbit count, only the per-class action, and the asserted
numeric anchor `F' = 4` was never verified.  The genuine arithmetic is (★).

## What this pass therefore delivers (all unconditional / honestly conditional)

* `cutCapMap_F_of_closure` — restated here from the (now understood-to-be-conditional)
  closure hypothesis, kept as the honest reduction;
* `cutSigmaCounts_of_dualPathSeparation` — the full `CutSigmaCounts` bundle with
  `V'` discharged unconditionally (`cutCapMap_V`), `F'` taken as the hypothesis
  `hF` (the genuine two-component content, *not* derivable at the σ/φ layer — see
  the counterexample), and connectivity discharged from the parallel-agent
  `DualPathSeparation` parameter `hsep`;
* `separates_of_jordan_narrowed` — the end-to-end chord-separation statement with the
  **narrowest remaining hypothesis set**: just `hF` and `hsep`, the Euler inequality
  already discharged unconditionally upstream.

The `V` field is `✓` (proved), `E` is `✓` (proved), `F` is now **precisely
characterised** ((★): equals `F + 2` exactly on the two-component locus, so it is a
genuine hypothesis equivalent to the Jordan separation and *not* a free σ/φ identity),
and connectivity is the `DualPathSeparation` parameter.

No `sorry`/`axiom`/`admit`/`native_decide` anywhere in this file.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

open CutCapCount

/-! ## The honest characterisation of the open quantity

The previously-isolated Prop `FaceChainClosureCount` equals the concrete cut-map face
count, by the proved algebraic identity.  We re-expose this equivalence cleanly. -/

/-- **The open quantity is exactly the concrete cut-map face count.**  This is the
proved reduction `cutCapMap_F_iff`, restated for the named Prop. -/
theorem faceChainClosureCount_iff_cutCapMap_F (C : SimplePrimalCycle M) :
    C.FaceChainClosureCount ↔ (C.cutCapMap).F = M.F + 2 := by
  rw [FaceChainClosureCount, ← cutCapMap_F_iff]

/-- **`FaceChainClosureCount` from the concrete face count.**  The genuine content
(`F' = F + 2`) is the two-component Jordan-separation fact (see the file header
counterexample); given it, the named Prop follows. -/
theorem faceChainClosureCount_of_cutCapMap_F (C : SimplePrimalCycle M)
    (hF : (C.cutCapMap).F = M.F + 2) :
    C.FaceChainClosureCount :=
  (C.faceChainClosureCount_iff_cutCapMap_F).2 hF

/-- **The concrete face count from the closure count**, restated unconditionally as a
reduction (this is the existing `cutCapMap_F_of_closure`, re-exported through the
imported face-walk layer for the downstream assembly). -/
theorem cutCapMap_F_of_closure' (C : SimplePrimalCycle M)
    (h : C.FaceChainClosureCount) :
    (C.cutCapMap).F = M.F + 2 :=
  C.cutCapMap_F_of_closure h

/-! ## Downstream assembly: `CutSigmaCounts` with the narrowest hypotheses

`V'` is unconditional (`cutCapMap_V`); `E'` is unconditional upstream; `F'` is the
genuine two-component Jordan fact taken as `hF`; connectivity is the
`DualPathSeparation` parameter `hsep` (provided per cycle edge under a cycle-avoiding
dual path).  We bundle them into `CutSigmaCounts` with `V'` already supplied. -/

/-- **`CutSigmaCounts` from the face count and the `DualPathSeparation` core**, with
the vertex count `V' = V + k` discharged unconditionally inside.  This is the
narrowest honest bundle: the only inputs are `hF` (the two-component face fact) and
`hsep` (the §4 separation core). -/
theorem cutSigmaCounts_of_faceCount_of_dps (C : SimplePrimalCycle M)
    (hF : (C.cutCapMap).F = M.F + 2)
    (hsep : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        C.DualPathSeparation i) :
    CutSigmaCounts M C :=
  C.cutSigmaCounts_of_faceCount_of_dualPathSeparation C.cutCapMap_V hF hsep

/-- **The Jordan lemma with the narrowest hypothesis set.**  Conditional only on the
face count `hF` (the genuine two-component fact, *not* a free σ/φ identity — see the
file-header counterexample) and the §4 `DualPathSeparation` core `hsep`; the Euler
inequality is discharged unconditionally upstream (`chi_le_two_of_connected`). -/
theorem jordan_simple_cycle_narrowed (C : SimplePrimalCycle M)
    (hchi : M.eulerChar = 2)
    (hF : (C.cutCapMap).F = M.F + 2)
    (hsep : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        C.DualPathSeparation i)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  jordan_simple_cycle_of_counts
    (C.cutSigmaCounts_of_faceCount_of_dps hF hsep) hchi
    (fun hconn => chi_le_two_of_connected _ hconn) i

end SimplePrimalCycle

/-! ## End-to-end chord separation with the narrowest remaining hypotheses

We restate the near-triangulation chord-separation conclusion with the Euler
inequality already discharged, so the only remaining hypotheses are the face count
`hF` and the §4 separation core `hsep` (plus the standard chord-cycle data the
design supplies). -/

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-- **The chord separates**, conditional only on the two remaining named facts
(`hF`: the genuine two-component face count `F' = F + 2`; `hsep`: the §4
`DualPathSeparation` core).  `V' = V + k` is supplied unconditionally inside; the
Euler inequality is discharged unconditionally via `chi_le_two_of_connected`.  This
is the Chapter-35 chord wall closed modulo exactly those two named facts — the same
honest residue as `separates_of_jordan_conditional`, re-exported through the
face-walk layer with the vertex count internalised. -/
theorem separates_of_jordan_narrowed {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hF : (C.cutCapMap).F = M.F + 2)
    (hsep : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        C.DualPathSeparation i)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  hNT.separates_of_jordan_conditional data C hsub C.cutCapMap_V hF hsep i₀ hleft hright

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
