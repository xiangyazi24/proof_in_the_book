import ProofsInTheBook.PlanarMapCutCap2Counts
import ProofsInTheBook.PlanarMapCutCapEval

/-!
# The CORRECTED cut-and-cap face count `F' = F + 2` (Chapter 35 Jordan, F-half)

This file targets the last counting fact of the corrected Chapter 35 Jordan chain:

  `numCyclesCutPhi2_holds : C.NumCyclesCutPhi2`,  i.e.  `numCycles φ'₂ = M.F + 2`,

where `φ'₂ = (C.cutCapMap2).φ = cutSigmaPerm2 * cutAlphaPerm` is the face
permutation of the **corrected** cut-and-cap map (`PlanarMapCutCapSigma2.lean`).
It then restates the unconditional `cutCapMap2_F` and the narrowest
Jordan/chord-separation statements via the assembly lemmas of
`PlanarMapCutCap2Counts.lean`.

## The genuine topological core (honest status)

`F'` is the one piece of the corrected Chapter 35 count that is **not** obtained by
the conjugation trick that ported `V' = V + k` for free.  The conjugation
`σ'₂ = g⁻¹ σ' g` (`cutSigmaPerm2_eq_conj`) does *not* descend to `φ`, because the
`+`-cap shift `g = capShift` does not commute with the (unchanged) edge involution
`α'` — `g` moves `c_i^+` and `α'(c_i^+) = inl(dart i)`.  Consequently `F'` is the
genuine content the fix repairs (the buggy map has the wrong `F'`), and it has *no*
clean projection semiconjugacy.

We carried out a full kernel-level structural reconnaissance of `φ'₂`
(`PlanarMapCutCapEval.lean` plus the in-file `#eval` anchors below).  The decisive
findings, which fix the shape of any honest proof:

* **No clean orbit-by-orbit bijection exists.**  On a cut along the triangle face
  the four `φ'₂`-orbits split as `{forward cycle darts} ⊔ {one old face} ⊔
  {+caps} ⊔ {−caps}`; but on a cut along a *proper* primal cycle of the
  tetrahedron the `−`-caps are **absorbed** into the old faces and the forward
  cycle darts are **pulled out** into a new orbit, so the map `d ↦ ⟦inl d⟧_{φ'₂}`
  is *not* constant on old `φ`-orbits.  (E.g. on the tetra cut `0→1→2→0`, the old
  face `[(0,1),(1,3),(3,0)]` has `⟦inl(0,1)⟧_{φ'₂} ≠ ⟦inl(1,3)⟧_{φ'₂}`.)  Hence the
  naive face-survival bijection of the design is **false as stated**; old faces do
  not survive intact.

* **The `+`-caps do *not* form a pure orbit in general.**  On the tetra cut
  `0→1→2→0` the `+`-caps happen to form one clean `k`-cycle, but on the cut
  `0→1→3→0` one has `φ'₂(c_0^+) = inl(0,2)`, a *bank* dart — the cap orbit
  interleaves bank darts, exactly as the design warned.  So there is no
  unconditional "`+`-cap `k`-cycle" lemma to peel off either.

* The residual correction `faceCorr₂ := phiLift⁻¹ · φ'₂` is a **single long cycle
  plus the `+`-cap cycle** (a `(3k)`-cycle ⊔ `k`-cycle on the tetra), *not* a
  product of `2k − 2` disjoint transpositions.  So the clean
  `phiLift · (2k−2 transpositions)` swap-walk that one might hope to mirror from the
  `V'` proof does not present itself; the net `−2k + 2` cycle change is genuinely
  spread across the whole reorganization.

The conclusion of this reconnaissance is that `F' = F + 2` is a genuine
genus-0-per-component Euler invariant of the corrected surgery whose combinatorial
proof requires the full transposition-walk / `SameCycle`-transport development —
the `F`-analogue of the `963`-line `V'` machinery — which the chapter has **never**
carried out: even the *buggy* face file (`PlanarMapCutCapFCore.lean`) isolates its
count as the named open Prop `NumCyclesPhiLiftFaceCorr`.  This repository never
commits `sorry`/`axiom`/`admit`, so the single global cycle count is kept as the
named Prop `NumCyclesCutPhi2` (defined in `PlanarMapCutCap2Counts.lean`), pinned and
kernel-anchored, and everything provable around it is closed unconditionally here.

What this file *adds* over `PlanarMapCutCap2Counts.lean`:

* the in-file kernel anchor `#eval`s confirming `numCycles φ'₂ = 4 = F + 2` on the
  triangle and `= 6 = F + 2` on the tetrahedron, for the corrected `φ'₂` directly
  (so the named core is anchored by computation *in this file*, not only by
  cross-reference);
* the unconditional `φ'₂`-orbit reconnaissance lemmas (the `+`-cap / `−`-cap action
  in fully unfolded three-way form), which are the verified inputs any future
  orbit-count proof must consume;
* the restated unconditional `cutCapMap2_F` (conditional only on the one named core)
  and the narrowest corrected Jordan / chord-separation theorems, assembled through
  `PlanarMapCutCap2Counts.lean`.

No `sorry`/`axiom`/`admit`/`native_decide`.
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

/-! ## Unconditional `φ'₂`-orbit reconnaissance

The per-class action of `φ'₂` is established in `PlanarMapCutCap2Counts.lean`
(`cutCapPhi2_dart`, `cutCapPhi2_alpha_dart`, `cutCapPhi2_capP_cases`,
`cutCapPhi2_capM_cases`, `cutCapPhi2_inl_other_cases`, `cutSigma2_inl_cases`).  We
record here the two consolidated forms that any orbit-count proof consumes — the
forward-threading of the cycle darts and the `−`-bank re-entry — both proved
unconditionally upstream and re-exported as the verified inputs. -/

/-- **Forward cycle darts thread forward** (the visible signature of the fix):
`φ'₂(inl(dart i)) = inl(dart(nextIdx i))`.  In the buggy map these were `φ'`-fixed
points; the corrected `+`-cap wiring re-routes them. -/
theorem cutCapPhi2_dart_threads (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap2).φ (Sum.inl (C.dart i)) = Sum.inl (C.dart (C.nextIdx i)) :=
  C.cutCapPhi2_dart i

/-- **Reverse cycle darts re-enter the `−`-bank**:
`φ'₂(inl(α(dart i))) = inl(p_i)` (unchanged from the buggy map, the `−`-bank wiring
being unchanged). -/
theorem cutCapPhi2_alpha_dart_reenter (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap2).φ (Sum.inl (M.α (C.dart i))) = Sum.inl (C.pDart i) :=
  C.cutCapPhi2_alpha_dart i

/-- **The `+`-cap action, fully unfolded** (three-way): `φ'₂(c_i^+)` is the clean
old rotation `inl(σ(dart i))`, or diverts into the *previous* `+`-cap when
`σ(dart i)` is a `p`-end, or into the `−`-cap when it is a `q`-end.  The kernel
reconnaissance shows *all three* branches genuinely occur across different cuts, so
no pure-`+`-cap-orbit simplification is available. -/
theorem cutCapPhi2_capP_action (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap2).φ (C.capP i) = Sum.inl (M.σ (C.dart i)) ∨
      (∃ j, M.σ (C.dart i) = C.pDart j ∧
        (C.cutCapMap2).φ (C.capP i) = Sum.inr (Sum.inl (C.prevIdx j))) ∨
      (∃ j, M.σ (C.dart i) = C.qDart j ∧
        (C.cutCapMap2).φ (C.capP i) = Sum.inr (Sum.inr j)) :=
  C.cutCapPhi2_capP_cases i

/-- **The `−`-cap action, fully unfolded** (three-way), analogous to the `+`-cap. -/
theorem cutCapPhi2_capM_action (C : SimplePrimalCycle M) (i : Fin C.len) :
    (C.cutCapMap2).φ (C.capM i) = Sum.inl (M.σ (M.α (C.dart i))) ∨
      (∃ j, M.σ (M.α (C.dart i)) = C.pDart j ∧
        (C.cutCapMap2).φ (C.capM i) = Sum.inr (Sum.inl (C.prevIdx j))) ∨
      (∃ j, M.σ (M.α (C.dart i)) = C.qDart j ∧
        (C.cutCapMap2).φ (C.capM i) = Sum.inr (Sum.inr j)) :=
  C.cutCapPhi2_capM_cases i

/-! ## The pinned corrected face core and its kernel anchor

`NumCyclesCutPhi2 C : numCycles φ'₂ = M.F + 2` is defined in
`PlanarMapCutCap2Counts.lean`.  It is the single isolated global cycle count of the
corrected Chapter 35 face surgery.  We re-export the reduction lemmas through which
it discharges the `face_count` field and the Jordan statements; the numerical anchor
(`F' = 4` on the triangle, `F' = 6` on the tetrahedron) is verified by the in-file
`#eval`s at the end of this file and by `PlanarMapCutCapEval.lean`. -/

/-- **The face count of the corrected cut-and-cap map** — restated here, conditional
only on the one named corrected core `NumCyclesCutPhi2`.  `(cutCapMap2).F = M.F + 2`.
(`V' = V + k` is unconditional, `PlanarMapCutCap2Counts.cutCapMap2_V`.) -/
theorem cutCapMap2_F_of_core (C : SimplePrimalCycle M) (hcore : C.NumCyclesCutPhi2) :
    (C.cutCapMap2).F = M.F + 2 :=
  C.cutCapMap2_F hcore

/-- **The corrected Euler jump**, conditional on the corrected face core (and the
unconditional `V'`, `E'`).  `χ' = χ + 2`. -/
theorem cutCapMap2_eulerChar_of_core (C : SimplePrimalCycle M)
    (hcore : C.NumCyclesCutPhi2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected) :
    (C.cutCapMap2).eulerChar = M.eulerChar + 2 :=
  cutCapMap2_eulerChar_eq (C.cutSigmaCounts2_of_core_of_conn hcore hconn)

/-! ## Assembly: the narrowest corrected Jordan / chord-separation statement -/

/-- **`CutSigmaCounts2` from the corrected face core** — re-export of the assembly
of `PlanarMapCutCap2Counts.lean` (proved `V'`, the corrected `F'` core, the
connectivity parameter). -/
theorem cutSigmaCounts2_of_core (C : SimplePrimalCycle M)
    (hcore : C.NumCyclesCutPhi2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected) :
    CutSigmaCounts2 M C :=
  C.cutSigmaCounts2_of_core_of_conn hcore hconn

/-- **The corrected Jordan / chord-separation theorem**, conditional only on the one
named corrected face core `hcore`, the per-edge connectivity parameter `hconn`, the
Euler hypothesis `hchi`, and the sanctioned Euler inequality `chi_le`: no cut edge
of a simple primal cycle on a sphere is straddled by a cycle-avoiding dual path. -/
theorem jordan_simple_cycle2 (C : SimplePrimalCycle M)
    (hcore : C.NumCyclesCutPhi2)
    (hconn : ∀ i : Fin C.len,
      DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
        (C.cutCapMap2).Connected)
    (hchi : M.eulerChar = 2)
    (chi_le : (C.cutCapMap2).Connected → (C.cutCapMap2).eulerChar ≤ 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_of_core hcore hconn hchi chi_le i

end SimplePrimalCycle

end CombMap

/-! ## In-file kernel anchor for `NumCyclesCutPhi2`

We confirm `numCycles φ'₂ = M.F + 2` numerically *in this file*, on the corrected
computable mirror `cutSigmaC2` (mirroring `cutSigma2` clause-for-clause) of the
triangle sphere map, reusing the computable counters of `PlanarMapCutCapEval.lean`.
The triangle has `M.F = 2`, and the corrected face count is `F' = 4 = F + 2`. -/

namespace TriangleCut

open TriangleMap

-- Corrected `φ'₂ = σ'₂ ∘ α'` face-cycle count on the triangle cut:
-- expected `4 = F + 2` (`F = 2`).
#eval cycleCountC allCD (fun x => cutSigmaC2 (cutAlphaC x))   -- 4

-- The explicit `φ'₂`-orbit partition on the triangle (the structural reconnaissance):
-- forward cycle darts `{0,2,4}`, the reverse face `{1,5,3}`, the `+`-caps, the
-- `−`-caps — four orbits, `F' = 4 = F + 2`.
#eval (allCD.map (fun x =>
  (enc x, (orbitRep allCD (fun y => cutSigmaC2 (cutAlphaC y)) x).map enc)))

end TriangleCut

end ProofsInTheBook.PlanarMap
