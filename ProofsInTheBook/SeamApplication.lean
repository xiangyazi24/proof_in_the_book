import ProofsInTheBook.SeamStructure
import ProofsInTheBook.PlanarMapBridgeWitness

/-!
# The near-triangulation chord application of the F-side `BankStepCert` route (Chapter 35)

`SeamStructure.lean` reduced the Chapter-35 F-side touch certificate to the single
isolated per-step field `BankStepCert.step_component`, and re-exported the
position-free lower bound and Jordan consequences through `TouchCert.lean`
(`cutCapMap2_F_lower_of_stepCert`, `jordan_simple_cycle2_lower_of_stepCert`).  This
file is the **application layer**: it specialises that lower-bound route to the
near-triangulation chord wall and assembles the end-to-end chord separation
(`SphereChordSeparation` / `Separates`), with the remaining hypotheses reduced to the
bridge-witness data of `PlanarMapBridgeWitness.lean` together with the single F-side
certificate.

## What this layer adds over `SeamStructure.lean`

`SeamStructure.lean` works for an abstract `SimplePrimalCycle`; the only F-side
residue it carries is `BankStepCert.step_component`.  Here we (1) make the
*destination analysis* of `step_component` explicit in the chord regime, and (2)
thread the lower-bound Jordan route into the chord-separation theorem, producing a
route **strictly parallel to** — and on the F-side strictly **lighter than** — the
`NumCyclesCutPhi2`-based `separates2_of_core`/`sphereChordSeparation_of_witness` of
`PlanarMapBridgeWitness.lean`.

### The `faceCorr₂` step destinations in the chord application (the heart)

`faceCorr₂ = phiLift⁻¹ · φ'₂` on the cut darts `CutDart = D ⊕ (Fin len ⊕ Fin len)`.
The `phiLift`-orbits are: each `inl d` lives in the `M.φ`-orbit of `d` (a *face* of
`M`, since `phiLift = M.φ ⊕ 1` on the `inl` summand), and each cap `inr c` is a
`phiLift`-fixed singleton orbit.  The step actions split into:

* **Forward bank-end darts** `inl (dart i)`:
  `faceCorr₂ (inl (dart i)) = inl (M.φ⁻¹ (dart (nextIdx i)))`
  (`faceCorr2_inl_dart`).  Its `phiLift`-orbit is the *face* containing
  `dart (nextIdx i)`.  Whether that face equals the face of `dart i` is the genus-0
  **seam incidence** `phiLift vᵢ = u_{i+1}` (`PlanarMapSeamSpec.lean`) — for an arc
  (boundary) dart this is the outer-face boundary-cycle walk visiting consecutive
  arc darts in order; for a chord dart it is the inner-triangle adjacency.  This
  single joint is what `step_component` carries.

* **Reverse bank-end darts** `inl (M.α (dart i))`:
  `faceCorr₂ (inl (M.α (dart i))) = inl (M.φ⁻¹ (pDart i))`
  (`faceCorr2_inl_alpha_dart`).  `pDart i` is the `−`-bank re-entry dart, adjacent
  to the `i`-th cap's generator edge.

* **Caps** `capP i`, `capM i`: by `SeamStructure.faceCorr2_capP_cases` /
  `faceCorr2_capM_cases` every cap is sent symbolically to a bank-end (`inl (α (dart i))`
  resp. `inl (dart i)`) or to another cap — *both* adjacent to the cap's own
  generator-edge endpoint.  So the cap half of `step_component` is forced once `gen`
  includes each cap's edge; **only the forward bank-end step is the genuine residue**.

The genuinely cut-dependent seam incidence is, in the repository's abstract
combinatorial setting, *not* derivable from `SimplePrimalCycle` together with the
`NearTriangulation` face structure alone — it is the embedding datum isolated as the
`SeamDecomposition` / `MergedOuterArcData` / `step_component` input across
`PlanarMapSeamSpec.lean`, `PlanarMapOuterArc.lean`, `TouchCert.lean`.  We therefore
carry it honestly as the one F-side certificate, exactly as the witness route carries
`NumCyclesCutPhi2`, and we expose the destination structure as proven lemmas so that
the residue is *named and located*, not faked.

No `sorry`/`axiom`/`admit`/`native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.PlanarMap

open Equiv Equiv.Perm Function

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

variable {M : CombMap D}

/-! ## The explicit `faceCorr₂` step destinations on the bank-end darts

These two lemmas pin the `faceCorr₂` action on the `inl`-bank darts symbolically
(via the proven `φ'₂` closed forms of `PlanarMapCutCap2F.lean` post-composed with
`phiLift⁻¹`), exhibiting the destinations the chord-application `step_component`
must connect.  They are the bank-end analogues of `faceCorr2_capP_cases` /
`faceCorr2_capM_cases`. -/

/-- **Forward bank-end step.**  `faceCorr₂ (inl (dart i)) = inl (φ⁻¹ (dart (nextIdx i)))`.
The destination's `phiLift`-orbit is the face containing `dart (nextIdx i)`; the
seam incidence (whether it equals the face of `dart i`) is the one isolated joint. -/
theorem faceCorr2_inl_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.faceCorr2 (Sum.inl (C.dart i)) = Sum.inl (M.φ⁻¹ (C.dart (C.nextIdx i))) := by
  rw [faceCorr2_apply, C.cutCapPhi2_dart_threads i, phiLift_symm_inl]

/-- **Reverse bank-end step.**  `faceCorr₂ (inl (α (dart i))) = inl (φ⁻¹ (pDart i))`.
The destination is the `−`-bank re-entry dart, adjacent to the `i`-th cap. -/
theorem faceCorr2_inl_alpha_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.faceCorr2 (Sum.inl (M.α (C.dart i))) = Sum.inl (M.φ⁻¹ (C.pDart i)) := by
  rw [faceCorr2_apply, C.cutCapPhi2_alpha_dart_reenter i, phiLift_symm_inl]

/-- **The forward bank-end destination lies in the face of `dart (nextIdx i)`.**
`pOrbOf phiLift (faceCorr₂ (inl (dart i)))` is the `phiLift`-orbit (= face) of
`inl (dart (nextIdx i))`: `φ⁻¹` moves within the `M.φ`-orbit, which is one
`phiLift`-orbit on the `inl` summand. -/
theorem pOrbOf_faceCorr2_inl_dart (C : SimplePrimalCycle M) (i : Fin C.len) :
    ProofsInTheBook.TouchRank.pOrbOf C.phiLift (C.faceCorr2 (Sum.inl (C.dart i)))
      = ProofsInTheBook.TouchRank.pOrbOf C.phiLift (Sum.inl (C.dart (C.nextIdx i))) := by
  rw [faceCorr2_inl_dart]
  -- `phiLift (inl (φ⁻¹ d)) = inl (φ (φ⁻¹ d)) = inl d`, so the two are `phiLift`-SameCycle.
  apply (ProofsInTheBook.TouchRank.pOrbOf_eq_iff C.phiLift _ _).mpr
  refine ⟨1, ?_⟩
  rw [zpow_one, phiLift_inl, Equiv.Perm.inv_def, M.φ.apply_symm_apply]

/-! ## The F-side Jordan and chord-separation from a `BankStepCert`

We thread `jordan_simple_cycle2_lower_of_stepCert` (F-side lower bound, via the
per-step certificate) with the bridge-witness connectivity discharge
`cutCapMap2_connected_of_bridgeWitness`, producing the Jordan statement from a
`BankStepCert` plus the bridge witnesses — the F-side analogue of
`jordan_simple_cycle2_of_witness`, with `NumCyclesCutPhi2` replaced by the strictly
smaller per-step field. -/

/-- **The Jordan / chord-wall theorem from a per-step bank certificate and the bridge
witnesses.**  For a simple primal cycle `C` on a sphere, the F-side per-step
certificate `cert`, the per-edge bridge witnesses `hwit`, `M.Connected`, and the
Euler hypotheses, no cut edge is straddled by a cycle-avoiding dual path.  The
connectivity parameter `hconn` of the lower-bound route is discharged from the bridge
witnesses, exactly as in `jordan_simple_cycle2_bridge`. -/
theorem jordan_simple_cycle2_of_stepCert_witness (C : SimplePrimalCycle M)
    (cert : C.BankStepCert)
    (hconn : M.Connected)
    (hwit : ∀ i : Fin C.len, C.CutBridgeWitness2 i)
    (hchi : M.eulerChar = 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_lower_of_stepCert cert hchi
    (C.cutCapMap2_connected_of_bridgeWitness hconn hwit) i

end SimplePrimalCycle

/-! ## The near-triangulation chord separation from the F-side per-step certificate

The chord application: `C` is the simple primal cycle built from the chord
`s(u,v)` plus a boundary arc (`hsub`), the two chord faces are the two incident
faces of `i₀` (`hleft`, `hright`).  We compose the F-side Jordan
`jordan_simple_cycle2_of_stepCert_witness` with the genus-0 separation analysis of
`PlanarMapSeparation.lean`, mirroring `sphereChordSeparation_of_witness` but with the
F-side input reduced from the exact face core `NumCyclesCutPhi2` to the per-step
`BankStepCert`. -/

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-- **The corrected chord separation from the F-side per-step certificate and the
bridge witnesses** (`SphereChordSeparation` form).  Given the chord `h`, the
simple primal cycle `C = chord ∪ arc` (`hsub`), the F-side per-step certificate
`cert`, the per-edge bridge witnesses `hwit`, and the index `i₀` whose incident faces
are the two chord faces, the two chord-incident inner faces are not joined by a
chord-avoiding interior-dual path.

This is the F-side-lower-bound analogue of `sphereChordSeparation_of_witness`: the
sphere connectivity / Euler hypotheses are read off `hNT.sphere`, and the F-side
input is the strictly-smaller per-step field rather than the exact face core. -/
theorem sphereChordSeparation_of_stepCert {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v)
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (cert : C.BankStepCert)
    (hwit : ∀ i : Fin C.len, C.CutBridgeWitness2 i)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h))) :
    hNT.SphereChordSeparation h := by
  intro hreach
  have hpath : DualReachableAvoidingCycle M C
      (M.dartFace (hNT.chordDart h)) (M.dartFace (M.α (hNT.chordDart h))) :=
    hNT.reachable_dualAvoidsCycle_of_chordSplitAdj C hsub hreach
  rw [← hleft, ← hright] at hpath
  exact C.jordan_simple_cycle2_of_stepCert_witness cert hNT.sphere.1 hwit
    hNT.sphere.2 i₀ hpath

/-- **The chord separates** (corrected map, `Separates` form), from the F-side
per-step certificate and the bridge witnesses.  This is the F-side-lower-bound
Chapter-35 target, parallel to `separates2_of_core` but with the F-side input reduced
to `BankStepCert`. -/
theorem separates2_of_stepCert {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (cert : C.BankStepCert)
    (hwit : ∀ i : Fin C.len, C.CutBridgeWitness2 i)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  data.separates_of_nearTriangulation
    (hNT.sphereChordSeparation_of_stepCert data.chord C hsub cert hwit i₀ hleft hright)

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap

/-! ## Non-vacuity: the F-side per-step destination lemmas fire on the symbolic actions

The genuinely cut-dependent seam joint (`step_component`) cannot be exhibited
unconditionally — the repository carries no concrete abstract `SimplePrimalCycle`
instance (see `TouchCert.lean` / `SeamStructure.lean`).  We instead confirm the
destination-analysis lemmas of this layer are non-degenerate by exercising them
against the proven symbolic `φ'₂` cap actions, ruling out the "vacuous reduction"
failure mode: every cap step lands on a bank-end or a cap (the forced half of
`step_component`), and the forward bank-end step lands in the face of the next cycle
dart (the isolated half). -/

namespace ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

variable {D : Type*} [Fintype D] [DecidableEq D] {M : CombMap D}

/-- The `+`-cap step lands on the `−`-bank end `inl (α (dart i))`, on a previous
`+`-cap, or on a `−`-cap — all adjacent to the cap's own generator edge.  This is the
forced (symbolically-pinned) half of `step_component`, re-exported here as the
application-layer record. -/
example (C : SimplePrimalCycle M) (i : Fin C.len) :
    C.faceCorr2 (C.capP i) = Sum.inl (M.α (C.dart i)) ∨
      (∃ j, M.σ (C.dart i) = C.pDart j ∧
        C.faceCorr2 (C.capP i) = C.capP (C.prevIdx j)) ∨
      (∃ j, M.σ (C.dart i) = C.qDart j ∧
        C.faceCorr2 (C.capP i) = C.capM j) :=
  C.faceCorr2_capP_cases i

/-- The forward bank-end step's destination orbit is the face of the next cycle
dart: the isolated seam half of `step_component`, located here as a proven orbit
identity (the residue is whether this face coincides with the face of `dart i`). -/
example (C : SimplePrimalCycle M) (i : Fin C.len) :
    ProofsInTheBook.TouchRank.pOrbOf C.phiLift (C.faceCorr2 (Sum.inl (C.dart i)))
      = ProofsInTheBook.TouchRank.pOrbOf C.phiLift (Sum.inl (C.dart (C.nextIdx i))) :=
  C.pOrbOf_faceCorr2_inl_dart i

end ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle

/-! ## Axiom audit -/

#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.faceCorr2_inl_dart
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.faceCorr2_inl_alpha_dart
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.pOrbOf_faceCorr2_inl_dart
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.jordan_simple_cycle2_of_stepCert_witness
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.sphereChordSeparation_of_stepCert
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.separates2_of_stepCert
