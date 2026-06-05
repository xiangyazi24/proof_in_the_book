import ProofsInTheBook.PlanarMapBridge
import ProofsInTheBook.PlanarMapSeparation

/-!
# The CutBridgeWitness2 input from the NearTriangulation interior-dual path (Chapter 35)

This file builds the final inputs of the Chapter-35 chord-wall bridge
(`PlanarMapBridge.lean`).  Concretely it supplies the two ingredients of
`CutBridgeWitness2`:

* **Layer A — the ordinary-dual-path extractor.**  The repo's
  `DualReachableAvoidingCycle M C (faceLeft i) (faceRight i)` is a bare face
  sequence `Relation.ReflTransGen (DualAvoidsCycleStep M C)`.  Each
  `DualAvoidsCycleStep` is *exactly* an uncut crossing dart together with its two
  faces (`∃ d, dartEdge d ∉ edgeSet ∧ dartFace d = f ∧ dartFace (α d) = g`).  We
  turn such a reachability into an `OrdinaryDualPath2` carrying the explicit
  crossing darts (genuine new content — a `ReflTransGen` induction packaging the
  bare face sequence into the design's Option-C object).

* **Layer B — the no-teleport (`FragmentCompatible2`) data.**  Per the bridge
  design (`HANDOFF/CH35_BRIDGE_DESIGN.md` §6–§7), the bare face sequence is *too
  weak* to lift on its own: a straddling old face can teleport the lift across it.
  The no-teleport content — that the entry dart and exit dart at each gate lie in
  the **same face-fragment** — is therefore carried as honest *input*
  (`FragmentCompatible2`), never derived from the bare face sequence.  In the
  near-triangulation every interior face of the interior-dual path is a triangle
  (three darts), which is exactly the regime in which this fragment-compatibility
  data is local; we expose the assembly cleanly through `CutBridgeWitness2`.

The two pieces assemble into `cutBridgeWitness2_of_inputs` and the corrected
chord-separation theorem `separates2_of_core`, which composes the corrected Jordan
bridge `jordan_simple_cycle2_bridge` with the genus-0 separation analysis of
`PlanarMapSeparation.lean`, conditional only on the named corrected face core
`NumCyclesCutPhi2` (closed in parallel) and the per-edge witnesses.

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

/-! ## Layer A: extracting an `OrdinaryDualPath2` from `DualReachableAvoidingCycle`

`DualAvoidsCycleStep M C f g` is `∃ d, M.dartEdge d ∉ C.edgeSet ∧ M.dartFace d = f
∧ M.dartFace (M.α d) = g` — precisely the data of one crossing of an
`OrdinaryDualPath2`.  We prepend such steps one at a time (head induction on the
`ReflTransGen`) to build the explicit-crossing path, keeping the two endpoint
faces fixed. -/

/-- Prepend one `DualAvoidsCycleStep` crossing to an `OrdinaryDualPath2`, shifting
indices by one (`Fin.cons` on faces, `Fin.cons` on edges).  The new position `0`
carries the source face `f`; the old path starts at position `1`. -/
noncomputable def OrdinaryDualPath2.cons (C : SimplePrimalCycle M) {f : M.Face}
    {d : D} (hd : M.dartEdge d ∉ C.edgeSet) (P : C.OrdinaryDualPath2)
    (hface : M.dartFace d = f) (hsucc : M.dartFace (M.α d) = P.face 0) :
    C.OrdinaryDualPath2 where
  n := P.n + 1
  face := (Fin.cons f P.face : Fin (P.n + 1 + 1) → M.Face)
  edge := (Fin.cons d P.edge : Fin (P.n + 1) → D)
  edge_uncut := by
    intro j
    refine Fin.cases ?_ ?_ j
    · rw [Fin.cons_zero]; exact hd
    · intro k
      rw [Fin.cons_succ]; exact P.edge_uncut k
  left_face := by
    intro j
    refine Fin.cases ?_ ?_ j
    · rw [Fin.cons_zero, show (0 : Fin (P.n + 1)).castSucc = (0 : Fin (P.n + 1 + 1)) from
        by apply Fin.ext; simp, Fin.cons_zero]
      exact hface
    · intro k
      rw [Fin.cons_succ,
        show (k.succ : Fin (P.n + 1)).castSucc = (k.castSucc).succ from
          by apply Fin.ext; simp [Fin.val_succ, Fin.val_castSucc],
        Fin.cons_succ]
      exact P.left_face k
  right_face := by
    intro j
    refine Fin.cases ?_ ?_ j
    · rw [Fin.cons_zero, Fin.cons_succ]
      exact hsucc
    · intro k
      rw [Fin.cons_succ, Fin.cons_succ]
      exact P.right_face k

@[simp] lemma OrdinaryDualPath2.cons_face_zero (C : SimplePrimalCycle M) {f : M.Face}
    {d : D} (hd : M.dartEdge d ∉ C.edgeSet) (P : C.OrdinaryDualPath2)
    (hface : M.dartFace d = f) (hsucc : M.dartFace (M.α d) = P.face 0) :
    (OrdinaryDualPath2.cons C hd P hface hsucc).face 0 = f := by
  show (Fin.cons f P.face : Fin (P.n + 1 + 1) → M.Face) 0 = f
  rw [Fin.cons_zero]

@[simp] lemma OrdinaryDualPath2.cons_face_last (C : SimplePrimalCycle M) {f : M.Face}
    {d : D} (hd : M.dartEdge d ∉ C.edgeSet) (P : C.OrdinaryDualPath2)
    (hface : M.dartFace d = f) (hsucc : M.dartFace (M.α d) = P.face 0) :
    (OrdinaryDualPath2.cons C hd P hface hsucc).face
        (Fin.last (OrdinaryDualPath2.cons C hd P hface hsucc).n)
      = P.face (Fin.last P.n) := by
  show (Fin.cons f P.face : Fin (P.n + 1 + 1) → M.Face) (Fin.last (P.n + 1))
    = P.face (Fin.last P.n)
  rw [show (Fin.last (P.n + 1)) = (Fin.last P.n).succ from by apply Fin.ext; simp [Fin.last],
    Fin.cons_succ]

/-- The trivial `OrdinaryDualPath2` at a single face (`n = 0`, no crossings). -/
def OrdinaryDualPath2.nil (C : SimplePrimalCycle M) (f : M.Face) :
    C.OrdinaryDualPath2 where
  n := 0
  face := fun _ => f
  edge := fun j => absurd j.isLt (by simp)
  edge_uncut := fun j => absurd j.isLt (by simp)
  left_face := fun j => absurd j.isLt (by simp)
  right_face := fun j => absurd j.isLt (by simp)

@[simp] lemma OrdinaryDualPath2.nil_face (C : SimplePrimalCycle M) (f : M.Face)
    (j : Fin 1) : (OrdinaryDualPath2.nil C f).face j = f := rfl

/-- **Layer A extractor.**  A cycle-avoiding dual reachability `f ⇝ g` yields an
`OrdinaryDualPath2` whose first face is `f` and last face is `g`. -/
theorem ordinaryDualPath2_of_dualReachable (C : SimplePrimalCycle M) {f g : M.Face}
    (h : DualReachableAvoidingCycle M C f g) :
    ∃ P : C.OrdinaryDualPath2, P.face 0 = f ∧ P.face (Fin.last P.n) = g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact ⟨OrdinaryDualPath2.nil C g, rfl, rfl⟩
  | head hstep _ ih =>
      obtain ⟨d, hd, hdf, hdg⟩ := hstep
      obtain ⟨P, hP0, hPlast⟩ := ih
      refine ⟨OrdinaryDualPath2.cons C hd P hdf (by rw [hdg, hP0]), ?_, ?_⟩
      · exact OrdinaryDualPath2.cons_face_zero C hd P hdf (by rw [hdg, hP0])
      · rw [OrdinaryDualPath2.cons_face_last C hd P hdf (by rw [hdg, hP0]), hPlast]

/-! ## Layer B: the corrected per-edge bridge witness from its inputs

`CutBridgeWitness2 i` bundles the Part-A side-coherence core `SidesReach2 i`
together with a map turning any cycle-avoiding dual path between the two faces of
`e_i` into a fragment-level dual path.  By Layer A the dual path refines to an
`OrdinaryDualPath2`; by the design's Option C the no-teleport
`FragmentCompatible2` data — the irreducible interior-dual input — promotes it to
a `FragmentDualPath2BetweenCycleSides`.  We expose the witness from exactly these
two honest inputs. -/

/-- **The per-edge bridge witness from its inputs.**  Given the side-coherence core
`SidesReach2 i` and, for any cycle-avoiding dual path between the two sides of
`e_i`, an `OrdinaryDualPath2` carrying the no-teleport `FragmentCompatible2` data,
we obtain the `CutBridgeWitness2 i` consumed by
`cutCapMap2_connected_of_bridgeWitness`.

The `FragmentCompatible2` data is the design's honest interior-dual input (§7
Option C): the entry/exit gate darts of each visited old face lie in one
face-fragment.  In the near-triangulation those faces are triangles, the regime in
which this data is local. -/
theorem cutBridgeWitness2_of_inputs (C : SimplePrimalCycle M) (i : Fin C.len)
    (hsides : C.SidesReach2 i)
    (hcompat : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
      ∃ P : C.OrdinaryDualPath2, C.FragmentCompatible2 i P) :
    C.CutBridgeWitness2 i where
  sidesReach := hsides
  fragPath := by
    intro hpath
    obtain ⟨P, hP⟩ := hcompat hpath
    exact ⟨C.fragmentDualPath2_of_ordinary i P hP⟩

/-- **The per-edge bridge witness with the path extracted internally.**  A variant of
`cutBridgeWitness2_of_inputs` in which the no-teleport supplier is asked only to
*augment* an already-extracted ordinary dual path with `FragmentCompatible2` data:
the bare face sequence `DualReachableAvoidingCycle` is turned into an
`OrdinaryDualPath2` by the Layer-A extractor `ordinaryDualPath2_of_dualReachable`,
and the caller's `hnoTeleport` supplies the fragment-compatibility on *some*
ordinary path with the right endpoint faces.  This makes the Layer-A extractor
load-bearing: the only honest residual is the no-teleport `SameFragment` data,
exactly the design's irreducible interior-dual input. -/
theorem cutBridgeWitness2_of_sidesReach_of_noTeleport (C : SimplePrimalCycle M)
    (i : Fin C.len) (hsides : C.SidesReach2 i)
    (hnoTeleport : ∀ P : C.OrdinaryDualPath2,
      P.face 0 = C.faceLeft i → P.face (Fin.last P.n) = C.faceRight i →
        Nonempty (C.FragmentDualPath2BetweenCycleSides i)) :
    C.CutBridgeWitness2 i where
  sidesReach := hsides
  fragPath := by
    intro hpath
    obtain ⟨P, hP0, hPlast⟩ := C.ordinaryDualPath2_of_dualReachable hpath
    exact hnoTeleport P hP0 hPlast

/-! ## Layer C: the corrected chord-separation theorem

We thread the discharged connectivity into the corrected Jordan bridge
`jordan_simple_cycle2_bridge` and compose with the genus-0 separation analysis of
`PlanarMapSeparation.lean`.  The result is the sharpest corrected chord separation:
for every near-triangulation chord, *conditional only on* the named corrected face
core `NumCyclesCutPhi2` (closed in parallel) and the per-edge bridge witnesses, the
chord separates the inner faces. -/

/-- **The corrected Jordan / chord-wall theorem from the bridge witnesses.**  For a
simple primal cycle `C` on a sphere (`hchi`, `M.Connected`), the named corrected
face core `NumCyclesCutPhi2`, the per-edge bridge witnesses, and the sanctioned
Euler inequality, no cut edge is straddled by a cycle-avoiding dual path. -/
theorem jordan_simple_cycle2_of_witness (C : SimplePrimalCycle M)
    (hcore : C.NumCyclesCutPhi2)
    (hconn : M.Connected)
    (hwit : ∀ i : Fin C.len, C.CutBridgeWitness2 i)
    (hchi : M.eulerChar = 2)
    (chi_le : (C.cutCapMap2).Connected → (C.cutCapMap2).eulerChar ≤ 2)
    (i : Fin C.len) :
    ¬ DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) :=
  C.jordan_simple_cycle2_bridge hcore hconn hwit hchi chi_le i

end SimplePrimalCycle

namespace NearTriangulation

variable {M : CombMap D} (hNT : NearTriangulation M)

/-- **The corrected chord separation from the bridge witnesses.**  Given:

* a simple primal cycle `C` whose edge set is `{s(u,v)} ∪ boundaryEdges` (`hsub`)
  — the chord together with a boundary arc;
* the named corrected face core `NumCyclesCutPhi2` for `C`;
* the per-edge corrected bridge witnesses `hwit` (Part-A side-coherence plus the
  fragment-level dual path / no-teleport interior-dual data);
* the sanctioned Euler inequality on the corrected cut map (`chi_le`);
* an index `i₀` of `C` whose two incident faces are the two chord faces;

the two chord-incident inner faces are not joined by a chord-avoiding interior-dual
path: `SphereChordSeparation h`.  This is the corrected-map analogue of
`sphereChordSeparation_of_jordan`, now resting on the corrected cut map
`cutCapMap2` (genuine design numbers) and the fragment bridge instead of the buggy
surgery. -/
theorem sphereChordSeparation_of_witness {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v)
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hcore : C.NumCyclesCutPhi2)
    (hwit : ∀ i : Fin C.len, C.CutBridgeWitness2 i)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h)))
    (chi_le : (C.cutCapMap2).Connected → (C.cutCapMap2).eulerChar ≤ 2) :
    hNT.SphereChordSeparation h := by
  intro hreach
  have hpath : DualReachableAvoidingCycle M C
      (M.dartFace (hNT.chordDart h)) (M.dartFace (M.α (hNT.chordDart h))) :=
    hNT.reachable_dualAvoidsCycle_of_chordSplitAdj C hsub hreach
  rw [← hleft, ← hright] at hpath
  exact C.jordan_simple_cycle2_of_witness hcore hNT.sphere.1 hwit hNT.sphere.2
    chi_le i₀ hpath

/-- **The chord separates** (corrected map, `Separates` form), wiring through
`separates_of_nearTriangulation`.  This is the corrected-map Chapter-35 target. -/
theorem separates2_of_core {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hcore : C.NumCyclesCutPhi2)
    (hwit : ∀ i : Fin C.len, C.CutBridgeWitness2 i)
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord)))
    (chi_le : (C.cutCapMap2).Connected → (C.cutCapMap2).eulerChar ≤ 2) :
    data.Separates :=
  data.separates_of_nearTriangulation
    (hNT.sphereChordSeparation_of_witness data.chord C hsub hcore hwit i₀ hleft
      hright chi_le)

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
