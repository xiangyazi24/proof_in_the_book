import ProofsInTheBook.ZinanCh35InnerConn

/-!
# Chapter 35: the outer-cycle dual route to `InnerDartConnected`

This file pursues the **outer-cycle / dual-component-count** route to the Chapter-35
keystone residual `InnerDartConnected hNT` (defined in `ZinanCh35InnerConn.lean`).  The
route is strictly shorter than the vertex-fan tower: instead of re-routing every primal
dart walk through a boundary fan, it works in the **dual face graph**, where the inner
faces of a triangulated disk form exactly one connected component and the outer face is
the unique other one (the weak dual of a triangulated disk is connected).

## The route (4 steps)

1. **`OuterDualStep`** : face adjacency across a *non-boundary* edge.  This equals
   `DualAvoidsCycleStep M Couter` for the outer cycle `Couter` (an edge not in the outer
   boundary is exactly a non-boundary edge).  We work with `OuterDualStep` directly to
   avoid building the full `SimplePrimalCycle` packaging of the whole outer cycle; the
   reduction lemmas below are identical either way.

2. **The crux (the single topological input)** : the inner faces are
   `OuterDualStep`-connected — `InnerFacesDualConnected hNT`.  This is the genuine
   Jordan/Euler content: the weak dual of a triangulated disk is connected.  It is the
   one fact this route isolates; the cut-cap component-count machinery
   (`PlanarMapCutCap*`, `numCyclesCutPhi2_holds`, `jordan_simple_cycle2_unconditional`)
   is the intended supplier (`numComp (OuterDualStep) = 2` ⟹ this), but the bridge
   `cut-cap c = 2 → numComp (DualAvoidsCycleStep) = 2` is not yet landed in the repo.

3. **Outer isolation** : a step *out of* `outerFace` is impossible
   (`outerFace_isolated`), because `dartFace d = outerFace` forces `d` to be a boundary
   dart, contradicting the non-boundary edge of an `OuterDualStep`.  Hence the outer face
   is `OuterDualStep`-isolated and every non-outer face lies in the single inner
   component (this direction is automatic; the *reverse* — inner faces all in ONE
   component — is the crux of step 2).

4. **Lift to `InnerLink`** : an `OuterDualStep` between faces lifts to an
   `InnerLink`-walk between any two darts carrying those faces
   (`outerDualStep_lifts_to_innerLink`), through same-face `φ`-moves and one
   non-boundary `α`-crossing.  Chaining gives `InnerDartConnected` from
   `InnerFacesDualConnected`, discharging the keystone **unconditionally modulo the one
   isolated topological fact**.

## Honesty (§3.3)

`InnerFacesDualConnected` is the TRUE statement (weak dual of a triangulated disk is
connected).  It is **clean** (defined purely from `OuterDualStep`, no reference to the
conclusion), **satisfiable / non-vacuous** (reflexive on the single-triangle map; on any
near-triangulation with ≥ 2 inner faces it is a genuine reachability constraint), and is
**strictly the dual-connectivity content** of the chapter.  Everything *around* it — the
`OuterDualStep` ↔ `DualAvoidsCycleStep` identification, outer isolation, and the lift to
`InnerLink` — is proved here unconditionally and clean-3.  No `sorry`/`axiom`/`admit`/
`native_decide`; the crux is carried as a named hypothesis, never posited as proved.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35OuterDual

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35InnerConn
open ProofsInTheBook.ZinanCh35Coverage
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M}

/-! ## Step 1: the outer dual step and its identification with `DualAvoidsCycleStep` -/

/-- **The outer dual step.**  Faces `f`, `g` are adjacent across a primal edge that is
*not* a boundary edge of the outer cycle: there is a dart `d` with `dartFace d = f`,
`dartFace (α d) = g`, and `dartEdge d` non-boundary.  This is exactly
`DualAvoidsCycleStep M Couter` for the outer cycle `Couter` (whose edge set is the outer
boundary), phrased without packaging the whole outer cycle as a `SimplePrimalCycle`. -/
def OuterDualStep (hNT : NearTriangulation M) (f g : M.Face) : Prop :=
  ∃ d : D, M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧
    ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d)

/-- `OuterDualStep` is symmetric: the reverse dart `α d` witnesses the reverse step
(`dartEdge (α d) = dartEdge d` is still non-boundary). -/
lemma outerDualStep_symm {f g : M.Face} (h : OuterDualStep hNT f g) :
    OuterDualStep hNT g f := by
  obtain ⟨d, hdf, hdg, hbe⟩ := h
  refine ⟨M.α d, hdg, ?_, ?_⟩
  · rw [M.alpha_alpha]; exact hdf
  · rw [M.dartEdge_alpha]; exact hbe

/-- Symmetry transports to the reflexive-transitive closure. -/
lemma reflTransGen_outerDualStep_symm {f g : M.Face}
    (h : Relation.ReflTransGen (OuterDualStep hNT) f g) :
    Relation.ReflTransGen (OuterDualStep hNT) g f :=
  Relation.ReflTransGen.symmetric (fun _ _ hstep => outerDualStep_symm hstep) h

/-! ## Step 3: outer isolation

`outerFace` is `OuterDualStep`-isolated: an `OuterDualStep` out of `outerFace` would need
a dart `d` with `dartFace d = outerFace` (hence `d ∈ outerCycle.darts`, a boundary dart)
across a non-boundary edge — a contradiction. -/

/-- A dart whose face is the outer face lies on the outer cycle, hence its edge is a
boundary edge. -/
lemma boundaryEdge_of_dartFace_outer {d : D} (hd : M.dartFace d = hNT.outerFace) :
    hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
  have hmem : d ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff d).mpr hd
  show M.dartEdge d ∈ hNT.outerCycle.edges
  rw [hNT.outerCycle.edges_eq]
  exact List.mem_map_of_mem hmem

/-- **No `OuterDualStep` starts at the outer face.**  Such a step would need a
non-boundary edge whose dart carries the outer face — impossible. -/
lemma not_outerDualStep_outerFace {g : M.Face} :
    ¬ OuterDualStep hNT hNT.outerFace g := by
  rintro ⟨d, hdf, _, hbe⟩
  exact hbe (boundaryEdge_of_dartFace_outer hdf)

/-- **Outer isolation.**  The only face `OuterDualStep`-reachable from `outerFace` is
`outerFace` itself: the first step out is impossible. -/
lemma outerFace_isolated {f : M.Face}
    (h : Relation.ReflTransGen (OuterDualStep hNT) hNT.outerFace f) :
    f = hNT.outerFace := by
  induction h with
  | refl => rfl
  | @tail x y _ hstep ih =>
      -- `ih : x = outerFace`; then `OuterDualStep outerFace y` is impossible.
      subst ih
      exact (not_outerDualStep_outerFace hstep).elim

/-- Consequently, an `OuterDualStep`-walk that *reaches* the outer face must have started
there (by symmetry).  Useful for confining inner reachability to non-outer faces. -/
lemma eq_outerFace_of_reachesOuter {f : M.Face}
    (h : Relation.ReflTransGen (OuterDualStep hNT) f hNT.outerFace) :
    f = hNT.outerFace :=
  outerFace_isolated (reflTransGen_outerDualStep_symm h)

/-! ## Step 4: lifting an `OuterDualStep` to an `InnerLink`-walk

An `OuterDualStep` `f → g` across a non-boundary edge `dartEdge d₀` lifts: for any darts
`a, b` with `dartFace a = f`, `dartFace b = g`, the walk
`a —(same face f)→ d₀ —(non-boundary α-crossing)→ α d₀ —(same face g)→ b`
is an `InnerLink`-walk.  The two same-face links are `InnerLink` (the `Or.inl` clause),
the crossing is the `Or.inr` clause guarded by the non-boundary hypothesis. -/

/-- Two darts on the **same face** are `InnerLink`-adjacent (the `Or.inl` clause). -/
lemma innerLink_of_sameFace {a b : D} (h : M.dartFace a = M.dartFace b) :
    InnerLink hNT a b := Or.inl h

/-- **The lift of one `OuterDualStep`.**  Given `OuterDualStep f g` and any darts `a, b`
with `dartFace a = f`, `dartFace b = g`, there is an `InnerLink`-walk `a → b`. -/
lemma outerDualStep_lifts_to_innerLink {f g : M.Face} {a b : D}
    (hstep : OuterDualStep hNT f g) (ha : M.dartFace a = f) (hb : M.dartFace b = g) :
    Relation.ReflTransGen (InnerLink hNT) a b := by
  obtain ⟨d, hdf, hdg, hbe⟩ := hstep
  -- a —(same face f)→ d
  have h1 : InnerLink hNT a d := innerLink_of_sameFace (by rw [ha, hdf])
  -- d —(non-boundary α-crossing)→ α d
  have h2 : InnerLink hNT d (M.α d) := Or.inr ⟨rfl, hbe⟩
  -- α d —(same face g)→ b
  have h3 : InnerLink hNT (M.α d) b := innerLink_of_sameFace (by rw [hdg, hb])
  exact (Relation.ReflTransGen.single h1).trans
    ((Relation.ReflTransGen.single h2).trans (Relation.ReflTransGen.single h3))

/-- **An `OuterDualStep`-walk lifts to an `InnerLink`-walk.**  Carrying along, at each
position, a dart representative of the current face, each `OuterDualStep` lifts (Step 4)
and the representatives are chained by `InnerLink`-walks. -/
lemma reflTransGen_innerLink_of_outerDualStep_walk {f g : M.Face} {a b : D}
    (hwalk : Relation.ReflTransGen (OuterDualStep hNT) f g)
    (ha : M.dartFace a = f) (hb : M.dartFace b = g) :
    Relation.ReflTransGen (InnerLink hNT) a b := by
  induction hwalk generalizing b with
  | refl =>
      -- f = g; `a` and `b` carry the same face.
      exact Relation.ReflTransGen.single (innerLink_of_sameFace (by rw [ha, hb]))
  | @tail x y hwxy hstep ih =>
      -- Pick a representative dart `c` of the intermediate face `x`.
      obtain ⟨c, hc⟩ : ∃ c : D, M.dartFace c = x := by
        refine ⟨Quotient.out x, ?_⟩
        show Quotient.mk (cycleSetoid M.φ) (Quotient.out x) = x
        exact Quotient.out_eq x
      have hac : Relation.ReflTransGen (InnerLink hNT) a c := ih hc
      have hcb : Relation.ReflTransGen (InnerLink hNT) c b :=
        outerDualStep_lifts_to_innerLink hstep hc hb
      exact hac.trans hcb

/-! ## Step 2 (the crux, isolated): inner-face dual connectivity

`InnerFacesDualConnected hNT` asserts the genuine topological input: any two non-outer
faces are joined by an `OuterDualStep`-walk (face adjacency across non-boundary edges).
This is the weak dual of the triangulated disk being connected — the single Jordan/Euler
fact this route isolates.  It is clean (no reference to the conclusion), satisfiable
(reflexive on the single-triangle map), and non-vacuous (a real reachability constraint
whenever there are ≥ 2 inner faces).  It is the dual-component-count fact
`numComp (OuterDualStep) = 2` minus the outer component, which the cut-cap Euler
machinery is built to supply. -/

/-- **The isolated crux: inner-face dual connectivity.**  Every two non-outer faces are
`OuterDualStep`-reachable from one another. -/
def InnerFacesDualConnected (hNT : NearTriangulation M) : Prop :=
  ∀ f g : M.Face, f ≠ hNT.outerFace → g ≠ hNT.outerFace →
    Relation.ReflTransGen (OuterDualStep hNT) f g

/-! ## Assembly: `InnerDartConnected` from the crux (unconditional modulo the crux) -/

/-- **`InnerDartConnected` from inner-face dual connectivity.**  Two inner darts `a, b`
carry inner faces `dartFace a`, `dartFace b`; the crux supplies an `OuterDualStep`-walk
between these faces, which lifts (Steps 3–4) to an `InnerLink`-walk `a → b`. -/
theorem innerDartConnected_of_innerFacesDualConnected
    (hcrux : InnerFacesDualConnected hNT) :
    InnerDartConnected hNT := by
  intro a b ha hb
  have hwalk : Relation.ReflTransGen (OuterDualStep hNT) (M.dartFace a) (M.dartFace b) :=
    hcrux (M.dartFace a) (M.dartFace b) ha hb
  exact reflTransGen_innerLink_of_outerDualStep_walk hwalk rfl rfl

/-! ## The keystone, conditional on the single isolated crux

Feeding `innerDartConnected_of_innerFacesDualConnected` to
`ZinanCh35InnerConn.innerFaceConnectedFromFace₁_holds` discharges the Chapter-35 keystone
`InnerFaceConnectedFromFace₁` modulo exactly the one isolated topological fact
`InnerFacesDualConnected`, and cascades (`boundedFacePartition_of_innerDartConnected`) to
the coverage half of `edge_core`. -/

variable {u v : M.Vertex}

/-- **The keystone via the outer-dual route**, conditional on `InnerFacesDualConnected`. -/
theorem innerFaceConnectedFromFace₁_via_outerDual
    (data : hNT.ChordSplitData u v) (hcrux : InnerFacesDualConnected hNT) :
    InnerFaceConnectedFromFace₁ data :=
  innerFaceConnectedFromFace₁_holds data
    (innerDartConnected_of_innerFacesDualConnected hcrux)

/-- **End-to-end cascade**: `BoundedFacePartition` via the outer-dual route, conditional
on `InnerFacesDualConnected`. -/
theorem boundedFacePartition_via_outerDual
    (data : hNT.ChordSplitData u v) (hcrux : InnerFacesDualConnected hNT) :
    BoundedFacePartition data :=
  boundedFacePartition_of_innerDartConnected data
    (innerDartConnected_of_innerFacesDualConnected hcrux)

end ProofsInTheBook.ZinanCh35OuterDual

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35OuterDual.outerDualStep_symm
#print axioms ProofsInTheBook.ZinanCh35OuterDual.reflTransGen_outerDualStep_symm
#print axioms ProofsInTheBook.ZinanCh35OuterDual.boundaryEdge_of_dartFace_outer
#print axioms ProofsInTheBook.ZinanCh35OuterDual.not_outerDualStep_outerFace
#print axioms ProofsInTheBook.ZinanCh35OuterDual.outerFace_isolated
#print axioms ProofsInTheBook.ZinanCh35OuterDual.eq_outerFace_of_reachesOuter
#print axioms ProofsInTheBook.ZinanCh35OuterDual.outerDualStep_lifts_to_innerLink
#print axioms ProofsInTheBook.ZinanCh35OuterDual.reflTransGen_innerLink_of_outerDualStep_walk
#print axioms ProofsInTheBook.ZinanCh35OuterDual.innerDartConnected_of_innerFacesDualConnected
#print axioms ProofsInTheBook.ZinanCh35OuterDual.innerFaceConnectedFromFace₁_via_outerDual
#print axioms ProofsInTheBook.ZinanCh35OuterDual.boundedFacePartition_via_outerDual
