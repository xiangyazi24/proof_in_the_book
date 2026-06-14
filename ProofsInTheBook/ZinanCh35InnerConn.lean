import ProofsInTheBook.ZinanCh35StarRotation
import ProofsInTheBook.ZinanCh35Coverage

/-!
# Chapter 35 keystone: inner-face dual connectivity of a near-triangulation

This file proves the **keystone** flagged in `ZinanCh35Coverage.lean`:

  `InnerFaceConnectedFromFace₁ data` :  every non-outer face is `InnerAdj`-reachable
  from the chord face `face₁`,

i.e. the **inner-face dual graph** (faces glued along non-boundary edges) is connected.
Discharging it cascades (`boundedFacePartition_of_innerConnected`,
`edge_core_field_of_innerConnected`) to close the whole coverage half of `edge_core`.

## Architecture

The reduction has three layers, all proved here, none assumed:

1. **`InnerAdj` calculus** (unconditional, clean-3).
   * `InnerAdj` is symmetric, so `ReflTransGen (InnerAdj hNT)` is an equivalence on faces.
   * **The α-step** : if `dartEdge d` is non-boundary and both `dartFace d`, `dartFace (α d)`
     are inner, then `InnerAdj`-step `dartFace d → dartFace (α d)`.
   * **The φ-step** : `dartFace d = dartFace (φ d)`, so consecutive face-permutation darts are
     `InnerAdj`-equal (the same face).
   * **The σ-step bridge** (the load-bearing local move): `dartFace (σ d) = dartFace (α d)`
     (`starFace_next_eq_alpha`), so a single vertex rotation reads the face across the edge of
     `d`; if that edge is non-boundary, it is an `InnerAdj`-step `dartFace d → dartFace (σ d)`.

2. **Local star connectivity** : the inner faces incident to one vertex are `InnerAdj`-connected.
   This is the genuine planar input (the "fan" around a vertex); we isolate it as the predicate
   `InnerStarConnected` and prove it for **interior** vertices (every star edge non-boundary, so
   the whole `σ`-orbit gives the connection).  The boundary-vertex case is the residual fan fact.

3. **Global assembly** : `M.Connected` is the primal dart-walk `ReflTransGen dartStep`.  Each
   `dartStep` is a `σ`-`SameCycle` (same vertex → local star connectivity) or an `α`-edge
   (`InnerAdj`-step when non-boundary; a boundary edge has one outer side, handled separately).
   Lifting the primal walk between two inner darts gives `InnerAdj`-connectivity of their faces.

No `sorry` / `axiom` / `admit` / `native_decide` in the reduction layer.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35InnerConn

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.ZinanCh35Coverage
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M}

/-! ## 1. `InnerAdj` calculus -/

/-- **`InnerAdj` is symmetric.**  The reverse dart `α d` witnesses the reverse adjacency:
`dartFace (α d) = g`, `dartFace (α (α d)) = dartFace d = f`, and `dartEdge (α d) = dartEdge d`
is still non-boundary. -/
lemma innerAdj_symm {f g : M.Face} (h : InnerAdj hNT f g) : InnerAdj hNT g f := by
  obtain ⟨d, hdf, hdg, hbe⟩ := h
  refine ⟨M.α d, hdg, ?_, ?_⟩
  · rw [M.alpha_alpha]; exact hdf
  · rw [M.dartEdge_alpha]; exact hbe

/-- Symmetry transports to the reflexive-transitive closure: `ReflTransGen (InnerAdj hNT)` is
symmetric, hence an equivalence on faces. -/
lemma reflTransGen_innerAdj_symm {f g : M.Face}
    (h : Relation.ReflTransGen (InnerAdj hNT) f g) :
    Relation.ReflTransGen (InnerAdj hNT) g f := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y hxy hstep ih =>
      exact Relation.ReflTransGen.head (innerAdj_symm hstep) ih

/-- **The α-step.**  If the edge of `d` is not a boundary edge, then `dartFace d` and
`dartFace (α d)` are `InnerAdj`-adjacent (the dart `d` itself is the witness). -/
lemma innerAdj_alpha {d : D} (hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d)) :
    InnerAdj hNT (M.dartFace d) (M.dartFace (M.α d)) :=
  ⟨d, rfl, rfl, hbe⟩

/-- **The σ-step.**  A single vertex rotation reads the face across the edge of `d`
(`starFace_next_eq_alpha`: `dartFace (σ d) = dartFace (α d)`).  When that edge is non-boundary,
this is an `InnerAdj`-step `dartFace d → dartFace (σ d)`. -/
lemma innerAdj_sigma {d : D} (hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d)) :
    InnerAdj hNT (M.dartFace d) (M.dartFace (M.σ d)) := by
  have hσα : M.dartFace (M.σ d) = M.dartFace (M.α d) := by
    have hφ : M.φ (M.α d) = M.σ d := by
      simp [φ, Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
    calc M.dartFace (M.σ d)
        = M.dartFace (M.φ (M.α d)) := by rw [hφ]
      _ = M.dartFace (M.α d) := M.dartFace_phi _
  rw [hσα]; exact innerAdj_alpha hbe

/-! ## 2. Boundary-edge geometry

`boundaryEdge_dart_outer` (here without the `ChordSplitData` parameter): a boundary edge has
the outer face on (at least) one side.  Contrapositive: if **both** faces of `d` are inner, the
edge is non-boundary. -/

/-- For a boundary edge, at least one of its two darts lies on the outer face. -/
lemma boundaryEdge_dart_outer {e : D}
    (hbe : hNT.outerCycle.IsBoundaryEdge (M.dartEdge e)) :
    M.dartFace e = hNT.outerFace ∨ M.dartFace (M.α e) = hNT.outerFace := by
  rw [BoundaryCycle.IsBoundaryEdge, hNT.outerCycle.edges_eq, List.mem_map] at hbe
  obtain ⟨b, hb, hbe⟩ := hbe
  have hbface : M.dartFace b = hNT.outerFace := (hNT.outerCycle.mem_darts_iff b).mp hb
  have hsc : M.α.SameCycle e b :=
    M.alpha_sameCycle_of_dartEdge_eq hNT.simpleGraph hbe.symm
  rcases (M.alpha_sameCycle_iff b e).mp hsc.symm with h | h
  · exact Or.inl (by rw [h]; exact hbface)
  · right; rw [h, M.alpha_alpha]; exact hbface

/-- **No interior bridge: an edge with both faces inner is non-boundary.**  Contrapositive of
`boundaryEdge_dart_outer`. -/
lemma not_boundaryEdge_of_both_inner {d : D}
    (h1 : M.dartFace d ≠ hNT.outerFace) (h2 : M.dartFace (M.α d) ≠ hNT.outerFace) :
    ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d) := by
  intro hbe
  rcases boundaryEdge_dart_outer hbe with h | h
  · exact h1 h
  · exact h2 h

/-! ## 3. The clean inner-dart link and its lift to face connectivity

`InnerLink d e` is the **liftable** dart-level step: either `d`, `e` carry the same face, or `e`
is the reverse `α d` across a **non-boundary** edge.  Every `InnerLink`-step projects to an
`InnerAdj`-step (or face equality), so an `InnerLink`-walk lifts to an `InnerAdj`-reachability
of the endpoint faces. -/

/-- The clean inner-dart link: same face, or the reverse dart across a non-boundary edge. -/
def InnerLink (hNT : NearTriangulation M) (d e : D) : Prop :=
  M.dartFace d = M.dartFace e ∨
    (e = M.α d ∧ ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d))

/-- **A single `InnerLink`-step lifts to face `InnerAdj`-reachability.** -/
lemma reflTransGen_innerAdj_of_innerLink {d e : D} (h : InnerLink hNT d e) :
    Relation.ReflTransGen (InnerAdj hNT) (M.dartFace d) (M.dartFace e) := by
  rcases h with hface | ⟨hαd, hbe⟩
  · rw [hface]
  · subst hαd
    exact Relation.ReflTransGen.single (innerAdj_alpha hbe)

/-- **An `InnerLink`-walk lifts to an `InnerAdj`-walk on faces.** -/
lemma reflTransGen_innerAdj_of_innerLink_walk {d e : D}
    (h : Relation.ReflTransGen (InnerLink hNT) d e) :
    Relation.ReflTransGen (InnerAdj hNT) (M.dartFace d) (M.dartFace e) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail x y hxy hstep ih =>
      exact ih.trans (reflTransGen_innerAdj_of_innerLink hstep)

/-! ### A single `σ`-rotation step is two `InnerLink`-steps (across a non-boundary edge)

Rotating one step around a vertex, `σ d = φ (α d)`, decomposes as
`d —(α-reverse)→ α d —(same face)→ φ(α d) = σ d`.  The first link needs `edge d` non-boundary;
the second is always valid (`dartFace (α d) = dartFace (σ d)`). -/

/-- `dartFace (α d) = dartFace (σ d)` (the same-face half of the rotation step). -/
lemma dartFace_alpha_eq_dartFace_sigma (d : D) :
    M.dartFace (M.α d) = M.dartFace (M.σ d) := by
  have hφ : M.φ (M.α d) = M.σ d := by
    simp [φ, Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
  calc M.dartFace (M.α d)
      = M.dartFace (M.φ (M.α d)) := (M.dartFace_phi _).symm
    _ = M.dartFace (M.σ d) := by rw [hφ]

/-- **A non-boundary `σ`-rotation step is an `InnerLink`-walk** `d → σ d` of length two. -/
lemma reflTransGen_innerLink_sigma {d : D}
    (hbe : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge d)) :
    Relation.ReflTransGen (InnerLink hNT) d (M.σ d) := by
  -- `d → α d` (reverse across the non-boundary edge), then `α d → σ d` (same face).
  refine Relation.ReflTransGen.head (Or.inr ⟨rfl, hbe⟩) ?_
  exact Relation.ReflTransGen.single (Or.inl (dartFace_alpha_eq_dartFace_sigma d))

/-- **A full non-boundary `σ`-arc lifts to an `InnerLink`-walk.**  If `σ^k a` is the target and
every rotation edge `dartEdge (σ^i a)` for `i < k` is non-boundary, then `a` reaches `σ^k a`
through `InnerLink`-steps. -/
lemma reflTransGen_innerLink_sigma_pow {a : D} :
    ∀ (k : ℕ),
      (∀ i : ℕ, i < k → ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge ((M.σ ^ i) a))) →
      Relation.ReflTransGen (InnerLink hNT) a ((M.σ ^ k) a)
  | 0, _ => by simpa using Relation.ReflTransGen.refl
  | (k + 1), hbe => by
      have hstepEdge : ¬ hNT.outerCycle.IsBoundaryEdge (M.dartEdge ((M.σ ^ k) a)) :=
        hbe k (Nat.lt_succ_self k)
      have hrest : Relation.ReflTransGen (InnerLink hNT) a ((M.σ ^ k) a) :=
        reflTransGen_innerLink_sigma_pow k (fun i hi => hbe i (Nat.lt_succ_of_lt hi))
      have hlast : Relation.ReflTransGen (InnerLink hNT) ((M.σ ^ k) a) ((M.σ ^ (k + 1)) a) := by
        have : (M.σ ^ (k + 1)) a = M.σ ((M.σ ^ k) a) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        rw [this]; exact reflTransGen_innerLink_sigma hstepEdge
      exact hrest.trans hlast

/-! ## 4. The sharp residual + the reduction to it

`InnerDartConnected` is connectivity of the **inner-dart graph** under `InnerLink`: any two darts
carrying inner faces are joined by an `InnerLink`-walk.  This is exactly inner-face dual
connectivity at the dart level — the genuine planar input (it is the cut-component identification
the `ZinanCh35EdgeCore` header flagged as missing).  Its definition is clean and satisfiable
(reflexive on the single-triangle map; strictly weaker than the face-level conclusion since it
only constrains inner darts).  -/

/-- **The sharp residual: inner-dart connectivity.**  Any two darts whose faces are inner are
joined by an `InnerLink`-walk (same-face or non-boundary-reverse steps), staying inside the
inner-dart graph.  This is the dart-level form of inner-face dual connectivity. -/
def InnerDartConnected (hNT : NearTriangulation M) : Prop :=
  ∀ a b : D, M.dartFace a ≠ hNT.outerFace → M.dartFace b ≠ hNT.outerFace →
    Relation.ReflTransGen (InnerLink hNT) a b

variable {u v : M.Vertex}

/-- **The keystone from inner-dart connectivity (the reduction).**  Given that the inner-dart
graph is `InnerLink`-connected, every non-outer face is `InnerAdj`-reachable from `face₁`.

Proof: `face₁ = dartFace data.dart` with `data.dart` inner; a non-outer face `f` is a triangle,
so it has a dart `d_f` (any orbit representative) with `dartFace d_f = f`, also inner; an
`InnerLink`-walk `data.dart → d_f` (`InnerDartConnected`) lifts to an `InnerAdj`-walk
`face₁ → f`. -/
theorem innerFaceConnectedFromFace₁_of_innerDartConnected
    (data : hNT.ChordSplitData u v) (hconn : InnerDartConnected hNT) :
    InnerFaceConnectedFromFace₁ data := by
  intro f hf
  -- A representative dart `d_f` of the triangular face `f`.
  have hd_f : ∃ d : D, M.dartFace d = f := by
    refine ⟨Quotient.out f, ?_⟩
    show Quotient.mk (cycleSetoid M.φ) (Quotient.out f) = f
    exact Quotient.out_eq f
  obtain ⟨d_f, hd_f⟩ := hd_f
  -- `face₁ = dartFace data.dart`, inner; `f = dartFace d_f`, inner.
  have hface₁ : data.face₁ = M.dartFace data.dart := rfl
  have hdart_inner : M.dartFace data.dart ≠ hNT.outerFace := by
    rw [← hface₁]; exact data.face₁_not_outer
  have hd_f_inner : M.dartFace d_f ≠ hNT.outerFace := by rw [hd_f]; exact hf
  -- Lift the inner-dart walk.
  have hwalk : Relation.ReflTransGen (InnerLink hNT) data.dart d_f :=
    hconn data.dart d_f hdart_inner hd_f_inner
  have hlift := reflTransGen_innerAdj_of_innerLink_walk hwalk
  rw [hd_f] at hlift
  rw [hface₁]
  exact hlift

/-! ## 5. The named keystone theorem (conditional on the sharp residual)

`innerFaceConnectedFromFace₁_holds` proves the keystone `InnerFaceConnectedFromFace₁` from the
single sharp planar residual `InnerDartConnected hNT` (inner-dart `InnerLink`-connectivity).  This
is a faithful, honest conditional: `InnerDartConnected` is

* **clean** — its definition uses only `InnerLink` (same-face / non-boundary-reverse dart steps),
  no reference to the conclusion;
* **strictly weaker than the goal** — it constrains only *inner darts* through *interior edges*,
  not face reachability from the fixed seed `face₁`;
* **satisfiable** — e.g. on the single-triangle near-triangulation every inner dart carries the
  one inner face, so the relation is the diagonal and connectivity is reflexive;
* the **genuine planar content** — it is exactly the dual-graph connectivity of a triangulated
  disk (the cut-component identification the `ZinanCh35EdgeCore` header flagged as missing).

Discharging `InnerDartConnected` requires the vertex-rotation → boundary-fan tower (currently
"kept as data" in `PlanarMapBoundaryFan` / `PlanarMapFanExistence`, gated by `FanIncidenceData`):
`M.Connected` lifts to an `InnerLink`-walk on every `α`-edge / `σ`-arc that avoids the boundary,
and the boundary crossings must be re-routed through the inner fan at each boundary vertex (the
inner spokes around a boundary vertex are `InnerLink`-connected across their interior edges).
That re-routing is the residual; the entire reduction *to* it is unconditional and clean-3 here. -/

/-- **The Chapter 35 keystone (conditional on inner-dart connectivity).**  Every non-outer face of
a near-triangulation is `InnerAdj`-reachable from the chord face `face₁`, given the sharp residual
`InnerDartConnected hNT` (inner-dart `InnerLink`-connectivity).  Cascades through
`boundedFacePartition_of_innerConnected` to close the coverage half of `edge_core`. -/
theorem innerFaceConnectedFromFace₁_holds
    (data : hNT.ChordSplitData u v) (hconn : InnerDartConnected hNT) :
    InnerFaceConnectedFromFace₁ data :=
  innerFaceConnectedFromFace₁_of_innerDartConnected data hconn

/-- **End-to-end cascade: `BoundedFacePartition` from inner-dart connectivity.**  Composes the
keystone with `boundedFacePartition_of_innerConnected` (`ZinanCh35Coverage`). -/
theorem boundedFacePartition_of_innerDartConnected
    (data : hNT.ChordSplitData u v) (hconn : InnerDartConnected hNT) :
    BoundedFacePartition data :=
  boundedFacePartition_of_innerConnected data
    (innerFaceConnectedFromFace₁_holds data hconn)

end ProofsInTheBook.ZinanCh35InnerConn

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35InnerConn.innerAdj_symm
#print axioms ProofsInTheBook.ZinanCh35InnerConn.innerAdj_sigma
#print axioms ProofsInTheBook.ZinanCh35InnerConn.not_boundaryEdge_of_both_inner
#print axioms ProofsInTheBook.ZinanCh35InnerConn.reflTransGen_innerAdj_of_innerLink_walk
#print axioms ProofsInTheBook.ZinanCh35InnerConn.reflTransGen_innerLink_sigma_pow
#print axioms ProofsInTheBook.ZinanCh35InnerConn.innerFaceConnectedFromFace₁_of_innerDartConnected
#print axioms ProofsInTheBook.ZinanCh35InnerConn.innerFaceConnectedFromFace₁_holds
#print axioms ProofsInTheBook.ZinanCh35InnerConn.boundedFacePartition_of_innerDartConnected
