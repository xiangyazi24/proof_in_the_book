import ProofsInTheBook.PlanarMapFanSurgery

/-!
# Fan connectivity: discharging the `connected` field of the deletion surgery

This file closes the `connected` field of `FanSurgeryReconstruction`
(`PlanarMapFanSurgery.lean`): the assertion that the boundary-vertex deletion
`M.deleteVertex d0` is again connected.

## The reduction (proved here, unconditional)

Connectivity of a `CombMap` is the dart-level statement
`∀ a b, Relation.ReflTransGen dartStep a b`, where
`dartStep a b := σ.SameCycle a b ∨ b = α a`.  Two facts make the deleted map's
step relation transparent:

* `deleteVertex_sigma_sameCycle_iff` : `(deleteVertex).σ.SameCycle x y` iff
  `M.σ.SameCycle x.1 y.1`;
* `deleteVertex_alpha_apply_coe` : `(deleteVertex).α x` has underlying dart
  `M.α x.1`.

Hence for two *surviving* darts `x y`, a deleted-map `dartStep` is exactly an
`M`-`dartStep` between their underlying darts: the deleted-map step relation is
`M.dartStep` restricted to the survivors.  Moreover `α` preserves survival
(`alpha_mem_deleteVertexSet_iff`), so the only way an `M`-`dartStep` can leave the
survivors is a `σ`-step into the deleted star of `v0`; an `α`-step never does.

We package the genuinely fan-geometric residue — that the surviving darts whose
vertices are *neighbours* of `v0` are reconnected among themselves without
passing through `v0` — as the explicit predicate
`DeleteVertexNeighborsConnected`.  This is the fan-path content
`x, z₁, …, z_t, w`: the consecutive fan triangles supply surviving edges
`z_i z_{i+1}` joining all neighbours of `v0`.  We then prove, **unconditionally
and `sorry`-free**, that

```
M.Connected → M.DeleteVertexNeighborsConnected v0 → (M.deleteVertex v0).Connected
```

The predicate `DeleteVertexNeighborsConnected` is satisfiable (it holds for any
real chordless boundary-vertex deletion, e.g. the tetrahedron `t = 1`), so the
reduction is **not vacuous**; it is strictly weaker than the conclusion (it
constrains only the neighbour darts of `v0`, not all surviving darts), so it is
not the goal in disguise.  It is precisely the local fan-reconnection fact that
`PlanarMapDelete.lean`'s `TwoEdgePathObstruction` shows cannot follow from the
`deleteSet` API alone (in the two-edge path the middle vertex's neighbours lose
all darts, so the predicate fails, and connectivity fails with it).
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## The deleted-map step relation is `M.dartStep` restricted to survivors -/

/-- An `α`-step between survivors lifts to the deleted map: if `x` survives then
so does `M.α x.1`, and `(deleteVertex).α x = ⟨M.α x.1, _⟩`. -/
lemma deleteVertex_dartStep_of_alpha (M : CombMap D) (v : D)
    (x : {d : D // d ∉ M.deleteVertexSet v})
    (y : {d : D // d ∉ M.deleteVertexSet v}) (h : y.1 = M.α x.1) :
    (M.deleteVertex v).dartStep x y := by
  right
  apply Subtype.ext
  rw [deleteVertex_alpha_apply_coe]
  exact h

/-- A `σ`-step between survivors lifts to the deleted map. -/
lemma deleteVertex_dartStep_of_sigma (M : CombMap D) (v : D)
    (x y : {d : D // d ∉ M.deleteVertexSet v}) (h : M.σ.SameCycle x.1 y.1) :
    (M.deleteVertex v).dartStep x y := by
  left
  exact (deleteVertex_sigma_sameCycle_iff M v x y).2 h

/-- `α` preserves survival: if `d` survives the star deletion of `v`, so does
`M.α d`. -/
lemma alpha_notMem_deleteVertexSet (M : CombMap D) (v : D) {d : D}
    (hd : d ∉ M.deleteVertexSet v) : M.α d ∉ M.deleteVertexSet v := by
  intro h
  exact hd ((M.alpha_mem_deleteVertexSet_iff v d).1 h)

/-! ## The fan-geometric residue

`DeleteVertexNeighborsConnected M v` asserts that any two surviving darts whose
underlying vertices are neighbours of `v` (i.e. each shares a `σ`-orbit with a
deleted dart) are connected in the deleted map.  This is the local
fan-reconnection fact: the fan path `x, z₁, …, z_t, w` keeps all neighbours of
`v` joined after the star is removed. -/
def DeleteVertexNeighborsConnected (M : CombMap D) (v : D) : Prop :=
  ∀ x y : {d : D // d ∉ M.deleteVertexSet v},
    (∃ e ∈ M.deleteVertexSet v, M.σ.SameCycle e x.1) →
    (∃ e ∈ M.deleteVertexSet v, M.σ.SameCycle e y.1) →
    Relation.ReflTransGen (M.deleteVertex v).dartStep x y

/-! ## Symmetry of the deleted-map step relation -/

/-- The deleted-map step relation is symmetric. -/
lemma deleteVertex_dartStep_symm (M : CombMap D) (v : D)
    {x y : {d : D // d ∉ M.deleteVertexSet v}}
    (h : (M.deleteVertex v).dartStep x y) :
    (M.deleteVertex v).dartStep y x := by
  rcases h with hσ | hα
  · exact Or.inl hσ.symm
  · -- `y = (deleteVertex).α x`, hence `x = (deleteVertex).α y` by involution.
    right
    have := congrArg (M.deleteVertex v).α hα
    rw [(M.deleteVertex v).alpha_alpha] at this
    exact this.symm

/-- The deleted-map reachability relation is symmetric. -/
lemma deleteVertex_reachable_symm (M : CombMap D) (v : D)
    {x y : {d : D // d ∉ M.deleteVertexSet v}}
    (h : Relation.ReflTransGen (M.deleteVertex v).dartStep x y) :
    Relation.ReflTransGen (M.deleteVertex v).dartStep y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih =>
      exact Relation.ReflTransGen.head (deleteVertex_dartStep_symm M v hbc) ih

/-! ## The connectivity reduction

We fix a base survivor `r` and prove that every survivor reaches `r` in the
deleted map, by a single backward induction on an `M`-`dartStep` walk
(`M.Connected`).  The invariant `Inv` records reachability of `r` from any
survivor at the current dart (alive case) and from *every* neighbour-survivor of
`v` (deleted case); the latter is maintained using the fan-geometric predicate
`DeleteVertexNeighborsConnected`. -/

section Reduction

variable (M : CombMap D) (v : D)

/-- Local abbreviation for surviving darts. -/
private abbrev Surv := {d : D // d ∉ M.deleteVertexSet v}

/-- A survivor is a *neighbour-survivor* of `v` if its vertex `σ`-orbit contains a
deleted dart (so its vertex is adjacent to `v`). -/
private def IsNbr (a : Surv M v) : Prop :=
  ∃ e ∈ M.deleteVertexSet v, M.σ.SameCycle e a.1

/-- The connectivity reduction: from `M`-connectivity and the fan-geometric
neighbour-reconnection predicate, the deleted map is connected. -/
theorem deleteVertex_connected_of_neighborsConnected
    (hconn : M.Connected)
    (hnbr : M.DeleteVertexNeighborsConnected v) :
    (M.deleteVertex v).Connected := by
  classical
  set S := M.deleteVertexSet v with hS
  -- It suffices to connect every survivor to a fixed base survivor `r`.
  intro x y
  set Rel : Surv M v → Surv M v → Prop :=
    fun a b => Relation.ReflTransGen (M.deleteVertex v).dartStep a b with hRel
  -- Abbreviation: every neighbour-survivor reaches the base.
  -- The backward-induction invariant on darts of `M`.
  set AllNbrReach : Surv M v → Prop :=
    fun r => ∀ a : Surv M v, IsNbr M v a → Rel a r with hAllNbr
  set Inv : Surv M v → D → Prop :=
    fun r c =>
      (∀ h : c ∉ S, Rel ⟨c, h⟩ r) ∧ (c ∈ S → AllNbrReach r) with hInv
  -- The key: every survivor reaches every base survivor `r`.
  have key : ∀ r : Surv M v, ∀ a : Surv M v, Rel a r := by
    intro r
    -- Base of the induction: `Inv r r.1`.
    have hbase : Inv r r.1 := by
      refine ⟨?_, ?_⟩
      · intro h
        have heq : (⟨r.1, h⟩ : Surv M v) = r := Subtype.ext rfl
        rw [heq]
      · intro hr
        exact absurd hr r.2
    -- Backward closure of `Inv` along `M.dartStep`.
    have hstep : ∀ c c' : D, M.dartStep c c' → Inv r c' → Inv r c := by
      intro c c' hcc' hc'
      refine ⟨?_, ?_⟩
      · -- alive case
        intro hc
        rcases hcc' with hσ | hα
        · -- σ-step `c → c'`
          by_cases hc'S : c' ∈ S
          · -- c' deleted: `⟨c,hc⟩` is a neighbour-survivor, use `Inv c'`'s nbr-clause.
            have hnbr_c : IsNbr M v ⟨c, hc⟩ := ⟨c', hc'S, hσ.symm⟩
            exact hc'.2 hc'S ⟨c, hc⟩ hnbr_c
          · -- c' alive: σ-step lifts, then `Inv c'`.
            have hreach : Rel ⟨c', hc'S⟩ r := hc'.1 hc'S
            have hd : (M.deleteVertex v).dartStep ⟨c, hc⟩ ⟨c', hc'S⟩ :=
              deleteVertex_dartStep_of_sigma M v ⟨c, hc⟩ ⟨c', hc'S⟩ hσ
            exact Relation.ReflTransGen.head hd hreach
        · -- α-step `c' = α c`; α preserves survival.
          have hc'S : c' ∉ S := by
            rw [hα]; exact alpha_notMem_deleteVertexSet M v hc
          have hreach : Rel ⟨c', hc'S⟩ r := hc'.1 hc'S
          have hd : (M.deleteVertex v).dartStep ⟨c, hc⟩ ⟨c', hc'S⟩ :=
            deleteVertex_dartStep_of_alpha M v ⟨c, hc⟩ ⟨c', hc'S⟩ hα
          exact Relation.ReflTransGen.head hd hreach
      · -- deleted case: maintain `AllNbrReach`.
        intro hcS
        rcases hcc' with hσ | hα
        · by_cases hc'S : c' ∈ S
          · exact hc'.2 hc'S
          · -- c' alive and is itself a neighbour-survivor; bridge all neighbours via `hnbr`.
            intro a ha
            have hreach_c' : Rel ⟨c', hc'S⟩ r := hc'.1 hc'S
            have hnbr_c' : IsNbr M v ⟨c', hc'S⟩ := ⟨c, hcS, hσ⟩
            have hbridge :
                Relation.ReflTransGen (M.deleteVertex v).dartStep a ⟨c', hc'S⟩ :=
              hnbr a ⟨c', hc'S⟩ ha hnbr_c'
            exact hbridge.trans hreach_c'
        · -- α-step `c' = α c`; `c' ∈ S` since `c ∈ S`.
          have hc'S : c' ∈ S := by
            rw [hα]
            exact (M.alpha_mem_deleteVertexSet_iff v c).2 hcS
          exact hc'.2 hc'S
    -- Run the backward induction over an `M`-walk from `a` to `r`.
    intro a
    have hwalk : Relation.ReflTransGen M.dartStep a.1 r.1 := hconn a.1 r.1
    have hInva : Inv r a.1 :=
      Relation.ReflTransGen.head_induction_on hwalk hbase
        (fun {b c} hbc _ ih => hstep b c hbc ih)
    have hfin : Rel (⟨a.1, a.2⟩ : Surv M v) r := hInva.1 a.2
    have heq : (⟨a.1, a.2⟩ : Surv M v) = a := Subtype.ext rfl
    rwa [heq] at hfin
  -- Conclude: every survivor reaches every base survivor, so `x` reaches `y`.
  exact key y x

end Reduction

/-! ## Discharging the neighbour-reconnection predicate from the fan

We now prove `DeleteVertexNeighborsConnected` itself from the boundary fan: the
consecutive fan triangles supply surviving edges `z_i z_{i+1}` that join all
neighbours of `v0` without passing through `v0`, so every neighbour-survivor is
reconnected. -/

namespace NearTriangulation

variable {M : CombMap D}

/-- A dart survives the star deletion of `v` iff neither it nor its reverse lies
in the `σ`-orbit of `v`. -/
private lemma notMem_deleteVertexSet_iff (v d : D) :
    d ∉ M.deleteVertexSet v ↔
      ¬ M.σ.SameCycle v d ∧ ¬ M.σ.SameCycle v (M.α d) := by
  rw [mem_deleteVertexSet_iff]
  simp only [mem_vertexDarts, not_or]

/-- A dart whose tail and head are both different from the vertex of `v` (as
`σ`-orbits) survives the star deletion. -/
private lemma notMem_deleteVertexSet_of_tail_head_ne {v d : D}
    (htail : M.tail d ≠ M.tail v) (hhead : M.head d ≠ M.tail v) :
    d ∉ M.deleteVertexSet v := by
  rw [notMem_deleteVertexSet_iff]
  refine ⟨?_, ?_⟩
  · intro h
    exact htail (Quotient.sound h).symm
  · intro h
    exact hhead (Quotient.sound h).symm

/-- One deleted-map reachability step from a `σ`-cycle relation between
survivors. -/
private lemma rel_of_sigma {v : D} (x y : {d : D // d ∉ M.deleteVertexSet v})
    (h : M.σ.SameCycle x.1 y.1) :
    Relation.ReflTransGen (M.deleteVertex v).dartStep x y :=
  Relation.ReflTransGen.single (deleteVertex_dartStep_of_sigma M v x y h)

/-- One deleted-map reachability step from `y = M.α x` between survivors. -/
private lemma rel_of_alpha {v : D} (x y : {d : D // d ∉ M.deleteVertexSet v})
    (h : y.1 = M.α x.1) :
    Relation.ReflTransGen (M.deleteVertex v).dartStep x y :=
  Relation.ReflTransGen.single (deleteVertex_dartStep_of_alpha M v x y h)

variable {hNT : NearTriangulation M} {v0 : M.Vertex}

/-- The "edge dart" of a fan triangle `(v0, a, b)`: its middle dart `d1` has tail
`a` and head `b`, and survives the deletion of any dart `d0` representing `v0`. -/
private lemma fanTriangle_edge_dart_survives {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d1 ∉ M.deleteVertexSet d0 := by
  have hdist := T.vertices_pairwiseDistinct
  -- tail T.d1 = a ≠ v0 = tail d0
  have htail : M.tail T.d1 ≠ M.tail d0 := by
    rw [T.tail1, htail0]
    exact (hdist.1).symm
  -- head T.d1 = b ≠ v0 = tail d0
  have hhead_eq : M.head T.d1 = b := by
    have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
    have hh : M.head T.d1 = M.tail T.d2 := by
      rw [← tail_phi, hphi]
    rw [hh, T.tail2]
  have hhead : M.head T.d1 ≠ M.tail d0 := by
    rw [hhead_eq, htail0]
    exact hdist.2.2
  exact notMem_deleteVertexSet_of_tail_head_ne htail hhead

/-- For a fan triangle `(v0, a, b)`, any surviving dart whose vertex is `a` is
deleted-map connected to any surviving dart whose vertex is `b`, via the
surviving triangle edge `a—b`. -/
private lemma fanTriangle_connects {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0)
    (p q : {d : D // d ∉ M.deleteVertexSet d0})
    (hp : M.tail p.1 = a) (hq : M.tail q.1 = b) :
    Relation.ReflTransGen (M.deleteVertex d0).dartStep p q := by
  -- The surviving edge dart `T.d1` (tail a, head b) and its reverse.
  have hd1 : T.d1 ∉ M.deleteVertexSet d0 :=
    fanTriangle_edge_dart_survives T htail0
  have hd1' : M.α T.d1 ∉ M.deleteVertexSet d0 :=
    alpha_notMem_deleteVertexSet M d0 hd1
  set e1 : {d : D // d ∉ M.deleteVertexSet d0} := ⟨T.d1, hd1⟩ with he1
  set e1' : {d : D // d ∉ M.deleteVertexSet d0} := ⟨M.α T.d1, hd1'⟩ with he1'
  -- p ↝ e1 (same vertex a)
  have hpe1 : M.σ.SameCycle p.1 T.d1 :=
    Quotient.exact (show M.tail p.1 = M.tail T.d1 by rw [hp, T.tail1])
  have step1 : Relation.ReflTransGen (M.deleteVertex d0).dartStep p e1 :=
    rel_of_sigma p e1 hpe1
  -- e1 ↝ e1' (edge step)
  have step2 : Relation.ReflTransGen (M.deleteVertex d0).dartStep e1 e1' :=
    rel_of_alpha e1 e1' rfl
  -- e1' ↝ q (same vertex b: tail (α T.d1) = head T.d1 = b)
  have hhead_eq : M.head T.d1 = b := by
    have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
    have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
    rw [hh, T.tail2]
  have he1'q : M.σ.SameCycle (M.α T.d1) q.1 :=
    Quotient.exact (show M.tail (M.α T.d1) = M.tail q.1 by rw [tail_alpha, hhead_eq, hq])
  have step3 : Relation.ReflTransGen (M.deleteVertex d0).dartStep e1' q :=
    rel_of_sigma e1' q he1'q
  exact (step1.trans step2).trans step3

/-- `consecutivePairs` of a two-or-more element list. -/
private lemma consecutivePairs_cons_cons {α : Type*} (a b : α) (l : List α) :
    consecutivePairs (a :: b :: l) = (a, b) :: consecutivePairs (b :: l) := by
  simp [consecutivePairs]

/-- Symmetric "all survivors at `a` connect to all survivors at `b`" relation. -/
private def VConn {d0 : D} (a b : M.Vertex) : Prop :=
  ∀ p q : {d : D // d ∉ M.deleteVertexSet d0},
    M.tail p.1 = a → M.tail q.1 = b →
    Relation.ReflTransGen (M.deleteVertex d0).dartStep p q

private lemma VConn.symm {d0 : D} {a b : M.Vertex} (h : VConn (M := M) (d0 := d0) a b) :
    VConn (M := M) (d0 := d0) b a := by
  intro p q hp hq
  exact deleteVertex_reachable_symm M d0 (h q p hq hp)

/-- A `FanTriangle` provides `VConn` between its two non-`v0` vertices, and a
surviving witness dart at each. -/
private lemma fanTriangle_vconn {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    VConn (M := M) (d0 := d0) a b :=
  fun p q hp hq => fanTriangle_connects T htail0 p q hp hq

/-- A `FanTriangle` provides a surviving dart whose vertex is its second
non-`v0` vertex `b` (the reverse `α T.d1` of the surviving edge dart). -/
private lemma fanTriangle_witness_snd {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = b := by
  have hd1 : T.d1 ∉ M.deleteVertexSet d0 := fanTriangle_edge_dart_survives T htail0
  have hd1' : M.α T.d1 ∉ M.deleteVertexSet d0 := alpha_notMem_deleteVertexSet M d0 hd1
  refine ⟨⟨M.α T.d1, hd1'⟩, ?_⟩
  have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
  have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
  show M.tail (M.α T.d1) = b
  rw [tail_alpha, hh, T.tail2]

/-- A `FanTriangle` provides a surviving dart whose vertex is its first non-`v0`
vertex `a` (the surviving edge dart `T.d1` itself, tail `a`). -/
private lemma fanTriangle_witness_fst {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = a :=
  ⟨⟨T.d1, fanTriangle_edge_dart_survives T htail0⟩, T.tail1⟩

/-- Chaining: if consecutive pairs of a list `L` (with at least the head vertex
present) all carry fan triangles in the **σ-predecessor** orientation
(`(a, b) ↦ FanTriangle v0 b a`, the fixed `triangle_of_pair` convention), then every
vertex of `L` is `VConn` to the head of `L`.  Proved by induction maintaining a
surviving witness at the head; `VConn` is symmetric so the orientation is immaterial. -/
private lemma vconn_head_of_pairs {d0 : D} (htail0 : M.tail d0 = v0) :
    ∀ (L : List M.Vertex) (hd : M.Vertex),
      (∀ a b : M.Vertex, (a, b) ∈ consecutivePairs (hd :: L) →
        FanTriangle hNT v0 b a) →
      ∀ u : M.Vertex, u ∈ (hd :: L) → VConn (M := M) (d0 := d0) u hd := by
  intro L
  induction L with
  | nil =>
      intro hd _ u hu
      have hueq : u = hd := by simpa using hu
      subst hueq
      intro p q hp hq
      exact rel_of_sigma p q
        (Quotient.exact (show M.tail p.1 = M.tail q.1 by rw [hp, hq]))
  | cons b l ih =>
      intro hd htri u hu
      -- The first pair `(hd, b)` carries a (predecessor-oriented) fan triangle.
      have hpair0 : (hd, b) ∈ consecutivePairs (hd :: b :: l) := by
        rw [consecutivePairs_cons_cons]; exact List.mem_cons.mpr (Or.inl rfl)
      have T0 : FanTriangle hNT v0 b hd := htri hd b hpair0
      have hVhd_b : VConn (M := M) (d0 := d0) hd b := (fanTriangle_vconn T0 htail0).symm
      -- triangles for the tail list `b :: l`.
      have htri' : ∀ a c : M.Vertex, (a, c) ∈ consecutivePairs (b :: l) →
          FanTriangle hNT v0 c a := by
        intro a c hac
        apply htri a c
        rw [consecutivePairs_cons_cons]
        exact List.mem_cons.mpr (Or.inr hac)
      have ihrun := ih b htri'
      rcases List.mem_cons.mp hu with hueq | hurest
      · -- u = hd: reflexive `VConn`.
        subst hueq
        intro p q hp hq
        exact rel_of_sigma p q
          (Quotient.exact (show M.tail p.1 = M.tail q.1 by rw [hp, hq]))
      · -- u ∈ b :: l: connect u → b (by IH) then b → hd (by T0).
        have hVu_b : VConn (M := M) (d0 := d0) u b := ihrun u hurest
        intro p q hp hq
        -- need a witness at `b` (the first label of the swapped triangle `T0`).
        obtain ⟨m, hm⟩ : ∃ m : {d : D // d ∉ M.deleteVertexSet d0}, M.tail m.1 = b :=
          fanTriangle_witness_fst T0 htail0
        have h1 : Relation.ReflTransGen (M.deleteVertex d0).dartStep p m :=
          hVu_b p m hp hm
        have h2 : Relation.ReflTransGen (M.deleteVertex d0).dartStep m q :=
          (hVhd_b.symm) m q hm hq
        exact h1.trans h2

/-- The vertex of a neighbour-survivor of `v0` lies on the fan path. -/
private lemma neighbor_tail_mem_path (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) {x : {d : D // d ∉ M.deleteVertexSet d0}}
    (hx : ∃ e ∈ M.deleteVertexSet d0, M.σ.SameCycle e x.1) :
    M.tail x.1 ∈ fan.path := by
  obtain ⟨e, heS, hex⟩ := hx
  -- `e ∈ vertexDarts d0` would force `x` into the deleted star.
  rw [mem_deleteVertexSet_iff] at heS
  rcases heS with he | hαe
  · exfalso
    rw [mem_vertexDarts] at he
    -- tail x = v0 ⟹ x deleted
    have : M.σ.SameCycle d0 x.1 := he.trans hex
    exact x.2 ((mem_deleteVertexSet_iff M d0 x.1).2 (Or.inl ((mem_vertexDarts M d0 x.1).2 this)))
  · -- `α e` is a rotation dart; its head is a neighbour, equal to `tail x`.
    rw [mem_vertexDarts] at hαe
    have hαe_mem : M.α e ∈ fan.rotation_order.darts := by
      have heq : M.vertexDarts d0 = fan.rotation_order.darts.toFinset :=
        fan.rotation_order.vertexDarts_eq htail0
      have : M.α e ∈ M.vertexDarts d0 := (mem_vertexDarts M d0 (M.α e)).2 hαe
      rw [heq, List.mem_toFinset] at this
      exact this
    -- tail x = tail e = head (α e)
    have htx : M.tail x.1 = M.head (M.α e) := by
      have h1 : M.tail x.1 = M.tail e := (Quotient.sound hex).symm
      rw [h1, head_alpha]
    -- head (α e) ∈ neighbors = fan.path
    have hmem : M.head (M.α e) ∈ fan.rotation_order.darts.map M.head :=
      List.mem_map_of_mem hαe_mem
    rw [fan.rotation_order.heads_eq] at hmem
    rw [htx, BoundaryVertexFan.path]
    exact hmem

/-- **The fan discharges `DeleteVertexNeighborsConnected`.**  Given a boundary
fan at `v0` and any dart `d0` representing `v0`, the neighbour-survivors of `v0`
are reconnected in the deleted map via the fan path. -/
theorem deleteVertex_neighborsConnected_of_fan (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    M.DeleteVertexNeighborsConnected d0 := by
  -- Every neighbour-survivor is `VConn` to the fan head `fan.x`.
  set L : List M.Vertex := fan.interior ++ [fan.w] with hL
  have hpath : fan.path = fan.x :: L := by
    rw [BoundaryVertexFan.path, fanPath, hL, List.cons_append]
  have htri : ∀ a b : M.Vertex,
      (a, b) ∈ consecutivePairs (fan.x :: L) → FanTriangle hNT v0 b a := by
    intro a b hab
    have hab' : (a, b) ∈ consecutivePairs fan.path := by rw [hpath]; exact hab
    exact fan.incident_faces_exact.triangle_of_pair (by
      simpa [BoundaryVertexFan.path] using hab')
  have hhead : ∀ u : M.Vertex, u ∈ fan.path →
      VConn (M := M) (d0 := d0) u fan.x := by
    intro u hu
    have hu' : u ∈ fan.x :: L := by rw [← hpath]; exact hu
    exact vconn_head_of_pairs htail0 L fan.x htri u hu'
  -- Assemble: two neighbour-survivors both connect to `fan.x`.
  intro x y hx hy
  have hxpath : M.tail x.1 ∈ fan.path := neighbor_tail_mem_path fan htail0 hx
  have hypath : M.tail y.1 ∈ fan.path := neighbor_tail_mem_path fan htail0 hy
  have hVx : VConn (M := M) (d0 := d0) (M.tail x.1) fan.x := hhead _ hxpath
  have hVy : VConn (M := M) (d0 := d0) (M.tail y.1) fan.x := hhead _ hypath
  -- a witness survivor at `fan.x`: the pair `(fan.x, _)` triangle, if it exists,
  -- else `x` itself routes through.  We use the head triangle witness.
  -- Connect x → fan.x → y.
  -- Need a witness at fan.x.  `fan.x` is the head of the path of length ≥ 2.
  obtain ⟨b, _l, hLb⟩ : ∃ b l', L = b :: l' := by
    rw [hL]
    cases fan.interior with
    | nil => exact ⟨fan.w, [], rfl⟩
    | cons c t => exact ⟨c, t ++ [fan.w], rfl⟩
  have hpair0 : (fan.x, b) ∈ consecutivePairs (fan.x :: L) := by
    rw [hLb, consecutivePairs_cons_cons]; exact List.mem_cons.mpr (Or.inl rfl)
  have T0 : FanTriangle hNT v0 b fan.x := htri fan.x b hpair0
  obtain ⟨m, hm⟩ : ∃ m : {d : D // d ∉ M.deleteVertexSet d0}, M.tail m.1 = fan.x :=
    fanTriangle_witness_snd T0 htail0
  have h1 : Relation.ReflTransGen (M.deleteVertex d0).dartStep x m :=
    hVx x m rfl hm
  have h2 : Relation.ReflTransGen (M.deleteVertex d0).dartStep m y :=
    (hVy.symm) m y hm rfl
  exact h1.trans h2

/-- **The deleted map is connected (fan form).**  Deleting the closed star of a
boundary vertex `v0` of a near-triangulation, where `d0` is a dart representing
`v0` and `fan` is a boundary fan at `v0`, leaves a connected combinatorial map.
The two boundary neighbours of `v0` and all interior fan vertices stay joined
through the surviving fan path `x, z₁, …, z_t, w`.

This discharges the `connected` field of `FanSurgeryReconstruction`
unconditionally from the fan and the near-triangulation invariant. -/
theorem deleteVertex_connected_of_fan (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) :
    (M.deleteVertex d0).Connected :=
  deleteVertex_connected_of_neighborsConnected M d0 hNT.sphere.1
    (deleteVertex_neighborsConnected_of_fan fan htail0)

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
