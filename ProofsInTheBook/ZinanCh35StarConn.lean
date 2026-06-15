import ProofsInTheBook.ZinanCh35EdgeCore

/-!
# Chapter 35: `SideRegionInterChordEnds` via local σ-star connectivity (UNCONDITIONAL)

This file discharges the `SideRegionInterChordEnds` residual of `ZinanCh35EdgeCore.lean`
**unconditionally** (clean-3), via local σ-star connectivity in the `ChordSplitAdj` relation —
NOT the fan tower, NOT the `StarFanOneSide` residual.

## The route (ChatGPT Pro R6 blueprint, `HANDOFF/ch35-residual-collapse-R6.md` §1)

`SideRegionInterChordEnds data` says: a vertex `w` lying in *both* side regions is a chord
endpoint (`w = u ∨ w = v`).  The proof is by contradiction:

1. **Extraction.**  `w ∈ sideRegion₁ data` gives a dart `d₁` with `tail d₁ = w` and
   `dartFace d₁ ∈ side₁` (non-outer).  Likewise `w ∈ sideRegion₂` gives `d₂` with
   `tail d₂ = w`, `dartFace d₂ ∈ side₂`.  (When the witnessing kept dart is an *outer-arc*
   dart, its `σ`-rotate carries the side face at `w`, using `dartFace (σ z) = dartFace (α z)`.)

2. **σ-star connectivity.**  `tail d₁ = tail d₂ = w` means `σ.SameCycle d₁ d₂`.  For
   `w ≠ u, v`, the two incident non-outer faces are `ChordSplitAdj`-connected
   (`incident_faces_same_component_of_not_chordEnd`).

3. **Contradiction with `Separates`.**  `dartFace d₁ ∈ side₁`, `dartFace d₂ ∈ side₂`, and
   `dartFace d₁ ~* dartFace d₂`, so by reachability symmetry `face₂ ∈ side₁`, contradicting
   `Separates = face₂ ∉ side₁`.

## Generic star engine

`FaceAdjAvoiding`, `sigma_step_faceAdjAvoiding`, `star_connected_avoiding`: a one-step face
adjacency that crosses a single dart whose edge is not `Forbidden`, and its σ-orbit closure.
Instantiating `Forbidden e := IsBoundaryEdge e ∨ e = s(u,v)` recovers `ChordSplitAdj`.

No `sorry` / `axiom` / `admit` / `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace ProofsInTheBook.ZinanCh35StarConn

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.CombMap
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation
open ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.ChordSplitData
open ProofsInTheBook.ChordReconClose
open ProofsInTheBook.ZinanCh35EdgeCore

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {M : CombMap D}
  {hNT : NearTriangulation M} {u v : M.Vertex}

/-! ## 0. Basic dart-rotation identities -/

/-- `dartFace (σ x) = dartFace (α x)`: because `φ (α x) = σ x` and `dartFace` is `φ`-invariant. -/
lemma dartFace_sigma_eq_alpha (x : D) :
    M.dartFace (M.σ x) = M.dartFace (M.α x) := by
  have hφ : M.φ (M.α x) = M.σ x := by
    show (M.σ * M.α) (M.α x) = M.σ x
    simp [Equiv.Perm.coe_mul, Function.comp_apply, M.alpha_alpha]
  calc M.dartFace (M.σ x) = M.dartFace (M.φ (M.α x)) := by rw [hφ]
    _ = M.dartFace (M.α x) := M.dartFace_phi _

/-- `σ.SameCycle a b` is exactly `tail a = tail b`. -/
lemma sigma_sameCycle_iff_tail (a b : D) :
    M.σ.SameCycle a b ↔ M.tail a = M.tail b := by
  show M.σ.SameCycle a b ↔
    (Quotient.mk (cycleSetoid M.σ) a : Quotient (cycleSetoid M.σ)) = Quotient.mk _ b
  rw [Quotient.eq]
  rfl

/-! ## 1. The generic forbidden-edge-avoiding face adjacency -/

/-- Two faces are adjacent *avoiding* a forbidden edge predicate when they share a dart whose
edge is not forbidden.  Instantiating `Forbidden e := IsBoundaryEdge e ∨ e = s(u,v)` gives
`ChordSplitAdj`. -/
def FaceAdjAvoiding (M : CombMap D) (Forbidden : Sym2 M.Vertex → Prop) (f g : M.Face) : Prop :=
  ∃ d : D, M.dartFace d = f ∧ M.dartFace (M.α d) = g ∧ ¬ Forbidden (M.dartEdge d)

/-- **One σ-step.**  If `dartEdge x` is not forbidden, then `dartFace x` and `dartFace (σ x)`
are `FaceAdjAvoiding`-adjacent (witness `x`, using `dartFace (α x) = dartFace (σ x)`). -/
lemma sigma_step_faceAdjAvoiding {Forbidden : Sym2 M.Vertex → Prop} {x : D}
    (hx : ¬ Forbidden (M.dartEdge x)) :
    FaceAdjAvoiding M Forbidden (M.dartFace x) (M.dartFace (M.σ x)) :=
  ⟨x, rfl, (dartFace_sigma_eq_alpha x).symm, hx⟩

/-- **σ-orbit connectivity, no-forbidden version.**  If `x` and `y` are in the same σ-cycle and
*every* dart in that σ-cycle has a non-forbidden edge, then `dartFace x` reaches `dartFace y`
through `FaceAdjAvoiding`.  (Induction on the σ-power connecting `x` to `y`.) -/
lemma star_connected_avoiding {Forbidden : Sym2 M.Vertex → Prop} {x y : D}
    (hσ : M.σ.SameCycle x y)
    (havoid : ∀ z, M.σ.SameCycle x z → ¬ Forbidden (M.dartEdge z)) :
    Relation.ReflTransGen (FaceAdjAvoiding M Forbidden) (M.dartFace x) (M.dartFace y) := by
  obtain ⟨i, hi⟩ := hσ.exists_nat_pow_eq
  -- prove a powered version by induction on `i`, then rewrite `y`.
  subst hi
  clear hσ
  induction i with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ k ih =>
    -- `σ^(k+1) x = σ (σ^k x)`.
    have hstep : (M.σ ^ (k + 1)) x = M.σ ((M.σ ^ k) x) := by
      rw [pow_succ']; rfl
    rw [hstep]
    refine ih.tail ?_
    -- one step from `dartFace (σ^k x)` to `dartFace (σ (σ^k x))`.
    have hsc : M.σ.SameCycle x ((M.σ ^ k) x) := ⟨k, by rw [zpow_natCast]⟩
    exact sigma_step_faceAdjAvoiding (havoid _ hsc)

/-! ## 2. `FaceAdjAvoiding` with the chord-split forbidden set IS `ChordSplitAdj` -/

/-- The chord-split forbidden-edge predicate. -/
def ChordForbidden (hNT : NearTriangulation M) (u v : M.Vertex) (e : Sym2 M.Vertex) : Prop :=
  hNT.outerCycle.IsBoundaryEdge e ∨ e = s(u, v)

/-- `FaceAdjAvoiding` with `ChordForbidden` is definitionally `ChordSplitAdj`. -/
lemma faceAdjAvoiding_chordForbidden_iff {f g : M.Face} :
    FaceAdjAvoiding M (ChordForbidden hNT u v) f g ↔ hNT.ChordSplitAdj u v f g := by
  constructor
  · rintro ⟨d, hdf, hdg, hF⟩
    exact ⟨d, hdf, hdg, fun hb => hF (Or.inl hb), fun hc => hF (Or.inr hc)⟩
  · rintro ⟨d, hdf, hdg, hbe, hch⟩
    refine ⟨d, hdf, hdg, ?_⟩
    rintro (hb | hc)
    · exact hbe hb
    · exact hch hc

/-- Transport a `FaceAdjAvoiding (ChordForbidden …)` reachability into `ChordSplitAdj`
reachability. -/
lemma reflTransGen_chordSplitAdj_of_avoiding {f g : M.Face}
    (h : Relation.ReflTransGen (FaceAdjAvoiding M (ChordForbidden hNT u v)) f g) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) f g := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (faceAdjAvoiding_chordForbidden_iff.mp hstep)

/-! ## 3. Extraction: a side-region vertex carries an incident side face

`w ∈ sideRegion₁` gives a kept dart `d` (`d ∈ keptSet₁ = (sideDarts₁ ∪ outerArc₁) \ {dart}`) with
`tail d = w`.  If `d ∈ sideDarts₁` its own face is in `side₁` (incident to `w` via `d`).  If
`d ∈ outerArc₁` then `dartFace (α d) ∈ side₁`; using `dartFace (σ d) = dartFace (α d)` and
`tail (σ d) = w`, the dart `σ d` is an incident witness for that side-1 face at `w`. -/

/-- **Side-1 extraction.**  A vertex in `sideRegion₁` is the tail of a dart whose face is in
`side₁`. -/
theorem incident_side₁_of_mem_sideRegion₁ (data : hNT.ChordSplitData u v)
    {w : M.Vertex} (hw : w ∈ sideRegion₁ data) :
    ∃ d : D, M.tail d = w ∧ M.dartFace d ∈ data.side₁ := by
  obtain ⟨d, hd, htail⟩ := hw
  -- `d ∈ keptSet₁`.
  have hkept : d ∈ data.keptSet₁ := (data.mem_keptDel₁_iff d).1 hd
  obtain ⟨hU, _⟩ := hkept
  rcases hU with hin | hout
  · -- `d ∈ sideDarts₁`: `dartFace d ∈ side₁`, tail `d = w`.
    exact ⟨d, htail, hin⟩
  · -- `d ∈ outerArc₁`: face of `σ d = α-face ∈ side₁`, tail `σ d = w`.
    obtain ⟨_houter, hαside⟩ := hout
    refine ⟨M.σ d, ?_, ?_⟩
    · rw [M.tail_sigma]; exact htail
    · rw [dartFace_sigma_eq_alpha]; exact hαside

/-- **Side-2 extraction.**  A vertex in `sideRegion₂` is the tail of a dart whose face is in
`side₂`. -/
theorem incident_side₂_of_mem_sideRegion₂ (data : hNT.ChordSplitData u v)
    {w : M.Vertex} (hw : w ∈ sideRegion₂ data) :
    ∃ d : D, M.tail d = w ∧ M.dartFace d ∈ data.side₂ := by
  obtain ⟨d, hd, htail⟩ := hw
  have hkept : d ∈ data.keptSet₂ := (data.mem_keptDel₂_iff d).1 hd
  obtain ⟨hU, _⟩ := hkept
  rcases hU with hin | hout
  · exact ⟨d, htail, hin⟩
  · obtain ⟨_houter, hαside⟩ := hout
    refine ⟨M.σ d, ?_, ?_⟩
    · rw [M.tail_sigma]; exact htail
    · rw [dartFace_sigma_eq_alpha]; exact hαside

/-! ## 4'. The non-outer σ-step is a `ChordSplitAdj` step (away from chord ends)

The pivotal local fact.  A σ-step `z → σ z` at a vertex `w = tail z ∉ {u, v}` is a valid
`ChordSplitAdj` step **whenever both `dartFace z` and `dartFace (σ z)` are non-outer**.  The
chord edge is never incident to `w` (`w ≠ u, v`); and a boundary edge at `z` would force one of
`dartFace z`, `dartFace (α z) = dartFace (σ z)` to be the outer face. -/

/-- A dart whose tail is not a chord endpoint does not carry the chord edge. -/
lemma dartEdge_ne_chord_of_tail_ne (data : hNT.ChordSplitData u v) {z : D}
    (htail : M.tail z = u → False) (htail' : M.tail z = v → False) :
    M.dartEdge z ≠ s(u, v) := by
  intro hz
  -- `dartEdge z = s(tail z, head z) = s(u, v)`, so `tail z ∈ {u, v}`.
  have hmem : M.tail z ∈ (s(u, v) : Sym2 M.Vertex) := by
    rw [← hz]; exact Sym2.mem_mk_left _ _
  rcases Sym2.mem_iff.1 hmem with h | h
  · exact htail h
  · exact htail' h

/-- **The non-outer σ-step.**  If `tail z ≠ u, v` and both `dartFace z`, `dartFace (σ z)` are
non-outer, then `ChordSplitAdj (dartFace z) (dartFace (σ z))`. -/
lemma chordSplitAdj_sigma_step_of_nonouter (data : hNT.ChordSplitData u v) {z : D}
    (hzu : M.tail z ≠ u) (hzv : M.tail z ≠ v)
    (hz : M.dartFace z ≠ hNT.outerFace) (hσz : M.dartFace (M.σ z) ≠ hNT.outerFace) :
    hNT.ChordSplitAdj u v (M.dartFace z) (M.dartFace (M.σ z)) := by
  refine ⟨z, rfl, (dartFace_sigma_eq_alpha z).symm, ?_, ?_⟩
  · -- non-boundary: a boundary edge would force `z` or `α z` onto the outer face.
    intro hbe
    rcases data.boundaryEdge_dart_outer hbe with h | h
    · exact hz h
    · exact hσz (by rw [dartFace_sigma_eq_alpha]; exact h)
  · exact dartEdge_ne_chord_of_tail_ne data hzu hzv

/-! ## 4''. The interior case

If `w` is not a boundary vertex, then *no* dart at `w` is on the outer face (an outer dart's
tail is a boundary vertex), so every σ-step in `w`'s star is a valid `ChordSplitAdj` step and
the two incident faces are connected by `star_connected_avoiding`. -/

/-- An outer-face dart's tail is a boundary vertex. -/
lemma isBoundaryVertex_tail_of_outer {z : D} (hz : M.dartFace z = hNT.outerFace) :
    hNT.outerCycle.IsBoundaryVertex (M.tail z) := by
  have hmem : z ∈ hNT.outerCycle.darts := (hNT.outerCycle.mem_darts_iff z).2 hz
  show M.tail z ∈ hNT.outerCycle.vertices
  rw [hNT.outerCycle.vertices_eq]
  exact List.mem_map_of_mem hmem

/-- **Interior star connectivity.**  At a non-boundary vertex `w ≠ u, v`, all incident faces are
non-outer and pairwise `ChordSplitAdj`-connected. -/
theorem interior_star_nonouter_connected (data : hNT.ChordSplitData u v)
    {w : M.Vertex} (hw_not_boundary : ¬ hNT.outerCycle.IsBoundaryVertex w)
    (hwu : w ≠ u) (hwv : w ≠ v) {d₁ d₂ : D}
    (h₁tail : M.tail d₁ = w) (h₂tail : M.tail d₂ = w) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) (M.dartFace d₁) (M.dartFace d₂) := by
  -- `σ.SameCycle d₁ d₂` from equal tails.
  have hσ : M.σ.SameCycle d₁ d₂ := (sigma_sameCycle_iff_tail d₁ d₂).2 (h₁tail.trans h₂tail.symm)
  -- every dart `z` σ-same-cycle with `d₁` has tail `w` (non-outer face, non-forbidden edge).
  have hconn :
      Relation.ReflTransGen (FaceAdjAvoiding M (ChordForbidden hNT u v))
        (M.dartFace d₁) (M.dartFace d₂) := by
    refine star_connected_avoiding hσ ?_
    intro z hz
    -- `tail z = w`.
    have hzw : M.tail z = w := by
      have := (sigma_sameCycle_iff_tail d₁ z).1 hz
      rw [← this]; exact h₁tail
    -- `z` is not on the outer face (else `w` boundary).
    have hzouter : M.dartFace z ≠ hNT.outerFace := by
      intro h; exact hw_not_boundary (hzw ▸ isBoundaryVertex_tail_of_outer h)
    -- and neither is `σ z` (its tail is also `w`).
    have hσzouter : M.dartFace (M.σ z) ≠ hNT.outerFace := by
      intro h
      have : M.tail (M.σ z) = w := by rw [M.tail_sigma]; exact hzw
      exact hw_not_boundary (this ▸ isBoundaryVertex_tail_of_outer h)
    -- forbidden = boundary ∨ chord; both excluded.
    rintro (hbe | hch)
    · rcases data.boundaryEdge_dart_outer hbe with h | h
      · exact hzouter h
      · exact hσzouter (by rw [dartFace_sigma_eq_alpha]; exact h)
    · exact dartEdge_ne_chord_of_tail_ne data (fun h => hwu (hzw ▸ h))
        (fun h => hwv (hzw ▸ h)) hch
  exact reflTransGen_chordSplitAdj_of_avoiding hconn

/-! ## 4'''. The boundary case

At a boundary vertex `w` (appearing once on the cycle by `VertexNodup`), there is a **unique**
outer-face dart `b` with `tail b = w`.  Every other dart at `w` is non-outer.  Anchoring at
`σ b`, every non-outer dart at `w` is `ChordSplitAdj`-reachable from `dartFace (σ b)`, walking
σ-forward through the contiguous non-outer arc (which never crosses `b`).  Two non-outer darts at
`w` are then connected through the anchor. -/

/-- **Uniqueness of the outer dart at a vertex.**  Two outer-face darts with the same tail are
equal (the boundary vertex list is `Nodup`). -/
lemma outer_dart_unique {z₁ z₂ : D}
    (h₁ : M.dartFace z₁ = hNT.outerFace) (h₂ : M.dartFace z₂ = hNT.outerFace)
    (ht : M.tail z₁ = M.tail z₂) : z₁ = z₂ :=
  hNT.outerCycle.tail_injective_on_darts hNT.outer_simple
    ((hNT.outerCycle.mem_darts_iff z₁).2 h₁) ((hNT.outerCycle.mem_darts_iff z₂).2 h₂) ht

/-- A dart sharing `b`'s tail but distinct from the outer dart `b` is non-outer. -/
lemma nonouter_of_ne_outer {b z : D} (hb : M.dartFace b = hNT.outerFace)
    (htz : M.tail z = M.tail b) (hzb : z ≠ b) : M.dartFace z ≠ hNT.outerFace :=
  fun hz => hzb (outer_dart_unique hz hb htz)

/-- `σ^m b ≠ b` for `0 < m < L` (`L = #(σ.cycleOf b).support`), provided `b ∈ σ.support`. -/
lemma sigma_pow_ne_self_of_lt {b : D} (hb : b ∈ M.σ.support) {m : ℕ}
    (hm0 : 0 < m) (hmL : m < (M.σ.cycleOf b).support.card) : (M.σ ^ m) b ≠ b := by
  set c := M.σ.cycleOf b with hc
  have hIsCycle : c.IsCycle := Equiv.Perm.isCycle_cycleOf M.σ (Equiv.Perm.mem_support.1 hb)
  have hord : orderOf c = c.support.card := hIsCycle.orderOf
  -- `b ∈ c.support`.
  have hbsupp : b ∈ c.support := by
    rw [hc, Equiv.Perm.mem_support, Equiv.Perm.cycleOf_apply_self, ← Equiv.Perm.mem_support]
    exact hb
  -- `(c^m).support = c.support` since `0 < m < L = orderOf c`.
  have hsupp_pow : (c ^ m).support = c.support :=
    hIsCycle.support_pow_of_pos_of_lt_orderOf hm0 (by rw [hord]; exact hmL)
  -- so `b ∈ (c^m).support`, i.e. `(c^m) b ≠ b`; and `(c^m) b = (σ^m) b`.
  have hbpow : b ∈ (c ^ m).support := by rw [hsupp_pow]; exact hbsupp
  have hne : (c ^ m) b ≠ b := Equiv.Perm.mem_support.1 hbpow
  intro hpow
  apply hne
  rw [hc, Equiv.Perm.cycleOf_pow_apply_self]; exact hpow

/-- `tail (σ^m b) = tail b`. -/
lemma tail_sigma_pow (b : D) (m : ℕ) : M.tail ((M.σ ^ m) b) = M.tail b := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, M.tail_sigma]; exact ih

/-- `dartFace (σ^m b) ≠ outerFace` for `0 < m < L`, where `b` is the outer dart at `w`. -/
lemma sigma_pow_nonouter {b : D} (hb_outer : M.dartFace b = hNT.outerFace)
    (hb_supp : b ∈ M.σ.support) {m : ℕ}
    (hm0 : 0 < m) (hmL : m < (M.σ.cycleOf b).support.card) :
    M.dartFace ((M.σ ^ m) b) ≠ hNT.outerFace :=
  nonouter_of_ne_outer hb_outer (tail_sigma_pow b m)
    (sigma_pow_ne_self_of_lt hb_supp hm0 hmL)

/-- **Anchor reachability.**  For `w ≠ u, v` and the outer dart `b` at `w`, every power
`σ^m b` with `1 ≤ m < L` has `dartFace (σ b)` reaching `dartFace (σ^m b)` in `ChordSplitAdj`. -/
lemma anchor_reaches (data : hNT.ChordSplitData u v) {b : D}
    (hb_outer : M.dartFace b = hNT.outerFace) (hb_supp : b ∈ M.σ.support)
    (hwu : M.tail b ≠ u) (hwv : M.tail b ≠ v) :
    ∀ m : ℕ, 1 ≤ m → m < (M.σ.cycleOf b).support.card →
      Relation.ReflTransGen (hNT.ChordSplitAdj u v)
        (M.dartFace (M.σ b)) (M.dartFace ((M.σ ^ m) b)) := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
    intro _hk1 hkL
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- `m = 1`: `σ^1 b = σ b`, refl.
      subst hk0
      simpa using Relation.ReflTransGen.refl
    · -- `m = k+1`, `k ≥ 1`: IH to `σ^k b`, then one step to `σ^(k+1) b`.
      have hkL' : k < (M.σ.cycleOf b).support.card := by omega
      have hreach := ih hkpos hkL'
      refine hreach.tail ?_
      -- one `ChordSplitAdj` step from `dartFace (σ^k b)` to `dartFace (σ^(k+1) b)`.
      have htail : M.tail ((M.σ ^ k) b) = M.tail b := tail_sigma_pow b k
      have hz_nonouter : M.dartFace ((M.σ ^ k) b) ≠ hNT.outerFace :=
        sigma_pow_nonouter hb_outer hb_supp hkpos hkL'
      have hσz_nonouter : M.dartFace (M.σ ((M.σ ^ k) b)) ≠ hNT.outerFace := by
        have heq : M.σ ((M.σ ^ k) b) = (M.σ ^ (k + 1)) b := by rw [pow_succ']; rfl
        rw [heq]
        exact sigma_pow_nonouter hb_outer hb_supp (by omega) hkL
      have hstep := chordSplitAdj_sigma_step_of_nonouter data
        (z := (M.σ ^ k) b) (by rw [htail]; exact hwu) (by rw [htail]; exact hwv)
        hz_nonouter hσz_nonouter
      -- rewrite `σ (σ^k b) = σ^(k+1) b`.
      have heq : M.σ ((M.σ ^ k) b) = (M.σ ^ (k + 1)) b := by rw [pow_succ']; rfl
      rwa [heq] at hstep

/-- **Boundary star connectivity.**  At a boundary vertex `w ≠ u, v`, any two non-outer darts
`d₁, d₂` with tail `w` have `ChordSplitAdj`-connected faces (both reach the anchor `dartFace (σ b)`
where `b` is the unique outer dart at `w`). -/
theorem boundary_star_nonouter_connected (data : hNT.ChordSplitData u v)
    {w : M.Vertex} (hw_boundary : hNT.outerCycle.IsBoundaryVertex w)
    (hwu : w ≠ u) (hwv : w ≠ v) {d₁ d₂ : D}
    (h₁tail : M.tail d₁ = w) (h₂tail : M.tail d₂ = w)
    (h₁nonouter : M.dartFace d₁ ≠ hNT.outerFace) (h₂nonouter : M.dartFace d₂ ≠ hNT.outerFace) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) (M.dartFace d₁) (M.dartFace d₂) := by
  -- the outer dart `b` at `w`.
  obtain ⟨b, hb_darts, hb_tail⟩ : ∃ b, b ∈ hNT.outerCycle.darts ∧ M.tail b = w := by
    have : w ∈ hNT.outerCycle.darts.map M.tail := by
      rw [← hNT.outerCycle.vertices_eq]; exact hw_boundary
    rcases List.mem_map.1 this with ⟨b, hb, hbw⟩; exact ⟨b, hb, hbw⟩
  have hb_outer : M.dartFace b = hNT.outerFace := (hNT.outerCycle.mem_darts_iff b).1 hb_darts
  have hb_supp : b ∈ M.σ.support :=
    Equiv.Perm.mem_support.2 (hNT.boundary_dart_sigma_ne hb_darts)
  -- both `d₁, d₂` reach `dartFace (σ b)`.
  set L := (M.σ.cycleOf b).support.card with hL
  have hbu : M.tail b ≠ u := by rw [hb_tail]; exact hwu
  have hbv : M.tail b ≠ v := by rw [hb_tail]; exact hwv
  have reach : ∀ {d : D}, M.tail d = w → M.dartFace d ≠ hNT.outerFace →
      Relation.ReflTransGen (hNT.ChordSplitAdj u v) (M.dartFace (M.σ b)) (M.dartFace d) := by
    intro d hdtail hdnonouter
    -- `σ.SameCycle b d` (equal tails), and `b ∈ support`.
    have hsc : M.σ.SameCycle b d :=
      (sigma_sameCycle_iff_tail b d).2 (by rw [hb_tail, hdtail])
    obtain ⟨m, hmL, hmd⟩ := hsc.exists_pow_eq_of_mem_support hb_supp
    -- `m ≠ 0` (else `d = b` is outer).
    have hm0 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exfalso; apply hdnonouter; rw [← hmd, h]; simpa using hb_outer
      · exact h
    have := anchor_reaches data hb_outer hb_supp hbu hbv m hm0 hmL
    rwa [hmd] at this
  have r₁ := reach h₁tail h₁nonouter
  have r₂ := reach h₂tail h₂nonouter
  -- `d₁ ~* anchor ~* d₂`.
  exact (Relation.ReflTransGen.symmetric (fun _ _ h => hNT.chordSplitAdj_symm h) r₁).trans r₂

/-! ## 5. The core star-connectivity lemma -/

/-- **Core star connectivity away from chord ends.**  For `w ≠ u, v`, any two non-outer darts
`d₁, d₂` with common tail `w` have `ChordSplitAdj`-connected faces.  Case split on whether `w`
is a boundary vertex: interior → `interior_star_nonouter_connected`; boundary →
`boundary_star_nonouter_connected`. -/
theorem star_nonouter_connected_away_from_chordEnds (data : hNT.ChordSplitData u v)
    {w : M.Vertex} (hwu : w ≠ u) (hwv : w ≠ v) {d₁ d₂ : D}
    (h₁tail : M.tail d₁ = w) (h₂tail : M.tail d₂ = w)
    (h₁nonouter : M.dartFace d₁ ≠ hNT.outerFace) (h₂nonouter : M.dartFace d₂ ≠ hNT.outerFace) :
    Relation.ReflTransGen (hNT.ChordSplitAdj u v) (M.dartFace d₁) (M.dartFace d₂) := by
  by_cases hw_boundary : hNT.outerCycle.IsBoundaryVertex w
  · exact boundary_star_nonouter_connected data hw_boundary hwu hwv h₁tail h₂tail
      h₁nonouter h₂nonouter
  · exact interior_star_nonouter_connected data hw_boundary hwu hwv h₁tail h₂tail

/-! ## 6. Assembly: `SideRegionInterChordEnds`, UNCONDITIONAL -/

/-- **`SideRegionInterChordEnds`, discharged unconditionally.**  A vertex `w` in both side regions
is a chord endpoint.  Proof by contradiction: extract incident side-1 / side-2 faces at `w`,
connect them via the core star-connectivity lemma (`w ≠ u, v`), and contradict `Separates`. -/
theorem sideRegionInterChordEnds_holds (data : hNT.ChordSplitData u v) (hsep : data.Separates) :
    SideRegionInterChordEnds data := by
  intro w hw1 hw2
  by_contra hnot
  have hwu : w ≠ u := fun h => hnot (Or.inl h)
  have hwv : w ≠ v := fun h => hnot (Or.inr h)
  -- extract incident side-1 and side-2 faces at `w`.
  obtain ⟨d₁, ht₁, hf₁⟩ := incident_side₁_of_mem_sideRegion₁ data hw1
  obtain ⟨d₂, ht₂, hf₂⟩ := incident_side₂_of_mem_sideRegion₂ data hw2
  have ho₁ : M.dartFace d₁ ≠ hNT.outerFace := data.side₁_subset_nonouter hf₁
  have ho₂ : M.dartFace d₂ ≠ hNT.outerFace := data.side₂_subset_nonouter hf₂
  -- connect the two faces.
  have hconn : Relation.ReflTransGen (hNT.ChordSplitAdj u v) (M.dartFace d₁) (M.dartFace d₂) :=
    star_nonouter_connected_away_from_chordEnds data hwu hwv ht₁ ht₂ ho₁ ho₂
  -- `face₂ ∈ side₁`, contradicting `Separates`.
  have hf₂_to_face₂ : data.face₂ ∈ hNT.Side u v (M.dartFace d₂) := side_mem_symm hf₂
  have : data.face₂ ∈ data.side₁ := (hf₁.trans hconn).trans hf₂_to_face₂
  exact hsep this

end ProofsInTheBook.ZinanCh35StarConn

/-! ## Axiom audit (expect: `propext`, `Classical.choice`, `Quot.sound`). -/

#print axioms ProofsInTheBook.ZinanCh35StarConn.interior_star_nonouter_connected
#print axioms ProofsInTheBook.ZinanCh35StarConn.boundary_star_nonouter_connected
#print axioms ProofsInTheBook.ZinanCh35StarConn.star_nonouter_connected_away_from_chordEnds
#print axioms ProofsInTheBook.ZinanCh35StarConn.sideRegionInterChordEnds_holds
