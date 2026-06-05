import ProofsInTheBook.PlanarMapFanFaces

/-!
# The merged-face single-orbit fact of the fan deletion (φ-level)

This file discharges `DeleteVertexMergedFaceSingleOrbit M d0` from the boundary
fan: the surviving darts whose `M`-face is incident with `v0` (the `t + 1` fan
triangles together with the old outer face) all lie in a single `φ'`-cycle of
the deleted map, i.e. they form one merged outer face.

It is the `φ`-level sibling of `deleteVertex_neighborsConnected_of_fan`
(`PlanarMapFanConnectivity.lean`), which is the `σ`/`α`-level reconnection.

## The closed-form `φ'`-successor at the seam

The crucial structural simplification.  For a survivor `x`, write
`z = M.head x.1` for the vertex at the head of `x.1`; the deleted map's
`φ'`-successor is computed by rotating `σ` from `M.α x.1` (a dart at `z`) to the
first surviving dart.  Because the only deleted darts at a vertex `z ≠ v0` are
the darts **pointing at `v0`** (`head = v0`), and in a simple graph there is at
most one such dart, the rotation skips **at most one** dart.  Concretely, with
`σ = M.φ ∘ M.α`:

* **Case A** (`M.φ x.1` survives): `φ' x = M.φ x.1`.
* **Case B** (`M.φ x.1` is deleted, i.e. `M.head (M.φ x.1) = v0`):
  `φ' x = M.σ (M.φ x.1) = M.φ (M.α (M.φ x.1))`, which then survives.

This closed form lets us trace the entire merged-face walk with `φ`/`α` algebra
alone — no seam rotation list is needed.

## The walk

Indexing the fan triangles `T_i = (v0, z_i, z_{i+1})` (`i = 0..t`, with
`z_0 = x`, `z_{t+1} = w`), exactly one dart of each triangle survives: the edge
dart `d1_i` (tail `z_i`, head `z_{i+1}`).  The closed form gives, via the spoke
shared by consecutive triangles,

```
φ'(d1_i) = d1_{i+1}            (i < t)
φ'(d1_t) = o_post             (jump into the old outer face after v0)
φ'(o_pre) = d1_0              (jump from the old outer face back to the x-side)
```

and on the surviving arc of the old outer face the `φ'`-steps are the old
`M.φ`-steps (clean steps), so the whole incident-survivor set is one `φ'`-cycle.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## `σ = φ · α` and the closed-form `φ'` successor -/

/-- The vertex rotation factors as `σ = φ · α` (since `φ = σ · α` and `α² = 1`). -/
lemma sigma_eq_phi_mul_alpha (M : CombMap D) : M.σ = M.φ * M.α := by
  rw [φ, mul_assoc, M.α_invol, mul_one]

/-- One `σ`-step is `φ` after `α`. -/
lemma sigma_apply (M : CombMap D) (d : D) : M.σ d = M.φ (M.α d) := by
  rw [sigma_eq_phi_mul_alpha]; rfl

/-- `σ (α d) = M.φ d`. -/
lemma sigma_alpha (M : CombMap D) (d : D) : M.σ (M.α d) = M.φ d := by
  rw [sigma_apply, M.alpha_alpha]

/-- **Closed-form `φ'` successor, Case B: the next dart is deleted.**  If `x`
survives, the immediate `M.φ`-successor `M.φ x.1` is deleted, but the following
`σ`-step `M.σ (M.φ x.1)` survives, then the deleted-map `φ'`-successor of `x`
is exactly `M.σ (M.φ x.1)`. -/
lemma deleteVertex_phi_apply_of_next_deleted (M : CombMap D) (v : D)
    (x : {d : D // d ∉ M.deleteVertexSet v})
    (hdel : M.φ x.1 ∈ M.deleteVertexSet v)
    (hsurv : M.σ (M.φ x.1) ∉ M.deleteVertexSet v) :
    ((M.deleteVertex v).φ x : D) = M.σ (M.φ x.1) := by
  classical
  set y : {d : D // d ∉ M.deleteVertexSet v} := M.alphaDeleteVertex v x with hy
  have hycoe : (y : D) = M.α x.1 := by rw [hy]; exact alphaDeleteVertex_apply_coe M v x
  -- σ¹ (α x.1) = M.φ x.1
  have hσ1 : (M.σ ^ 1) (y : D) = M.φ x.1 := by
    rw [pow_one, hycoe, sigma_alpha]
  -- σ² (α x.1) = σ (M.φ x.1)
  have hσ2 : (M.σ ^ 2) (y : D) = M.σ (M.φ x.1) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, pow_succ']
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [hσ1]
  -- firstOutside = 2
  have hfo : Equiv.Perm.DeleteSet.firstOutside M.σ (M.deleteVertexSet v) y = 2 := by
    refine (Nat.find_eq_iff (Equiv.Perm.DeleteSet.exists_pos_pow_notMem M.σ (M.deleteVertexSet v) y)).2 ?_
    refine ⟨⟨by norm_num, by rw [hσ2]; exact hsurv⟩, ?_⟩
    intro m hm ⟨hmpos, hmnot⟩
    interval_cases m
    · rw [hσ1] at hmnot; exact hmnot hdel
  rw [deleteVertex_phi_apply_coe]
  rw [show (M.alphaDeleteVertex v x) = y from rfl, hfo, ← hycoe, hσ2]

/-! ## Survival-run iterate: `φ'` follows `M.φ` along any run of survivors

If a forward `M.φ`-run of length `k` from a survivor `x` stays entirely inside
the survivors, then `(φ')^k x` has underlying dart `(M.φ ^ k) x.1`.  Unlike the
clean-face iterate of `PlanarMapFanFaces`, this needs no face condition — only
that the visited darts survive.  This is the tool for walking the surviving arc
of the old outer face. -/

/-- A forward `M.φ`-run of survivors is followed step-for-step by `φ'`. -/
lemma deleteVertex_phi_survRun_iterate (M : CombMap D) (v : D)
    (x : {d : D // d ∉ M.deleteVertexSet v}) (k : ℕ)
    (hrun : ∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet v) :
    (((M.deleteVertex v).φ ^ k) x : D) = (M.φ ^ k) x.1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have ihrun : ∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet v :=
        fun j hj => hrun j (Nat.le_succ_of_le hj)
      have hval : (((M.deleteVertex v).φ ^ k) x : D) = (M.φ ^ k) x.1 := ih ihrun
      -- the dart we are stepping from survives
      have hxk : (M.φ ^ k) x.1 ∉ M.deleteVertexSet v := hrun k (Nat.le_succ k)
      -- its M.φ-successor survives
      have hnext : M.φ ((M.φ ^ k) x.1) ∉ M.deleteVertexSet v := by
        have : (M.φ ^ (k + 1)) x.1 = M.φ ((M.φ ^ k) x.1) := by
          rw [pow_succ']; rfl
        rw [← this]; exact hrun (k + 1) (le_refl _)
      have hiter1 : ((M.deleteVertex v).φ ^ (k + 1)) x
          = (M.deleteVertex v).φ (((M.deleteVertex v).φ ^ k) x) := by
        rw [pow_succ']; rfl
      rw [hiter1]
      -- φ' agrees with M.φ on the surviving dart ⟨(M.φ^k) x.1, hxk⟩
      have hstep : ((M.deleteVertex v).φ (((M.deleteVertex v).φ ^ k) x) : D)
          = M.φ ((M.φ ^ k) x.1) := by
        have hpt : (((M.deleteVertex v).φ ^ k) x) = (⟨(M.φ ^ k) x.1, hxk⟩ :
            {d : D // d ∉ M.deleteVertexSet v}) := Subtype.ext hval
        rw [hpt]
        exact deleteVertex_phi_apply_of_next_kept M v ⟨(M.φ ^ k) x.1, hxk⟩ hnext
      rw [hstep, pow_succ']; rfl

/-- Two survivors on the same `M`-face whose connecting forward `M.φ`-run stays
inside the survivors are in the same `φ'`-cycle. -/
lemma deleteVertex_phi_sameCycle_of_survRun (M : CombMap D) (v : D)
    (x y : {d : D // d ∉ M.deleteVertexSet v}) (k : ℕ)
    (hrun : ∀ j ≤ k, (M.φ ^ j) x.1 ∉ M.deleteVertexSet v)
    (hk : (M.φ ^ k) x.1 = y.1) :
    (M.deleteVertex v).φ.SameCycle x y := by
  refine ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast]
  apply Subtype.ext
  rw [deleteVertex_phi_survRun_iterate M v x k hrun, hk]

namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}

/-! ## Triangle-dart endpoint and survival facts

For a fan triangle `T = (v0, a, b)` (darts `d0 : v0→a`, `d1 : a→b`, `d2 : b→v0`
in cyclic `φ`-order), the edge dart `d1` is the only surviving dart of the
triangle's `φ`-orbit; `d0` and `d2` are deleted (they touch `v0`). -/

/-- The head of `T.d1` is `b`. -/
private lemma fanTriangle_head1 {a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    M.head T.d1 = b := by
  have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
  have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
  rw [hh, T.tail2]

/-- The head of `T.d2` is `v0`. -/
private lemma fanTriangle_head2 {a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    M.head T.d2 = v0 := by
  have hphi : M.φ T.d2 = T.d0 := T.triangle.2.2
  have hh : M.head T.d2 = M.tail T.d0 := by rw [← tail_phi, hphi]
  rw [hh, T.tail0]

/-- The head of `T.d0` is `a`. -/
private lemma fanTriangle_head0 {a b : M.Vertex} (T : FanTriangle hNT v0 a b) :
    M.head T.d0 = a := by
  have hphi : M.φ T.d0 = T.d1 := T.triangle.1
  have hh : M.head T.d0 = M.tail T.d1 := by rw [← tail_phi, hphi]
  rw [hh, T.tail1]

/-- `T.d1` survives the deletion of any dart `d0` representing `v0`. -/
private lemma fanTriangle_d1_survives {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d1 ∉ M.deleteVertexSet d0 := by
  have hdist := T.vertices_pairwiseDistinct
  have htail : M.tail T.d1 ≠ M.tail d0 := by rw [T.tail1, htail0]; exact (hdist.1).symm
  have hhead : M.head T.d1 ≠ M.tail d0 := by
    rw [fanTriangle_head1 T, htail0]; exact hdist.2.2
  rw [mem_deleteVertexSet_iff]; push_neg
  rw [mem_vertexDarts, mem_vertexDarts]
  refine ⟨fun h => htail (Quotient.sound h).symm, fun h => ?_⟩
  have heq : M.tail d0 = M.tail (M.α T.d1) := Quotient.sound h
  rw [tail_alpha] at heq
  exact hhead heq.symm

/-- `T.d2` is deleted (its head is `v0`). -/
private lemma fanTriangle_d2_deleted {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d2 ∈ M.deleteVertexSet d0 := by
  rw [mem_deleteVertexSet_iff]; right
  rw [mem_vertexDarts]
  -- α T.d2 has tail = head T.d2 = v0 = tail d0
  exact Quotient.exact (show M.tail d0 = M.tail (M.α T.d2) by
    rw [tail_alpha, fanTriangle_head2 T, htail0])

/-! ## The shared spoke and the triangle chain step -/

/-- **Consecutive fan triangles share the `v0`-spoke.**  If `Ti = (v0, a, b)` and
`Tj = (v0, b, c)` are consecutive fan triangles, then the reverse of `Ti.d2`
(tail `b`, head `v0`) is `Tj.d0` (tail `v0`, head `b`): they are the two darts of
the single edge `v0—b`. -/
private lemma fanTriangle_shared_spoke {a b c : M.Vertex}
    (Ti : FanTriangle hNT v0 a b) (Tj : FanTriangle hNT v0 b c) :
    M.α Ti.d2 = Tj.d0 := by
  have hsame : M.α.SameCycle Ti.d2 Tj.d0 :=
    alpha_sameCycle_of_same_endpoints_symm M hNT.simpleGraph
      (by rw [Ti.tail2, fanTriangle_head0 Tj])
      (by rw [fanTriangle_head2 Ti, Tj.tail0])
  rcases (alpha_sameCycle_iff M Ti.d2 Tj.d0).1 hsame with h | h
  · -- Tj.d0 = Ti.d2 impossible: different tails (v0 vs b)
    exfalso
    have hbv0 : (b : M.Vertex) = v0 := by
      have : M.tail Tj.d0 = M.tail Ti.d2 := by rw [h]
      rw [Tj.tail0, Ti.tail2] at this; exact this.symm
    exact (Tj.vertices_pairwiseDistinct).1 hbv0.symm
  · rw [h]

/-- **Triangle chain step.**  The deleted-map `φ'`-successor of `Ti.d1` is
`Tj.d1`, where `Tj` is the next consecutive fan triangle. -/
private lemma fanTriangle_chain_step {a b c : M.Vertex}
    (Ti : FanTriangle hNT v0 a b) (Tj : FanTriangle hNT v0 b c)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    ((M.deleteVertex d0).φ ⟨Ti.d1, fanTriangle_d1_survives Ti htail0⟩ : D) = Tj.d1 := by
  have hdel : M.φ Ti.d1 ∈ M.deleteVertexSet d0 := by
    have hphi : M.φ Ti.d1 = Ti.d2 := Ti.triangle.2.1
    rw [hphi]; exact fanTriangle_d2_deleted Ti htail0
  -- σ (M.φ Ti.d1) = σ Ti.d2 = M.φ (α Ti.d2) = M.φ Tj.d0 = Tj.d1
  have hphi1 : M.φ Ti.d1 = Ti.d2 := Ti.triangle.2.1
  have hsig : M.σ (M.φ Ti.d1) = Tj.d1 := by
    rw [hphi1, sigma_apply, fanTriangle_shared_spoke Ti Tj]
    exact Tj.triangle.1
  have hsurv : M.σ (M.φ Ti.d1) ∉ M.deleteVertexSet d0 := by
    rw [hsig]; exact fanTriangle_d1_survives Tj htail0
  rw [deleteVertex_phi_apply_of_next_deleted M d0 _ hdel hsurv, hsig]

/-- `φ'`-cycle form of the chain step: consecutive triangle edge darts are in one
`φ'`-cycle. -/
private lemma fanTriangle_chain_sameCycle {a b c : M.Vertex}
    (Ti : FanTriangle hNT v0 a b) (Tj : FanTriangle hNT v0 b c)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    (M.deleteVertex d0).φ.SameCycle
      ⟨Ti.d1, fanTriangle_d1_survives Ti htail0⟩
      ⟨Tj.d1, fanTriangle_d1_survives Tj htail0⟩ := by
  refine ⟨1, ?_⟩
  apply Subtype.ext
  rw [zpow_one]
  exact fanTriangle_chain_step Ti Tj htail0

/-! ## All fan-triangle edge darts lie in one `φ'`-cycle

Walking the fan path `x, z_1, …, z_t, w`, the consecutive triangles' edge darts
chain together, so every fan triangle's edge dart is in the `φ'`-cycle of the
head triangle's edge dart. -/

/-- `consecutivePairs` of a two-or-more element list. -/
private lemma consecutivePairs_cons_cons {α : Type*} (a b : α) (l : List α) :
    consecutivePairs (a :: b :: l) = (a, b) :: consecutivePairs (b :: l) := by
  simp [consecutivePairs]

/-- Every triangle edge dart along the path is in the `φ'`-cycle of a fixed
reference survivor `r`, provided `r` is already linked to the head triangle's
edge dart and all consecutive pairs carry triangles. -/
private lemma fanTriangle_edge_dart_sameCycle_ref {d0 : D} (htail0 : M.tail d0 = v0)
    (r : {d : D // d ∉ M.deleteVertexSet d0}) :
    ∀ (L : List M.Vertex) (hd : M.Vertex)
      (htri : ∀ a b : M.Vertex, (a, b) ∈ consecutivePairs (hd :: L) →
        FanTriangle hNT v0 a b),
      (∀ (c : M.Vertex) (hpc : (hd, c) ∈ consecutivePairs (hd :: L)),
        (M.deleteVertex d0).φ.SameCycle r
          ⟨(htri hd c hpc).d1, fanTriangle_d1_survives _ htail0⟩) →
      ∀ {a b : M.Vertex} (hab : (a, b) ∈ consecutivePairs (hd :: L)),
        (M.deleteVertex d0).φ.SameCycle r
          ⟨(htri a b hab).d1, fanTriangle_d1_survives _ htail0⟩ := by
  intro L
  induction L with
  | nil => intro hd htri _ a b hab; simp [consecutivePairs] at hab
  | cons c t ih =>
      intro hd htri hhead a b hab
      have hpc : (hd, c) ∈ consecutivePairs (hd :: c :: t) := by
        rw [consecutivePairs_cons_cons]; exact List.mem_cons.mpr (Or.inl rfl)
      -- lift a (c::t)-pair to a (hd::c::t)-pair.
      have lift : ∀ a' b' : M.Vertex, (a', b') ∈ consecutivePairs (c :: t) →
          (a', b') ∈ consecutivePairs (hd :: c :: t) := fun a' b' hab' => by
        rw [consecutivePairs_cons_cons]; exact List.mem_cons.mpr (Or.inr hab')
      -- triangle provider for the tail list, definitionally `htri ∘ lift`.
      set htri' : ∀ a' b' : M.Vertex, (a', b') ∈ consecutivePairs (c :: t) →
          FanTriangle hNT v0 a' b' :=
        fun a' b' hab' => htri a' b' (lift a' b' hab') with htri'def
      -- new head hypothesis: r links to (c, c')'s edge dart for each first pair of (c::t).
      have hhead' : ∀ (c' : M.Vertex) (hpc' : (c, c') ∈ consecutivePairs (c :: t)),
          (M.deleteVertex d0).φ.SameCycle r
            ⟨(htri' c c' hpc').d1, fanTriangle_d1_survives _ htail0⟩ := by
        intro c' hpc'
        have hchain := fanTriangle_chain_sameCycle (htri hd c hpc)
          (htri' c c' hpc') htail0
        exact (hhead c hpc).trans hchain
      rw [consecutivePairs_cons_cons] at hab
      rcases List.mem_cons.mp hab with hhd | htl
      · -- (a,b) = (hd,c).
        have hae : a = hd := (Prod.ext_iff.mp hhd).1
        have hbe : b = c := (Prod.ext_iff.mp hhd).2
        cases hae; cases hbe
        exact hhead c hab
      · exact ih c htri' hhead' htl

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
