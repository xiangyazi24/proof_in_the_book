import ProofsInTheBook.PlanarMapEuler

/-!
# Deleting darts from planar maps

This file starts the vertex-deletion layer needed for the Chapter 35 five-color
development.  The first part is a general operation on finite permutations:
delete a finite set of points from every cycle and reconnect the surviving
points in the original cyclic order.
-/

namespace Equiv.Perm

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace DeleteSet

omit [DecidableEq D] in
/-- There is always a positive iterate of `p` from a surviving point back to a
surviving point: `orderOf p` returns to the starting point. -/
lemma exists_pos_pow_notMem (p : Equiv.Perm D) (S : Finset D) (x : {d : D // d ∉ S}) :
    ∃ n : ℕ, 0 < n ∧ (p ^ n) x.1 ∉ S := by
  refine ⟨orderOf p, orderOf_pos p, ?_⟩
  simpa using x.2

/-- The first positive `p`-iterate of `x` outside `S`. -/
noncomputable def firstOutside (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) : ℕ :=
  Nat.find (exists_pos_pow_notMem p S x)

lemma firstOutside_spec (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    0 < firstOutside p S x ∧ (p ^ firstOutside p S x) x.1 ∉ S :=
  Nat.find_spec (exists_pos_pow_notMem p S x)

lemma firstOutside_pos (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    0 < firstOutside p S x :=
  (firstOutside_spec p S x).1

lemma firstOutside_notMem (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    (p ^ firstOutside p S x) x.1 ∉ S :=
  (firstOutside_spec p S x).2

lemma firstOutside_min (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) {m : ℕ}
    (hm : m < firstOutside p S x) :
    ¬ (0 < m ∧ (p ^ m) x.1 ∉ S) :=
  Nat.find_min (exists_pos_pow_notMem p S x) hm

/-- The underlying function of `deleteSet`: move to the first surviving forward
iterate. -/
noncomputable def deleteSetFun (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) : {d : D // d ∉ S} :=
  ⟨(p ^ firstOutside p S x) x.1, firstOutside_notMem p S x⟩

@[simp]
lemma deleteSetFun_coe (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    (deleteSetFun p S x : D) = (p ^ firstOutside p S x) x.1 :=
  rfl

lemma firstOutside_inv_deleteSetFun (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    firstOutside p⁻¹ S (deleteSetFun p S x) = firstOutside p S x := by
  classical
  let n := firstOutside p S x
  have hnpos : 0 < n := firstOutside_pos p S x
  have hnnot : (p ^ n) x.1 ∉ S := firstOutside_notMem p S x
  refine (Nat.find_eq_iff (exists_pos_pow_notMem p⁻¹ S (deleteSetFun p S x))).2 ?_
  constructor
  · constructor
    · exact hnpos
    · have hpow : ((p⁻¹) ^ n) ((deleteSetFun p S x : {d : D // d ∉ S}) : D) = x.1 := by
        simp only [deleteSetFun_coe]
        rw [inv_pow]
        change (p ^ n).symm ((p ^ n) x.1) = x.1
        exact Equiv.symm_apply_apply (p ^ n) x.1
      simpa [hpow] using x.2
  · intro m hm
    rintro ⟨hmpos, hmnot⟩
    have hmn : m < n := hm
    have hsubpos : 0 < n - m := Nat.sub_pos_of_lt hmn
    have hsub_lt : n - m < n := Nat.sub_lt hnpos hmpos
    have hforward :
        (p ^ (n - m)) x.1 =
          ((p⁻¹) ^ m) ((deleteSetFun p S x : {d : D // d ∉ S}) : D) := by
      simp only [deleteSetFun_coe]
      rw [inv_pow]
      have hle : m ≤ n := le_of_lt hmn
      have hperm : (p ^ m)⁻¹ * p ^ n = p ^ (n - m) := by
        have hpown : p ^ n = p ^ m * p ^ (n - m) := by
          have hadd : m + (n - m) = n := Nat.add_sub_of_le hle
          calc
            p ^ n = p ^ (m + (n - m)) := by rw [hadd]
            _ = p ^ m * p ^ (n - m) := by rw [pow_add]
        calc
          (p ^ m)⁻¹ * p ^ n = (p ^ m)⁻¹ * (p ^ m * p ^ (n - m)) := by
            rw [hpown]
          _ = p ^ (n - m) := by
            rw [← mul_assoc, inv_mul_cancel, one_mul]
      calc
        (p ^ (n - m)) x.1 = ((p ^ m)⁻¹ * (p ^ n)) x.1 := by
          rw [hperm]
        _ = ((p ^ m)⁻¹) ((p ^ n) x.1) := rfl
        _ = ((p⁻¹) ^ m) ((p ^ n) x.1) := by rw [inv_pow]
    have hbad : 0 < n - m ∧ (p ^ (n - m)) x.1 ∉ S := by
      exact ⟨hsubpos, by simpa [hforward] using hmnot⟩
    exact firstOutside_min p S x hsub_lt hbad

lemma deleteSetFun_inv_apply (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    deleteSetFun p⁻¹ S (deleteSetFun p S x) = x := by
  classical
  apply Subtype.ext
  rw [deleteSetFun_coe, firstOutside_inv_deleteSetFun p S x, deleteSetFun_coe]
  rw [inv_pow]
  change (p ^ firstOutside p S x).symm ((p ^ firstOutside p S x) x.1) = x.1
  exact Equiv.symm_apply_apply (p ^ firstOutside p S x) x.1

end DeleteSet

open DeleteSet

/-- Delete a finite set from the cycles of a permutation, reconnecting the
surviving points by skipping deleted points. -/
noncomputable def deleteSet (p : Equiv.Perm D) (S : Finset D) :
    Equiv.Perm {d : D // d ∉ S} where
  toFun := deleteSetFun p S
  invFun := deleteSetFun p⁻¹ S
  left_inv := deleteSetFun_inv_apply p S
  right_inv := by
    intro x
    simpa using deleteSetFun_inv_apply p⁻¹ S x

@[simp]
lemma deleteSet_apply_coe (p : Equiv.Perm D) (S : Finset D)
    (x : {d : D // d ∉ S}) :
    ((deleteSet p S x : {d : D // d ∉ S}) : D) =
      (p ^ firstOutside p S x) x.1 :=
  rfl

lemma sameCycle_deleteSet_imp (p : Equiv.Perm D) (S : Finset D)
    {x y : {d : D // d ∉ S}} :
    (deleteSet p S).SameCycle x y → p.SameCycle x.1 y.1 := by
  classical
  intro hxy
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.SameCycle.exists_nat_pow_eq (f := deleteSet p S) hxy
  clear hxy
  revert x
  induction m with
  | zero =>
      intro x hm
      simp only [pow_zero, Equiv.Perm.coe_one, id_eq] at hm
      exact (congrArg Subtype.val hm).sameCycle p
  | succ m ih =>
      intro x hm
      let z : {d : D // d ∉ S} := deleteSet p S x
      have hstep : p.SameCycle x.1 z.1 := by
        refine ⟨(firstOutside p S x : ℤ), ?_⟩
        rw [zpow_natCast]
        rfl
      have htail : ((deleteSet p S) ^ m) z = y := by
        simpa [z, pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hm
      exact hstep.trans (ih (x := z) htail)

lemma sameCycle_deleteSet_of_pow (p : Equiv.Perm D) (S : Finset D) :
    ∀ m : ℕ, ∀ x y : {d : D // d ∉ S},
      (p ^ m) x.1 = y.1 → (deleteSet p S).SameCycle x y := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro x y hxy
      by_cases hm0 : m = 0
      · subst hm0
        apply (Subtype.ext ?_).sameCycle
        simpa using hxy
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        let n := firstOutside p S x
        have hnpos : 0 < n := firstOutside_pos p S x
        have hnot_lt : ¬ m < n := by
          intro hmn
          have hbad : 0 < m ∧ (p ^ m) x.1 ∉ S := by
            exact ⟨hmpos, by simpa [hxy] using y.2⟩
          exact firstOutside_min p S x hmn hbad
        have hnm : n ≤ m := le_of_not_gt hnot_lt
        let z : {d : D // d ∉ S} := deleteSet p S x
        have hxz : z.1 = (p ^ n) x.1 := rfl
        have hstep : (deleteSet p S).SameCycle x z := by
          refine ⟨1, ?_⟩
          change deleteSet p S x = z
          rfl
        by_cases hnm_eq : n = m
        · have hzy : z = y := by
            apply Subtype.ext
            rw [hxz, hnm_eq, hxy]
          simpa [hzy] using hstep
        · have hlt : m - n < m := Nat.sub_lt hmpos hnpos
          have hpow : (p ^ (m - n)) z.1 = y.1 := by
            rw [hxz]
            rw [← mul_apply, ← pow_add]
            have hadd : m - n + n = m := Nat.sub_add_cancel hnm
            rw [hadd, hxy]
          exact hstep.trans (ih (m - n) hlt z y hpow)

lemma sameCycle_deleteSet_iff (p : Equiv.Perm D) (S : Finset D)
    (x y : {d : D // d ∉ S}) :
    (deleteSet p S).SameCycle x y ↔ p.SameCycle x.1 y.1 := by
  classical
  constructor
  · exact sameCycle_deleteSet_imp p S
  · intro h
    obtain ⟨m, hm⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq (f := p) h
    exact sameCycle_deleteSet_of_pow p S m x y hm

end Equiv.Perm

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The darts in the `σ`-orbit of a dart representative `v`. -/
def vertexDarts (M : CombMap D) (v : D) : Finset D :=
  Finset.univ.filter (fun d => M.σ.SameCycle v d)

/-- Degree of the vertex represented by `v`, as a dart count. -/
def dartVertexDegree (M : CombMap D) (v : D) : ℕ :=
  (M.vertexDarts v).card

/-- No loop based at the vertex represented by `v`: the edge reverse of a dart
at `v` is not also a dart at `v`.  This is needed for the simple edge-count
formula `E' = E - deg(v)`. -/
def NoLoopAt (M : CombMap D) (v : D) : Prop :=
  ∀ d : D, d ∈ M.vertexDarts v → M.α d ∉ M.vertexDarts v

@[simp]
lemma mem_vertexDarts (M : CombMap D) (v d : D) :
    d ∈ M.vertexDarts v ↔ M.σ.SameCycle v d := by
  simp [vertexDarts]

lemma self_mem_vertexDarts (M : CombMap D) (v : D) :
    v ∈ M.vertexDarts v := by
  simpa [vertexDarts] using Equiv.Perm.SameCycle.refl M.σ v

/-- The closed dart star of `v`: the darts at `v` and their edge reverses.
This is the set that is actually stable under `α`, hence the one on which
`α` can be restricted after deleting a vertex and all incident edges. -/
def deleteVertexSet (M : CombMap D) (v : D) : Finset D :=
  M.vertexDarts v ∪ (M.vertexDarts v).image M.α.toEmbedding

lemma mem_deleteVertexSet_iff (M : CombMap D) (v d : D) :
    d ∈ M.deleteVertexSet v ↔ d ∈ M.vertexDarts v ∨ M.α d ∈ M.vertexDarts v := by
  classical
  constructor
  · intro hd
    rw [deleteVertexSet, Finset.mem_union, Finset.mem_image] at hd
    rcases hd with hd | ⟨x, hx, hxd⟩
    · exact Or.inl hd
    · right
      have : M.α d = x := by
        rw [← hxd]
        have hα : M.α * M.α = 1 := M.α_invol
        have happ := congrArg (fun f : Equiv.Perm D => f x) hα
        simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
      simpa [this] using hx
  · intro hd
    rw [deleteVertexSet, Finset.mem_union, Finset.mem_image]
    rcases hd with hd | hd
    · exact Or.inl hd
    · right
      refine ⟨M.α d, hd, ?_⟩
      have hα : M.α * M.α = 1 := M.α_invol
      have happ := congrArg (fun f : Equiv.Perm D => f d) hα
      simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ

lemma alpha_mem_deleteVertexSet_iff (M : CombMap D) (v d : D) :
    M.α d ∈ M.deleteVertexSet v ↔ d ∈ M.deleteVertexSet v := by
  classical
  rw [mem_deleteVertexSet_iff, mem_deleteVertexSet_iff]
  have hαd : M.α (M.α d) = d := by
    have hα : M.α * M.α = 1 := M.α_invol
    have happ := congrArg (fun f : Equiv.Perm D => f d) hα
    simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
  simp [hαd, or_comm]

/-- Restrict the edge involution to the complement of an `α`-stable deleted set. -/
noncomputable def alphaDeleteVertex (M : CombMap D) (v : D) :
    Equiv.Perm {d : D // d ∉ M.deleteVertexSet v} :=
  M.α.subtypePerm (fun d => by
    constructor
    · intro hd hdel
      exact hd ((alpha_mem_deleteVertexSet_iff M v d).2 hdel)
    · intro hd hdel
      exact hd ((alpha_mem_deleteVertexSet_iff M v d).1 hdel))

@[simp]
lemma alphaDeleteVertex_apply_coe (M : CombMap D) (v : D)
    (d : {d : D // d ∉ M.deleteVertexSet v}) :
    (M.alphaDeleteVertex v d : D) = M.α d.1 := by
  simp [alphaDeleteVertex]

/-- Delete the closed dart star of `v`.  The vertex rotation skips all deleted
darts; the edge involution is the restriction of `α` to the surviving darts. -/
noncomputable def deleteVertex (M : CombMap D) (v : D) :
    CombMap {d : D // d ∉ M.deleteVertexSet v} where
  α := M.alphaDeleteVertex v
  σ := M.σ.deleteSet (M.deleteVertexSet v)
  α_invol := by
    ext d
    simp [alphaDeleteVertex, Equiv.Perm.subtypePerm_apply]
    have hα : M.α * M.α = 1 := M.α_invol
    have happ := congrArg (fun f : Equiv.Perm D => f d.1) hα
    simpa [Equiv.Perm.coe_mul, Function.comp_apply] using happ
  α_no_fixed := by
    intro d h
    exact M.α_no_fixed d.1 (by
      have := congrArg Subtype.val h
      simpa [alphaDeleteVertex] using this)

@[simp]
lemma deleteVertex_alpha_apply_coe (M : CombMap D) (v : D)
    (d : {d : D // d ∉ M.deleteVertexSet v}) :
    ((M.deleteVertex v).α d : D) = M.α d.1 :=
  rfl

@[simp]
lemma deleteVertex_sigma_sameCycle_iff (M : CombMap D) (v : D)
    (x y : {d : D // d ∉ M.deleteVertexSet v}) :
    (M.deleteVertex v).σ.SameCycle x y ↔ M.σ.SameCycle x.1 y.1 := by
  simpa [deleteVertex] using Equiv.Perm.sameCycle_deleteSet_iff M.σ (M.deleteVertexSet v) x y

lemma deleteVertexSet_card_eq_two_mul_degree (M : CombMap D) (v : D)
    (hloop : M.NoLoopAt v) :
    (M.deleteVertexSet v).card = 2 * M.dartVertexDegree v := by
  classical
  have hdisj :
      Disjoint (M.vertexDarts v) ((M.vertexDarts v).image M.α.toEmbedding) := by
    rw [Finset.disjoint_left]
    intro d hd hdi
    rw [Finset.mem_image] at hdi
    obtain ⟨x, hx, hxd⟩ := hdi
    exact hloop x hx (by simpa [← hxd] using hd)
  rw [deleteVertexSet, Finset.card_union_of_disjoint hdisj]
  have himg :
      ((M.vertexDarts v).image M.α.toEmbedding).card = (M.vertexDarts v).card := by
    simpa using
      Finset.card_image_of_injective (M.vertexDarts v) M.α.injective
  rw [himg]
  simp [dartVertexDegree, Nat.two_mul]

lemma fintype_card_compl_finset (S : Finset D) :
    Fintype.card {d : D // d ∉ S} = Fintype.card D - S.card := by
  classical
  rw [Fintype.card_subtype_compl (fun d : D => d ∈ S)]
  rw [Fintype.card_coe S]

/-- Vertex-count reduction, factored through the exact quotient equivalence
that remains to be proved for the chosen deletion set.

For the closed-star deletion used by `deleteVertex`, this equivalence is not
automatic from `Perm.deleteSet`: deleting the opposite darts of incident edges
also removes darts from neighboring `σ`-orbits.  One must prove that every
nondeleted vertex orbit has a surviving representative and that the deleted
orbit of `v` has none. -/
lemma deleteVertex_V_of_orbitEquiv (M : CombMap D) (v : D)
    (hQ :
      Quotient (cycleSetoid (M.deleteVertex v).σ) ≃
        {Q : Quotient (cycleSetoid M.σ) //
          Q ≠ Quotient.mk (cycleSetoid M.σ) v}) :
    (M.deleteVertex v).V = M.V - 1 := by
  classical
  let qv : Quotient (cycleSetoid M.σ) := Quotient.mk (cycleSetoid M.σ) v
  have hcard :
      Fintype.card {Q : Quotient (cycleSetoid M.σ) // Q ≠ qv}
        = Fintype.card (Quotient (cycleSetoid M.σ)) - 1 := by
    rw [Fintype.card_subtype_compl (fun Q : Quotient (cycleSetoid M.σ) => Q = qv)]
    rw [Fintype.card_subtype_eq qv]
  have hcongr := Fintype.card_congr hQ
  change
      Fintype.card (Quotient (cycleSetoid (M.deleteVertex v).σ)) =
        Fintype.card {Q : Quotient (cycleSetoid M.σ) //
          Q ≠ Quotient.mk (cycleSetoid M.σ) v} at hcongr
  simpa [V, qv] using hcongr.trans hcard

lemma deleteVertex_E (M : CombMap D) (v : D) (hloop : M.NoLoopAt v) :
    (M.deleteVertex v).E = M.E - M.dartVertexDegree v := by
  classical
  let M' := M.deleteVertex v
  have h2E : 2 * M.E = Fintype.card D := two_mul_E_eq_card M
  have h2E' : 2 * M'.E = Fintype.card {d : D // d ∉ M.deleteVertexSet v} :=
    two_mul_E_eq_card M'
  have hcard :
      Fintype.card {d : D // d ∉ M.deleteVertexSet v}
        = Fintype.card D - 2 * M.dartVertexDegree v := by
    rw [fintype_card_compl_finset, deleteVertexSet_card_eq_two_mul_degree M v hloop]
  have h2 : 2 * M'.E = 2 * (M.E - M.dartVertexDegree v) := by
    rw [h2E', hcard, ← h2E]
    omega
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) h2

/-- The faces of `M` touched by the vertex represented by `v`, recorded as
`φ`-orbit quotients. -/
noncomputable def vertexFaces (M : CombMap D) (v : D) :
    Finset (Quotient (cycleSetoid M.φ)) :=
  (M.vertexDarts v).image (fun d => Quotient.mk (cycleSetoid M.φ) d)

/-- The local simple-boundary condition that each dart at `v` lies on a
different face.  Without it, a cut vertex or bridge can make the same face
appear more than once around `v`, so the connected face-count formula is not
`F' = F - deg(v) + 1`. -/
def VertexFacesDistinct (M : CombMap D) (v : D) : Prop :=
  Set.InjOn (fun d => Quotient.mk (cycleSetoid M.φ) d) (M.vertexDarts v : Set D)

lemma vertexFaces_card_eq_degree (M : CombMap D) (v : D)
    (hdistinct : M.VertexFacesDistinct v) :
    (M.vertexFaces v).card = M.dartVertexDegree v := by
  classical
  rw [vertexFaces, dartVertexDegree]
  exact Finset.card_image_of_injOn hdistinct

/-- The quotient-level face model for connected vertex deletion: all faces not
incident with `v` survive, while the faces incident with `v` are replaced by
one merged boundary face.  The hard topological boundary lemma is precisely an
equivalence from the actual deleted-map face quotients to this model. -/
abbrev deleteVertexFaceModel (M : CombMap D) (v : D) :=
  {Q : Quotient (cycleSetoid M.φ) // Q ∉ M.vertexFaces v} ⊕ Unit

/-- Quotient-level statement of the deleted-star boundary lemma for the
connected case. -/
def DeleteVertexFacesMerge (M : CombMap D) (v : D) : Prop :=
  Nonempty
    (Quotient (cycleSetoid (M.deleteVertex v).φ) ≃ M.deleteVertexFaceModel v)

lemma deleteVertexFacesMerge_iff_face_card_eq (M : CombMap D) (v : D) :
    M.DeleteVertexFacesMerge v ↔
      Fintype.card (Quotient (cycleSetoid (M.deleteVertex v).φ)) =
        Fintype.card (M.deleteVertexFaceModel v) := by
  classical
  constructor
  · rintro ⟨e⟩
    exact Fintype.card_congr e
  · intro h
    exact ⟨Fintype.equivOfCardEq h⟩

lemma deleteVertexFaceModel_card (M : CombMap D) (v : D)
    (hdistinct : M.VertexFacesDistinct v) :
    Fintype.card (M.deleteVertexFaceModel v) =
      M.F - M.dartVertexDegree v + 1 := by
  classical
  have hcard := vertexFaces_card_eq_degree M v hdistinct
  change
    Fintype.card
        ({Q : Quotient (cycleSetoid M.φ) // Q ∉ M.vertexFaces v} ⊕ Unit) =
      M.F - M.dartVertexDegree v + 1
  rw [Fintype.card_sum, Fintype.card_unit,
    Fintype.card_subtype_compl (fun Q : Quotient (cycleSetoid M.φ) =>
      Q ∈ M.vertexFaces v),
    Fintype.card_coe, F, hcard]

lemma deleteVertexFacesMerge_of_F_eq (M : CombMap D) (v : D)
    (hdistinct : M.VertexFacesDistinct v)
    (hF : (M.deleteVertex v).F = M.F - M.dartVertexDegree v + 1) :
    M.DeleteVertexFacesMerge v := by
  classical
  rw [deleteVertexFacesMerge_iff_face_card_eq]
  change
    (M.deleteVertex v).F =
      Fintype.card (M.deleteVertexFaceModel v)
  rw [hF, deleteVertexFaceModel_card M v hdistinct]

lemma deleteVertex_F_of_facesMerge (M : CombMap D) (v : D)
    (hdistinct : M.VertexFacesDistinct v)
    (hmerge : M.DeleteVertexFacesMerge v) :
    (M.deleteVertex v).F = M.F - M.dartVertexDegree v + 1 := by
  classical
  rcases hmerge with ⟨e⟩
  change
    Fintype.card (Quotient (cycleSetoid (M.deleteVertex v).φ)) =
      M.F - M.dartVertexDegree v + 1
  exact (Fintype.card_congr e).trans (deleteVertexFaceModel_card M v hdistinct)

lemma dartVertexDegree_le_E (M : CombMap D) (v : D) (hloop : M.NoLoopAt v) :
    M.dartVertexDegree v ≤ M.E := by
  classical
  have hsubset : M.deleteVertexSet v ⊆ Finset.univ := by
    intro d _; exact Finset.mem_univ d
  have hcardle : (M.deleteVertexSet v).card ≤ Fintype.card D := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card hsubset
  have hdel := deleteVertexSet_card_eq_two_mul_degree M v hloop
  have h2E := two_mul_E_eq_card M
  have hmul : 2 * M.dartVertexDegree v ≤ 2 * M.E := by
    rw [← hdel, h2E]
    exact hcardle
  omega

lemma dartVertexDegree_le_F_of_vertexFacesDistinct (M : CombMap D) (v : D)
    (hdistinct : M.VertexFacesDistinct v) :
    M.dartVertexDegree v ≤ M.F := by
  classical
  have hcard := vertexFaces_card_eq_degree M v hdistinct
  have hsubset : M.vertexFaces v ⊆ Finset.univ := by
    intro Q _; exact Finset.mem_univ Q
  have hle : (M.vertexFaces v).card ≤
      Fintype.card (Quotient (cycleSetoid M.φ)) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card hsubset
  simpa [F, hcard] using hle

lemma one_le_V_of_dart (M : CombMap D) (v : D) : 1 ≤ M.V := by
  classical
  have hpos : 0 < Fintype.card (Quotient (cycleSetoid M.σ)) :=
    Fintype.card_pos_iff.mpr ⟨Quotient.mk (cycleSetoid M.σ) v⟩
  simpa [V] using hpos

lemma deleteVertex_eulerChar_of_facesMerge (M : CombMap D) (v : D)
    (hsphereEuler : M.eulerChar = 2) (hloop : M.NoLoopAt v)
    (hQ :
      Quotient (cycleSetoid (M.deleteVertex v).σ) ≃
        {Q : Quotient (cycleSetoid M.σ) //
          Q ≠ Quotient.mk (cycleSetoid M.σ) v})
    (hdistinct : M.VertexFacesDistinct v)
    (hmerge : M.DeleteVertexFacesMerge v) :
    (M.deleteVertex v).eulerChar = 2 := by
  classical
  have hV := deleteVertex_V_of_orbitEquiv M v hQ
  have hE := deleteVertex_E M v hloop
  have hF := deleteVertex_F_of_facesMerge M v hdistinct hmerge
  have hVle : 1 ≤ M.V := one_le_V_of_dart M v
  have hdegE : M.dartVertexDegree v ≤ M.E := dartVertexDegree_le_E M v hloop
  have hdegF : M.dartVertexDegree v ≤ M.F :=
    dartVertexDegree_le_F_of_vertexFacesDistinct M v hdistinct
  unfold eulerChar
  rw [hV, hE, hF]
  unfold eulerChar at hsphereEuler
  omega

/-- Connected-case vertex deletion: assuming the remaining vertex quotient is
exactly the old vertex quotient with `v` removed, and assuming the deleted-star
face quotient really is the connected face-merge model, Euler characteristic is
preserved.  The final `hconn` is the graph-theoretic connectedness of the
deleted map. -/
theorem deleteVertex_isSphereMap (M : CombMap D) (v : D) (hsphere : M.IsSphereMap)
    (hloop : M.NoLoopAt v)
    (hQ :
      Quotient (cycleSetoid (M.deleteVertex v).σ) ≃
        {Q : Quotient (cycleSetoid M.σ) //
          Q ≠ Quotient.mk (cycleSetoid M.σ) v})
    (hdistinct : M.VertexFacesDistinct v)
    (hmerge : M.DeleteVertexFacesMerge v)
    (hconn : (M.deleteVertex v).Connected) :
    (M.deleteVertex v).IsSphereMap := by
  exact
    ⟨hconn,
      deleteVertex_eulerChar_of_facesMerge M v hsphere.2 hloop hQ hdistinct hmerge⟩

/-- Per-component packaging: once a deleted component has been isolated as its
own `CombMap`, the sphere assertion is exactly connectedness plus Euler
characteristic `2`.  Component extraction supplies these two hypotheses. -/
theorem deleteVertex_isSphereMap_per_component
    {D' : Type*} [Fintype D'] [DecidableEq D'] (N : CombMap D')
    (hconn : N.Connected) (heuler : N.eulerChar = 2) :
    N.IsSphereMap := by
  exact ⟨hconn, heuler⟩

section TwoEdgePathObstruction

/-!
The two-edge path is a sphere map with no loop at the middle vertex, but its
closed-star deletion removes every dart.  It is the minimal obstruction showing
that `IsSphereMap` and `NoLoopAt` alone cannot imply the quotient hypotheses
used above.
-/

def twoEdgePathAlpha : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3

def twoEdgePathSigma : Equiv.Perm (Fin 4) :=
  Equiv.swap (1 : Fin 4) 2

def twoEdgePathMap : CombMap (Fin 4) where
  α := twoEdgePathAlpha
  σ := twoEdgePathSigma
  α_invol := by
    ext x
    fin_cases x <;> decide
  α_no_fixed := by
    intro d
    fin_cases d <;> decide

lemma twoEdgePathMap_connected : twoEdgePathMap.Connected := by
  have h01 : twoEdgePathMap.dartStep (0 : Fin 4) 1 := by right; decide
  have h10 : twoEdgePathMap.dartStep (1 : Fin 4) 0 := by right; decide
  have h12 : twoEdgePathMap.dartStep (1 : Fin 4) 2 := by left; decide
  have h21 : twoEdgePathMap.dartStep (2 : Fin 4) 1 := by left; decide
  have h23 : twoEdgePathMap.dartStep (2 : Fin 4) 3 := by right; decide
  have h32 : twoEdgePathMap.dartStep (3 : Fin 4) 2 := by right; decide
  intro a b
  fin_cases a <;> fin_cases b
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h01
  · exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h01) h12
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail (Relation.ReflTransGen.single h01) h12) h23
  · exact Relation.ReflTransGen.single h10
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h12
  · exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h12) h23
  · exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h21) h10
  · exact Relation.ReflTransGen.single h21
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h23
  · exact Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail (Relation.ReflTransGen.single h32) h21) h10
  · exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single h32) h21
  · exact Relation.ReflTransGen.single h32
  · exact Relation.ReflTransGen.refl

lemma twoEdgePathMap_isSphereMap : twoEdgePathMap.IsSphereMap := by
  exact ⟨twoEdgePathMap_connected, by decide⟩

lemma twoEdgePathMap_noLoopAt_middle :
    twoEdgePathMap.NoLoopAt (1 : Fin 4) := by
  intro d hd
  fin_cases d
  · exfalso
    exact (by decide : ¬ twoEdgePathMap.σ.SameCycle (1 : Fin 4) 0)
      (by simpa [vertexDarts] using hd)
  · exact
      (by decide :
        twoEdgePathMap.α (1 : Fin 4) ∉ twoEdgePathMap.vertexDarts (1 : Fin 4))
  · exact
      (by decide :
        twoEdgePathMap.α (2 : Fin 4) ∉ twoEdgePathMap.vertexDarts (1 : Fin 4))
  · exfalso
    exact (by decide : ¬ twoEdgePathMap.σ.SameCycle (1 : Fin 4) 3)
      (by simpa [vertexDarts] using hd)

lemma twoEdgePathMap_deleteVertexSet_middle :
    twoEdgePathMap.deleteVertexSet (1 : Fin 4) = Finset.univ := by
  decide

lemma twoEdgePathMap_not_vertexFacesDistinct_middle :
    ¬ twoEdgePathMap.VertexFacesDistinct (1 : Fin 4) := by
  intro hdistinct
  have h1 : (1 : Fin 4) ∈ twoEdgePathMap.vertexDarts (1 : Fin 4) := by
    exact twoEdgePathMap.self_mem_vertexDarts (1 : Fin 4)
  have h2 : (2 : Fin 4) ∈ twoEdgePathMap.vertexDarts (1 : Fin 4) := by
    simpa [vertexDarts] using
      (by decide : twoEdgePathMap.σ.SameCycle (1 : Fin 4) 2)
  have hface :
      Quotient.mk (cycleSetoid twoEdgePathMap.φ) (1 : Fin 4) =
        Quotient.mk (cycleSetoid twoEdgePathMap.φ) (2 : Fin 4) := by
    exact Quotient.sound (by decide : twoEdgePathMap.φ.SameCycle (1 : Fin 4) 2)
  have h12 : (1 : Fin 4) = 2 := hdistinct h1 h2 hface
  exact (by decide : (1 : Fin 4) ≠ 2) h12

lemma twoEdgePathMap_not_deleteVertex_vertexQuotient_middle :
    ¬ Nonempty
      (Quotient (cycleSetoid (twoEdgePathMap.deleteVertex (1 : Fin 4)).σ) ≃
        {Q : Quotient (cycleSetoid twoEdgePathMap.σ) //
          Q ≠ Quotient.mk (cycleSetoid twoEdgePathMap.σ) (1 : Fin 4)}) := by
  intro hQ
  rcases hQ with ⟨e⟩
  let q0 :
      {Q : Quotient (cycleSetoid twoEdgePathMap.σ) //
        Q ≠ Quotient.mk (cycleSetoid twoEdgePathMap.σ) (1 : Fin 4)} :=
    ⟨Quotient.mk (cycleSetoid twoEdgePathMap.σ) (0 : Fin 4), by
      intro h
      have hsame : twoEdgePathMap.σ.SameCycle (0 : Fin 4) 1 := Quotient.eq.mp h
      exact (by decide : ¬ twoEdgePathMap.σ.SameCycle (0 : Fin 4) 1) hsame⟩
  let q : Quotient (cycleSetoid (twoEdgePathMap.deleteVertex (1 : Fin 4)).σ) :=
    e.symm q0
  obtain ⟨x, _hx⟩ := q.exists_rep
  have hxmem : (x : Fin 4) ∈ twoEdgePathMap.deleteVertexSet (1 : Fin 4) := by
    simp [twoEdgePathMap_deleteVertexSet_middle]
  exact x.2 hxmem

lemma twoEdgePathMap_not_deleteVertexFacesMerge_middle :
    ¬ twoEdgePathMap.DeleteVertexFacesMerge (1 : Fin 4) := by
  intro hmerge
  rcases hmerge with ⟨e⟩
  let q : Quotient (cycleSetoid (twoEdgePathMap.deleteVertex (1 : Fin 4)).φ) :=
    e.symm (Sum.inr ())
  obtain ⟨x, _hx⟩ := q.exists_rep
  have hxmem : (x : Fin 4) ∈ twoEdgePathMap.deleteVertexSet (1 : Fin 4) := by
    simp [twoEdgePathMap_deleteVertexSet_middle]
  exact x.2 hxmem

end TwoEdgePathObstruction

end CombMap

end ProofsInTheBook.PlanarMap
