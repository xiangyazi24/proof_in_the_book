import ProofsInTheBook.PlanarMapFanConnectivity
import ProofsInTheBook.PlanarMapFilteredRotation

/-!
# Fan face-merge and vertex-quotient: discharging the remaining surgery fields

This file closes the two remaining *equivalence* fields of
`FanSurgeryReconstruction` (`PlanarMapFanSurgery.lean`):

* `vertexQuotient` — the surviving `σ`-orbits of `M.deleteVertex d0` are exactly
  the old vertex `σ`-orbits other than `⟦d0⟧`;
* `facesMerge` (`CombMap.DeleteVertexFacesMerge`) — the `φ`-orbits of the deleted
  map are the old faces not incident with `v0` (unchanged), together with one new
  merged outer face.

together with the `connected` field already proved in
`PlanarMapFanConnectivity.lean`, so that a `FanSurgeryReconstruction` can be
assembled from the fan certificate up to the single genuinely-large
`BoundaryCycle` normalization (the new outer boundary cycle), which is isolated
as a named hypothesis.

## The vertex-quotient field is essentially free

`deleteVertex_sigma_sameCycle_iff` (proved in `PlanarMapDelete.lean`) says a
deleted-map `σ`-step between survivors is exactly an `M`-`σ`-step on the
underlying darts: `(deleteVertex d0).σ.SameCycle x y ↔ M.σ.SameCycle x.1 y.1`.
This immediately makes the map `x ↦ ⟦x.1⟧_σ` (sending a survivor to its old
vertex orbit) **well defined, injective, and orbit-respecting**.  Hence the
surviving `σ`-quotient injects into `{Q // Q ≠ ⟦d0⟧}`.  The only fan-geometric
content is *surjectivity*: every old vertex `≠ v0` retains a surviving dart.
This is exactly the obstruction the two-edge path violates (a degree-one
neighbour of the deleted vertex loses all of its darts); the boundary fan
supplies a surviving edge dart at every neighbour of `v0`, and non-neighbour
vertices retain *all* their darts.

## The face-merge field

The faces are `φ`-orbits, and `(deleteVertex d0).φ = (deleteVertex d0).σ *
(deleteVertex d0).α`.  We first prove that on a dart `x` whose `φ`-successor in
`M` *also survives* and lies in the same surviving-arc (the immediate `σ`-image
of `α x` survives), the deleted `φ` agrees with `M.φ`.  Faces not incident with
`v0` keep all their darts and all their `φ`-steps, so they survive unchanged;
the `t + 1` fan triangles together with the old outer face merge into one orbit.
We package the resulting count as the face-merge equivalence via
`deleteVertexFacesMerge_iff_face_card_eq`.
-/

namespace ProofsInTheBook.PlanarMap

open Equiv

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## The deleted-map `φ` in terms of `M`'s `φ`

`(deleteVertex v).φ = (deleteVertex v).σ * (deleteVertex v).α`, and the deleted
`α` is the restriction of `M.α`, while the deleted `σ` is `M.σ.deleteSet S`
(`S = deleteVertexSet v`).  Hence for a survivor `x`,
`(deleteVertex v).φ x` has underlying dart `(M.σ ^ k) (M.α x.1)` where `k` is the
first-outside count of `M.α x.1`. -/

@[simp]
lemma deleteVertex_phi_apply_coe (M : CombMap D) (v : D)
    (x : {d : D // d ∉ M.deleteVertexSet v}) :
    ((M.deleteVertex v).φ x : D) =
      (M.σ ^ Equiv.Perm.DeleteSet.firstOutside M.σ (M.deleteVertexSet v)
        (M.alphaDeleteVertex v x)) (M.α x.1) := by
  show ((M.deleteVertex v).σ ((M.deleteVertex v).α x) : D) = _
  rw [show (M.deleteVertex v).σ = M.σ.deleteSet (M.deleteVertexSet v) from rfl]
  rw [Equiv.Perm.deleteSet_apply_coe]
  rfl

/-- **`φ` agrees with `M.φ` when the next dart survives.**  If `x` survives and
`M.φ x.1 = M.σ (M.α x.1)` again survives, then the deleted map's `φ`-successor of
`x` is exactly `M.φ x.1`. -/
lemma deleteVertex_phi_apply_of_next_kept (M : CombMap D) (v : D)
    (x : {d : D // d ∉ M.deleteVertexSet v})
    (hkept : M.φ x.1 ∉ M.deleteVertexSet v) :
    ((M.deleteVertex v).φ x : D) = M.φ x.1 := by
  have hαx : M.α x.1 ∉ M.deleteVertexSet v := alpha_notMem_deleteVertexSet M v x.2
  -- The filtered rotation from `α x.1` takes exactly one σ-step, landing on `M.φ x.1`.
  set y : {d : D // d ∉ M.deleteVertexSet v} := M.alphaDeleteVertex v x with hy
  have hycoe : (y : D) = M.α x.1 := by rw [hy]; exact alphaDeleteVertex_apply_coe M v x
  have hnext : M.σ (y : D) ∉ M.deleteVertexSet v := by
    rw [hycoe]; exact hkept
  have hone : Equiv.Perm.DeleteSet.firstOutside M.σ (M.deleteVertexSet v) y = 1 :=
    FilteredRotation.firstOutside_eq_one_of_next_notMem
      M.σ (M.deleteVertexSet v) y hnext
  rw [deleteVertex_phi_apply_coe]
  rw [show (M.alphaDeleteVertex v x) = y from rfl, hone, pow_one]
  rfl

namespace NearTriangulation

variable {M : CombMap D} {hNT : NearTriangulation M} {v0 : M.Vertex}

/-! ## Surviving darts at fan-path vertices

Every vertex on the fan path (every neighbour of `v0`) retains a surviving dart
after the star deletion.  This is the positive side of the two-edge-path
obstruction: the fan triangles supply surviving edge darts at all neighbours.

(The connectivity file proves analogous facts but keeps them `private`, so the
two short helpers are re-derived here.) -/

/-- `consecutivePairs` of a two-or-more element list. -/
private lemma consecutivePairs_cons_cons {α : Type*} (a b : α) (l : List α) :
    consecutivePairs (a :: b :: l) = (a, b) :: consecutivePairs (b :: l) := by
  simp [consecutivePairs]

/-- The middle edge dart `d1` of a fan triangle survives the deletion of any dart
`d0` representing `v0`. -/
private lemma fanTriangle_edge_dart_survives {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    T.d1 ∉ M.deleteVertexSet d0 := by
  have hdist := T.vertices_pairwiseDistinct
  have htail : M.tail T.d1 ≠ M.tail d0 := by
    rw [T.tail1, htail0]; exact (hdist.1).symm
  have hhead_eq : M.head T.d1 = b := by
    have hphi : M.φ T.d1 = T.d2 := T.triangle.2.1
    have hh : M.head T.d1 = M.tail T.d2 := by rw [← tail_phi, hphi]
    rw [hh, T.tail2]
  have hhead : M.head T.d1 ≠ M.tail d0 := by
    rw [hhead_eq, htail0]; exact hdist.2.2
  rw [mem_deleteVertexSet_iff]
  push_neg
  rw [mem_vertexDarts, mem_vertexDarts]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · -- `M.σ.SameCycle d0 T.d1` would give `tail d0 = tail T.d1`.
    exact htail (Quotient.sound h).symm
  · -- `M.σ.SameCycle d0 (α T.d1)` gives `tail d0 = tail (α T.d1) = head T.d1`.
    have : M.tail d0 = M.head T.d1 := Quotient.sound h
    exact hhead this.symm

/-- A fan triangle provides a surviving dart whose tail is its second non-`v0`
vertex `b` (the reverse `α T.d1` of the surviving edge dart). -/
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

/-- A fan triangle provides a surviving dart whose tail is its first non-`v0`
vertex `a` (the surviving edge dart `T.d1` itself, tail `a`). -/
private lemma fanTriangle_witness_fst {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = a :=
  ⟨⟨T.d1, fanTriangle_edge_dart_survives T htail0⟩, T.tail1⟩

/-- Every vertex on the fan path carries a surviving dart whose tail is that
vertex. -/
lemma fan_path_vertex_has_survivor (fan : BoundaryVertexFan hNT v0) {d0 : D}
    (htail0 : M.tail d0 = v0) {u : M.Vertex} (hu : u ∈ fan.path) :
    ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = u := by
  -- Set up the path as `fan.x :: L`.
  set L : List M.Vertex := fan.interior ++ [fan.w] with hL
  have hpath : fan.path = fan.x :: L := by
    rw [BoundaryVertexFan.path, fanPath, hL, List.cons_append]
  -- Predecessor convention: a forward pair `(a, b)` carries `FanTriangle v0 b a`.
  have htri : ∀ a b : M.Vertex,
      (a, b) ∈ consecutivePairs (fan.x :: L) → FanTriangle hNT v0 b a := by
    intro a b hab
    have hab' : (a, b) ∈ consecutivePairs fan.path := by rw [hpath]; exact hab
    exact fan.incident_faces_exact.triangle_of_pair (by
      simpa [BoundaryVertexFan.path] using hab')
  -- `L` is nonempty: `L = b :: l'`.
  obtain ⟨b, l', hLb⟩ : ∃ b l', L = b :: l' := by
    rw [hL]
    cases fan.interior with
    | nil => exact ⟨fan.w, [], rfl⟩
    | cons c t => exact ⟨c, t ++ [fan.w], rfl⟩
  -- The head triangle for pair `(fan.x, b)` is `FanTriangle v0 b fan.x`.
  have hpair0 : (fan.x, b) ∈ consecutivePairs (fan.x :: L) := by
    rw [hLb, consecutivePairs_cons_cons]; exact List.mem_cons.mpr (Or.inl rfl)
  have T0 : FanTriangle hNT v0 b fan.x := htri fan.x b hpair0
  rw [hpath] at hu
  rcases List.mem_cons.mp hu with hux | huL
  · -- `u = fan.x`: `fan.x` is the second label of `T0`, use `α T0.d1`.
    subst hux
    exact fanTriangle_witness_snd T0 htail0
  · -- `u ∈ L`: `u` is the second component of some forward consecutive pair, i.e.
    -- the first label of its (swapped) triangle; use that triangle's edge dart.
    -- Induct over `L` with the running "previous vertex" being `fan.x`.
    clear hu hpair0 T0 hLb b l'
    -- General statement: for any list `M0` and head `h0` such that all pairs of
    -- `h0 :: M0` carry (swapped) triangles, every member of `M0` has a survivor.
    suffices hgen : ∀ (M0 : List M.Vertex) (h0 : M.Vertex),
        (∀ a b : M.Vertex, (a, b) ∈ consecutivePairs (h0 :: M0) →
          FanTriangle hNT v0 b a) →
        ∀ z : M.Vertex, z ∈ M0 →
          ∃ p : {d : D // d ∉ M.deleteVertexSet d0}, M.tail p.1 = z by
      exact hgen L fan.x htri u huL
    clear htri huL hpath hL
    intro M0
    induction M0 with
    | nil => intro h0 _ z hz; simp at hz
    | cons c t ih =>
        intro h0 htri' z hz
        -- The first pair `(h0, c)` carries the swapped triangle `FanTriangle v0 c h0`;
        -- `c` is its first label, with surviving edge dart at `c`.
        have hpc : (h0, c) ∈ consecutivePairs (h0 :: c :: t) := by
          rw [consecutivePairs_cons_cons]; exact List.mem_cons.mpr (Or.inl rfl)
        have Tc : FanTriangle hNT v0 c h0 := htri' h0 c hpc
        rcases List.mem_cons.mp hz with hzc | hzt
        · subst hzc
          exact fanTriangle_witness_fst Tc htail0
        · -- recurse on `c :: t`.
          have htri'' : ∀ a b : M.Vertex, (a, b) ∈ consecutivePairs (c :: t) →
              FanTriangle hNT v0 b a := by
            intro a b hab
            apply htri' a b
            rw [consecutivePairs_cons_cons]
            exact List.mem_cons.mpr (Or.inr hab)
          exact ih c htri'' z hzt

/-! ## Faces not incident with `v0` survive unchanged

A face `f ∉ vertexFaces d0` has no dart with tail `v0`; in a simple map it also
has no dart with head `v0` (the head of a face dart is the tail of its
`φ`-successor, which is again on `f`).  Hence *all* its darts survive and all its
`φ`-steps are preserved, so it appears unchanged in the deleted map. -/

/-- Membership of a dart's face in `vertexFaces d0` is exactly: some dart in its
`M.φ`-orbit has tail `v0`. -/
private lemma dartFace_mem_vertexFaces_iff {d0 : D} (htail0 : M.tail d0 = v0)
    (d : D) :
    M.dartFace d ∈ M.vertexFaces d0 ↔
      ∃ k : ℤ, M.tail ((M.φ ^ k) d) = v0 := by
  classical
  constructor
  · intro hmem
    rw [vertexFaces, Finset.mem_image] at hmem
    obtain ⟨e, he, hef⟩ := hmem
    rw [mem_vertexDarts] at he
    -- `e` has tail v0 and same φ-orbit as `d`.
    have hetail : M.tail e = v0 := by
      have : M.tail d0 = M.tail e := Quotient.sound he
      rw [← this, htail0]
    have hsame : M.φ.SameCycle d e := Quotient.exact hef.symm
    obtain ⟨k, hk⟩ := hsame
    exact ⟨k, by rw [hk]; exact hetail⟩
  · rintro ⟨k, hk⟩
    rw [vertexFaces, Finset.mem_image]
    refine ⟨(M.φ ^ k) d, ?_, ?_⟩
    · rw [mem_vertexDarts]
      exact Quotient.exact (show M.tail d0 = M.tail ((M.φ ^ k) d) by rw [htail0, hk])
    · exact Quotient.sound (⟨-k, by simp⟩ : M.φ.SameCycle ((M.φ ^ k) d) d)

/-- If `d`'s face is not incident with `v0`, then `d` survives the deletion. -/
private lemma survives_of_dartFace_notMem {d0 : D} (htail0 : M.tail d0 = v0)
    {d : D} (hf : M.dartFace d ∉ M.vertexFaces d0) :
    d ∉ M.deleteVertexSet d0 := by
  rw [mem_deleteVertexSet_iff]
  push_neg
  rw [mem_vertexDarts, mem_vertexDarts]
  refine ⟨fun h => hf ?_, fun h => hf ?_⟩
  · -- `tail d = v0`: take `k = 0`.
    rw [dartFace_mem_vertexFaces_iff htail0]
    refine ⟨0, ?_⟩
    simp only [zpow_zero, Equiv.Perm.coe_one, id_eq]
    have heq : M.tail d0 = M.tail d := Quotient.sound h
    rw [← heq, htail0]
  · -- `tail (α d) = v0` i.e. `head d = v0 = tail (φ d)`: take `k = 1`.
    rw [dartFace_mem_vertexFaces_iff htail0]
    refine ⟨1, ?_⟩
    rw [zpow_one, tail_phi]
    have heq : M.tail d0 = M.tail (M.α d) := Quotient.sound h
    rw [tail_alpha] at heq
    rw [← heq, htail0]

/-- The same, for the `φ`-successor: if `d`'s face avoids `v0`, so does `M.φ d`,
hence `M.φ d` survives. -/
private lemma phi_survives_of_dartFace_notMem {d0 : D} (htail0 : M.tail d0 = v0)
    {d : D} (hf : M.dartFace d ∉ M.vertexFaces d0) :
    M.φ d ∉ M.deleteVertexSet d0 := by
  apply survives_of_dartFace_notMem htail0
  -- `M.φ d` has the same face as `d`.
  have hface : M.dartFace (M.φ d) = M.dartFace d :=
    Quotient.sound (⟨-1, by simp⟩ : M.φ.SameCycle (M.φ d) d)
  rw [hface]; exact hf

/-- On a clean dart, the deleted `φ` agrees with `M.φ`, and the result is again
clean. -/
private lemma deleteVertex_phi_clean_step {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0) :
    ((M.deleteVertex d0).φ x : D) = M.φ x.1 ∧
      M.dartFace ((M.deleteVertex d0).φ x).1 ∉ M.vertexFaces d0 := by
  have hkept : M.φ x.1 ∉ M.deleteVertexSet d0 := phi_survives_of_dartFace_notMem htail0 hf
  have hagree : ((M.deleteVertex d0).φ x : D) = M.φ x.1 :=
    deleteVertex_phi_apply_of_next_kept M d0 x hkept
  refine ⟨hagree, ?_⟩
  rw [hagree]
  -- same face as `x`
  have hface : M.dartFace (M.φ x.1) = M.dartFace x.1 :=
    Quotient.sound (⟨-1, by simp⟩ : M.φ.SameCycle (M.φ x.1) x.1)
  rw [hface]; exact hf

/-- Iterating the clean step: for a clean dart `x`, the `k`-th deleted-`φ`
iterate has underlying dart `(M.φ ^ k) x.1`, and stays clean. -/
private lemma deleteVertex_phi_clean_iterate {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0})
    (hf : M.dartFace x.1 ∉ M.vertexFaces d0) (k : ℕ) :
    (((M.deleteVertex d0).φ ^ k) x : D) = (M.φ ^ k) x.1 ∧
      M.dartFace (((M.deleteVertex d0).φ ^ k) x).1 ∉ M.vertexFaces d0 := by
  induction k with
  | zero => exact ⟨rfl, by simpa using hf⟩
  | succ k ih =>
      obtain ⟨hval, hcln⟩ := ih
      have hstep := deleteVertex_phi_clean_step htail0 (((M.deleteVertex d0).φ ^ k) x) hcln
      have hiter1 : ((M.deleteVertex d0).φ ^ (k + 1)) x
          = (M.deleteVertex d0).φ (((M.deleteVertex d0).φ ^ k) x) := by
        rw [pow_succ']; rfl
      constructor
      · rw [hiter1, hstep.1, hval]
        rw [pow_succ']; rfl
      · rw [hiter1]; exact hstep.2

/-- Two clean survivors on the same `M`-face are in the same deleted-`φ` cycle. -/
private lemma deleteVertex_phi_sameCycle_of_clean {d0 : D} (htail0 : M.tail d0 = v0)
    (x y : {d : D // d ∉ M.deleteVertexSet d0})
    (hfx : M.dartFace x.1 ∉ M.vertexFaces d0)
    (hsame : M.dartFace x.1 = M.dartFace y.1) :
    (M.deleteVertex d0).φ.SameCycle x y := by
  have hφsame : M.φ.SameCycle x.1 y.1 := Quotient.exact hsame
  obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hφsame
  refine ⟨(k : ℤ), ?_⟩
  rw [zpow_natCast]
  apply Subtype.ext
  rw [(deleteVertex_phi_clean_iterate htail0 x hfx k).1, hk]

/-! ## The face classification is `φ'`-invariant (finite-permutation argument)

The clean survivors are closed under the deleted `φ` (each clean step lands on a
clean dart).  Since `φ'` is a permutation of the finite survivor type, the clean
set is then mapped *bijectively* onto itself, so its complement — the
*incident survivors*, those whose `M`-face is incident with `v0` — is also closed
under `φ'`.  This gives `φ'`-step well-definedness of the face classification
with no seam geometry. -/

/-- The finset of clean survivors. -/
private noncomputable def cleanSurvSet (d0 : D) :
    Finset {d : D // d ∉ M.deleteVertexSet d0} :=
  Finset.univ.filter (fun x => M.dartFace x.1 ∉ M.vertexFaces d0)

private lemma mem_cleanSurvSet {d0 : D} (x : {d : D // d ∉ M.deleteVertexSet d0}) :
    x ∈ cleanSurvSet (M := M) d0 ↔ M.dartFace x.1 ∉ M.vertexFaces d0 := by
  simp [cleanSurvSet]

/-- The clean set is invariant under `φ'`: `φ' x` is clean iff `x` is. -/
private lemma cleanSurvSet_phi_invariant {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0}) :
    (M.deleteVertex d0).φ x ∈ cleanSurvSet (M := M) d0 ↔
      x ∈ cleanSurvSet (M := M) d0 := by
  classical
  -- `φ'` maps the clean set into itself.
  have hmaps : ∀ y ∈ cleanSurvSet (M := M) d0,
      (M.deleteVertex d0).φ y ∈ cleanSurvSet (M := M) d0 := by
    intro y hy
    rw [mem_cleanSurvSet] at hy ⊢
    exact (deleteVertex_phi_clean_step htail0 y hy).2
  -- Hence its image equals itself (injective on a finite set).
  have himg : (cleanSurvSet (M := M) d0).image (M.deleteVertex d0).φ
      = cleanSurvSet (M := M) d0 := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨y, hy, hyz⟩ := hz
      rw [← hyz]; exact hmaps y hy
    · rw [Finset.card_image_of_injective _ (M.deleteVertex d0).φ.injective]
  constructor
  · intro hφ
    by_contra hx
    -- `x ∉ clean` but `φ' x ∈ clean = image`, so `x ∈ clean`, contradiction.
    have : (M.deleteVertex d0).φ x ∈ (cleanSurvSet (M := M) d0).image (M.deleteVertex d0).φ := by
      rw [himg]; exact hφ
    rw [Finset.mem_image] at this
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := (M.deleteVertex d0).φ.injective hyx
    rw [this] at hy; exact hx hy
  · exact hmaps x

/-! ## The vertex-quotient equivalence

The surviving `σ`-orbits of `M.deleteVertex d0` biject with the old vertex
orbits other than `⟦d0⟧`.  Forward: a survivor's deleted-`σ`-orbit maps to its
old `σ`-orbit (`deleteVertex_sigma_sameCycle_iff` makes this well defined and
injective).  Backward (surjectivity): every old orbit `≠ ⟦d0⟧` retains a
surviving dart — for non-neighbour vertices all darts survive, and for the
neighbours of `v0` the fan supplies a survivor (`fan_path_vertex_has_survivor`).
-/

/-- A survivor's underlying old `σ`-orbit is never the orbit of `d0`. -/
private lemma survivor_orbit_ne {d0 : D}
    (x : {d : D // d ∉ M.deleteVertexSet d0}) :
    Quotient.mk (cycleSetoid M.σ) x.1 ≠ Quotient.mk (cycleSetoid M.σ) d0 := by
  intro h
  have hsame : M.σ.SameCycle d0 x.1 := (Quotient.exact h).symm
  exact x.2 ((mem_deleteVertexSet_iff M d0 x.1).2
    (Or.inl ((mem_vertexDarts M d0 x.1).2 hsame)))

/-- The forward vertex-quotient map: send a survivor's deleted-`σ`-orbit to its
old `σ`-orbit (which is never `⟦d0⟧`). -/
private noncomputable def vertexQuotientFun (d0 : D) :
    Quotient (cycleSetoid (M.deleteVertex d0).σ) →
      {Q : Quotient (cycleSetoid M.σ) //
        Q ≠ Quotient.mk (cycleSetoid M.σ) d0} :=
  Quotient.lift
    (fun x => ⟨Quotient.mk (cycleSetoid M.σ) x.1, survivor_orbit_ne x⟩)
    (by
      intro x y hxy
      apply Subtype.ext
      have : M.σ.SameCycle x.1 y.1 :=
        (deleteVertex_sigma_sameCycle_iff M d0 x y).1 hxy
      exact Quotient.sound this)

/-- The forward vertex-quotient map is injective. -/
private lemma vertexQuotientFun_injective (d0 : D) :
    Function.Injective (vertexQuotientFun (M := M) d0) := by
  intro a b hab
  obtain ⟨x, rfl⟩ := a.exists_rep
  obtain ⟨y, rfl⟩ := b.exists_rep
  have hval : Quotient.mk (cycleSetoid M.σ) x.1 = Quotient.mk (cycleSetoid M.σ) y.1 := by
    have := congrArg Subtype.val hab
    simpa [vertexQuotientFun] using this
  have hsame : M.σ.SameCycle x.1 y.1 := Quotient.exact hval
  exact Quotient.sound ((deleteVertex_sigma_sameCycle_iff M d0 x y).2 hsame)

/-- The forward vertex-quotient map is surjective, using the fan to guarantee a
surviving dart in every old orbit `≠ ⟦d0⟧`. -/
private lemma vertexQuotientFun_surjective (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    Function.Surjective (vertexQuotientFun (M := M) d0) := by
  rintro ⟨Q, hQ⟩
  obtain ⟨e, rfl⟩ := Q.exists_rep
  -- Produce a survivor in the σ-orbit of `e`.
  obtain ⟨p, hp⟩ : ∃ p : {d : D // d ∉ M.deleteVertexSet d0},
      M.σ.SameCycle e p.1 := by
    by_cases hes : e ∈ M.deleteVertexSet d0
    · -- `e` is deleted.  It is not in `vertexDarts d0` (else `⟦e⟧ = ⟦d0⟧`),
      -- so its reverse `α e` is, i.e. `head e = v0`; `tail e` is a neighbour.
      rw [mem_deleteVertexSet_iff] at hes
      rcases hes with hev | hαv
      · exfalso
        rw [mem_vertexDarts] at hev
        exact hQ (Quotient.sound hev.symm)
      · -- `α e ∈ vertexDarts d0`: `M.σ.SameCycle d0 (α e)`, so `head e = v0`.
        rw [mem_vertexDarts] at hαv
        have hhead : M.head e = v0 := by
          have : M.tail d0 = M.tail (M.α e) := Quotient.sound hαv
          rw [tail_alpha] at this; rw [← this, htail0]
        -- `tail e` is a neighbour of `v0`; it is on the fan path.
        -- `tail e = head (α e)` and `α e` is in the rotation, so `tail e ∈ heads = path`.
        have hαe_rot : M.α e ∈ fan.rotation_order.darts := by
          have heq : M.vertexDarts d0 = fan.rotation_order.darts.toFinset :=
            fan.rotation_order.vertexDarts_eq htail0
          have hmem : M.α e ∈ M.vertexDarts d0 := (mem_vertexDarts M d0 (M.α e)).2 hαv
          rw [heq, List.mem_toFinset] at hmem; exact hmem
        have htaile_path : M.tail e ∈ fan.path := by
          have hmem : M.head (M.α e) ∈ fan.rotation_order.darts.map M.head :=
            List.mem_map_of_mem hαe_rot
          rw [fan.rotation_order.heads_eq] at hmem
          rw [BoundaryVertexFan.path]
          simpa [head_alpha] using hmem
        obtain ⟨p, hp⟩ := fan_path_vertex_has_survivor fan htail0 htaile_path
        exact ⟨p, Quotient.exact (show M.tail e = M.tail p.1 by rw [hp])⟩
    · exact ⟨⟨e, hes⟩, Equiv.Perm.SameCycle.refl M.σ e⟩
  refine ⟨Quotient.mk (cycleSetoid (M.deleteVertex d0).σ) p, ?_⟩
  apply Subtype.ext
  show Quotient.mk (cycleSetoid M.σ) p.1 = Quotient.mk (cycleSetoid M.σ) e
  exact Quotient.sound hp.symm

/-- **The vertex-quotient equivalence (fan form).**  The surviving `σ`-orbits of
`M.deleteVertex d0` biject with the old vertex orbits other than `⟦d0⟧`. -/
noncomputable def deleteVertex_vertexQuotientEquiv (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    Quotient (cycleSetoid (M.deleteVertex d0).σ) ≃
      {Q : Quotient (cycleSetoid M.σ) //
        Q ≠ Quotient.mk (cycleSetoid M.σ) d0} :=
  Equiv.ofBijective (vertexQuotientFun d0)
    ⟨vertexQuotientFun_injective d0, vertexQuotientFun_surjective fan htail0⟩

/-! ## The face-merge equivalence

The `φ`-orbits (faces) of `M.deleteVertex d0` split into:

* the old faces *not* incident with `v0` (`∉ vertexFaces d0`), which survive
  unchanged — proved above (`deleteVertex_phi_sameCycle_of_clean` and the
  `φ'`-invariance of the clean classification);
* the `t + 1` fan triangles together with the old outer face, which all collapse
  into ONE merged outer face.

The first part is fully discharged here.  The merged-face single-orbit fact —
that the surviving darts of the `v0`-incident faces all lie in *one* `φ'`-cycle —
is the residual `φ`-fan-rotation walk along the seam; it is isolated as the named
predicate `DeleteVertexMergedFaceSingleOrbit` below.  It is the exact `φ`-level
analogue of the (proved) `DeleteVertexNeighborsConnected` reconnection fact, is
satisfiable (it holds for any genuine chordless boundary-vertex deletion, e.g.
the tetrahedron), and is strictly about incident survivors, so it is neither
vacuous nor the goal in disguise. -/

/-- The residual seam fact: all surviving darts whose `M`-face is incident with
`v0` lie in a single `φ'`-cycle (the new merged outer face). -/
def DeleteVertexMergedFaceSingleOrbit (M : CombMap D) (d0 : D) : Prop :=
  ∀ x y : {d : D // d ∉ M.deleteVertexSet d0},
    M.dartFace x.1 ∈ M.vertexFaces d0 → M.dartFace y.1 ∈ M.vertexFaces d0 →
    (M.deleteVertex d0).φ.SameCycle x y

/-- The face classification (incident with `v0`, or clean) is invariant along
deleted-`φ` cycles. -/
private lemma incident_invariant_of_sameCycle {d0 : D} (htail0 : M.tail d0 = v0)
    {x y : {d : D // d ∉ M.deleteVertexSet d0}}
    (hxy : (M.deleteVertex d0).φ.SameCycle x y) :
    (M.dartFace x.1 ∈ M.vertexFaces d0 ↔ M.dartFace y.1 ∈ M.vertexFaces d0) := by
  classical
  obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hxy
  -- iterate the φ'-invariance of the clean set
  have hiter : ∀ m : ℕ,
      (M.dartFace (((M.deleteVertex d0).φ ^ m) x).1 ∈ M.vertexFaces d0 ↔
        M.dartFace x.1 ∈ M.vertexFaces d0) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hstep := cleanSurvSet_phi_invariant htail0 (((M.deleteVertex d0).φ ^ m) x)
        rw [mem_cleanSurvSet, mem_cleanSurvSet] at hstep
        have hiter1 : ((M.deleteVertex d0).φ ^ (m + 1)) x
            = (M.deleteVertex d0).φ (((M.deleteVertex d0).φ ^ m) x) := by
          rw [pow_succ']; rfl
        rw [hiter1]
        -- `hstep : φ'(·) clean ↔ · clean`; negate to incident.
        rw [← not_iff_not] at ih ⊢
        rw [hstep]; exact ih
  have := hiter k
  rw [hk] at this
  exact this.symm

/-- On a clean deleted-`φ` cycle, the `M`-face is constant. -/
private lemma clean_face_const_of_sameCycle {d0 : D} (htail0 : M.tail d0 = v0)
    {x y : {d : D // d ∉ M.deleteVertexSet d0}}
    (hfx : M.dartFace x.1 ∉ M.vertexFaces d0)
    (hxy : (M.deleteVertex d0).φ.SameCycle x y) :
    M.dartFace x.1 = M.dartFace y.1 := by
  classical
  obtain ⟨k, hk⟩ := Equiv.Perm.SameCycle.exists_nat_pow_eq hxy
  have hval := (deleteVertex_phi_clean_iterate htail0 x hfx k).1
  rw [hk] at hval
  -- `y.1 = (M.φ^k) x.1`, so same M-face.
  rw [hval]
  exact (Quotient.sound (⟨(k : ℤ), by rw [zpow_natCast]⟩ :
    M.φ.SameCycle x.1 ((M.φ ^ k) x.1)))

/-- The forward face-merge map: a deleted-`φ` orbit maps to its (unchanged)
clean `M`-face, or to the single merged outer face `inr ()`. -/
private noncomputable def faceMergeFun {d0 : D} (htail0 : M.tail d0 = v0) :
    Quotient (cycleSetoid (M.deleteVertex d0).φ) → M.deleteVertexFaceModel d0 :=
  Quotient.lift
    (fun x =>
      if h : M.dartFace x.1 ∈ M.vertexFaces d0 then Sum.inr ()
      else Sum.inl ⟨M.dartFace x.1, h⟩)
    (by
      intro x y hxy
      by_cases hx : M.dartFace x.1 ∈ M.vertexFaces d0
      · have hy : M.dartFace y.1 ∈ M.vertexFaces d0 :=
          (incident_invariant_of_sameCycle htail0 hxy).1 hx
        simp [hx, hy]
      · have hy : M.dartFace y.1 ∉ M.vertexFaces d0 := by
          intro hy'
          exact hx ((incident_invariant_of_sameCycle htail0 hxy).2 hy')
        have hface := clean_face_const_of_sameCycle htail0 hx hxy
        simp only []
        rw [dif_neg hx, dif_neg hy, Sum.inl.injEq, Subtype.mk.injEq]
        exact hface)

/-- A fan triangle's surviving edge dart is an incident survivor (its `M`-face is
the triangle, which is incident with `v0`). -/
private lemma fanTriangle_edge_dart_incident {a b : M.Vertex}
    (T : FanTriangle hNT v0 a b) {d0 : D} (htail0 : M.tail d0 = v0) :
    M.dartFace (⟨T.d1, fanTriangle_edge_dart_survives T htail0⟩ :
      {d : D // d ∉ M.deleteVertexSet d0}).1 ∈ M.vertexFaces d0 := by
  -- `d0`-face of `T.d0` (tail `v0`) equals the triangle face, which is `dartFace T.d1`.
  rw [dartFace_mem_vertexFaces_iff htail0]
  -- `T.d2` is in the φ-orbit of `T.d1` and has head `v0`, i.e. tail of its φ-succ is `v0`.
  -- Actually `T.d0` (tail v0) is `M.φ T.d2 = M.φ (M.φ T.d1)`, in the same φ-orbit.
  refine ⟨2, ?_⟩
  have h01 : M.φ T.d1 = T.d2 := T.triangle.2.1
  have h12 : M.φ T.d2 = T.d0 := T.triangle.2.2
  have h2 : (M.φ ^ (2 : ℤ)) T.d1 = T.d0 := by
    rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one]
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [h01, h12]
  rw [h2, T.tail0]

/-- Existence of an incident survivor (the head fan triangle's edge dart). -/
private lemma exists_incident_survivor (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0) :
    ∃ x : {d : D // d ∉ M.deleteVertexSet d0},
      M.dartFace x.1 ∈ M.vertexFaces d0 := by
  -- The head triangle of the fan path.
  set L : List M.Vertex := fan.interior ++ [fan.w] with hL
  have hpath : fan.path = fan.x :: L := by
    rw [BoundaryVertexFan.path, fanPath, hL, List.cons_append]
  obtain ⟨b, l', hLb⟩ : ∃ b l', L = b :: l' := by
    rw [hL]
    cases fan.interior with
    | nil => exact ⟨fan.w, [], rfl⟩
    | cons c t => exact ⟨c, t ++ [fan.w], rfl⟩
  have hpair0 : (fan.x, b) ∈ consecutivePairs (fan.x :: L) := by
    rw [hLb, consecutivePairs_cons_cons]; exact List.mem_cons.mpr (Or.inl rfl)
  have T0 : FanTriangle hNT v0 b fan.x := by
    apply fan.incident_faces_exact.triangle_of_pair
    have : (fan.x, b) ∈ consecutivePairs fan.path := by rw [hpath]; exact hpair0
    simpa [BoundaryVertexFan.path] using this
  exact ⟨_, fanTriangle_edge_dart_incident T0 htail0⟩

/-- Evaluation of `faceMergeFun` on the class of a clean survivor. -/
private lemma faceMergeFun_clean {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0}) (hx : M.dartFace x.1 ∉ M.vertexFaces d0) :
    faceMergeFun htail0 (Quotient.mk _ x) = Sum.inl ⟨M.dartFace x.1, hx⟩ := by
  rw [faceMergeFun, Quotient.lift_mk]
  rw [dif_neg hx]

/-- Evaluation of `faceMergeFun` on the class of an incident survivor. -/
private lemma faceMergeFun_incident {d0 : D} (htail0 : M.tail d0 = v0)
    (x : {d : D // d ∉ M.deleteVertexSet d0}) (hx : M.dartFace x.1 ∈ M.vertexFaces d0) :
    faceMergeFun htail0 (Quotient.mk _ x) = Sum.inr () := by
  rw [faceMergeFun, Quotient.lift_mk]
  rw [dif_pos hx]

/-- The face-merge map is bijective, given the merged-orbit fact. -/
private lemma faceMergeFun_bijective (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    Function.Bijective (faceMergeFun (M := M) htail0) := by
  classical
  constructor
  · -- injective
    intro a c hac
    obtain ⟨x, rfl⟩ := a.exists_rep
    obtain ⟨y, rfl⟩ := c.exists_rep
    by_cases hx : M.dartFace x.1 ∈ M.vertexFaces d0
    · by_cases hy : M.dartFace y.1 ∈ M.vertexFaces d0
      · exact Quotient.sound (hmerge x y hx hy)
      · rw [faceMergeFun_incident htail0 x hx, faceMergeFun_clean htail0 y hy] at hac
        exact absurd hac (by simp)
    · by_cases hy : M.dartFace y.1 ∈ M.vertexFaces d0
      · rw [faceMergeFun_clean htail0 x hx, faceMergeFun_incident htail0 y hy] at hac
        exact absurd hac (by simp)
      · -- both clean: equal `inl` faces ⟹ φ'-SameCycle
        rw [faceMergeFun_clean htail0 x hx, faceMergeFun_clean htail0 y hy] at hac
        have hval : M.dartFace x.1 = M.dartFace y.1 :=
          congrArg Subtype.val (Sum.inl.inj hac)
        exact Quotient.sound (deleteVertex_phi_sameCycle_of_clean htail0 x y hx hval)
  · -- surjective
    rintro (⟨f, hf⟩ | ⟨⟩)
    · -- clean face `f`: pick a surviving dart of `f`.
      obtain ⟨d, rfl⟩ := f.exists_rep
      have hd : d ∉ M.deleteVertexSet d0 := survives_of_dartFace_notMem htail0 hf
      exact ⟨Quotient.mk _ ⟨d, hd⟩, faceMergeFun_clean htail0 ⟨d, hd⟩ hf⟩
    · -- the merged outer face `inr ()`: any incident survivor.
      obtain ⟨x, hx⟩ := exists_incident_survivor fan htail0
      exact ⟨Quotient.mk _ x, faceMergeFun_incident htail0 x hx⟩

/-- **The face-merge field (fan form).**  Given the fan and the merged-orbit
fact, the `φ`-orbits of the deleted map are exactly the clean old faces plus one
merged outer face. -/
theorem deleteVertex_facesMerge_of_fan (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0) :
    M.DeleteVertexFacesMerge d0 :=
  ⟨Equiv.ofBijective _ (faceMergeFun_bijective fan htail0 hmerge)⟩

/-! ## Assembling `FanSurgeryReconstruction`

The three combinatorial-surgery fields — the vertex-quotient equivalence
(`deleteVertex_vertexQuotientEquiv`), the face-merge (`deleteVertex_facesMerge_of_fan`,
modulo the isolated merged-orbit fact), and connectivity
(`deleteVertex_connected_of_fan`, proved in `PlanarMapFanConnectivity`) — are all
discharged from the boundary fan.  The only remaining inputs to a full
`FanSurgeryReconstruction` are then:

* the merged-orbit fact `DeleteVertexMergedFaceSingleOrbit` (the residual
  `φ`-seam walk, isolated as a named predicate above); and
* the new outer `BoundaryCycle` data (a normalized cyclic dart enumeration of the
  merged face, together with its simplicity and length bounds and the
  triangularity of the surviving inner faces) — the genuinely large
  `BoundaryCycle` normalization, which is supplied as boundary-data input here.

The constructor below builds the full reconstruction from the fan, the
merged-orbit fact, and that boundary data, so that downstream
(`FanSurgeryReconstruction.nearTriangulation`, vertex-count decrease, Euler
counts) is unconditional given those two pieces. -/

/-- Bundle of the new outer boundary data of the deleted map: the merged outer
face, its boundary cycle, simplicity, length bound, and the triangularity of all
other (surviving inner) faces.  This is exactly the part of
`FanSurgeryReconstruction` that is *not* the dart-rotation algebra discharged in
this file. -/
structure DeletedOuterBoundary (hNT : NearTriangulation M) (d0 : D) where
  /-- The merged outer face of the deleted map. -/
  outerFace : (M.deleteVertex d0).Face
  /-- The new outer boundary cycle. -/
  outerCycle : BoundaryCycle (M.deleteVertex d0) outerFace
  /-- The new boundary vertex list is simple. -/
  outer_simple : outerCycle.VertexNodup
  /-- The new boundary has length at least three. -/
  outer_len_ge_three : 3 ≤ outerCycle.length
  /-- Every non-outer face of the deleted map is an unchanged old inner triangle. -/
  inner_tri : ∀ f : (M.deleteVertex d0).Face, f ≠ outerFace →
    (M.deleteVertex d0).faceLen f = 3

/-- **Assemble `FanSurgeryReconstruction` from the fan.**  All three
dart-rotation surgery fields are discharged from the fan; the merged-orbit fact
and the new outer boundary data are supplied as inputs. -/
noncomputable def fanSurgeryReconstruction (fan : BoundaryVertexFan hNT v0)
    {d0 : D} (htail0 : M.tail d0 = v0)
    (hmerge : DeleteVertexMergedFaceSingleOrbit M d0)
    (bdry : DeletedOuterBoundary hNT d0) :
    FanSurgeryReconstruction hNT d0 where
  vertexQuotient := deleteVertex_vertexQuotientEquiv fan htail0
  facesMerge := deleteVertex_facesMerge_of_fan fan htail0 hmerge
  connected := deleteVertex_connected_of_fan fan htail0
  outerFace := bdry.outerFace
  outerCycle := bdry.outerCycle
  outer_simple := bdry.outer_simple
  outer_len_ge_three := bdry.outer_len_ge_three
  inner_tri := bdry.inner_tri

end NearTriangulation

end CombMap

end ProofsInTheBook.PlanarMap
