import ProofsInTheBook.Ch13ComponentClose
import ProofsInTheBook.ChordFaceCount
import ProofsInTheBook.PlanarMapSimple

/-!
# Face-diagonal surgery for combinatorial maps

This file packages the fresh-dart adjunction as an internal face diagonal.
The implemented diagonal uses the same anchor convention as the chord-side
maps: if the chosen face darts are `d0` and `d1`, the fresh darts are spliced
after `σ⁻¹ d0` and `σ⁻¹ d1`.  Thus the fresh edge has endpoints
`tail d0` and `tail d1`, while the face permutation is cut immediately before
`d0` and `d1`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ProofsInTheBook.PlanarMap.CombMap

open ProofsInTheBook.PlanarMap
open ProofsInTheBook.PlanarMap.FilteredRotation
open ProofsInTheBook.ChordSplitEuler
open ProofsInTheBook.ChordFaceCount
open ProofsInTheBook.ChordSideRecon

universe u

variable {D : Type u} [Fintype D] [DecidableEq D]

/-- A choice of two non-adjacent boundary darts of a common face whose tail
vertices can be joined by a new diagonal edge.  The field
`nonadjacent_on_face` records the local boundary bookkeeping: the two cut
locations are not consecutive in either direction on the selected face. -/
structure FaceDiagonalChoice (M : CombMap D) where
  f : M.Face
  d0 : D
  d1 : D
  same_face : M.dartFace d0 = f
  same_face' : M.dartFace d1 = f
  endpoints_distinct : M.tail d0 ≠ M.tail d1
  no_existing_edge : ¬ M.toSimpleGraph.Adj (M.tail d0) (M.tail d1)
  nonadjacent_on_face : M.φ d0 ≠ d1 ∧ M.φ d1 ≠ d0

namespace FaceDiagonalChoice

variable {M : CombMap D} (c : FaceDiagonalChoice M)

/-- First splice anchor: the dart whose `σ`-successor is the first chosen
face dart. -/
def anchor0 : D :=
  M.σ.symm c.d0

/-- Second splice anchor: the dart whose `σ`-successor is the second chosen
face dart. -/
def anchor1 : D :=
  M.σ.symm c.d1

@[simp] lemma sigma_anchor0 : M.σ c.anchor0 = c.d0 := by
  simp [anchor0]

@[simp] lemma sigma_anchor1 : M.σ c.anchor1 = c.d1 := by
  simp [anchor1]

lemma tail_anchor0 : M.tail c.anchor0 = M.tail c.d0 := by
  have h := M.tail_sigma (M.σ.symm c.d0)
  simpa [anchor0] using h.symm

lemma tail_anchor1 : M.tail c.anchor1 = M.tail c.d1 := by
  have h := M.tail_sigma (M.σ.symm c.d1)
  simpa [anchor1] using h.symm

/-- The two splice anchors are distinct because their tail vertices are
distinct. -/
lemma anchors_ne : c.anchor0 ≠ c.anchor1 := by
  intro h
  apply c.endpoints_distinct
  calc
    M.tail c.d0 = M.tail c.anchor0 := (c.tail_anchor0).symm
    _ = M.tail c.anchor1 := by rw [h]
    _ = M.tail c.d1 := c.tail_anchor1

/-- The selected darts lie in the same old face orbit. -/
lemma same_face_sameCycle : M.φ.SameCycle c.d0 c.d1 := by
  change (cycleSetoid M.φ).r c.d0 c.d1
  apply Quotient.exact
  exact c.same_face.trans c.same_face'.symm

/-- The same-face condition in the exact form consumed by
`freshMap_F_same_face`. -/
lemma keptPhi_anchor_successors_sameCycle :
    (keptPhi M.α M.σ).SameCycle (M.σ c.anchor0) (M.σ c.anchor1) := by
  simpa [keptPhi, CombMap.φ] using c.same_face_sameCycle

end FaceDiagonalChoice

/-- Add one internal face diagonal by the generic fresh-dart adjunction. -/
noncomputable def addFaceDiagonal (M : CombMap D) (c : FaceDiagonalChoice M) :
    CombMap (D ⊕ Fin 2) :=
  freshMap M.α M.σ M.α_invol M.α_no_fixed c.anchor0 c.anchor1 c.anchors_ne

/-- Face excess: total surplus over triangular faces. -/
noncomputable def faceExcess (M : CombMap D) : ℕ :=
  ∑ f : M.Face, (M.faceLen f - 3)

theorem faceExcess_eq_two_mul_E_sub_three_mul_F
    (M : CombMap D) (h3 : M.FaceLengthGe 3) :
    faceExcess M = 2 * M.E - 3 * M.F := by
  unfold faceExcess
  have hsum := Finset.sum_tsub_distrib (s := (Finset.univ : Finset M.Face))
    (f := fun Q : M.Face => M.faceLen Q) (g := fun _ : M.Face => 3)
    (by intro Q _; exact h3 Q)
  calc
    (∑ Q : M.Face, (M.faceLen Q - 3))
        = (∑ Q : M.Face, M.faceLen Q) - Fintype.card M.Face * 3 := by
          simpa using hsum
    _ = 2 * M.E - 3 * M.F := by
          rw [sum_faceLen]
          simp [CombMap.F, Nat.mul_comm]

lemma sameCycle_mem_triple_of_phi_cube {p : Equiv.Perm D} {d e : D}
    (hcube : p (p (p d)) = d) (h : p.SameCycle d e) :
    e = d ∨ e = p d ∨ e = p (p d) := by
  obtain ⟨i, hi⟩ := h
  have hinv0 : p.symm d = p (p d) := by
    rw [Equiv.symm_apply_eq]
    exact hcube.symm
  have hinv1 : p.symm (p d) = d := by
    rw [Equiv.symm_apply_eq]
  have hinv2 : p.symm (p (p d)) = p d := by
    rw [Equiv.symm_apply_eq]
  have key : ∀ k : ℤ, (p ^ k) d = d ∨ (p ^ k) d = p d ∨
      (p ^ k) d = p (p d) := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · left
      simp
    · intro n ih
      rw [show ((n : ℤ) + 1) = 1 + (n : ℤ) by ring, zpow_add, zpow_one,
        Equiv.Perm.mul_apply]
      rcases ih with h0 | h1 | h2
      · right
        left
        rw [h0]
      · right
        right
        rw [h1]
      · left
        rw [h2]
        exact hcube
    · intro n ih
      have hstep : (p ^ (-(n : ℤ) - 1)) d = p.symm ((p ^ (-(n : ℤ))) d) := by
        rw [show (-(n : ℤ) - 1) = (-1) + (-(n : ℤ)) by ring, zpow_add,
          Equiv.Perm.mul_apply, show (p ^ (-1 : ℤ)) = p.symm from by
            rw [zpow_neg, zpow_one]
            rfl]
      rw [hstep]
      rcases ih with h0 | h1 | h2
      · rw [h0]
        right
        right
        exact hinv0
      · rw [h1]
        left
        exact hinv1
      · rw [h2]
        right
        left
        exact hinv2
  rcases key i with h0 | h1 | h2
  · left
    rw [← hi, h0]
  · right
    left
    rw [← hi, h1]
  · right
    right
    rw [← hi, h2]

namespace FaceDiagonal

variable (M : CombMap D) (c : FaceDiagonalChoice M)

/-- The old vertices embed into the fresh map by sending an old dart orbit to
the corresponding `inl` fresh-rotation orbit. -/
noncomputable def includeVertex :
    M.Vertex → (addFaceDiagonal M c).Vertex :=
  Quotient.lift
    (fun d : D =>
      Quotient.mk (cycleSetoid (addFaceDiagonal M c).σ) (Sum.inl d))
    (by
      intro d e hde
      apply Quotient.sound
      change (freshSigma M.σ c.anchor0 c.anchor1 c.anchors_ne).SameCycle
        (Sum.inl d) (Sum.inl e)
      rw [freshSigma_sameCycle_iff M.σ c.anchors_ne]
      simpa using hde)

@[simp] lemma includeVertex_tail (d : D) :
    includeVertex M c (M.tail d)
      = (addFaceDiagonal M c).tail (Sum.inl d) :=
  rfl

/-- The old-vertex embedding is injective. -/
theorem includeVertex_injective :
    Function.Injective (includeVertex M c) := by
  intro x y hxy
  refine Quotient.inductionOn₂ x y ?_ hxy
  intro d e hde
  have hfresh :
      (freshSigma M.σ c.anchor0 c.anchor1 c.anchors_ne).SameCycle
        (Sum.inl d) (Sum.inl e) := by
    exact Quotient.exact hde
  have hold : M.σ.SameCycle d e := by
    have hproj := (freshSigma_sameCycle_iff M.σ c.anchors_ne
      (Sum.inl d) (Sum.inl e)).1 hfresh
    simpa using hproj
  exact Quotient.sound hold

lemma includeVertex_head (d : D) :
    includeVertex M c (M.head d)
      = (addFaceDiagonal M c).head (Sum.inl d) := by
  rfl

/-- Collapse a fresh-map vertex back to the old vertex containing its anchor
projection. -/
noncomputable def vertexToOld :
    (addFaceDiagonal M c).Vertex → M.Vertex :=
  Quotient.lift
    (fun x : D ⊕ Fin 2 => M.tail (proj c.anchor0 c.anchor1 x))
    (by
      intro x y hxy
      have hsc :
          (freshSigma M.σ c.anchor0 c.anchor1 c.anchors_ne).SameCycle x y := by
        simpa [addFaceDiagonal] using hxy
      have hproj : M.σ.SameCycle
          (proj c.anchor0 c.anchor1 x) (proj c.anchor0 c.anchor1 y) :=
        (freshSigma_sameCycle_iff M.σ c.anchors_ne x y).1 hsc
      exact Quotient.sound hproj)

@[simp] lemma vertexToOld_tail (x : D ⊕ Fin 2) :
    vertexToOld M c ((addFaceDiagonal M c).tail x)
      = M.tail (proj c.anchor0 c.anchor1 x) :=
  rfl

@[simp] lemma vertexToOld_head (x : D ⊕ Fin 2) :
    vertexToOld M c ((addFaceDiagonal M c).head x)
      = M.tail (proj c.anchor0 c.anchor1 ((addFaceDiagonal M c).α x)) :=
  rfl

@[simp] lemma vertexToOld_tail_inl (d : D) :
    vertexToOld M c ((addFaceDiagonal M c).tail (Sum.inl d)) = M.tail d := by
  simp [vertexToOld_tail, proj]

@[simp] lemma vertexToOld_head_inl (d : D) :
    vertexToOld M c ((addFaceDiagonal M c).head (Sum.inl d)) = M.head d := by
  rw [vertexToOld_head]
  simp [addFaceDiagonal, proj, CombMap.head]

@[simp] lemma vertexToOld_tail_inr_zero :
    vertexToOld M c ((addFaceDiagonal M c).tail (Sum.inr (0 : Fin 2))) = M.tail c.d0 := by
  simp [vertexToOld_tail, proj, c.tail_anchor0]

@[simp] lemma vertexToOld_head_inr_zero :
    vertexToOld M c ((addFaceDiagonal M c).head (Sum.inr (0 : Fin 2))) = M.tail c.d1 := by
  rw [vertexToOld_head]
  simp [addFaceDiagonal, proj, c.tail_anchor1]

@[simp] lemma vertexToOld_tail_inr_one :
    vertexToOld M c ((addFaceDiagonal M c).tail (Sum.inr (1 : Fin 2))) = M.tail c.d1 := by
  simp [vertexToOld_tail, proj, c.tail_anchor1]

@[simp] lemma vertexToOld_head_inr_one :
    vertexToOld M c ((addFaceDiagonal M c).head (Sum.inr (1 : Fin 2))) = M.tail c.d0 := by
  rw [vertexToOld_head]
  simp [addFaceDiagonal, proj, c.tail_anchor0]

lemma map_dartEdge_inl (d : D) :
    Sym2.map (vertexToOld M c) ((addFaceDiagonal M c).dartEdge (Sum.inl d))
      = M.dartEdge d := by
  rw [CombMap.dartEdge, Sym2.map_mk]
  simp only [vertexToOld_tail_inl, vertexToOld_head_inl]
  rfl

lemma map_dartEdge_inr_zero :
    Sym2.map (vertexToOld M c)
        ((addFaceDiagonal M c).dartEdge (Sum.inr (0 : Fin 2)))
      = s(M.tail c.d0, M.tail c.d1) := by
  rw [CombMap.dartEdge, Sym2.map_mk]
  simp only [vertexToOld_tail_inr_zero, vertexToOld_head_inr_zero]

lemma map_dartEdge_inr_one :
    Sym2.map (vertexToOld M c)
        ((addFaceDiagonal M c).dartEdge (Sum.inr (1 : Fin 2)))
      = s(M.tail c.d0, M.tail c.d1) := by
  rw [CombMap.dartEdge, Sym2.map_mk]
  simp only [vertexToOld_tail_inr_one, vertexToOld_head_inr_one]
  exact Sym2.eq_swap

/-- A fresh diagonal dart is not a loop under the endpoint-distinct hypothesis,
and old darts remain non-loops from the original simple-map hypothesis. -/
theorem no_loop (hSimple : M.IsSimpleGraph) :
    ∀ x : D ⊕ Fin 2, (addFaceDiagonal M c).tail x ≠ (addFaceDiagonal M c).head x := by
  intro x h
  have hsc :
      (freshSigma M.σ c.anchor0 c.anchor1 c.anchors_ne).SameCycle
        x (freshAlpha M.α x) := by
    simpa [addFaceDiagonal] using (Quotient.exact h)
  have hproj := (freshSigma_sameCycle_iff M.σ c.anchors_ne
    x (freshAlpha M.α x)).1 hsc
  cases x with
  | inl d =>
      have hold : M.σ.SameCycle d (M.α d) := by
        simpa [proj] using hproj
      exact hSimple.no_loop d (Quotient.sound hold)
  | inr j =>
      fin_cases j
      · have ht : M.tail c.anchor0 = M.tail c.anchor1 := by
          exact Quotient.sound (by simpa [proj] using hproj)
        apply c.endpoints_distinct
        calc
          M.tail c.d0 = M.tail c.anchor0 := (c.tail_anchor0).symm
          _ = M.tail c.anchor1 := ht
          _ = M.tail c.d1 := c.tail_anchor1
      · have ht : M.tail c.anchor1 = M.tail c.anchor0 := by
          exact Quotient.sound (by simpa [proj] using hproj)
        apply c.endpoints_distinct
        calc
          M.tail c.d0 = M.tail c.anchor0 := (c.tail_anchor0).symm
          _ = M.tail c.anchor1 := ht.symm
          _ = M.tail c.d1 := c.tail_anchor1

lemma freshAlpha_sameCycle_inl_of_alpha_sameCycle {d e : D}
    (h : M.α.SameCycle d e) :
    (addFaceDiagonal M c).α.SameCycle (Sum.inl d) (Sum.inl e) := by
  rcases (M.alpha_sameCycle_iff d e).1 h with rfl | rfl
  · exact Equiv.Perm.SameCycle.refl _ _
  · refine ⟨1, ?_⟩
    simp [addFaceDiagonal]

lemma freshAlpha_sameCycle_inr (j k : Fin 2) :
    (addFaceDiagonal M c).α.SameCycle (Sum.inr j) (Sum.inr k) := by
  fin_cases j <;> fin_cases k
  · exact Equiv.Perm.SameCycle.refl _ _
  · refine ⟨1, ?_⟩
    simp [addFaceDiagonal]
  · refine ⟨1, ?_⟩
    simp [addFaceDiagonal]
  · exact Equiv.Perm.SameCycle.refl _ _

lemma no_old_fresh_parallel (hSimple : M.IsSimpleGraph) {d : D} {j : Fin 2}
    (h : (addFaceDiagonal M c).dartEdge (Sum.inl d)
        = (addFaceDiagonal M c).dartEdge (Sum.inr j)) :
    False := by
  have hmap := congrArg (Sym2.map (vertexToOld M c)) h
  have hedge : M.dartEdge d = s(M.tail c.d0, M.tail c.d1) := by
    fin_cases j
    · simpa [map_dartEdge_inl, map_dartEdge_inr_zero] using hmap
    · simpa [map_dartEdge_inl, map_dartEdge_inr_one] using hmap
  have hadj : M.Adj (M.tail c.d0) (M.tail c.d1) := ⟨d, hedge⟩
  exact c.no_existing_edge ⟨c.endpoints_distinct, hadj⟩

/-- The face diagonal preserves map simplicity: old parallel edges are handled
by `hSimple`, the fresh edge is non-loop by `endpoints_distinct`, and it is not
parallel to an old edge by `no_existing_edge`. -/
theorem simple (hSimple : M.IsSimpleGraph) :
    (addFaceDiagonal M c).IsSimpleGraph := by
  refine ⟨no_loop M c hSimple, ?_⟩
  intro x y hxy
  cases x with
  | inl d =>
      cases y with
      | inl e =>
          have hmap := congrArg (Sym2.map (vertexToOld M c)) hxy
          have hold : M.dartEdge d = M.dartEdge e := by
            simpa [map_dartEdge_inl] using hmap
          exact freshAlpha_sameCycle_inl_of_alpha_sameCycle M c (hSimple.no_parallel hold)
      | inr j =>
          exact False.elim (no_old_fresh_parallel M c hSimple hxy)
  | inr j =>
      cases y with
      | inl e =>
          exact (False.elim (no_old_fresh_parallel M c hSimple hxy.symm))
      | inr k =>
          exact freshAlpha_sameCycle_inr M c j k

/-- The vertex count is unchanged by inserting the two fresh darts into
existing vertex rotations. -/
theorem V_eq :
    (addFaceDiagonal M c).V = M.V := by
  simpa [addFaceDiagonal, CombMap.V] using
    (freshMap_V M.σ c.anchors_ne M.α M.α_invol M.α_no_fixed)

/-- The edge count rises by one: the two new darts form one new `α`-orbit. -/
theorem E_eq :
    (addFaceDiagonal M c).E = M.E + 1 := by
  have hfresh :
      2 * (addFaceDiagonal M c).E = Fintype.card D + 2 := by
    simpa [addFaceDiagonal] using
      (freshMap_two_mul_E M.α M.σ M.α_invol M.α_no_fixed
        c.anchor0 c.anchor1 c.anchors_ne)
  have hold : 2 * M.E = Fintype.card D := M.two_mul_E_eq_card
  omega

/-- The selected old face orbit is split into two old-plus-fresh face orbits;
all other old face orbits are unchanged at the cycle-count level. -/
theorem F_eq :
    (addFaceDiagonal M c).F = M.F + 1 := by
  have hsame := c.keptPhi_anchor_successors_sameCycle
  have hF :
      (addFaceDiagonal M c).F = numCycles (keptPhi M.α M.σ) + 1 := by
    simpa [addFaceDiagonal] using
      (freshMap_F_same_face M.α M.σ M.α_invol M.α_no_fixed
        c.anchors_ne hsame)
  rw [hF]
  have hOld : M.F = numCycles (keptPhi M.α M.σ) := by
    rw [M.F_eq_numCycles]
    rfl
  omega

/-- The fresh map remains connected when the old map is connected. -/
theorem connected (hconn : M.Connected) :
    (addFaceDiagonal M c).Connected := by
  simpa [addFaceDiagonal, keptCombMap] using
    (freshMap_connected_of_kept M.α M.σ M.α_invol M.α_no_fixed
      c.anchors_ne (by simpa [keptCombMap] using hconn))

/-- Sphere-map preservation from the count identities. -/
theorem sphere (hS : M.IsSphereMap) :
    (addFaceDiagonal M c).IsSphereMap := by
  refine ⟨connected M c hS.1, ?_⟩
  unfold CombMap.eulerChar
  have hV := V_eq M c
  have hE := E_eq M c
  have hF := F_eq M c
  rw [hV, hE, hF]
  norm_num [Nat.cast_add]
  ring_nf
  simpa [CombMap.eulerChar] using hS.2

/-- Old adjacency embeds into the fresh map through `includeVertex`. -/
theorem old_adj_embed {u v : M.Vertex}
    (hadj : M.toSimpleGraph.Adj u v) :
    (addFaceDiagonal M c).toSimpleGraph.Adj
      (includeVertex M c u) (includeVertex M c v) := by
  rcases hadj with ⟨hne, d, hd⟩
  refine ⟨?_, Sum.inl d, ?_⟩
  · intro h
    exact hne (includeVertex_injective M c h)
  · have hmap := congrArg (Sym2.map (includeVertex M c)) hd
    simpa [CombMap.dartEdge, includeVertex_head] using hmap

lemma old_E_ge_two (c : FaceDiagonalChoice M) (hSimple : M.IsSimpleGraph) : 2 ≤ M.E := by
  have hd01 : c.d0 ≠ c.d1 := by
    intro h
    exact c.endpoints_distinct (by rw [h])
  have hφ0 : M.φ c.d0 ≠ c.d0 := by
    intro h
    apply hSimple.no_loop c.d0
    rw [← M.tail_phi c.d0, h]
  have hφ01 : M.φ c.d0 ≠ c.d1 := c.nonadjacent_on_face.1
  let f : Fin 3 → D := fun i =>
    if i = 0 then c.d0 else if i = 1 then c.d1 else M.φ c.d0
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, hd01, hd01.symm, hφ0, hφ0.symm, hφ01, hφ01.symm] at hij ⊢
  have hcard : 3 ≤ Fintype.card D := by
    simpa using Fintype.card_le_of_injective f hf
  have htwo := M.two_mul_E_eq_card
  omega

theorem faceLengthGe_three (c : FaceDiagonalChoice M)
    (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph) :
    M.FaceLengthGe 3 := by
  intro Q
  have hdeg := ProofsInTheBook.Ch13ComponentClose.three_le_faceDeg_of_connected_simple_twoEdge
    (A := M) hSimple hS.1 (old_E_ge_two M c hSimple) Q
  simpa [ProofsInTheBook.Ch13ComponentClose.faceDeg_eq_faceLen] using hdeg

theorem faceLengthGe_three_add (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph) :
    (addFaceDiagonal M c).FaceLengthGe 3 := by
  intro Q
  have hS' := sphere M c hS
  have hSimple' := simple M c hSimple
  have hEold := old_E_ge_two M c hSimple
  have hE' : 2 ≤ (addFaceDiagonal M c).E := by
    have hEeq := E_eq M c
    omega
  have hdeg := ProofsInTheBook.Ch13ComponentClose.three_le_faceDeg_of_connected_simple_twoEdge
    (A := addFaceDiagonal M c) hSimple' hS'.1 hE' Q
  simpa [ProofsInTheBook.Ch13ComponentClose.faceDeg_eq_faceLen] using hdeg

lemma chosen_face_len_ne_three (hSimple : M.IsSimpleGraph) :
    M.faceLen c.f ≠ 3 := by
  intro hlen
  have hlen0 : M.faceLen (M.dartFace c.d0) = 3 := by
    rw [c.same_face, hlen]
  have hcube := faceLen_three_phi_cube_eq_self M hSimple hlen0
  have hsc : M.φ.SameCycle c.d0 c.d1 := c.same_face_sameCycle
  rcases sameCycle_mem_triple_of_phi_cube hcube hsc with h | h | h
  · apply c.endpoints_distinct
    rw [h]
  · exact c.nonadjacent_on_face.1 h.symm
  · have hφd1 : M.φ c.d1 = c.d0 := by
      rw [h]
      simpa [pow_succ, Equiv.Perm.coe_mul, Function.comp_apply] using hcube
    exact c.nonadjacent_on_face.2 hφd1

lemma faceExcess_pos (c : FaceDiagonalChoice M)
    (h3 : M.FaceLengthGe 3) (hSimple : M.IsSimpleGraph) :
    0 < faceExcess M := by
  have hne := chosen_face_len_ne_three M c hSimple
  have hlt : 3 < M.faceLen c.f := by
    exact lt_of_le_of_ne (h3 c.f) (by intro h; exact hne h.symm)
  have hterm : 0 < M.faceLen c.f - 3 := Nat.sub_pos_of_lt hlt
  unfold faceExcess
  have hle :
      M.faceLen c.f - 3 ≤ ∑ f : M.Face, (M.faceLen f - 3) := by
    simpa using Finset.single_le_sum
      (s := (Finset.univ : Finset M.Face))
      (f := fun f : M.Face => M.faceLen f - 3)
      (by intro f _; exact Nat.zero_le _)
      (Finset.mem_univ c.f)
  exact lt_of_lt_of_le hterm hle

theorem faceExcess_decrease (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph) :
    faceExcess (addFaceDiagonal M c) < faceExcess M := by
  have h3old := faceLengthGe_three M c hS hSimple
  have h3new := faceLengthGe_three_add M c hS hSimple
  have hold := faceExcess_eq_two_mul_E_sub_three_mul_F M h3old
  have hnew := faceExcess_eq_two_mul_E_sub_three_mul_F (addFaceDiagonal M c) h3new
  have hE := E_eq M c
  have hF := F_eq M c
  have hpos := faceExcess_pos M c h3old hSimple
  rw [hnew, hold, hE, hF] at *
  omega

end FaceDiagonal

/-- A one-step face-diagonal insertion certificate.  The generic fresh-map
count, connectivity, simplicity, old-edge embedding, and excess decrease fields
are produced below. -/
structure FaceDiagonalInsertion
    (M : CombMap D) (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph)
    (c : FaceDiagonalChoice M) where
  D' : Type u
  [fintypeD' : Fintype D']
  [decEqD' : DecidableEq D']
  M' : CombMap D'
  includeDart : D → D'
  includeVertex : M.Vertex → M'.Vertex
  sphere' : M'.IsSphereMap
  simple' : M'.IsSimpleGraph
  old_adj_embed :
    ∀ {u v : M.Vertex}, M.toSimpleGraph.Adj u v →
      M'.toSimpleGraph.Adj (includeVertex u) (includeVertex v)
  V_eq : M'.V = M.V
  E_eq : M'.E = M.E + 1
  F_eq : M'.F = M.F + 1
  faceExcess_decrease : faceExcess M' < faceExcess M

attribute [instance] FaceDiagonalInsertion.fintypeD' FaceDiagonalInsertion.decEqD'

namespace FaceDiagonalInsertion

/-- Assemble the diagonal insertion certificate from the two remaining local
geometric obligations. -/
noncomputable def of_addFaceDiagonal
    (M : CombMap D) (hS : M.IsSphereMap) (hSimple : M.IsSimpleGraph)
    (c : FaceDiagonalChoice M) :
    FaceDiagonalInsertion M hS hSimple c where
  D' := D ⊕ Fin 2
  M' := addFaceDiagonal M c
  includeDart := Sum.inl
  includeVertex := FaceDiagonal.includeVertex M c
  sphere' := FaceDiagonal.sphere M c hS
  simple' := FaceDiagonal.simple M c hSimple
  old_adj_embed := by
    intro u v h
    exact FaceDiagonal.old_adj_embed M c h
  V_eq := FaceDiagonal.V_eq M c
  E_eq := FaceDiagonal.E_eq M c
  F_eq := FaceDiagonal.F_eq M c
  faceExcess_decrease := FaceDiagonal.faceExcess_decrease M c hS hSimple

end FaceDiagonalInsertion

end ProofsInTheBook.PlanarMap.CombMap
