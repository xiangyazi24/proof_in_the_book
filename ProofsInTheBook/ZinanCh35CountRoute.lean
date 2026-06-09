import ProofsInTheBook.FaceCorrWord
import ProofsInTheBook.ChordSeparationClose

/-!
# Chapter 35 count route: split certificates instead of seam decompositions

This file contains the conditional count-route plumbing for the corrected Chapter 35
cut-and-cap face count.  The single geometric/combinatorial input left explicit is the
split-count bound for the actual split positions of the `faceCorr₂` transposition word:


FaceCorrWord.concatLen Ls + 2 ≤ 2 * (actualSplitFinset C Ls).card + 2 * C.len


Everything after that bound is pure permutation algebra / wiring.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Equiv Equiv.Perm Function List
open scoped Finset

namespace ForcedSplits

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The actual split indices of a transposition word: the swaps whose endpoints are already
in the same cycle of the prefix permutation. -/
noncomputable def actualSplitFinset (p : Equiv.Perm X) {m : ℕ}
    (W : Fin m → ForcedSplits.Swap X) : Finset (Fin m) :=
  Finset.univ.filter fun j =>
    (ForcedSplits.prefixPerm p W j.val).SameCycle (W j).x (W j).y

/-- A non-split transposition step lowers the cycle count by exactly one. -/
lemma stepDelta_eq_neg_one_of_not_sameCycle (p : Equiv.Perm X) {m : ℕ}
    (W : Fin m → ForcedSplits.Swap X) (j : Fin m)
    (hne : (W j).x ≠ (W j).y)
    (hnot :
      ¬ (ForcedSplits.prefixPerm p W j.val).SameCycle (W j).x (W j).y) :
    ForcedSplits.stepDelta p W j = -1 := by
  classical
  have hj : j.val < m := j.isLt
  rw [ForcedSplits.stepDelta, ForcedSplits.prefixPerm_succ p W hj,
    ForcedSplits.Swap.perm]
  have hnum := numCycles_mul_swap_of_not_sameCycle
    (ForcedSplits.prefixPerm p W j.val) hne hnot
  have hnumZ :
      (numCycles (ForcedSplits.prefixPerm p W j.val *
          Equiv.swap (W j).x (W j).y) : ℤ) + 1 =
        (numCycles (ForcedSplits.prefixPerm p W j.val) : ℤ) := by
    exact_mod_cast hnum
  linarith

/-- The sum of actual step deltas is `-m + 2 * (# actual splits)`. -/
theorem sum_stepDelta_eq_neg_m_add_two_actualSplits (p : Equiv.Perm X) {m : ℕ}
    (W : Fin m → ForcedSplits.Swap X)
    (hne : ∀ j : Fin m, (W j).x ≠ (W j).y) :
    (∑ j : Fin m, ForcedSplits.stepDelta p W j)
      = -(m : ℤ) + 2 * ((ForcedSplits.actualSplitFinset p W).card : ℤ) := by
  classical
  let S : Finset (Fin m) := ForcedSplits.actualSplitFinset p W
  have h_onS : ∀ j ∈ S, ForcedSplits.stepDelta p W j = 1 := by
    intro j hj
    have hsc :
        (ForcedSplits.prefixPerm p W j.val).SameCycle (W j).x (W j).y := by
      simpa [S, ForcedSplits.actualSplitFinset] using (Finset.mem_filter.mp hj).2
    exact ForcedSplits.stepDelta_eq_one_of_forced_split p W j (hne j) hsc
  have h_offS : ∀ j ∈ Sᶜ, ForcedSplits.stepDelta p W j = -1 := by
    intro j hj
    have hjnot : j ∉ S := by simpa using hj
    have hnot :
        ¬ (ForcedSplits.prefixPerm p W j.val).SameCycle (W j).x (W j).y := by
      intro hsc
      exact hjnot (by
        simp [S, ForcedSplits.actualSplitFinset, hsc])
    exact ForcedSplits.stepDelta_eq_neg_one_of_not_sameCycle p W j (hne j) hnot
  calc
    (∑ j : Fin m, ForcedSplits.stepDelta p W j)
        = (∑ j ∈ S, ForcedSplits.stepDelta p W j)
            + (∑ j ∈ Sᶜ, ForcedSplits.stepDelta p W j) := by
          rw [← Finset.sum_add_sum_compl S]
    _ = (∑ _j ∈ S, (1 : ℤ)) + (∑ _j ∈ Sᶜ, (-1 : ℤ)) := by
          congr 1
          · exact Finset.sum_congr rfl (fun j hj => h_onS j hj)
          · exact Finset.sum_congr rfl (fun j hj => h_offS j hj)
    _ = -(m : ℤ) + 2 * ((ForcedSplits.actualSplitFinset p W).card : ℤ) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          have hcardC : (Sᶜ).card = m - S.card := by
            rw [Finset.card_compl, Fintype.card_fin]
          have hcardCZ : ((Sᶜ).card : ℤ) = (m : ℤ) - (S.card : ℤ) := by
            rw [hcardC]
            have hle : S.card ≤ m := by
              simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ S
            omega
          rw [hcardCZ]
          dsimp [S]
          ring

end ForcedSplits

namespace ProofsInTheBook.PlanarMap

namespace FaceCorrWord

open ForcedSplits SeamChain

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A cycle-list decomposition with nodup cycle lists. -/
theorem exists_cycleListProd_nodup (q : Equiv.Perm X) :
    ∃ Ls : List (List X),
      (∀ L ∈ Ls, 2 ≤ L.length ∧ L.Nodup) ∧
      FaceCorrWord.cycleListProd Ls = q := by
  classical
  induction q using Equiv.Perm.cycle_induction_on with
  | base_one =>
      exact ⟨[], by simp, rfl⟩
  | base_cycles σ hσ =>
      obtain ⟨x, hx, -⟩ := id hσ
      have hxs : x ∈ σ.support := by
        rw [Equiv.Perm.mem_support]
        exact hx
      refine ⟨[Equiv.Perm.toList σ x], ?_, ?_⟩
      · intro L hL
        simp only [List.mem_singleton] at hL
        subst hL
        constructor
        · exact Equiv.Perm.two_le_length_toList_iff_mem_support.mpr hxs
        · -- If Mathlib renamed this, alternates: `Equiv.Perm.toList_nodup`,
          -- `Equiv.Perm.nodup_toList`.
          exact Equiv.Perm.nodup_toList σ x
      · simp only [FaceCorrWord.cycleListProd, mul_one, SeamChain.cycleOfList]
        rw [Equiv.Perm.formPerm_toList, Equiv.Perm.IsCycle.cycleOf_eq hσ hx]
  | induction_disjoint σ τ hdisj hσ hστ hτ =>
      obtain ⟨Lσ, hLσ, hfacσ⟩ := hστ
      obtain ⟨Lτ, hLτ, hfacτ⟩ := hτ
      refine ⟨Lσ ++ Lτ, ?_, ?_⟩
      · intro L hL
        rcases List.mem_append.mp hL with h | h
        · exact hLσ L h
        · exact hLτ L h
      · rw [FaceCorrWord.cycleListProd_append, hfacσ, hfacτ]

/-- Consecutive entries in a nodup list are distinct, in the form needed by `wordOfList`. -/
lemma wordOfList_ne_of_nodup (L : List X) (hL : L.Nodup)
    (j : Fin (L.length - 1)) :
    (FaceCorrWord.wordOfList L j).x ≠ (FaceCorrWord.wordOfList L j).y := by
  classical
  dsimp [FaceCorrWord.wordOfList]
  intro h
  have hj0 : j.val < L.length := by
    have := j.isLt
    omega
  have hj1 : j.val + 1 < L.length := by
    have := j.isLt
    omega
  have hidx : j.val = j.val + 1 := by
    -- If Mathlib renamed this, alternates: `List.Nodup.getElem_inj`,
    -- `List.Nodup.getElem_inj_iff`.
    exact (List.Nodup.getElem_inj_iff hL).mp h
  omega

/-- All swaps in a concatenated word of nodup cycle lists have distinct endpoints. -/
lemma concatWord_ne_of_nodup (Ls : List (List X))
    (hpos : ∀ L ∈ Ls, 2 ≤ L.length)
    (hnodup : ∀ L ∈ Ls, L.Nodup)
    (j : Fin (FaceCorrWord.concatLen Ls)) :
    (FaceCorrWord.concatWord Ls j).x ≠ (FaceCorrWord.concatWord Ls j).y := by
  classical
  induction Ls with
  | nil =>
      exact absurd j.isLt (by simp [FaceCorrWord.concatLen])
  | cons L rest ih =>
      have hLpos : 2 ≤ L.length := hpos L List.mem_cons_self
      have hLnodup : L.Nodup := hnodup L List.mem_cons_self
      have hpos_rest : ∀ L' ∈ rest, 2 ≤ L'.length := by
        intro L' hL'
        exact hpos L' (List.mem_cons_of_mem _ hL')
      have hnodup_rest : ∀ L' ∈ rest, L'.Nodup := by
        intro L' hL'
        exact hnodup L' (List.mem_cons_of_mem _ hL')
      by_cases hj : j.val < L.length - 1
      · have hjFin : j.val < (L.length - 1) := hj
        have hcast : (⟨j.val, hjFin⟩ : Fin (L.length - 1)) =
            ⟨j.val, hjFin⟩ := rfl
        simpa [FaceCorrWord.concatWord, FaceCorrWord.concatLen,
          FaceCorrWord.appendWord, hj] using
          FaceCorrWord.wordOfList_ne_of_nodup L hLnodup ⟨j.val, hjFin⟩
      · have hjRest : j.val - (L.length - 1) < FaceCorrWord.concatLen rest := by
          have hlt := j.isLt
          have hcl : FaceCorrWord.concatLen (L :: rest)
              = (L.length - 1) + FaceCorrWord.concatLen rest := rfl
          omega
        have hnot : ¬ j.val < L.length - 1 := hj
        have ihj := ih hpos_rest hnodup_rest
          ⟨j.val - (L.length - 1), hjRest⟩
        simpa [FaceCorrWord.concatWord, FaceCorrWord.concatLen,
          FaceCorrWord.appendWord, hnot] using ihj

end FaceCorrWord

namespace CombMap

variable {D : Type*} [Fintype D] [DecidableEq D]

namespace SimplePrimalCycle

open ForcedSplits FaceCorrWord SeamChain

variable {M : CombMap D}

/-- A cycle-list decomposition of `faceCorr₂`, with enough list hygiene for the
consecutive-transposition word. -/
structure FaceCorrCycleLists (C : SimplePrimalCycle M)
    (Ls : List (List C.CutDart)) : Prop where
  pos : ∀ L ∈ Ls, 2 ≤ L.length
  nodup : ∀ L ∈ Ls, L.Nodup
  factor : FaceCorrWord.cycleListProd Ls = C.faceCorr2

/-- The actual split indices of the canonical cycle-list word for `faceCorr₂`. -/
noncomputable def actualSplitFinset (C : SimplePrimalCycle M)
    (Ls : List (List C.CutDart)) :
    Finset (Fin (FaceCorrWord.concatLen Ls)) :=
  ForcedSplits.actualSplitFinset C.phiLift (FaceCorrWord.concatWord Ls)

/-- The concatenated word of a `FaceCorrCycleLists` certificate is nondegenerate. -/
lemma concatWord_ne_of_nodup (C : SimplePrimalCycle M) {Ls : List (List C.CutDart)}
    (H : C.FaceCorrCycleLists Ls) (j : Fin (FaceCorrWord.concatLen Ls)) :
    (FaceCorrWord.concatWord Ls j).x ≠ (FaceCorrWord.concatWord Ls j).y :=
  FaceCorrWord.concatWord_ne_of_nodup Ls H.pos H.nodup j

/-- Every `faceCorr₂` has a nodup cycle-list decomposition. -/
theorem exists_faceCorrCycleLists (C : SimplePrimalCycle M) :
    ∃ Ls : List (List C.CutDart), C.FaceCorrCycleLists Ls := by
  classical
  obtain ⟨Ls, hLs, hfac⟩ := FaceCorrWord.exists_cycleListProd_nodup C.faceCorr2
  refine ⟨Ls, ?_⟩
  exact ⟨fun L hL => (hLs L hL).1, fun L hL => (hLs L hL).2, hfac⟩

/-- Conditional lower bound from a sufficient actual-split count. -/
theorem numCycles_phiLift_faceCorr2_lower_of_splitsEnough
    (C : SimplePrimalCycle M) {Ls : List (List C.CutDart)}
    (H : C.FaceCorrCycleLists Ls)
    (hsplits :
      FaceCorrWord.concatLen Ls + 2 ≤
        2 * (C.actualSplitFinset Ls).card + 2 * C.len) :
    (numCycles (C.phiLift * C.faceCorr2) : ℤ) ≥ (M.F : ℤ) + 2 := by
  classical
  let W : Fin (FaceCorrWord.concatLen Ls) → ForcedSplits.Swap C.CutDart :=
    FaceCorrWord.concatWord Ls
  have hpos0 : ∀ L ∈ Ls, 0 < L.length := by
    intro L hL
    have := H.pos L hL
    omega
  have hprefix :
      ForcedSplits.prefixPerm C.phiLift W (FaceCorrWord.concatLen Ls)
        = C.phiLift * C.faceCorr2 := by
    dsimp [W]
    rw [FaceCorrWord.prefixPerm_concatWord C.phiLift Ls hpos0, H.factor]
  have htel := ForcedSplits.numCycles_prefix_telescopes C.phiLift W
  have hsum := ForcedSplits.sum_stepDelta_eq_neg_m_add_two_actualSplits
    C.phiLift W (fun j => C.concatWord_ne_of_nodup H j)
  have hdiff :
      (numCycles (ForcedSplits.prefixPerm C.phiLift W (FaceCorrWord.concatLen Ls)) : ℤ)
        - (numCycles C.phiLift : ℤ)
        =
      -(FaceCorrWord.concatLen Ls : ℤ)
        + 2 * ((C.actualSplitFinset Ls).card : ℤ) := by
    rw [SimplePrimalCycle.actualSplitFinset, htel, hsum]
  rw [hprefix] at hdiff
  have hphi :
      (numCycles C.phiLift : ℤ) = (M.F : ℤ) + 2 * (C.len : ℤ) := by
    rw [C.numCycles_phiLift]
    push_cast
    ring
  have hboundZ :
      (FaceCorrWord.concatLen Ls : ℤ) + 2 ≤
        2 * ((C.actualSplitFinset Ls).card : ℤ) + 2 * (C.len : ℤ) := by
    exact_mod_cast hsplits
  linarith

/-- Enumerate a finset by `Fin card`, returning elements of the ambient type. -/
noncomputable def splitIdxOfFinset {n : ℕ} (S : Finset (Fin n)) :
    Fin S.card → Fin n :=
  fun i => (S.orderIsoOfFin rfl i : Fin n)
-- If Mathlib renamed this, alternates: `Finset.orderIsoOfFin S`,
-- `Fintype.equivFin {x // x ∈ S}`.

lemma splitIdxOfFinset_mem {n : ℕ} (S : Finset (Fin n)) (i : Fin S.card) :
    splitIdxOfFinset S i ∈ S :=
  (S.orderIsoOfFin rfl i).2

lemma splitIdxOfFinset_injective {n : ℕ} (S : Finset (Fin n)) :
    Function.Injective (splitIdxOfFinset S) := by
  intro i j h
  exact (S.orderIsoOfFin rfl).injective (Subtype.ext h)

/-- Build the repository's split certificate from a cycle-list certificate and the sufficient
actual-split count. -/
noncomputable def faceCorrSplitCert_of_cycleLists (C : SimplePrimalCycle M)
    {Ls : List (List C.CutDart)}
    (H : C.FaceCorrCycleLists Ls)
    (hsplits :
      FaceCorrWord.concatLen Ls + 2 ≤
        2 * (C.actualSplitFinset Ls).card + 2 * C.len) :
    C.FaceCorrSplitCert := by
  classical
  let S : Finset (Fin (FaceCorrWord.concatLen Ls)) := C.actualSplitFinset Ls
  refine
    { Ls := Ls
      Ls_pos := ?_
      factor := H.factor
      s := S.card
      hbound := ?_
      splitIdx := splitIdxOfFinset S
      splitIdx_injective := splitIdxOfFinset_injective S
      split_ne := ?_
      forced_split := ?_ }
  · intro L hL
    have := H.pos L hL
    omega
  · simpa [S]
      using hsplits
  · intro i
    exact C.concatWord_ne_of_nodup H (splitIdxOfFinset S i)
  · intro i
    have hmem : splitIdxOfFinset S i ∈ S := splitIdxOfFinset_mem S i
    simpa [S, SimplePrimalCycle.actualSplitFinset, ForcedSplits.actualSplitFinset]
      using (Finset.mem_filter.mp hmem).2

/-- If every cycle-list decomposition has enough actual splits, then `faceCorr₂` has a
`FaceCorrSplitCert`.  This is the conditional replacement for the unproved geometric
split-count theorem. -/
noncomputable def faceCorrSplitCert_of_splitsEnough (C : SimplePrimalCycle M)
    (hsplitsAll :
      ∀ Ls : List (List C.CutDart), C.FaceCorrCycleLists Ls →
        FaceCorrWord.concatLen Ls + 2 ≤
          2 * (C.actualSplitFinset Ls).card + 2 * C.len) :
    C.FaceCorrSplitCert := by
  classical
  exact C.faceCorrSplitCert_of_cycleLists
    (C.exists_faceCorrCycleLists).choose_spec
    (hsplitsAll _ (C.exists_faceCorrCycleLists).choose_spec)

/-- If every cycle-list decomposition has enough actual splits, then the lower count follows. -/
theorem numCycles_phiLift_faceCorr2_lower_of_splitsEnough_all
    (C : SimplePrimalCycle M)
    (hsplitsAll :
      ∀ Ls : List (List C.CutDart), C.FaceCorrCycleLists Ls →
        FaceCorrWord.concatLen Ls + 2 ≤
          2 * (C.actualSplitFinset Ls).card + 2 * C.len) :
    (numCycles (C.phiLift * C.faceCorr2) : ℤ) ≥ (M.F : ℤ) + 2 := by
  classical
  obtain ⟨Ls, H⟩ := C.exists_faceCorrCycleLists
  exact C.numCycles_phiLift_faceCorr2_lower_of_splitsEnough H (hsplitsAll Ls H)

/-- Sphere-SHAPED wrapper for the conditional lower-count route — NOT the master sphere
theorem: the split-count bound is still an explicit hypothesis and `hconn`/`hchi` are
unused.  The genuine remaining Ch35 residue is exactly discharging `hsplitsAll`
(the actual-split count of the `faceCorr₂` word — conjecturally genus-FREE, per the
`PlanarMapSeamInst` kernel anchors showing `F' − F = 2` across genus). -/
theorem numCycles_phiLift_faceCorr2_lower_sphereShape_of_splitsEnough
    (C : SimplePrimalCycle M)
    (hsplitsAll :
      ∀ Ls : List (List C.CutDart), C.FaceCorrCycleLists Ls →
        FaceCorrWord.concatLen Ls + 2 ≤
          2 * (C.actualSplitFinset Ls).card + 2 * C.len)
    (_hconn : M.Connected) (_hchi : M.eulerChar = 2) :
    (numCycles (C.phiLift * C.faceCorr2) : ℤ) ≥ (M.F : ℤ) + 2 :=
  C.numCycles_phiLift_faceCorr2_lower_of_splitsEnough_all hsplitsAll

/-- Corrected lower-bound Jordan input: the face side is a split certificate, and the
connectivity side is exactly the corrected cap-channel endpoint/interior-gate supplier
from `ChordJordanInput'`. -/
structure ChordJordanInputLower' (C : SimplePrimalCycle M) where
  /-- The lower-bound face-count certificate. -/
  faceSplit : C.FaceCorrSplitCert
  /-- The corrected cap-channel endpoint link plus interior triangle gates, matching
  `ChordJordanInput'.gateCompat'`. -/
  gateCompat' : ∀ i : Fin C.len,
    DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i) →
      ∃ P : C.OrdinaryDualPath2, C.EndpointCapLink i P ∧ C.InteriorTriangleGates P

/-- Connectivity of `cutCapMap2` from the lower-bound corrected input. -/
theorem connectivity_of_inputLower' (C : SimplePrimalCycle M) (hconn : M.Connected)
    (hin : C.ChordJordanInputLower') (i : Fin C.len)
    (hpath : DualReachableAvoidingCycle M C (C.faceLeft i) (C.faceRight i)) :
    (C.cutCapMap2).Connected := by
  obtain ⟨P, hlink, hg⟩ := hin.gateCompat' i hpath
  exact C.cutCapMap2_connected_of_corrected i hconn P hlink hg

end SimplePrimalCycle

end CombMap

namespace CombMap.NearTriangulation

variable {D : Type*} [Fintype D] [DecidableEq D]
variable {M : CombMap D} (hNT : NearTriangulation M)

open SimplePrimalCycle

/-- `SphereChordSeparation` from the lower-bound corrected residue. -/
theorem sphereChordSeparation_of_inputLower' {u v : M.Vertex}
    (h : hNT.outerCycle.Chord u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hin : C.ChordJordanInputLower')
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart h))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart h))) :
    hNT.SphereChordSeparation h := by
  intro hreach
  have hpath : DualReachableAvoidingCycle M C
      (M.dartFace (hNT.chordDart h))
      (M.dartFace (M.α (hNT.chordDart h))) :=
    hNT.reachable_dualAvoidsCycle_of_chordSplitAdj C hsub hreach
  rw [← hleft, ← hright] at hpath
  exact C.jordan_simple_cycle2_lower_of_splitCert hin.faceSplit
    hNT.sphere.2
    (fun i hp => C.connectivity_of_inputLower' hNT.sphere.1 hin i hp)
    i₀ hpath

/-- `Separates` form from the lower-bound corrected residue. -/
theorem separates_of_inputLower' {u v : M.Vertex}
    (data : hNT.ChordSplitData u v)
    (C : CombMap.SimplePrimalCycle M)
    (hsub : ∀ e ∈ C.edgeSet, e = s(u, v) ∨ hNT.outerCycle.IsBoundaryEdge e)
    (hin : C.ChordJordanInputLower')
    (i₀ : Fin C.len)
    (hleft : C.faceLeft i₀ = M.dartFace (hNT.chordDart data.chord))
    (hright : C.faceRight i₀ = M.dartFace (M.α (hNT.chordDart data.chord))) :
    data.Separates :=
  data.separates_of_nearTriangulation
    (hNT.sphereChordSeparation_of_inputLower'
      data.chord C hsub hin i₀ hleft hright)

end CombMap.NearTriangulation

end ProofsInTheBook.PlanarMap

/-! ## Axiom audit -/

#print axioms ForcedSplits.stepDelta_eq_neg_one_of_not_sameCycle
#print axioms ForcedSplits.sum_stepDelta_eq_neg_m_add_two_actualSplits
#print axioms ProofsInTheBook.PlanarMap.FaceCorrWord.exists_cycleListProd_nodup
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.exists_faceCorrCycleLists
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.numCycles_phiLift_faceCorr2_lower_of_splitsEnough
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.faceCorrSplitCert_of_cycleLists
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.faceCorrSplitCert_of_splitsEnough
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.numCycles_phiLift_faceCorr2_lower_sphereShape_of_splitsEnough
#print axioms ProofsInTheBook.PlanarMap.CombMap.SimplePrimalCycle.connectivity_of_inputLower'
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.sphereChordSeparation_of_inputLower'
#print axioms ProofsInTheBook.PlanarMap.CombMap.NearTriangulation.separates_of_inputLower'
