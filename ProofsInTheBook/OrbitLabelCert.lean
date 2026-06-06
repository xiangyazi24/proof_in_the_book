/-
The abstract orbit-label certificate engine (Chapter 35, genus-free F count,
design HANDOFF/CH35_GENUSFREE_DESIGN.md §1-2).

A permutation whose orbits are classified by a finite label type — a label
function constant along the permutation, an anchor in each fiber, and the
fact that every point reaches its label's anchor — has exactly `card β`
cycles.  Completely independent of maps, genus, chains, and `faceCorr₂`.
-/
import ProofsInTheBook.PermTranspositionCycleCount

set_option linter.unusedSectionVars false

open Equiv Equiv.Perm Function

namespace ProofsInTheBook

variable {X β : Type*} [Fintype X] [DecidableEq X] [Fintype β] [DecidableEq β]

/-- An orbit-label certificate for a permutation `q`: a finite label type `β`,
a label constant along `q`, and an anchor in each label fiber reachable from
every point of the fiber. -/
structure OrbitLabelCert (q : Equiv.Perm X) (β : Type*) where
  label : X → β
  anchor : β → X
  label_anchor : ∀ b, label (anchor b) = b
  label_invariant : ∀ x, label (q x) = label x
  same_anchor : ∀ x, q.SameCycle x (anchor (label x))

namespace OrbitLabelCert

variable {q : Equiv.Perm X} (C : OrbitLabelCert q β)

theorem label_inv_apply (x : X) : C.label (q⁻¹ x) = C.label x := by
  have h := C.label_invariant (q⁻¹ x)
  simp at h
  exact h.symm

theorem label_zpow (i : ℤ) (x : X) : C.label ((q ^ i) x) = C.label x := by
  induction i using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have : ((q : Equiv.Perm X) ^ ((n : ℤ) + 1)) x = q ((q ^ (n : ℤ)) x) := by
        rw [zpow_add_one, Equiv.Perm.mul_apply]
      rw [this, C.label_invariant, ih]
  | pred n ih =>
      have : ((q : Equiv.Perm X) ^ (-(n : ℤ) - 1)) x = q⁻¹ ((q ^ (-(n : ℤ))) x) := by
        rw [sub_eq_add_neg, zpow_add]
        simp [Equiv.Perm.mul_apply]
      rw [this, C.label_inv_apply, ih]

theorem label_eq_of_sameCycle {x y : X} (h : q.SameCycle x y) :
    C.label x = C.label y := by
  obtain ⟨i, hi⟩ := h
  rw [← hi, C.label_zpow]

/-- The orbit quotient is equivalent to the label type. -/
noncomputable def orbitEquiv : Quotient (SameCycle.setoid q) ≃ β where
  toFun := Quotient.lift C.label (fun _ _ h => C.label_eq_of_sameCycle h)
  invFun b := Quotient.mk (SameCycle.setoid q) (C.anchor b)
  left_inv := by
    intro z
    induction z using Quotient.inductionOn with
    | h x =>
        apply Quotient.sound
        exact (C.same_anchor x).symm
  right_inv := by
    intro b
    simpa using C.label_anchor b

/-- **The abstract engine**: a permutation with an orbit-label certificate
over `β` has exactly `card β` cycles. -/
theorem numCycles_eq_card : numCycles q = Fintype.card β := by
  classical
  unfold numCycles
  exact Fintype.card_congr (orbitEquiv C)

end OrbitLabelCert

end ProofsInTheBook
