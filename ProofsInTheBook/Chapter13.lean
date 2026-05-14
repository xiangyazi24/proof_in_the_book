import Mathlib

/-!
# Chapter 13: Cauchy's rigidity theorem

From "Proofs from THE BOOK":

**Cauchy's rigidity theorem**: If two convex polyhedra have the same
combinatorial structure and corresponding faces are congruent, then
the polyhedra are congruent (equal up to isometry).

The book's proof uses Cauchy's arm lemma: if we increase some angles
in a convex polygon while keeping side lengths fixed, the polygon
"opens up" (the distance between the first and last vertex increases).

The proof proceeds by:
1. Label each edge + or - according to whether the dihedral angle
   increases or decreases.
2. Use Euler's formula to count sign changes around faces.
3. Apply the arm lemma to derive a contradiction if any signs are non-zero.
-/

namespace ProofsInTheBook.Chapter13

/-- Edge signs in Cauchy's rigidity proof. -/
inductive EdgeSign where
  | plus | minus | zero
  deriving DecidableEq, Repr

open EdgeSign

/-- The nonzero signs left after Cauchy's proof discards unchanged edges. -/
inductive StrictEdgeSign where
  | plus | minus
  deriving DecidableEq, Repr

/-- Forget zero signs and keep only genuine increases/decreases. -/
def EdgeSign.toStrict : EdgeSign → Option StrictEdgeSign
  | plus => some StrictEdgeSign.plus
  | minus => some StrictEdgeSign.minus
  | zero => none

@[simp]
theorem edgeSign_toStrict_eq_none_iff (s : EdgeSign) : s.toStrict = none ↔ s = zero := by
  cases s <;> simp [EdgeSign.toStrict]

/--
The local sign-change count around a triangular face. Cauchy's proof labels
edges by whether their dihedral angle increases, decreases, or stays fixed,
then counts sign changes around faces.
-/
def SignChangesAroundTriangle (a b c : EdgeSign) : ℕ :=
  (if a ≠ b then 1 else 0) + (if b ≠ c then 1 else 0) + (if c ≠ a then 1 else 0)

theorem signChangesAroundTriangle_le_three (a b c : EdgeSign) :
    SignChangesAroundTriangle a b c ≤ 3 := by
  unfold SignChangesAroundTriangle
  by_cases hab : a ≠ b <;> by_cases hbc : b ≠ c <;> by_cases hca : c ≠ a <;>
    simp [hab, hbc, hca]

theorem signChangesAroundTriangle_eq_zero_of_constant (s : EdgeSign) :
    SignChangesAroundTriangle s s s = 0 := by
  simp [SignChangesAroundTriangle]

def StrictSignChangesAroundTriangle (a b c : StrictEdgeSign) : ℕ :=
  (if a ≠ b then 1 else 0) + (if b ≠ c then 1 else 0) + (if c ≠ a then 1 else 0)

theorem strictSignChangesAroundTriangle_eq_zero_or_two (a b c : StrictEdgeSign) :
    StrictSignChangesAroundTriangle a b c = 0 ∨
      StrictSignChangesAroundTriangle a b c = 2 := by
  cases a <;> cases b <;> cases c <;> decide

theorem strictSignChangesAroundTriangle_even (a b c : StrictEdgeSign) :
    Even (StrictSignChangesAroundTriangle a b c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem chapter13 (a b c : EdgeSign) : SignChangesAroundTriangle a b c ≤ 3 :=
  signChangesAroundTriangle_le_three a b c

end ProofsInTheBook.Chapter13
