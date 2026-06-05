/-
Chapter 33 (book chapter 32, "Completing Latin squares"): the unconditional
Evans/Smetaniuk completion theorem.

This file only wires together the two halves proved in
`Chapter33Smetaniuk.lean` (the Smetaniuk singleton-element induction,
following the book proof: normalize the unique symbol onto the diagonal,
delete it, induct, and recover it from the back-diagonal extension) and
`Chapter33Ryser.lean` (book Lemma 2: a sparse partial Latin square using at
most `n / 2` symbols completes, by conjugacy and Hall's theorem).
-/
import ProofsInTheBook.Chapter33Smetaniuk
import ProofsInTheBook.Chapter33Ryser

namespace ProofsInTheBook.Chapter33

/-- The bridge: the Ryser-file theorem (book Lemma 2) discharges the
few-symbols hypothesis of the Smetaniuk-file induction.  `elementsUsed` and
`usedSymbols` are the same filter. -/
theorem ryser_hypothesis_holds (n : ℕ) : ryser_few_elements_completes n := by
  intro P hP hcard helem
  cases n with
  | zero =>
      exact ⟨fun i => i.elim0, ⟨fun i => i.elim0, fun j => j.elim0⟩,
        fun i => i.elim0⟩
  | succ m =>
      refine lemma2_few_elements_completes (m + 1) P hP (by omega) ?_
      have heq : elementsUsed P = usedSymbols P := by
        ext a
        simp [elementsUsed, usedSymbols]
      rw [heq]
      exact helem

/--
**Chapter 33, the Evans conjecture (Smetaniuk's theorem), unconditional.**
Every partial Latin square of order `n` with at most `n - 1` filled cells
completes to a Latin square of the same order.
-/
theorem chapter33_unconditional :
    ∀ n : ℕ, LatinSquareCompletionTheorem n :=
  chapter33_unconditional_of_ryser ryser_hypothesis_holds

end ProofsInTheBook.Chapter33
