import Mathlib
import ProofsInTheBook.Chapter24

namespace ProofsInTheBook.Chapter24

/--
Chapter 24 (Herglotz trick, conditional form):
The Herglotz trick shows that any two functions belonging to the Herglotz class
(periodic-one and odd), which are continuous and satisfy the duplication formula,
must be identical everywhere.
This captures the structural uniqueness argument of the Herglotz trick.
TODO (Tier 2): Verify these hypotheses for the continuous extension of `π·cot(πx)`
and the partial-fraction series `1/x + ∑ 2x/(x²-k²)`.
-/
theorem chapter24 {f g : ℝ → ℝ}
    (hf : HerglotzClass f) (hg : HerglotzClass g)
    (hfc : Continuous f) (hgc : Continuous g)
    (hdup_f : ∀ x, 2 * f x = f (x / 2) + f ((x + 1) / 2))
    (hdup_g : ∀ x, 2 * g x = g (x / 2) + g ((x + 1) / 2))
    (x : ℝ) : f x = g x := by
  have heq : f = g :=
    herglotz_uniqueness_of_continuous_periodic_odd f g hf hg hfc hgc hdup_f hdup_g
      (by rw [hf.eval_half, hg.eval_half])
  rw [heq]

end ProofsInTheBook.Chapter24
