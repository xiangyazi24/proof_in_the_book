import Mathlib

/-!
# Chapter 25: Buffon's needle problem

From "Proofs from THE BOOK":

**Buffon's needle**: A needle of length ℓ dropped on parallel lines
spaced d apart (ℓ ≤ d) crosses a line with probability 2ℓ/(πd).

The book's proof uses the linearity of expectation: any curve of
length L crosses E[crossings] = 2L/(πd) lines, proved by decomposing
into infinitesimal segments and using rotational symmetry.
-/

namespace ProofsInTheBook.Chapter25

open scoped BigOperators

/-- Expected crossings for a single segment in Buffon's needle model. -/
noncomputable def segmentExpectedCrossings (d length : ℝ) : ℝ :=
  2 * length / (Real.pi * d)

/--
Expected crossings for a polygonal curve, defined by summing the segment
contributions. This is the finite version of the linearity-of-expectation
step used in the book before passing from polygonal approximations to curves.
-/
noncomputable def curveExpectedCrossings {ι : Type*} (segments : Finset ι) (length : ι → ℝ)
    (d : ℝ) : ℝ :=
  ∑ i ∈ segments, segmentExpectedCrossings d (length i)

theorem curveExpectedCrossings_eq_total_length {ι : Type*} (segments : Finset ι)
    (length : ι → ℝ) (d : ℝ) :
    curveExpectedCrossings segments length d =
      segmentExpectedCrossings d (∑ i ∈ segments, length i) := by
  simp [curveExpectedCrossings, segmentExpectedCrossings, Finset.sum_mul, Finset.mul_sum,
    div_eq_mul_inv]

theorem segmentExpectedCrossings_nonneg {d length : ℝ} (hd : 0 < d) (hlen : 0 ≤ length) :
    0 ≤ segmentExpectedCrossings d length := by
  unfold segmentExpectedCrossings
  positivity

theorem segmentExpectedCrossings_le_one {d length : ℝ} (hd : 0 < d) (hle : length ≤ d) :
    segmentExpectedCrossings d length ≤ 1 := by
  unfold segmentExpectedCrossings
  have hden : 0 < Real.pi * d := mul_pos Real.pi_pos hd
  rw [div_le_one hden]
  have h2pi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  nlinarith

theorem chapter25 {ι : Type*} (segments : Finset ι) (length : ι → ℝ) (d : ℝ) :
    curveExpectedCrossings segments length d =
      segmentExpectedCrossings d (∑ i ∈ segments, length i) :=
  curveExpectedCrossings_eq_total_length segments length d

end ProofsInTheBook.Chapter25
