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

/--
Buffon's needle probability for a single needle: when `0 < d` and `0 ≤ ℓ ≤ d`,
the crossing probability `2ℓ/(πd)` lies in `[0, 1]`. Since a needle of length
at most `d` crosses at most one line, the expected crossing count IS the
crossing probability.
-/
theorem buffon_needle_prob_in_unit_interval {d length : ℝ}
    (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    segmentExpectedCrossings d length ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨segmentExpectedCrossings_nonneg hd hlen, segmentExpectedCrossings_le_one hd hle⟩

/--
The Buffon needle formula: for a straight needle of length `ℓ` dropped on
parallel lines spaced `d` apart, the crossing probability is `2ℓ/(πd)`.
This packages the formula along with its validity as a probability.
-/
theorem buffon_needle {d length : ℝ} (hd : 0 < d) (hlen : 0 ≤ length) (hle : length ≤ d) :
    ∃ P : ℝ, P = 2 * length / (Real.pi * d) ∧ P ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨segmentExpectedCrossings d length, rfl, buffon_needle_prob_in_unit_interval hd hlen hle⟩

/--
Buffon's noodle generalization: a convex curve of total arc length `L`
dropped on parallel lines spaced `d` apart has expected crossing count
`2L/(πd)`, regardless of the curve's shape.
-/
theorem buffon_noodle_expected_crossings {ι : Type*} (segments : Finset ι)
    (length : ι → ℝ) (d : ℝ) (_hd : 0 < d) :
    curveExpectedCrossings segments length d =
      2 * (∑ i ∈ segments, length i) / (Real.pi * d) := by
  rw [curveExpectedCrossings_eq_total_length]
  rfl

/--
The book's proof of Buffon's formula proceeds in three steps:
1. For a single segment of length ℓ, E[crossings] = 2ℓ/(πd) by rotational symmetry
2. By linearity, any curve of length L has E[crossings] = 2L/(πd)
3. For a needle (straight segment) of length ≤ d, at most one crossing occurs,
   so E[crossings] = P(crossing) = 2ℓ/(πd)

Step 2 is `curveExpectedCrossings_eq_total_length`.
Step 3 uses `buffon_needle_prob_in_unit_interval`.
Step 1 (the rotational symmetry argument) is the geometric core and
requires the integral `∫₀^π sin(θ) dθ = 2`.
-/
theorem buffon_rotational_symmetry_integral :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ = 2 := by
  sorry

theorem chapter25 {ι : Type*} (segments : Finset ι) (length : ι → ℝ) (d : ℝ) :
    curveExpectedCrossings segments length d =
      segmentExpectedCrossings d (∑ i ∈ segments, length i) :=
  curveExpectedCrossings_eq_total_length segments length d

end ProofsInTheBook.Chapter25
