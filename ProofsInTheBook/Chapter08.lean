import Mathlib

/-!
# Chapter 8: Three times π²/6

From "Proofs from THE BOOK":

**The Basel problem**: ∑_{k=1}^∞ 1/k² = π²/6.

The book presents three proofs:
1. Euler's original proof via the product formula for sin(x)/x.
2. A proof using Parseval's identity for Fourier series.
3. A proof using the substitution x = π·t in ∫₀¹ log(sin πt) dt.

All three establish that ζ(2) = π²/6.
-/

namespace ProofsInTheBook.Chapter08

open Real

/-!
### The Basel problem: ∑ 1/k² = π²/6

*Book proof 1 (Euler).* From the product formula sin(x)/x = ∏(1 - x²/(n²π²)),
expand and compare the x² coefficient: -1/6 = -∑ 1/(n²π²), giving ∑ 1/n² = π²/6.

*Book proof 2 (Parseval).* Apply Parseval's identity to f(x) = x on [-π, π]:
∑ |cₙ|² = (1/2π) ∫ |f|², computing Fourier coefficients explicitly.
-/

theorem chapter08_basel : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) :=
  hasSum_zeta_two

/--
The Euler product formula for sine, in the form `Real.tendsto_euler_sin_prod`:
the partial products `π·x·∏_{j<n} (1 - x²/(j+1)²)` converge to `sin(πx)`.
This is the starting point of the book's first proof of the Basel problem:
expanding the limit and comparing the `x²` coefficient gives `∑ 1/n² = π²/6`.
-/
theorem euler_sine_product_coefficient (x : ℝ) :
    Filter.Tendsto
        (fun n : ℕ => π * x * ∏ j ∈ Finset.range n, ((1 : ℝ) - x ^ 2 / ((j : ℝ) + 1) ^ 2))
        Filter.atTop (nhds (sin (π * x))) :=
  Real.tendsto_euler_sin_prod x

/--
The integral that anchors the book's Parseval proof: `∫_{-π}^{π} x² dx = 2π³/3`.
Combined with Parseval's identity `∑_{n=-∞}^∞ |cₙ|² = (1/2π) ∫ |f|²` for `f(x)=x`
and Fourier coefficients `cₙ = (-1)^n / (n·i)` for `n ≠ 0`, this yields
`∑_{n≠0} 1/n² = π²/3`, hence `∑_{n=1}^∞ 1/n² = π²/6`.
-/
theorem parseval_proof_step :
    ∫ x in (-π)..π, x ^ 2 = 2 * π ^ 3 / 3 := by
  rw [integral_pow]
  ring

theorem chapter08 : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2) (π ^ 2 / 6) :=
  chapter08_basel

end ProofsInTheBook.Chapter08
