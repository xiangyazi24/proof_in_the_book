import Mathlib

/-!
# Chapter 18: In praise of inequalities

From "Proofs from THE BOOK":

**AM-GM inequality**: the geometric mean of finitely many non-negative reals is at most
their arithmetic mean.  The two-variable case `√(ab) ≤ (a+b)/2` is the book's warm-up
(from `(√a - √b)² ≥ 0`); the headline `chapter18` is the general `n`-variable statement.

**Cauchy-Schwarz**: `(∑ aᵢbᵢ)² ≤ (∑ aᵢ²)(∑ bᵢ²)`, the discriminant inequality.
-/

namespace ProofsInTheBook.Chapter18

/-!
### AM-GM: the (a-b)² ≥ 0 trick (two-variable warm-up)
-/

theorem chapter18_sq_abs_le (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem chapter18_am_gm_sq (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    a * b ≤ ((a + b) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Two-variable AM-GM (the book's `(√a - √b)² ≥ 0` proof). -/
theorem chapter18_two_var (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have hsq : a * b ≤ ((a + b) / 2) ^ 2 :=
    chapter18_am_gm_sq a b ha hb
  exact (Real.sqrt_le_left (by nlinarith [ha, hb])).mpr hsq

/-!
### General AM-GM and Cauchy-Schwarz
-/

/-- **AM-GM inequality (general).**  The geometric mean of finitely many non-negative
reals over a nonempty finite index set is at most their arithmetic mean. -/
theorem chapter18 {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹) ≤ (∑ i ∈ s, z i) / s.card := by
  have hcard : (0 : ℝ) < s.card := by
    exact_mod_cast Finset.card_pos.mpr hs
  set w : ι → ℝ := fun _ => (s.card : ℝ)⁻¹ with hw_def
  have hw : ∀ i ∈ s, 0 ≤ w i := by
    intro i _; positivity
  have hw' : ∑ i ∈ s, w i = 1 := by
    simp only [hw_def, Finset.sum_const, nsmul_eq_mul]
    field_simp
  have hgm := Real.geom_mean_le_arith_mean_weighted s w z hw hw' hz
  -- LHS: ∏ z i ^ (1/n) = (∏ z i) ^ (1/n)
  have hprod : ∏ i ∈ s, z i ^ ((s.card : ℝ)⁻¹) = (∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹) :=
    Real.finsetProd_rpow s z hz _
  -- RHS: ∑ (1/n) * z i = (∑ z i) / n
  have hrhs : ∑ i ∈ s, w i * z i = (∑ i ∈ s, z i) / s.card := by
    simp only [hw_def]
    rw [← Finset.mul_sum]
    field_simp
  calc (∏ i ∈ s, z i) ^ ((s.card : ℝ)⁻¹)
      = ∏ i ∈ s, z i ^ ((s.card : ℝ)⁻¹) := hprod.symm
    _ ≤ ∑ i ∈ s, w i * z i := hgm
    _ = (∑ i ∈ s, z i) / s.card := hrhs

/-- **Cauchy-Schwarz inequality** (discrete form): `(∑ fᵢgᵢ)² ≤ (∑ fᵢ²)(∑ gᵢ²)`. -/
theorem chapter18_cauchy_schwarz {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * (∑ i ∈ s, g i ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq s f g

end ProofsInTheBook.Chapter18
