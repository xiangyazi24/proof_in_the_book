import Mathlib

/-!
# Chapter 20: One square and an odd number of triangles

From "Proofs from THE BOOK":

**Monsky's theorem**: A square cannot be divided into an odd number
of triangles of equal area.

The book's proof uses a 2-adic valuation argument: define a coloring
of the plane using the 2-adic valuation of coordinates, then apply
Sperner's lemma to show the triangulation must have an even count.

Formalization status: this file closes the finite coloring and parity layer.
It defines Monsky's three colors, red-green boundary edges, trichromatic
triangles, proves the local parity identity, proves an abstract Sperner
parity theorem, and derives `chapter20`: a `MonskyCertificate n` yields a
trichromatic triangle.  It also packages Mathlib's local-subring/Zorn
infrastructure into `exists_valuation_extension`, which gives an extension of
any valuation on a field to any field extension; in particular
`exists_real_twoAdic_extension` extends `Rat.padicValuation 2` from `ℚ` to `ℝ`.
Using one chosen extension, the file defines Monsky's coloring on `ℝ²`, proves
the unit-square side color constraints, proves the odd red-green boundary
count for any finite subdivision of the square boundary, constructs
`MonskyCertificate` from finite unordered-edge parity, and proves the
valuation contradiction for a trichromatic triangle of oriented rational
double area `± 2 / n` with `n` odd.

Gap to the full book theorem: the remaining work is geometric triangulation
infrastructure.  One needs a finite real triangulation model for the unit
square, extraction of its finite vertex type and triangle list, a theorem that
the odd-multiplicity triangle edges are exactly the four boundary side chains,
and an equal-area theorem expressing every listed triangle as oriented double
area `± 2 / n`.  Mathlib has valuation and geometry components, but not this
assembled polygonal Sperner/Monsky triangulation package.
-/

namespace ProofsInTheBook.Chapter20

open IsLocalRing

/--
Mathlib does not currently expose a one-line theorem named "extend a valuation
to an arbitrary field extension".  The needed existence statement follows from
`IsLocalRing.exists_factor_valuationRing`: apply it to the valuation subring of
the base field, then use localness to prove the new valuation subring lies
exactly over the old one.
-/
theorem exists_valuationSubring_extension
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    ∃ W : ValuationSubring L,
      ∀ x : K, algebraMap K L x ∈ W ↔ x ∈ v.valuationSubring := by
  classical
  let O : ValuationSubring K := v.valuationSubring
  let f : O →+* L := (algebraMap K L).comp O.subtype
  obtain ⟨W, hWmem, _hWlocal⟩ := IsLocalRing.exists_factor_valuationRing (K := L) f
  refine ⟨W, ?_⟩
  intro x
  constructor
  · intro hxW
    by_contra hxO
    have hx0 : x ≠ 0 := by
      intro hx0
      exact hxO (by simp [hx0])
    have hxinvO : x⁻¹ ∈ O := by
      rcases O.mem_or_inv_mem x with hx | hx
      · exact (hxO hx).elim
      · exact hx
    let a : O := ⟨x⁻¹, hxinvO⟩
    let g : O →+* W := f.codRestrict W.toSubring hWmem
    have hmax : a ∈ maximalIdeal O := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]
      exact (ValuationSubring.inv_mem_nonunits_iff (A := O)).2 (Or.inr hxO)
    have hgmax : g a ∈ maximalIdeal W := by
      exact map_nonunit g a hmax
    have hgunit : IsUnit (g a) := by
      refine IsUnit.of_mul_eq_one (M := W) (a := g a) ⟨algebraMap K L x, hxW⟩ ?_
      ext
      simp [g, f, a, hx0]
    exact hgmax hgunit
  · intro hxO
    simpa [f, O] using hWmem ⟨x, hxO⟩

/--
Every valuation on a field extends, up to Mathlib's valuation equivalence, to
any field extension.  The extended valuation takes values in the natural value
group attached to the chosen valuation subring of the extension field.
-/
theorem exists_valuation_extension
    {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    ∃ W : ValuationSubring L, v.HasExtension W.valuation := by
  classical
  obtain ⟨W, hW⟩ := exists_valuationSubring_extension (K := K) (L := L) v
  refine ⟨W, ?_⟩
  refine ⟨?_⟩
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  change v x ≤ 1 ↔ W.valuation (algebraMap K L x) ≤ 1
  rw [ValuationSubring.valuation_le_one_iff, hW, Valuation.mem_valuationSubring_iff]

/-- The 2-adic valuation on `ℚ` has a valuation-subring extension to `ℝ`. -/
theorem exists_real_twoAdic_extension :
    ∃ W : ValuationSubring ℝ, (Rat.padicValuation 2).HasExtension W.valuation :=
  exists_valuation_extension (K := ℚ) (L := ℝ) (Rat.padicValuation 2)

/-- The three colors used in Monsky's 2-adic coloring argument. -/
inductive MonskyColor where
  | red | green | blue
  deriving DecidableEq, Repr, Fintype

open MonskyColor

@[simp]
theorem MonskyColor.card : Fintype.card MonskyColor = 3 := rfl

/--
Monsky's coloring in multiplicative valuation language.  Additive conditions
`v(x) > 0` and `v(x) ≤ v(y)` become `V(x) < 1` and `V(y) ≤ V(x)` for the
multiplicative valuation used by Mathlib's `Valuation`.
-/
def colorOfValues {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (vx vy : Γ) :
    MonskyColor :=
  if vx < 1 ∧ vy < 1 then red
  else if 1 ≤ vx ∧ vy ≤ vx then green
  else blue

@[simp]
theorem colorOfValues_zero_zero {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] :
    colorOfValues (0 : Γ) (0 : Γ) = red := by
  simp [colorOfValues]

@[simp]
theorem colorOfValues_one_zero {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] :
    colorOfValues (1 : Γ) (0 : Γ) = green := by
  simp [colorOfValues]

@[simp]
theorem colorOfValues_zero_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] :
    colorOfValues (0 : Γ) (1 : Γ) = blue := by
  simp [colorOfValues]

@[simp]
theorem colorOfValues_one_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] :
    colorOfValues (1 : Γ) (1 : Γ) = green := by
  simp [colorOfValues]

theorem colorOfValues_zero_right_red_or_green {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vx : Γ) : colorOfValues vx 0 = red ∨ colorOfValues vx 0 = green := by
  unfold colorOfValues
  by_cases hx : vx < 1
  · simp [hx]
  · have hxge : 1 ≤ vx := le_of_not_gt hx
    right
    simp [hx, hxge]

theorem colorOfValues_one_left_green_or_blue {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vy : Γ) : colorOfValues 1 vy = green ∨ colorOfValues 1 vy = blue := by
  unfold colorOfValues
  by_cases hy : vy ≤ 1
  · left
    simp [hy]
  · right
    simp [hy]

theorem colorOfValues_one_right_green_or_blue {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vx : Γ) : colorOfValues vx 1 = green ∨ colorOfValues vx 1 = blue := by
  unfold colorOfValues
  by_cases hx : 1 ≤ vx
  · left
    simp [hx]
  · right
    have hxlt : vx < 1 := lt_of_not_ge hx
    simp [hx, hxlt]

theorem colorOfValues_zero_left_red_or_blue {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (vy : Γ) : colorOfValues 0 vy = red ∨ colorOfValues 0 vy = blue := by
  unfold colorOfValues
  by_cases hy : vy < 1
  · left
    simp [hy]
  · right
    simp [hy]

theorem colorOfValues_eq_red_iff {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {vx vy : Γ} :
    colorOfValues vx vy = red ↔ vx < 1 ∧ vy < 1 := by
  unfold colorOfValues
  by_cases hred : vx < 1 ∧ vy < 1
  · simp [hred]
  · by_cases hgreen : 1 ≤ vx ∧ vy ≤ vx
    · simp [hred, hgreen]
    · simp [hred, hgreen]

theorem colorOfValues_green_le {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {vx vy : Γ} (h : colorOfValues vx vy = green) : 1 ≤ vx ∧ vy ≤ vx := by
  unfold colorOfValues at h
  by_cases hred : vx < 1 ∧ vy < 1
  · simp [hred] at h
  · by_cases hgreen : 1 ≤ vx ∧ vy ≤ vx
    · exact hgreen
    · simp [hred, hgreen] at h

theorem colorOfValues_green_not_red {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {vx vy : Γ} (h : colorOfValues vx vy = green) : ¬ (vx < 1 ∧ vy < 1) := by
  unfold colorOfValues at h
  by_cases hred : vx < 1 ∧ vy < 1
  · simp [hred] at h
  · exact hred

theorem colorOfValues_blue_lt_and_one_le {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {vx vy : Γ} (h : colorOfValues vx vy = blue) : vx < vy ∧ 1 ≤ vy := by
  unfold colorOfValues at h
  by_cases hred : vx < 1 ∧ vy < 1
  · simp [hred] at h
  · by_cases hgreen : 1 ≤ vx ∧ vy ≤ vx
    · simp [hred, hgreen] at h
    · simp [hred, hgreen] at h
      have hvx_lt_one_or : vx < 1 ∨ 1 ≤ vx := lt_or_ge vx 1
      have hvy_lt_or : vy < 1 ∨ 1 ≤ vy := lt_or_ge vy 1
      constructor
      · by_contra hnot
        have hvyle : vy ≤ vx := le_of_not_gt hnot
        rcases hvx_lt_one_or with hvxlt | hvxge
        · have hvylt : vy < 1 := lt_of_le_of_lt hvyle hvxlt
          exact hred ⟨hvxlt, hvylt⟩
        · exact hgreen ⟨hvxge, hvyle⟩
      · rcases hvy_lt_or with hvylt | hvyge
        · rcases hvx_lt_one_or with hvxlt | hvxge
          · exact (hred ⟨hvxlt, hvylt⟩).elim
          · exact (hgreen ⟨hvxge, (le_of_lt hvylt).trans hvxge⟩).elim
        · exact hvyge

/-- The Monsky coloring of a point from any multiplicative valuation. -/
def valuationColor {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (p : K × K) : MonskyColor :=
  colorOfValues (v p.1) (v p.2)

@[simp]
theorem valuationColor_origin {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) :
    valuationColor v (0, 0) = red := by
  simp [valuationColor, colorOfValues]

@[simp]
theorem valuationColor_one_zero {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) :
    valuationColor v (1, 0) = green := by
  simp [valuationColor, colorOfValues]

@[simp]
theorem valuationColor_zero_one {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) :
    valuationColor v (0, 1) = blue := by
  simp [valuationColor, colorOfValues]

@[simp]
theorem valuationColor_one_one {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) :
    valuationColor v (1, 1) = green := by
  simp [valuationColor, colorOfValues]

/-- Twice the oriented area of a triangle with coordinates in a ring. -/
def doubleArea {K : Type*} [Ring K] (a b c : K × K) : K :=
  (b.1 - a.1) * (c.2 - a.2) - (c.1 - a.1) * (b.2 - a.2)

/--
A red-green-blue triangle has double area with valuation at least `1` in
Mathlib's multiplicative convention.  This is the valuation side of Monsky's
area contradiction; an odd equal subdivision will later give double area
`2 / n`, whose 2-adic valuation is `< 1`.
-/
theorem valuation_doubleArea_red_green_blue
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {r g b : K × K}
    (hr : valuationColor v r = red)
    (hg : valuationColor v g = green)
    (hb : valuationColor v b = blue) :
    1 ≤ v (doubleArea r g b) := by
  have hr_lt : v r.1 < 1 ∧ v r.2 < 1 := colorOfValues_eq_red_iff.mp hr
  have hg_le : 1 ≤ v g.1 ∧ v g.2 ≤ v g.1 := colorOfValues_green_le hg
  have hb_lt : v b.1 < v b.2 ∧ 1 ≤ v b.2 := colorOfValues_blue_lt_and_one_le hb
  have hrgx : v (g.1 - r.1) = v g.1 := by
    exact v.map_sub_eq_of_lt_left (lt_of_lt_of_le hr_lt.1 hg_le.1)
  have hrby : v (b.2 - r.2) = v b.2 := by
    exact v.map_sub_eq_of_lt_left (lt_of_lt_of_le hr_lt.2 hb_lt.2)
  have hrgy_le : v (g.2 - r.2) ≤ v g.1 := by
    exact v.map_sub_le hg_le.2 ((le_of_lt hr_lt.2).trans hg_le.1)
  have hrbx_lt : v (b.1 - r.1) < v b.2 := by
    exact lt_of_le_of_lt (v.map_sub b.1 r.1)
      (max_lt hb_lt.1 (lt_of_lt_of_le hr_lt.1 hb_lt.2))
  let t₁ : K := (g.1 - r.1) * (b.2 - r.2)
  let t₂ : K := (b.1 - r.1) * (g.2 - r.2)
  have ht₁ : v t₁ = v g.1 * v b.2 := by
    simp [t₁, hrgx, hrby]
  have ht₂_lt : v t₂ < v g.1 * v b.2 := by
    have hle :
        v (b.1 - r.1) * v (g.2 - r.2) ≤ v (b.1 - r.1) * v g.1 :=
      mul_le_mul' le_rfl hrgy_le
    have hlt : v (b.1 - r.1) * v g.1 < v b.2 * v g.1 := by
      exact (strictMono_mul_right_of_pos (lt_of_lt_of_le zero_lt_one hg_le.1)) hrbx_lt
    have hmul : v (b.1 - r.1) * v (g.2 - r.2) < v b.2 * v g.1 :=
      lt_of_le_of_lt hle hlt
    simpa [t₂, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hdet : v (doubleArea r g b) = v g.1 * v b.2 := by
    change v (t₁ - t₂) = v g.1 * v b.2
    rw [v.map_sub_eq_of_lt_left]
    · exact ht₁
    · rw [ht₁]
      exact ht₂_lt
  rw [hdet]
  calc
    (1 : Γ) = 1 * 1 := by rw [mul_one]
    _ ≤ v g.1 * v b.2 := mul_le_mul' hg_le.1 hb_lt.2

/-- A chosen valuation subring of `ℝ` extending the 2-adic valuation on `ℚ`. -/
noncomputable def realTwoAdicSubring : ValuationSubring ℝ :=
  Classical.choose exists_real_twoAdic_extension

/-- The corresponding chosen real-valued-field valuation for Monsky coloring. -/
noncomputable def realTwoAdicValuation : Valuation ℝ realTwoAdicSubring.ValueGroup :=
  realTwoAdicSubring.valuation

theorem realTwoAdic_hasExtension :
    (Rat.padicValuation 2).HasExtension realTwoAdicValuation :=
  Classical.choose_spec exists_real_twoAdic_extension

/-- Odd natural numbers have 2-adic valuation `1` in multiplicative notation. -/
theorem rat_twoAdicValuation_natCast_of_odd {n : ℕ} (hn : Odd n) :
    Rat.padicValuation 2 (n : ℚ) = 1 := by
  have hnotdvd_nat : ¬ 2 ∣ n := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hn) ((even_iff_two_dvd).2 h)
  have hnotdvd_int : ¬ (2 : ℤ) ∣ (n : ℤ) := by
    exact_mod_cast hnotdvd_nat
  change Rat.padicValuation 2 (((n : ℤ) : ℚ)) = 1
  rw [Rat.padicValuation_cast]
  exact (Int.padicValuation_eq_one_iff (p := 2) (x := (n : ℤ))).2 hnotdvd_int

/-- If `n` is odd, the rational double area `2 / n` has 2-adic valuation `< 1`. -/
theorem rat_twoAdicValuation_two_div_odd_lt_one {n : ℕ} (hn : Odd n) :
    Rat.padicValuation 2 ((2 : ℚ) / n) < 1 := by
  rw [map_div₀]
  have h2 : Rat.padicValuation 2 ((2 : ℚ)) = WithZero.exp (-1 : ℤ) := by
    simpa using Rat.padicValuation_self 2
  rw [h2, rat_twoAdicValuation_natCast_of_odd hn, div_one]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

/--
The same `< 1` estimate after transporting `2 / n` into the chosen real
2-adic valuation extension.
-/
theorem realTwoAdicValuation_rat_two_div_odd_lt_one {n : ℕ} (hn : Odd n) :
    realTwoAdicValuation (((2 : ℚ) / n : ℚ) : ℝ) < 1 := by
  letI : (Rat.padicValuation 2).HasExtension realTwoAdicValuation := realTwoAdic_hasExtension
  have hrat :
      Rat.padicValuation 2 (((2 : ℚ) / n : ℚ)) < Rat.padicValuation 2 (1 : ℚ) := by
    simpa using rat_twoAdicValuation_two_div_odd_lt_one hn
  have h := (Valuation.HasExtension.val_map_lt_iff
    (vR := Rat.padicValuation 2) (vA := realTwoAdicValuation) (((2 : ℚ) / n : ℚ)) 1).2 hrat
  simpa using h

/-- The chosen Monsky 2-adic coloring on the real plane. -/
noncomputable def realTwoAdicColor (p : ℝ × ℝ) : MonskyColor :=
  valuationColor realTwoAdicValuation p

/--
A red-green-blue triangle cannot have rational double area `2 / n` when `n`
is odd.  This is the valuation contradiction at the end of Monsky's proof,
separated from the still-missing geometric construction of the finite
triangulation certificate.
-/
theorem not_real_doubleArea_eq_two_div_odd_of_red_green_blue {n : ℕ} (hn : Odd n)
    {r g b : ℝ × ℝ}
    (hr : realTwoAdicColor r = red)
    (hg : realTwoAdicColor g = green)
    (hb : realTwoAdicColor b = blue)
    (harea : doubleArea r g b = (((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  have hge : 1 ≤ realTwoAdicValuation (doubleArea r g b) := by
    exact valuation_doubleArea_red_green_blue realTwoAdicValuation
      (by simpa [realTwoAdicColor] using hr)
      (by simpa [realTwoAdicColor] using hg)
      (by simpa [realTwoAdicColor] using hb)
  rw [harea] at hge
  exact not_lt_of_ge hge (realTwoAdicValuation_rat_two_div_odd_lt_one hn)

/-- Negating the odd-denominator rational double area does not change the 2-adic bound. -/
theorem realTwoAdicValuation_neg_rat_two_div_odd_lt_one {n : ℕ} (hn : Odd n) :
    realTwoAdicValuation (-(((2 : ℚ) / n : ℚ) : ℝ)) < 1 := by
  simpa using realTwoAdicValuation_rat_two_div_odd_lt_one hn

/-- The negative-orientation variant of the Monsky area contradiction. -/
theorem not_real_doubleArea_eq_neg_two_div_odd_of_red_green_blue {n : ℕ} (hn : Odd n)
    {r g b : ℝ × ℝ}
    (hr : realTwoAdicColor r = red)
    (hg : realTwoAdicColor g = green)
    (hb : realTwoAdicColor b = blue)
    (harea : doubleArea r g b = -(((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  have hge : 1 ≤ realTwoAdicValuation (doubleArea r g b) := by
    exact valuation_doubleArea_red_green_blue realTwoAdicValuation
      (by simpa [realTwoAdicColor] using hr)
      (by simpa [realTwoAdicColor] using hg)
      (by simpa [realTwoAdicColor] using hb)
  rw [harea] at hge
  exact not_lt_of_ge hge (realTwoAdicValuation_neg_rat_two_div_odd_lt_one hn)

@[simp]
theorem realTwoAdicColor_origin : realTwoAdicColor (0, 0) = red := by
  simp [realTwoAdicColor, valuationColor, colorOfValues, realTwoAdicValuation]

@[simp]
theorem realTwoAdicColor_one_zero : realTwoAdicColor (1, 0) = green := by
  simp [realTwoAdicColor, valuationColor, colorOfValues, realTwoAdicValuation]

@[simp]
theorem realTwoAdicColor_zero_one : realTwoAdicColor (0, 1) = blue := by
  simp [realTwoAdicColor, valuationColor, colorOfValues, realTwoAdicValuation]

@[simp]
theorem realTwoAdicColor_one_one : realTwoAdicColor (1, 1) = green := by
  simp [realTwoAdicColor, valuationColor, colorOfValues, realTwoAdicValuation]

theorem realTwoAdicColor_bottom_red_or_green (x : ℝ) :
    realTwoAdicColor (x, 0) = red ∨ realTwoAdicColor (x, 0) = green := by
  simpa [realTwoAdicColor, valuationColor] using
    colorOfValues_zero_right_red_or_green (realTwoAdicValuation x)

theorem realTwoAdicColor_right_green_or_blue (y : ℝ) :
    realTwoAdicColor (1, y) = green ∨ realTwoAdicColor (1, y) = blue := by
  simpa [realTwoAdicColor, valuationColor] using
    colorOfValues_one_left_green_or_blue (realTwoAdicValuation y)

theorem realTwoAdicColor_top_green_or_blue (x : ℝ) :
    realTwoAdicColor (x, 1) = green ∨ realTwoAdicColor (x, 1) = blue := by
  simpa [realTwoAdicColor, valuationColor] using
    colorOfValues_one_right_green_or_blue (realTwoAdicValuation x)

theorem realTwoAdicColor_left_red_or_blue (y : ℝ) :
    realTwoAdicColor (0, y) = red ∨ realTwoAdicColor (0, y) = blue := by
  simpa [realTwoAdicColor, valuationColor] using
    colorOfValues_zero_left_red_or_blue (realTwoAdicValuation y)

/-- A triangle is trichromatic when its three vertex colors are pairwise different. -/
def TrichromaticTriangle (a b c : MonskyColor) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ a

/-- Orientation-free red-green edge predicate used in the Sperner parity count. -/
def RedGreenEdge (a b : MonskyColor) : Prop :=
  (a = red ∧ b = green) ∨ (a = green ∧ b = red)

instance decidableRedGreenEdge (a b : MonskyColor) : Decidable (RedGreenEdge a b) := by
  unfold RedGreenEdge
  infer_instance

/--
The red-green boundary count for the four unit-square corners, traversed
counterclockwise.  This is the corner-level oddness that the full geometric
boundary triangulation must refine.
-/
noncomputable def unitSquareCornerBoundaryRGCount : ℕ :=
  (if RedGreenEdge (realTwoAdicColor (0, 0)) (realTwoAdicColor (1, 0)) then 1 else 0) +
  (if RedGreenEdge (realTwoAdicColor (1, 0)) (realTwoAdicColor (1, 1)) then 1 else 0) +
  (if RedGreenEdge (realTwoAdicColor (1, 1)) (realTwoAdicColor (0, 1)) then 1 else 0) +
  (if RedGreenEdge (realTwoAdicColor (0, 1)) (realTwoAdicColor (0, 0)) then 1 else 0)

theorem unitSquareCornerBoundaryRGCount_eq_one :
    unitSquareCornerBoundaryRGCount = 1 := by
  simp [unitSquareCornerBoundaryRGCount, RedGreenEdge]

theorem unitSquareCornerBoundaryRGCount_odd : Odd unitSquareCornerBoundaryRGCount := by
  rw [unitSquareCornerBoundaryRGCount_eq_one]
  exact odd_one

instance decidableTrichromaticTriangle (a b c : MonskyColor) :
    Decidable (TrichromaticTriangle a b c) := by
  unfold TrichromaticTriangle
  infer_instance

theorem trichromatic_of_eq_red_green_blue {a b c : MonskyColor}
    (ha : a = red) (hb : b = green) (hc : c = blue) : TrichromaticTriangle a b c := by
  subst a
  subst b
  subst c
  simp [TrichromaticTriangle]

/-- `TrichromaticTriangle` is invariant under swapping the last two vertices. -/
theorem trichromaticTriangle_swap_right {a b c : MonskyColor} :
    TrichromaticTriangle a b c ↔ TrichromaticTriangle a c b := by
  cases a <;> cases b <;> cases c <;> decide

/--
Any trichromatic triangle with odd rational double area contradicts the chosen
real 2-adic Monsky coloring.  The case split only reorders the three vertices
so that the area estimate sees them in red-green-blue order.
-/
theorem not_real_doubleArea_eq_two_div_odd_of_trichromatic {n : ℕ} (hn : Odd n)
    {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c))
    (harea : doubleArea a b c = (((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  generalize hca : realTwoAdicColor a = ca at htri
  generalize hcb : realTwoAdicColor b = cb at htri
  generalize hcc : realTwoAdicColor c = cc at htri
  cases ca <;> cases cb <;> cases cc <;> simp [TrichromaticTriangle] at htri
  · exact not_real_doubleArea_eq_two_div_odd_of_red_green_blue hn hca hcb hcc harea
  · have hperm : doubleArea a c b = -doubleArea a b c := by
      unfold doubleArea
      ring
    have harea' : doubleArea a c b = -(((2 : ℚ) / n : ℚ) : ℝ) := by
      rw [hperm, harea]
    exact not_real_doubleArea_eq_neg_two_div_odd_of_red_green_blue hn hca hcc hcb harea'
  · have hperm : doubleArea b a c = -doubleArea a b c := by
      unfold doubleArea
      ring
    have harea' : doubleArea b a c = -(((2 : ℚ) / n : ℚ) : ℝ) := by
      rw [hperm, harea]
    exact not_real_doubleArea_eq_neg_two_div_odd_of_red_green_blue hn hcb hca hcc harea'
  · have hperm : doubleArea c a b = doubleArea a b c := by
      unfold doubleArea
      ring
    have harea' : doubleArea c a b = (((2 : ℚ) / n : ℚ) : ℝ) := by
      rw [hperm, harea]
    exact not_real_doubleArea_eq_two_div_odd_of_red_green_blue hn hcc hca hcb harea'
  · have hperm : doubleArea b c a = doubleArea a b c := by
      unfold doubleArea
      ring
    have harea' : doubleArea b c a = (((2 : ℚ) / n : ℚ) : ℝ) := by
      rw [hperm, harea]
    exact not_real_doubleArea_eq_two_div_odd_of_red_green_blue hn hcb hcc hca harea'
  · have hperm : doubleArea c b a = -doubleArea a b c := by
      unfold doubleArea
      ring
    have harea' : doubleArea c b a = -(((2 : ℚ) / n : ℚ) : ℝ) := by
      rw [hperm, harea]
    exact not_real_doubleArea_eq_neg_two_div_odd_of_red_green_blue hn hcc hcb hca harea'

/-- The negative-orientation form of `not_real_doubleArea_eq_two_div_odd_of_trichromatic`. -/
theorem not_real_doubleArea_eq_neg_two_div_odd_of_trichromatic {n : ℕ} (hn : Odd n)
    {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c))
    (harea : doubleArea a b c = -(((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  have hperm : doubleArea a c b = -doubleArea a b c := by
    unfold doubleArea
    ring
  have harea' : doubleArea a c b = (((2 : ℚ) / n : ℚ) : ℝ) := by
    rw [hperm, harea]
    simp
  exact not_real_doubleArea_eq_two_div_odd_of_trichromatic hn
    (trichromaticTriangle_swap_right.mp htri) harea'

/-- Orientation-free odd equal-area contradiction for a trichromatic triangle. -/
theorem not_real_doubleArea_eq_abs_two_div_odd_of_trichromatic {n : ℕ} (hn : Odd n)
    {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c))
    (harea : doubleArea a b c = (((2 : ℚ) / n : ℚ) : ℝ) ∨
      doubleArea a b c = -(((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  rcases harea with harea | harea
  · exact not_real_doubleArea_eq_two_div_odd_of_trichromatic hn htri harea
  · exact not_real_doubleArea_eq_neg_two_div_odd_of_trichromatic hn htri harea

theorem not_trichromatic_of_first_two_same {a b c : MonskyColor}
    (hab : a = b) : ¬ TrichromaticTriangle a b c := by
  intro h
  exact h.1 hab

/-- `RedGreenEdge` is symmetric in its two arguments. -/
theorem redGreenEdge_symm {a b : MonskyColor} : RedGreenEdge a b ↔ RedGreenEdge b a := by
  unfold RedGreenEdge; tauto

/-- A `RedGreenEdge` pair has distinct vertices. -/
theorem redGreenEdge_ne {a b : MonskyColor} (h : RedGreenEdge a b) : a ≠ b := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst ha <;> subst hb <;> decide

/-- A `RedGreenEdge` pair never contains a blue vertex. -/
theorem redGreenEdge_not_blue {a b : MonskyColor} (h : RedGreenEdge a b) :
    a ≠ blue ∧ b ≠ blue := by
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> subst ha <;> subst hb <;> exact ⟨by decide, by decide⟩

/-- A self-loop is never a red-green edge. -/
@[simp]
theorem not_redGreenEdge_self (a : MonskyColor) : ¬ RedGreenEdge a a := by
  cases a <;> decide

/-- A red-green edge between `a` and `b` forces one to be red and the other green. -/
theorem redGreenEdge_cases {a b : MonskyColor} (h : RedGreenEdge a b) :
    (a = red ∧ b = green) ∨ (a = green ∧ b = red) := h

/-- Predicate for colors lying on the red-green side of the Monsky boundary argument. -/
def colorIsRedGreen (c : MonskyColor) : Prop := c = red ∨ c = green

/-- Predicate for colors lying on the green-blue sides of the Monsky boundary argument. -/
def colorIsGreenBlue (c : MonskyColor) : Prop := c = green ∨ c = blue

/-- Predicate for colors lying on the red-blue side of the Monsky boundary argument. -/
def colorIsRedBlue (c : MonskyColor) : Prop := c = red ∨ c = blue

/-- Encode red/green colors in `ZMod 2`; blue is unused when the red-green invariant applies. -/
def colorRGParityBit : MonskyColor → ZMod 2
  | red => 0
  | green => 1
  | blue => 0

/-- Red-green transition count along a finite color chain. -/
def listRGTransitionCount : List MonskyColor → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if RedGreenEdge a b then 1 else 0) + listRGTransitionCount (b :: rest)

theorem redGreenEdge_indicator_zmod_eq_bit_add {a b : MonskyColor}
    (ha : colorIsRedGreen a) (hb : colorIsRedGreen b) :
    ((if RedGreenEdge a b then 1 else 0 : ℕ) : ZMod 2) =
      colorRGParityBit a + colorRGParityBit b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem listRGTransitionCount_cons_append_zmod {a b : MonskyColor} (middle : List MonskyColor)
    (hcolors : ∀ c ∈ a :: middle ++ [b], colorIsRedGreen c) :
    (listRGTransitionCount (a :: middle ++ [b]) : ZMod 2) =
      colorRGParityBit a + colorRGParityBit b := by
  induction middle generalizing a with
  | nil =>
      have ha : colorIsRedGreen a := hcolors a (by simp)
      have hb : colorIsRedGreen b := hcolors b (by simp)
      simp [listRGTransitionCount, redGreenEdge_indicator_zmod_eq_bit_add ha hb]
  | cons x xs ih =>
      have ha : colorIsRedGreen a := hcolors a (by simp)
      have hx : colorIsRedGreen x := hcolors x (by simp)
      have htail : ∀ c ∈ x :: xs ++ [b], colorIsRedGreen c := by
        intro c hc
        exact hcolors c (List.mem_cons.mpr (Or.inr hc))
      have hfirst := redGreenEdge_indicator_zmod_eq_bit_add ha hx
      have htailcount := ih (a := x) htail
      simp only [List.cons_append] at htailcount
      simp only [List.cons_append, listRGTransitionCount]
      rw [Nat.cast_add, hfirst, htailcount]
      rcases hx with rfl | rfl <;> cases a <;> cases b <;> decide

theorem listRGTransitionCount_odd_of_red_to_green (middle : List MonskyColor)
    (hcolors : ∀ c ∈ red :: middle ++ [green], colorIsRedGreen c) :
    Odd (listRGTransitionCount (red :: middle ++ [green])) := by
  have h := listRGTransitionCount_cons_append_zmod (a := red) (b := green) middle hcolors
  simp [colorRGParityBit] at h
  exact ZMod.natCast_eq_one_iff_odd.mp h

theorem not_redGreenEdge_of_greenBlue {a b : MonskyColor}
    (ha : colorIsGreenBlue a) (hb : colorIsGreenBlue b) : ¬ RedGreenEdge a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem not_redGreenEdge_of_redBlue {a b : MonskyColor}
    (ha : colorIsRedBlue a) (hb : colorIsRedBlue b) : ¬ RedGreenEdge a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

theorem listRGTransitionCount_eq_zero_of_greenBlue :
    ∀ l : List MonskyColor, (∀ c ∈ l, colorIsGreenBlue c) → listRGTransitionCount l = 0 := by
  intro l
  induction l with
  | nil => simp [listRGTransitionCount]
  | cons a tail ih =>
      intro h
      cases tail with
      | nil => simp [listRGTransitionCount]
      | cons b rest =>
          have ha : colorIsGreenBlue a := h a (by simp)
          have hb : colorIsGreenBlue b := h b (by simp)
          have htail : ∀ c ∈ b :: rest, colorIsGreenBlue c := by
            intro c hc
            exact h c (List.mem_cons.mpr (Or.inr hc))
          have hn : ¬ RedGreenEdge a b := not_redGreenEdge_of_greenBlue ha hb
          simp [listRGTransitionCount, hn, ih htail]

theorem listRGTransitionCount_eq_zero_of_redBlue :
    ∀ l : List MonskyColor, (∀ c ∈ l, colorIsRedBlue c) → listRGTransitionCount l = 0 := by
  intro l
  induction l with
  | nil => simp [listRGTransitionCount]
  | cons a tail ih =>
      intro h
      cases tail with
      | nil => simp [listRGTransitionCount]
      | cons b rest =>
          have ha : colorIsRedBlue a := h a (by simp)
          have hb : colorIsRedBlue b := h b (by simp)
          have htail : ∀ c ∈ b :: rest, colorIsRedBlue c := by
            intro c hc
            exact h c (List.mem_cons.mpr (Or.inr hc))
          have hn : ¬ RedGreenEdge a b := not_redGreenEdge_of_redBlue ha hb
          simp [listRGTransitionCount, hn, ih htail]

/--
Boundary-color parity for a square contour already split into four side chains.
This is the finite-color statement behind Monsky's boundary oddness.
-/
theorem squareBoundaryRGCount_odd_of_side_color_lists
    (bottom right top left : List MonskyColor)
    (hbottom : ∀ c ∈ red :: bottom ++ [green], colorIsRedGreen c)
    (hright : ∀ c ∈ green :: right ++ [green], colorIsGreenBlue c)
    (htop : ∀ c ∈ green :: top ++ [blue], colorIsGreenBlue c)
    (hleft : ∀ c ∈ blue :: left ++ [red], colorIsRedBlue c) :
    Odd (listRGTransitionCount (red :: bottom ++ [green]) +
      listRGTransitionCount (green :: right ++ [green]) +
      listRGTransitionCount (green :: top ++ [blue]) +
      listRGTransitionCount (blue :: left ++ [red])) := by
  have hbot := listRGTransitionCount_odd_of_red_to_green bottom hbottom
  have hright0 := listRGTransitionCount_eq_zero_of_greenBlue (green :: right ++ [green]) hright
  have htop0 := listRGTransitionCount_eq_zero_of_greenBlue (green :: top ++ [blue]) htop
  have hleft0 := listRGTransitionCount_eq_zero_of_redBlue (blue :: left ++ [red]) hleft
  rw [hright0, htop0, hleft0]
  simpa using hbot

theorem realTwoAdicColor_bottom_list_redGreen (xs : List ℝ) :
    ∀ c ∈ red :: ((xs.map fun x => realTwoAdicColor (x, 0)) ++ [green]),
      colorIsRedGreen c := by
  intro c hc
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
  rcases hc with rfl | ⟨x, _hx, rfl⟩ | hlast
  · exact Or.inl rfl
  · exact realTwoAdicColor_bottom_red_or_green x
  · rcases hlast with rfl | hnil
    · exact Or.inr rfl
    · cases hnil

theorem realTwoAdicColor_right_list_greenBlue (ys : List ℝ) :
    ∀ c ∈ green :: ((ys.map fun y => realTwoAdicColor (1, y)) ++ [green]),
      colorIsGreenBlue c := by
  intro c hc
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
  rcases hc with rfl | ⟨y, _hy, rfl⟩ | hlast
  · exact Or.inl rfl
  · exact realTwoAdicColor_right_green_or_blue y
  · rcases hlast with rfl | hnil
    · exact Or.inl rfl
    · cases hnil

theorem realTwoAdicColor_top_list_greenBlue (xs : List ℝ) :
    ∀ c ∈ green :: ((xs.map fun x => realTwoAdicColor (x, 1)) ++ [blue]),
      colorIsGreenBlue c := by
  intro c hc
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
  rcases hc with rfl | ⟨x, _hx, rfl⟩ | hlast
  · exact Or.inl rfl
  · exact realTwoAdicColor_top_green_or_blue x
  · rcases hlast with rfl | hnil
    · exact Or.inr rfl
    · cases hnil

theorem realTwoAdicColor_left_list_redBlue (ys : List ℝ) :
    ∀ c ∈ blue :: ((ys.map fun y => realTwoAdicColor (0, y)) ++ [red]),
      colorIsRedBlue c := by
  intro c hc
  simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
  rcases hc with rfl | ⟨y, _hy, rfl⟩ | hlast
  · exact Or.inr rfl
  · exact realTwoAdicColor_left_red_or_blue y
  · rcases hlast with rfl | hnil
    · exact Or.inl rfl
    · cases hnil

/-- Boundary oddness for any finite subdivision of the four sides of the unit square. -/
theorem realTwoAdic_squareBoundaryRGCount_odd_of_side_subdivisions
    (bottom right top left : List ℝ) :
    Odd (listRGTransitionCount
        (red :: ((bottom.map fun x => realTwoAdicColor (x, 0)) ++ [green])) +
      listRGTransitionCount
        (green :: ((right.map fun y => realTwoAdicColor (1, y)) ++ [green])) +
      listRGTransitionCount
        (green :: ((top.map fun x => realTwoAdicColor (x, 1)) ++ [blue])) +
      listRGTransitionCount
        (blue :: ((left.map fun y => realTwoAdicColor (0, y)) ++ [red]))) := by
  exact squareBoundaryRGCount_odd_of_side_color_lists
    (bottom.map fun x => realTwoAdicColor (x, 0))
    (right.map fun y => realTwoAdicColor (1, y))
    (top.map fun x => realTwoAdicColor (x, 1))
    (left.map fun y => realTwoAdicColor (0, y))
    (realTwoAdicColor_bottom_list_redGreen bottom)
    (realTwoAdicColor_right_list_greenBlue right)
    (realTwoAdicColor_top_list_greenBlue top)
    (realTwoAdicColor_left_list_redBlue left)

/-- Red-green count along the four color-constrained sides of the unit square. -/
noncomputable def realTwoAdicSquareBoundaryRGChainCount
    (bottom right top left : List ℝ) : ℕ :=
  listRGTransitionCount (red :: ((bottom.map fun x => realTwoAdicColor (x, 0)) ++ [green])) +
  listRGTransitionCount (green :: ((right.map fun y => realTwoAdicColor (1, y)) ++ [green])) +
  listRGTransitionCount (green :: ((top.map fun x => realTwoAdicColor (x, 1)) ++ [blue])) +
  listRGTransitionCount (blue :: ((left.map fun y => realTwoAdicColor (0, y)) ++ [red]))

theorem realTwoAdicSquareBoundaryRGChainCount_odd (bottom right top left : List ℝ) :
    Odd (realTwoAdicSquareBoundaryRGChainCount bottom right top left) := by
  exact realTwoAdic_squareBoundaryRGCount_odd_of_side_subdivisions bottom right top left

/-- `TrichromaticTriangle` is invariant under cyclic permutation of vertices. -/
theorem trichromaticTriangle_cycle {a b c : MonskyColor} :
    TrichromaticTriangle a b c ↔ TrichromaticTriangle b c a := by
  cases a <;> cases b <;> cases c <;> decide

/-- `TrichromaticTriangle` is invariant under reverse-cyclic permutation. -/
theorem trichromaticTriangle_swap_outer {a b c : MonskyColor} :
    TrichromaticTriangle a b c ↔ TrichromaticTriangle c b a := by
  cases a <;> cases b <;> cases c <;> decide

/-- In a trichromatic triangle, the set of vertex colors equals all of MonskyColor. -/
theorem trichromaticTriangle_iff_red_green_blue_present {a b c : MonskyColor} :
    TrichromaticTriangle a b c ↔
      ((a = red ∨ b = red ∨ c = red) ∧
       (a = green ∨ b = green ∨ c = green) ∧
       (a = blue ∨ b = blue ∨ c = blue)) := by
  cases a <;> cases b <;> cases c <;> decide

/--
Local Sperner parity atom: a triangle is trichromatic exactly when it has an
odd number of red-green edges.
-/
theorem odd_redGreenEdges_iff_trichromatic (a b c : MonskyColor) :
    Odd
      ((if RedGreenEdge a b then 1 else 0 : ℕ) +
       (if RedGreenEdge b c then 1 else 0 : ℕ) +
       (if RedGreenEdge c a then 1 else 0 : ℕ)) ↔
      TrichromaticTriangle a b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem redGreenEdges_zmod_two_eq_trichromatic (a b c : MonskyColor) :
    ((if RedGreenEdge a b then 1 else 0 : ZMod 2) +
     (if RedGreenEdge b c then 1 else 0 : ZMod 2) +
     (if RedGreenEdge c a then 1 else 0 : ZMod 2)) =
    (if TrichromaticTriangle a b c then 1 else 0 : ZMod 2) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Colors attached to the three vertices of one combinatorial triangle. -/
def triangleColorsOfVertices {α : Type*} (color : α → MonskyColor) (t : α × α × α) :
    MonskyColor × MonskyColor × MonskyColor :=
  (color t.1, color t.2.1, color t.2.2)

/-- The three unoriented edges of a triangle, in cyclic order. -/
def triangleEdge {α : Type*} (t : α × α × α) : Fin 3 → Sym2 α :=
  ![s(t.1, t.2.1), s(t.2.1, t.2.2), s(t.2.2, t.1)]

/-- Red-green predicate on an unordered edge. -/
def edgeRedGreen {α : Type*} (color : α → MonskyColor) : Sym2 α → Prop :=
  Sym2.lift ⟨fun a b => RedGreenEdge (color a) (color b),
    fun _ _ => propext redGreenEdge_symm⟩

@[simp]
theorem edgeRedGreen_mk {α : Type*} (color : α → MonskyColor) (a b : α) :
    edgeRedGreen color s(a, b) ↔ RedGreenEdge (color a) (color b) := by
  rfl

/-- Numeric indicator for red-green unordered edges. -/
noncomputable def edgeRGIndicator {α : Type*} (color : α → MonskyColor)
    (e : Sym2 α) : ℕ := by
  classical
  exact if edgeRedGreen color e then 1 else 0

@[simp]
theorem edgeRGIndicator_mk {α : Type*} (color : α → MonskyColor) (a b : α) :
    edgeRGIndicator color s(a, b) =
      if RedGreenEdge (color a) (color b) then 1 else 0 := by
  classical
  by_cases h : RedGreenEdge (color a) (color b) <;> simp [edgeRGIndicator, h]

theorem edgeRGIndicator_eq_zero_or_one {α : Type*} (color : α → MonskyColor)
    (e : Sym2 α) :
    edgeRGIndicator color e = 0 ∨ edgeRGIndicator color e = 1 := by
  classical
  unfold edgeRGIndicator
  by_cases h : edgeRedGreen color e <;> simp [h]

/-- The local red-green edge count of one colored triangle. -/
def triangleLocalRGCount (c : MonskyColor × MonskyColor × MonskyColor) : ℕ :=
  (if RedGreenEdge c.1 c.2.1 then 1 else 0) +
  (if RedGreenEdge c.2.1 c.2.2 then 1 else 0) +
  (if RedGreenEdge c.2.2 c.1 then 1 else 0)

theorem triangleLocalRGCount_ofVertices_eq_sum_edges {α : Type*}
    (color : α → MonskyColor) (t : α × α × α) :
    triangleLocalRGCount (triangleColorsOfVertices color t) =
      ∑ e : Fin 3, edgeRGIndicator color (triangleEdge t e) := by
  classical
  rcases t with ⟨a, b, c⟩
  rw [Fin.sum_univ_three]
  by_cases hab : RedGreenEdge (color a) (color b) <;>
  by_cases hbc : RedGreenEdge (color b) (color c) <;>
  by_cases hca : RedGreenEdge (color c) (color a) <;>
  simp [triangleLocalRGCount, triangleColorsOfVertices, triangleEdge, hab, hbc, hca]

theorem sum_triangleLocalRGCount_eq_sum_edgeIndicators
    {α : Type*} {n : ℕ} (triangles : Fin n → α × α × α) (color : α → MonskyColor) :
    (∑ i : Fin n, triangleLocalRGCount (triangleColorsOfVertices color (triangles i))) =
      ∑ p : Fin n × Fin 3, edgeRGIndicator color (triangleEdge (triangles p.1) p.2) := by
  classical
  simp_rw [triangleLocalRGCount_ofVertices_eq_sum_edges]
  rw [Fintype.sum_prod_type]

/-- Multiplicity of an unordered edge in the list of all triangle edges. -/
noncomputable def edgeMultiplicity {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (triangles : Fin n → α × α × α) (e : Sym2 α) : ℕ := by
  classical
  exact (Finset.univ.filter fun p : Fin n × Fin 3 =>
    triangleEdge (triangles p.1) p.2 = e).card

/--
The boundary count supplied by a finite edge pairing: count red-green edges
whose total triangle-edge multiplicity is odd.  For an honest triangulated
disk these are exactly the boundary red-green edges.
-/
noncomputable def oddEdgeRedGreenCount {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (triangles : Fin n → α × α × α) (color : α → MonskyColor) : ℕ :=
  (Finset.univ.filter fun e : Sym2 α =>
    edgeRGIndicator color e = 1 ∧ Odd (edgeMultiplicity triangles e)).card

theorem sum_triangle_edge_indicators_eq_sum_multiplicity
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (triangles : Fin n → α × α × α) (color : α → MonskyColor) :
    (∑ p : Fin n × Fin 3, edgeRGIndicator color (triangleEdge (triangles p.1) p.2)) =
      ∑ e : Sym2 α, edgeMultiplicity triangles e * edgeRGIndicator color e := by
  classical
  rw [← Finset.sum_fiberwise' (s := Finset.univ)
    (g := fun p : Fin n × Fin 3 => triangleEdge (triangles p.1) p.2)
    (f := edgeRGIndicator color)]
  simp [edgeMultiplicity, Finset.sum_const, mul_comm]

/--
Abstract Sperner parity lemma: in a finite triangulation where each edge
belongs to at most two triangles, the number of trichromatic triangles has
the same parity as the number of red-green boundary edges.

`triangles` is the finite set of triangles, each given by three color assignments.
`boundaryRG` counts red-green edges on the boundary (shared by exactly one triangle).
-/
private theorem sum_nat_mod_two_eq_sum_mod_two
    {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ x ∈ s, f x) % 2 = (∑ x ∈ s, f x % 2) % 2 := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    conv_lhs => rw [Nat.add_mod (f a) _ 2, ih]
    conv_rhs => rw [Nat.add_mod (f a % 2) _ 2]
    simp

theorem edgeMultiplicity_mul_indicator_mod_two {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (triangles : Fin n → α × α × α) (color : α → MonskyColor) (e : Sym2 α) :
    (edgeMultiplicity triangles e * edgeRGIndicator color e) % 2 =
      if edgeRGIndicator color e = 1 ∧ Odd (edgeMultiplicity triangles e) then 1 else 0 := by
  rcases edgeRGIndicator_eq_zero_or_one color e with hzero | hone
  · simp [hzero]
  · by_cases hodd : Odd (edgeMultiplicity triangles e)
    · simp [hone, hodd, Nat.odd_iff.mp hodd]
    · have heven : Even (edgeMultiplicity triangles e) := Nat.not_odd_iff_even.mp hodd
      have hmod : edgeMultiplicity triangles e % 2 = 0 := Nat.even_iff.mp heven
      simp [hone, hodd, hmod]

theorem sum_multiplicity_indicator_mod_two_eq_oddEdgeRedGreenCount
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (triangles : Fin n → α × α × α) (color : α → MonskyColor) :
    (∑ e : Sym2 α, edgeMultiplicity triangles e * edgeRGIndicator color e) % 2 =
      oddEdgeRedGreenCount triangles color % 2 := by
  classical
  calc
    (∑ e : Sym2 α, edgeMultiplicity triangles e * edgeRGIndicator color e) % 2
        = (∑ e : Sym2 α,
            (edgeMultiplicity triangles e * edgeRGIndicator color e) % 2) % 2 := by
          simpa using sum_nat_mod_two_eq_sum_mod_two (Finset.univ : Finset (Sym2 α))
            (fun e => edgeMultiplicity triangles e * edgeRGIndicator color e)
    _ = (∑ e : Sym2 α,
          if edgeRGIndicator color e = 1 ∧ Odd (edgeMultiplicity triangles e) then 1 else 0) %
        2 := by
          congr 1
          exact Finset.sum_congr rfl fun e _ =>
            edgeMultiplicity_mul_indicator_mod_two triangles color e
    _ = oddEdgeRedGreenCount triangles color % 2 := by
          rw [oddEdgeRedGreenCount, Finset.card_eq_sum_ones]
          rw [Finset.sum_filter]

theorem sum_triangleLocalRGCount_mod_two_eq_oddEdgeRedGreenCount
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (triangles : Fin n → α × α × α) (color : α → MonskyColor) :
    (∑ i : Fin n, triangleLocalRGCount (triangleColorsOfVertices color (triangles i))) % 2 =
      oddEdgeRedGreenCount triangles color % 2 := by
  rw [sum_triangleLocalRGCount_eq_sum_edgeIndicators]
  rw [sum_triangle_edge_indicators_eq_sum_multiplicity]
  exact sum_multiplicity_indicator_mod_two_eq_oddEdgeRedGreenCount triangles color

theorem sperner_parity_abstract
    (n : ℕ) (triangleColors : Fin n → MonskyColor × MonskyColor × MonskyColor)
    (boundaryRGCount : ℕ)
    (totalRG : ℕ)
    (htotal : totalRG = ∑ i : Fin n,
      ((if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0)))
    (hparity : totalRG % 2 = boundaryRGCount % 2) :
    (Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2).card % 2 = boundaryRGCount % 2 := by
  classical
  let f : Fin n → ℕ := fun i =>
    (if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
    (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
    (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0)
  let T : Fin n → Prop := fun i =>
    TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
      (triangleColors i).2.2
  have hlocal : ∀ i : Fin n, f i % 2 = if T i then 1 else 0 := by
    intro i
    have hodd := odd_redGreenEdges_iff_trichromatic (triangleColors i).1
      (triangleColors i).2.1 (triangleColors i).2.2
    by_cases ht : T i
    · rw [if_pos ht]
      exact Nat.odd_iff.mp (hodd.mpr ht)
    · rw [if_neg ht]
      by_contra h
      have : f i % 2 = 1 := by omega
      exact ht (hodd.mp (Nat.odd_iff.mpr this))
  have hreplace : (∑ i : Fin n, f i % 2) = ∑ i : Fin n, if T i then 1 else 0 :=
    Finset.sum_congr rfl fun i _ => hlocal i
  have hcard : (∑ i : Fin n, if T i then (1 : ℕ) else 0) =
      (Finset.univ.filter T).card := by
    rw [← Finset.sum_filter]; simp
  calc (Finset.univ.filter T).card % 2
      = (∑ i : Fin n, if T i then (1 : ℕ) else 0) % 2 := by rw [hcard]
    _ = (∑ i : Fin n, f i % 2) % 2 := by rw [hreplace]
    _ = (∑ i : Fin n, f i) % 2 := (sum_nat_mod_two_eq_sum_mod_two _ _).symm
    _ = totalRG % 2 := by rw [htotal]
    _ = boundaryRGCount % 2 := hparity

/--
Corollary: if the boundary red-green edge count is odd, at least one triangle
is trichromatic.
-/
theorem exists_trichromatic_of_odd_boundary
    (n : ℕ) (triangleColors : Fin n → MonskyColor × MonskyColor × MonskyColor)
    (boundaryRGCount : ℕ)
    (totalRG : ℕ)
    (htotal : totalRG = ∑ i : Fin n,
      ((if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0)))
    (hparity : totalRG % 2 = boundaryRGCount % 2)
    (hodd : Odd boundaryRGCount) :
    ∃ i : Fin n,
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2 := by
  by_contra hall
  push Not at hall
  have hempty : (Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _
    exact hall i
  have hcard0 : (Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2).card = 0 := by
    simp [hempty]
  have := sperner_parity_abstract n triangleColors boundaryRGCount totalRG htotal hparity
  rw [hcard0] at this
  rcases hodd with ⟨k, hk⟩
  omega

/-- Certificate for Monsky's theorem: a 2-adic-style coloring of triangle
vertices together with the double-counting witness that boundary red-green
edge count is odd. -/
structure MonskyCertificate (n : ℕ) where
  /-- The triangle colorings induced by a (hypothetical) equal-area
      odd-triangulation of the unit square. -/
  triangleColors : Fin n → MonskyColor × MonskyColor × MonskyColor
  /-- The boundary red-green edge count (from the square's edge contour). -/
  boundaryRGCount : ℕ
  /-- Total RG edge count summed over all triangles. -/
  totalRG : ℕ
  /-- Total = sum of triangle-local RG counts (double-counting bookkeeping). -/
  htotal : totalRG = ∑ i : Fin n,
    ((if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
     (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
     (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0))
  /-- 2-adic constraint: parity of total RG = parity of boundary RG. -/
  hparity : totalRG % 2 = boundaryRGCount % 2
  /-- Crux of Monsky's argument: boundary RG count is ODD (from the unit
      square's specific 2-adic coloring at corners). -/
  hodd : Odd boundaryRGCount

/--
Construct a `MonskyCertificate` from finite triangle-edge parity.  The input
`hodd` is now the concrete combinatorial boundary statement: the red-green
unordered edges with odd triangle-edge multiplicity are odd in number.
-/
noncomputable def edgeParityMonskyCertificate {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (triangles : Fin n → α × α × α) (color : α → MonskyColor)
    (hodd : Odd (oddEdgeRedGreenCount triangles color)) : MonskyCertificate n where
  triangleColors := fun i => triangleColorsOfVertices color (triangles i)
  boundaryRGCount := oddEdgeRedGreenCount triangles color
  totalRG := ∑ i : Fin n, triangleLocalRGCount (triangleColorsOfVertices color (triangles i))
  htotal := by
    simp [triangleLocalRGCount]
  hparity := sum_triangleLocalRGCount_mod_two_eq_oddEdgeRedGreenCount triangles color
  hodd := hodd

/-
Remaining geometric interface: given a hypothetical equal-area triangulation
of the unit square into an odd number of real triangles, one still needs to
extract the finite list of triangle vertices, show their `realTwoAdicColor`
values make `oddEdgeRedGreenCount` odd, and express the equal-area hypothesis
as oriented double area `± 2 / n` for each listed triangle.
-/

/-- Chapter 20 (Monsky's theorem, Tier 1 conditional):
Given a Monsky 2-adic coloring certificate (which packages the 2-adic
extension construction + the double-counting parity result + the odd-boundary
witness), there exists a trichromatic triangle — corresponding to the
contradiction that closes the proof (such a triangle has area with 2-adic
valuation incompatible with 1/(odd integer)).

TODO (frontier — construct `MonskyCertificate` from an actual equal-area
odd-triangulation of the unit square (geometric triangulation model giving
boundary RG-chain = 4 edges + oriented double-area `±2/n`); needs triangulation
infra not in Mathlib.)
-/
theorem chapter20 {n : ℕ} (cert : MonskyCertificate n) :
    ∃ i : Fin n,
      TrichromaticTriangle (cert.triangleColors i).1
        (cert.triangleColors i).2.1 (cert.triangleColors i).2.2 :=
  exists_trichromatic_of_odd_boundary n cert.triangleColors
    cert.boundaryRGCount cert.totalRG cert.htotal cert.hparity cert.hodd

/--
Sperner conclusion from a finite edge-parity boundary count, without manually
supplying the `MonskyCertificate` parity fields.
-/
theorem chapter20_from_edge_parity {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (triangles : Fin n → α × α × α) (color : α → MonskyColor)
    (hodd : Odd (oddEdgeRedGreenCount triangles color)) :
    ∃ i : Fin n,
      TrichromaticTriangle (triangleColorsOfVertices color (triangles i)).1
        (triangleColorsOfVertices color (triangles i)).2.1
        (triangleColorsOfVertices color (triangles i)).2.2 := by
  simpa using chapter20 (edgeParityMonskyCertificate triangles color hodd)

/--
Once a `MonskyCertificate` is realized by actual real triangles whose colors
come from the chosen Monsky coloring and whose oriented double areas are all
`2 / n`, odd `n` is impossible.  The only unformalized book input left before
this theorem is producing such a realization from a geometric triangulation of
the square.
-/
theorem no_odd_equalArea_realization_of_monskyCertificate {n : ℕ} (hn : Odd n)
    (triangles : Fin n → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ))
    (cert : MonskyCertificate n)
    (hcolors : ∀ i : Fin n, cert.triangleColors i =
      (realTwoAdicColor (triangles i).1,
       realTwoAdicColor (triangles i).2.1,
       realTwoAdicColor (triangles i).2.2))
    (harea : ∀ i : Fin n,
      doubleArea (triangles i).1 (triangles i).2.1 (triangles i).2.2 =
        (((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  obtain ⟨i, hi⟩ := chapter20 cert
  have htri : TrichromaticTriangle (realTwoAdicColor (triangles i).1)
      (realTwoAdicColor (triangles i).2.1) (realTwoAdicColor (triangles i).2.2) := by
    simpa [hcolors i] using hi
  exact not_real_doubleArea_eq_two_div_odd_of_trichromatic hn htri (harea i)

/--
Orientation-free version of
`no_odd_equalArea_realization_of_monskyCertificate`, allowing each listed
triangle to have double area `2 / n` or `-2 / n`.
-/
theorem no_odd_equalArea_realization_of_monskyCertificate_abs {n : ℕ} (hn : Odd n)
    (triangles : Fin n → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ))
    (cert : MonskyCertificate n)
    (hcolors : ∀ i : Fin n, cert.triangleColors i =
      (realTwoAdicColor (triangles i).1,
       realTwoAdicColor (triangles i).2.1,
       realTwoAdicColor (triangles i).2.2))
    (harea : ∀ i : Fin n,
      doubleArea (triangles i).1 (triangles i).2.1 (triangles i).2.2 =
        (((2 : ℚ) / n : ℚ) : ℝ) ∨
      doubleArea (triangles i).1 (triangles i).2.1 (triangles i).2.2 =
        -(((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  obtain ⟨i, hi⟩ := chapter20 cert
  have htri : TrichromaticTriangle (realTwoAdicColor (triangles i).1)
      (realTwoAdicColor (triangles i).2.1) (realTwoAdicColor (triangles i).2.2) := by
    simpa [hcolors i] using hi
  exact not_real_doubleArea_eq_abs_two_div_odd_of_trichromatic hn htri (harea i)

/--
Finite-vertex version of the current Monsky contradiction.  This is the target
shape for the remaining geometric triangulation extraction: vertices are a
finite type, triangles name three vertices, the boundary parity is computed
from odd edge multiplicities, and the real point map supplies the areas.
-/
theorem no_odd_equalArea_realization_of_edgeParity
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : Odd n)
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (hboundary : Odd (oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices)))
    (harea : ∀ i : Fin n,
      doubleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        (((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  let cert : MonskyCertificate n :=
    edgeParityMonskyCertificate triangles (realTwoAdicColor ∘ vertices) hboundary
  exact no_odd_equalArea_realization_of_monskyCertificate hn
    (fun i => (vertices (triangles i).1, vertices (triangles i).2.1,
      vertices (triangles i).2.2))
    cert
    (by intro i; rfl)
    harea

/--
Orientation-free finite-vertex version of the current Monsky contradiction.
This is the form closest to an unoriented geometric triangulation.
-/
theorem no_odd_equalArea_realization_of_edgeParity_abs
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : Odd n)
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (hboundary : Odd (oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices)))
    (harea : ∀ i : Fin n,
      doubleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        (((2 : ℚ) / n : ℚ) : ℝ) ∨
      doubleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        -(((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  let cert : MonskyCertificate n :=
    edgeParityMonskyCertificate triangles (realTwoAdicColor ∘ vertices) hboundary
  exact no_odd_equalArea_realization_of_monskyCertificate_abs hn
    (fun i => (vertices (triangles i).1, vertices (triangles i).2.1,
      vertices (triangles i).2.2))
    cert
    (by intro i; rfl)
    harea

/--
Turn the exact geometric boundary-incidence statement into the odd boundary
hypothesis needed by the finite edge-parity form.  This isolates the remaining
frontier lemma: for a real triangulation of the square, the red-green
odd-multiplicity triangle edges must be exactly the four side chains.
-/
theorem oddEdgeRedGreenCount_odd_of_squareBoundaryIncidence
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (bottom right top left : List ℝ)
    (hboundary : oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices) =
      realTwoAdicSquareBoundaryRGChainCount bottom right top left) :
    Odd (oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices)) := by
  rw [hboundary]
  exact realTwoAdicSquareBoundaryRGChainCount_odd bottom right top left

/--
Current non-fake frontier theorem: an extracted finite real triangulation with
the correct square-boundary incidence and oriented equal-area facts cannot have
odd size.  The remaining unproved geometric work is to derive `hboundary` and
`harea` from an actual topological/geometric triangulation object.
-/
theorem no_odd_equalArea_realization_of_squareBoundaryIncidence_abs
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : Odd n)
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (bottom right top left : List ℝ)
    (hboundary : oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices) =
      realTwoAdicSquareBoundaryRGChainCount bottom right top left)
    (harea : ∀ i : Fin n,
      doubleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        (((2 : ℚ) / n : ℚ) : ℝ) ∨
      doubleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        -(((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  exact no_odd_equalArea_realization_of_edgeParity_abs hn vertices triangles
    (oddEdgeRedGreenCount_odd_of_squareBoundaryIncidence vertices triangles bottom right top left
      hboundary)
    harea

/-- The empty triangulation cannot carry a Monsky certificate: with 0 triangles,
the local RG sum is 0 (even), but the certificate demands an odd boundary RG
count of the same parity.  Contradiction. -/
theorem MonskyCertificate.isEmpty_zero : IsEmpty (MonskyCertificate 0) := by
  constructor
  intro cert
  have htot : cert.totalRG = 0 := by rw [cert.htotal]; simp
  have hpar := cert.hparity
  rw [htot] at hpar
  rcases cert.hodd with ⟨k, hk⟩
  omega

/-- A Monsky certificate has positive boundary RG count (since it's odd). -/
theorem MonskyCertificate.boundaryRGCount_pos {n : ℕ} (cert : MonskyCertificate n) :
    0 < cert.boundaryRGCount := by
  rcases cert.hodd with ⟨k, hk⟩
  omega

/-- A Monsky certificate has positive total RG count. -/
theorem MonskyCertificate.totalRG_pos {n : ℕ} (cert : MonskyCertificate n) :
    0 < cert.totalRG := by
  -- totalRG ≡ boundaryRGCount mod 2, both odd; so totalRG is odd, hence positive.
  have hpos := cert.boundaryRGCount_pos
  rcases cert.hodd with ⟨k, hk⟩
  have hpar := cert.hparity
  rw [hk] at hpar
  -- hpar : totalRG % 2 = (2 * k + 1) % 2 = 1, so totalRG % 2 = 1, hence totalRG ≥ 1.
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  rw [h1] at hpar
  omega

/-- The Monsky certificate's `totalRG` count is itself odd, since it matches the
parity of the (odd) boundary RG count.  Combined with the Sperner parity
identity, this is the stronger form behind `totalRG_pos`. -/
theorem MonskyCertificate.totalRG_odd {n : ℕ} (cert : MonskyCertificate n) :
    Odd cert.totalRG := by
  rcases cert.hodd with ⟨k, hk⟩
  have hpar := cert.hparity
  rw [hk] at hpar
  have h1 : (2 * k + 1) % 2 = 1 := by omega
  rw [h1] at hpar
  exact Nat.odd_iff.mpr hpar

/-- Any Monsky certificate has at least one trichromatic triangle — packaging
of `chapter20` plus the cardinality lower bound.  This is the "≥ 1 trichromatic
triangle exists" form used by the contradiction step in Monsky's argument. -/
theorem MonskyCertificate.one_le_trichromatic_card {n : ℕ} (cert : MonskyCertificate n) :
    1 ≤ (Finset.univ.filter fun i : Fin n =>
        TrichromaticTriangle (cert.triangleColors i).1
          (cert.triangleColors i).2.1 (cert.triangleColors i).2.2).card := by
  obtain ⟨i, hi⟩ := chapter20 cert
  exact Finset.card_pos.mpr ⟨i, by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi⟩

end ProofsInTheBook.Chapter20
