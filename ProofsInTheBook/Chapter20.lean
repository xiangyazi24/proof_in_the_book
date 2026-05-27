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
count for any finite subdivision of the square boundary, identifies that count
with an explicit finite list of unit-square boundary point-edges, constructs
`MonskyCertificate` from finite unordered-edge parity, and proves the valuation
contradiction for a trichromatic triangle of ordinary real area `1 / n` with
`n` odd.

Gap to the full book theorem: the remaining work is geometric triangulation
infrastructure.  One needs a finite real triangulation model for the unit
square and an extraction theorem producing:
1. a finite vertex type `α`, a point map `vertices : α → ℝ × ℝ`, and triangles
   `triangles : Fin n → α × α × α`;
2. four side subdivision lists `bottom right top left : List ℝ`, or equivalently
   the explicit point-edge chain `realTwoAdicSquareBoundaryPointEdgeList`;
3. the boundary-incidence theorem that the odd-multiplicity triangle edges are
   exactly that square boundary chain after mapping boundary points to the
   finite vertex type;
4. the ordinary equal-area fact
   `∀ i, realTriangleArea ... = (1 / n : ℚ)`.
Mathlib has `Analysis.Convex.SimplicialComplex` and `Geometry.Polygon.Basic`,
but not this assembled theorem extracting boundary chains and equal-area facts
from a triangulation of the unit square.
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

/-- The ordinary Euclidean area of a real triangle, expressed through `doubleArea`. -/
noncomputable def realTriangleArea (a b c : ℝ × ℝ) : ℝ :=
  |doubleArea a b c| / 2

theorem abs_doubleArea_eq_two_div_of_realTriangleArea_eq_one_div
    {n : ℕ} (hn : n ≠ 0) {a b c : ℝ × ℝ}
    (harea : realTriangleArea a b c = (((1 : ℚ) / n : ℚ) : ℝ)) :
    |doubleArea a b c| = (((2 : ℚ) / n : ℚ) : ℝ) := by
  have hareaR : realTriangleArea a b c = (1 : ℝ) / n := by
    simpa using harea
  have h := congrArg (fun x : ℝ => x * 2) hareaR
  unfold realTriangleArea at h
  have hR : |doubleArea a b c| = (2 : ℝ) / n := by
    field_simp [Nat.cast_ne_zero.mpr hn] at h ⊢
    linarith
  simpa using hR

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

theorem real_two_div_natCast_nonneg_of_odd {n : ℕ} (hn : Odd n) :
    (0 : ℝ) ≤ (((2 : ℚ) / n : ℚ) : ℝ) := by
  rcases hn with ⟨k, hk⟩
  have hnpos : 0 < n := by omega
  positivity

/--
Absolute double area is the usual orientation-free area input.  For odd `n`,
the valuation contradiction only needs the two oriented alternatives obtained
from `|doubleArea| = 2 / n`.
-/
theorem not_real_abs_doubleArea_eq_two_div_odd_of_trichromatic {n : ℕ} (hn : Odd n)
    {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c))
    (harea : |doubleArea a b c| = (((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  exact not_real_doubleArea_eq_abs_two_div_odd_of_trichromatic hn htri
    ((abs_eq (real_two_div_natCast_nonneg_of_odd hn)).mp harea)

/--
Area form of the trichromatic valuation contradiction: a trichromatic triangle
cannot have ordinary real area `1 / n` when `n` is odd.
-/
theorem not_real_triangleArea_eq_one_div_odd_of_trichromatic {n : ℕ} (hn : Odd n)
    {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c))
    (harea : realTriangleArea a b c = (((1 : ℚ) / n : ℚ) : ℝ)) : False := by
  have hn0 : n ≠ 0 := by
    rcases hn with ⟨k, hk⟩
    omega
  exact not_real_abs_doubleArea_eq_two_div_odd_of_trichromatic hn htri
    (abs_doubleArea_eq_two_div_of_realTriangleArea_eq_one_div hn0 harea)

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

/-- Red-green count on a finite set of unordered boundary edges. -/
noncomputable def boundaryEdgeRedGreenCount {α : Type*} (boundary : Finset (Sym2 α))
    (color : α → MonskyColor) : ℕ :=
  (boundary.filter fun e => edgeRGIndicator color e = 1).card

/--
If the odd-multiplicity triangle edges are exactly a finite boundary edge set,
then `oddEdgeRedGreenCount` is the red-green count on that boundary set.
-/
theorem oddEdgeRedGreenCount_eq_boundaryEdgeRedGreenCount_of_oddMultiplicity
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (triangles : Fin n → α × α × α) (color : α → MonskyColor)
    (boundary : Finset (Sym2 α))
    (hboundary : ∀ e : Sym2 α, Odd (edgeMultiplicity triangles e) ↔ e ∈ boundary) :
    oddEdgeRedGreenCount triangles color = boundaryEdgeRedGreenCount boundary color := by
  classical
  unfold oddEdgeRedGreenCount boundaryEdgeRedGreenCount
  congr 1
  ext e
  simp [hboundary e, and_comm]

theorem oddEdgeRedGreenCount_odd_of_boundaryEdges
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (triangles : Fin n → α × α × α) (color : α → MonskyColor)
    (boundary : Finset (Sym2 α))
    (hboundary : ∀ e : Sym2 α, Odd (edgeMultiplicity triangles e) ↔ e ∈ boundary)
    (hodd : Odd (boundaryEdgeRedGreenCount boundary color)) :
    Odd (oddEdgeRedGreenCount triangles color) := by
  rw [oddEdgeRedGreenCount_eq_boundaryEdgeRedGreenCount_of_oddMultiplicity
    triangles color boundary hboundary]
  exact hodd

/-- Consecutive unordered edges in a finite vertex chain. -/
def consecutiveEdges {α : Type*} : List α → List (Sym2 α)
  | a :: b :: rest => s(a, b) :: consecutiveEdges (b :: rest)
  | _ => []

/-- Red-green count on a finite list of unordered edges. -/
noncomputable def listEdgeRGCount {α : Type*} (edges : List (Sym2 α))
    (color : α → MonskyColor) : ℕ :=
  (edges.filter fun e => edgeRGIndicator color e = 1).length

theorem consecutiveEdges_RGCount_eq_listRGTransitionCount_map {α : Type*}
    (vertices : List α) (color : α → MonskyColor) :
    listEdgeRGCount (consecutiveEdges vertices) color =
      listRGTransitionCount (vertices.map color) := by
  induction vertices with
  | nil => simp [consecutiveEdges, listEdgeRGCount, listRGTransitionCount]
  | cons a tail ih =>
      cases tail with
      | nil => simp [consecutiveEdges, listEdgeRGCount, listRGTransitionCount]
      | cons b rest =>
          have ih' : listEdgeRGCount (consecutiveEdges (b :: rest)) color =
              listRGTransitionCount (color b :: List.map color rest) := by
            simpa using ih
          simp only [List.map_cons, consecutiveEdges, listRGTransitionCount]
          rw [← ih']
          by_cases h : RedGreenEdge (color a) (color b)
          · simp [listEdgeRGCount, edgeRGIndicator_mk, h, Nat.add_comm]
          · simp [listEdgeRGCount, edgeRGIndicator_mk, h]

theorem listEdgeRGCount_append {α : Type*} (edges₁ edges₂ : List (Sym2 α))
    (color : α → MonskyColor) :
    listEdgeRGCount (edges₁ ++ edges₂) color =
      listEdgeRGCount edges₁ color + listEdgeRGCount edges₂ color := by
  simp [listEdgeRGCount, List.filter_append]

theorem boundaryEdgeRedGreenCount_toFinset {α : Type*} [DecidableEq α]
    (edges : List (Sym2 α)) (color : α → MonskyColor) (hnodup : edges.Nodup) :
    boundaryEdgeRedGreenCount edges.toFinset color = listEdgeRGCount edges color := by
  classical
  unfold boundaryEdgeRedGreenCount listEdgeRGCount
  have htf : (edges.filter fun e => edgeRGIndicator color e = 1).toFinset =
      edges.toFinset.filter fun e => edgeRGIndicator color e = 1 := by
    ext e
    simp
  rw [← htf]
  exact List.toFinset_card_of_nodup (hnodup.filter _)

/--
Boundary edge list for a square-like contour, split into the four side chains
and the four corner vertices.
-/
def squareBoundaryEdgeList {α : Type*} (bottom right top left : List α)
    (bottomLeft bottomRight topRight topLeft : α) : List (Sym2 α) :=
  consecutiveEdges (bottomLeft :: bottom ++ [bottomRight]) ++
  consecutiveEdges (bottomRight :: right ++ [topRight]) ++
  consecutiveEdges (topRight :: top ++ [topLeft]) ++
  consecutiveEdges (topLeft :: left ++ [bottomLeft])

theorem squareBoundaryEdgeList_RGCount_eq {α : Type*}
    (bottom right top left : List α) (bottomLeft bottomRight topRight topLeft : α)
    (color : α → MonskyColor) :
    listEdgeRGCount
        (squareBoundaryEdgeList bottom right top left bottomLeft bottomRight topRight topLeft)
        color =
      listRGTransitionCount ((bottomLeft :: bottom ++ [bottomRight]).map color) +
      listRGTransitionCount ((bottomRight :: right ++ [topRight]).map color) +
      listRGTransitionCount ((topRight :: top ++ [topLeft]).map color) +
      listRGTransitionCount ((topLeft :: left ++ [bottomLeft]).map color) := by
  simp [squareBoundaryEdgeList, listEdgeRGCount_append,
    consecutiveEdges_RGCount_eq_listRGTransitionCount_map, List.map_append]
  omega

/-- The explicit point-edge chain on the boundary of the unit square. -/
noncomputable def realTwoAdicSquareBoundaryPointEdgeList
    (bottom right top left : List ℝ) : List (Sym2 (ℝ × ℝ)) :=
  squareBoundaryEdgeList
    (bottom.map fun x => (x, 0))
    (right.map fun y => (1, y))
    (top.map fun x => (x, 1))
    (left.map fun y => (0, y))
    (0, 0) (1, 0) (1, 1) (0, 1)

theorem realTwoAdicSquareBoundaryPointEdgeList_RGCount_eq
    (bottom right top left : List ℝ) :
    listEdgeRGCount (realTwoAdicSquareBoundaryPointEdgeList bottom right top left)
        realTwoAdicColor =
      realTwoAdicSquareBoundaryRGChainCount bottom right top left := by
  simp [realTwoAdicSquareBoundaryPointEdgeList, squareBoundaryEdgeList_RGCount_eq,
    realTwoAdicSquareBoundaryRGChainCount, List.map_map, Function.comp_def]

theorem realTwoAdicSquareBoundaryPointEdgeList_RGCount_odd
    (bottom right top left : List ℝ) :
    Odd (listEdgeRGCount (realTwoAdicSquareBoundaryPointEdgeList bottom right top left)
      realTwoAdicColor) := by
  rw [realTwoAdicSquareBoundaryPointEdgeList_RGCount_eq]
  exact realTwoAdicSquareBoundaryRGChainCount_odd bottom right top left

theorem squareBoundaryVertexChainRGCount_odd_of_side_colors {α : Type*}
    (bottom right top left : List α) (bottomLeft bottomRight topRight topLeft : α)
    (color : α → MonskyColor)
    (hbottomLeft : color bottomLeft = red)
    (hbottomRight : color bottomRight = green)
    (htopRight : color topRight = green)
    (htopLeft : color topLeft = blue)
    (hbottom : ∀ v ∈ bottom, colorIsRedGreen (color v))
    (hright : ∀ v ∈ right, colorIsGreenBlue (color v))
    (htop : ∀ v ∈ top, colorIsGreenBlue (color v))
    (hleft : ∀ v ∈ left, colorIsRedBlue (color v)) :
    Odd (listEdgeRGCount
      (squareBoundaryEdgeList bottom right top left bottomLeft bottomRight topRight topLeft)
      color) := by
  rw [squareBoundaryEdgeList_RGCount_eq]
  have hbottomColors :
      ∀ c ∈ red :: (bottom.map color) ++ [green], colorIsRedGreen c := by
    intro c hc
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
    rcases hc with hfirst | hlast
    · rcases hfirst with hc | ⟨v, hv, hvc⟩
      · subst c
        exact Or.inl rfl
      · rw [← hvc]
        exact hbottom v hv
    · rcases hlast with hc | hnil
      · subst c
        exact Or.inr rfl
      · cases hnil
  have hrightColors :
      ∀ c ∈ green :: (right.map color) ++ [green], colorIsGreenBlue c := by
    intro c hc
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
    rcases hc with hfirst | hlast
    · rcases hfirst with hc | ⟨v, hv, hvc⟩
      · subst c
        exact Or.inl rfl
      · rw [← hvc]
        exact hright v hv
    · rcases hlast with hc | hnil
      · subst c
        exact Or.inl rfl
      · cases hnil
  have htopColors :
      ∀ c ∈ green :: (top.map color) ++ [blue], colorIsGreenBlue c := by
    intro c hc
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
    rcases hc with hfirst | hlast
    · rcases hfirst with hc | ⟨v, hv, hvc⟩
      · subst c
        exact Or.inl rfl
      · rw [← hvc]
        exact htop v hv
    · rcases hlast with hc | hnil
      · subst c
        exact Or.inr rfl
      · cases hnil
  have hleftColors :
      ∀ c ∈ blue :: (left.map color) ++ [red], colorIsRedBlue c := by
    intro c hc
    simp only [List.mem_cons, List.mem_append, List.mem_map] at hc
    rcases hc with hfirst | hlast
    · rcases hfirst with hc | ⟨v, hv, hvc⟩
      · subst c
        exact Or.inr rfl
      · rw [← hvc]
        exact hleft v hv
    · rcases hlast with hc | hnil
      · subst c
        exact Or.inl rfl
      · cases hnil
  have hodd := squareBoundaryRGCount_odd_of_side_color_lists
    (bottom.map color) (right.map color) (top.map color) (left.map color)
    hbottomColors hrightColors htopColors hleftColors
  simpa [hbottomLeft, hbottomRight, htopRight, htopLeft, List.map_append] using hodd

theorem oddEdgeRedGreenCount_odd_of_squareBoundaryVertexChain
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (triangles : Fin n → α × α × α) (color : α → MonskyColor)
    (bottom right top left : List α) (bottomLeft bottomRight topRight topLeft : α)
    (hboundary : ∀ e : Sym2 α,
      Odd (edgeMultiplicity triangles e) ↔
        e ∈ (squareBoundaryEdgeList bottom right top left
          bottomLeft bottomRight topRight topLeft).toFinset)
    (hnodup : (squareBoundaryEdgeList bottom right top left
      bottomLeft bottomRight topRight topLeft).Nodup)
    (hbottomLeft : color bottomLeft = red)
    (hbottomRight : color bottomRight = green)
    (htopRight : color topRight = green)
    (htopLeft : color topLeft = blue)
    (hbottom : ∀ v ∈ bottom, colorIsRedGreen (color v))
    (hright : ∀ v ∈ right, colorIsGreenBlue (color v))
    (htop : ∀ v ∈ top, colorIsGreenBlue (color v))
    (hleft : ∀ v ∈ left, colorIsRedBlue (color v)) :
    Odd (oddEdgeRedGreenCount triangles color) := by
  refine oddEdgeRedGreenCount_odd_of_boundaryEdges triangles color
    (squareBoundaryEdgeList bottom right top left bottomLeft bottomRight topRight topLeft).toFinset
    hboundary ?_
  rw [boundaryEdgeRedGreenCount_toFinset _ color hnodup]
  exact squareBoundaryVertexChainRGCount_odd_of_side_colors bottom right top left
    bottomLeft bottomRight topRight topLeft color
    hbottomLeft hbottomRight htopRight htopLeft hbottom hright htop hleft

theorem oddEdgeRedGreenCount_odd_of_realSquareBoundaryVertexChain
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (bottom right top left : List α) (bottomLeft bottomRight topRight topLeft : α)
    (hboundary : ∀ e : Sym2 α,
      Odd (edgeMultiplicity triangles e) ↔
        e ∈ (squareBoundaryEdgeList bottom right top left
          bottomLeft bottomRight topRight topLeft).toFinset)
    (hnodup : (squareBoundaryEdgeList bottom right top left
      bottomLeft bottomRight topRight topLeft).Nodup)
    (hbottomLeft : vertices bottomLeft = (0, 0))
    (hbottomRight : vertices bottomRight = (1, 0))
    (htopRight : vertices topRight = (1, 1))
    (htopLeft : vertices topLeft = (0, 1))
    (hbottom : ∀ v ∈ bottom, ∃ x : ℝ, vertices v = (x, 0))
    (hright : ∀ v ∈ right, ∃ y : ℝ, vertices v = (1, y))
    (htop : ∀ v ∈ top, ∃ x : ℝ, vertices v = (x, 1))
    (hleft : ∀ v ∈ left, ∃ y : ℝ, vertices v = (0, y)) :
    Odd (oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices)) := by
  refine oddEdgeRedGreenCount_odd_of_squareBoundaryVertexChain triangles
    (realTwoAdicColor ∘ vertices) bottom right top left bottomLeft bottomRight topRight topLeft
    hboundary hnodup ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [hbottomLeft]
  · simp [hbottomRight]
  · simp [htopRight]
  · simp [htopLeft]
  · intro v hv
    obtain ⟨x, hx⟩ := hbottom v hv
    simpa [Function.comp_def, hx] using realTwoAdicColor_bottom_red_or_green x
  · intro v hv
    obtain ⟨y, hy⟩ := hright v hv
    simpa [Function.comp_def, hy] using realTwoAdicColor_right_green_or_blue y
  · intro v hv
    obtain ⟨x, hx⟩ := htop v hv
    simpa [Function.comp_def, hx] using realTwoAdicColor_top_green_or_blue x
  · intro v hv
    obtain ⟨y, hy⟩ := hleft v hv
    simpa [Function.comp_def, hy] using realTwoAdicColor_left_red_or_blue y

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
extract the finite list of triangle vertices, identify the odd-multiplicity
triangle edges with the explicit square boundary point-edge chain, and express
the equal-area hypothesis as oriented double area `± 2 / n` for each listed
triangle.
-/

/-- Chapter 20 (Monsky's theorem, Tier 1 conditional):
Given a Monsky 2-adic coloring certificate (which packages the 2-adic
extension construction + the double-counting parity result + the odd-boundary
witness), there exists a trichromatic triangle — corresponding to the
contradiction that closes the proof (such a triangle has area with 2-adic
valuation incompatible with 1/(odd integer)).

TODO (frontier): construct `MonskyCertificate` from an actual equal-area
odd-triangulation of the unit square.  The exact missing extraction lemma must
produce finite data `α`, `vertices`, `triangles`, `bottom right top left`, show
that the odd-multiplicity triangle edges are precisely the image of
`realTwoAdicSquareBoundaryPointEdgeList bottom right top left` in `Sym2 α`, and
prove the oriented double-area alternative `±2/n` for each triangle.  This
needs square triangulation/boundary-chain infrastructure and oriented-area
accounting not currently assembled in Mathlib.
-/
theorem chapter20 {n : ℕ} (cert : MonskyCertificate n) :
    ∃ i : Fin n,
      TrichromaticTriangle (cert.triangleColors i).1
        (cert.triangleColors i).2.1 (cert.triangleColors i).2.2 :=
  exists_trichromatic_of_odd_boundary n cert.triangleColors
    cert.boundaryRGCount cert.totalRG cert.htotal cert.hparity cert.hodd

/--
The stronger Sperner conclusion packaged by a `MonskyCertificate`: the number
of trichromatic triangles is odd, not merely nonzero.
-/
theorem chapter20_trichromatic_count_odd {n : ℕ} (cert : MonskyCertificate n) :
    Odd ((Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle (cert.triangleColors i).1
        (cert.triangleColors i).2.1 (cert.triangleColors i).2.2).card) := by
  have hmod := sperner_parity_abstract n cert.triangleColors cert.boundaryRGCount
    cert.totalRG cert.htotal cert.hparity
  exact Nat.odd_iff.mpr (by
    rw [hmod]
    exact Nat.odd_iff.mp cert.hodd)

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
Finite edge-parity form of the stronger Sperner conclusion: the number of
trichromatic triangles is odd.
-/
theorem trichromatic_count_odd_from_edge_parity {α : Type*} [Fintype α] [DecidableEq α]
    {n : ℕ} (triangles : Fin n → α × α × α) (color : α → MonskyColor)
    (hodd : Odd (oddEdgeRedGreenCount triangles color)) :
    Odd ((Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle (triangleColorsOfVertices color (triangles i)).1
        (triangleColorsOfVertices color (triangles i)).2.1
        (triangleColorsOfVertices color (triangles i)).2.2).card) := by
  simpa using chapter20_trichromatic_count_odd
    (edgeParityMonskyCertificate triangles color hodd)

/--
Sperner conclusion for a finite real square-boundary vertex chain: the
2-adic coloring forces an odd number of trichromatic listed triangles.
-/
theorem trichromatic_count_odd_of_realSquareBoundaryVertexChain
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (bottom right top left : List α) (bottomLeft bottomRight topRight topLeft : α)
    (hboundary : ∀ e : Sym2 α,
      Odd (edgeMultiplicity triangles e) ↔
        e ∈ (squareBoundaryEdgeList bottom right top left
          bottomLeft bottomRight topRight topLeft).toFinset)
    (hnodup : (squareBoundaryEdgeList bottom right top left
      bottomLeft bottomRight topRight topLeft).Nodup)
    (hbottomLeft : vertices bottomLeft = (0, 0))
    (hbottomRight : vertices bottomRight = (1, 0))
    (htopRight : vertices topRight = (1, 1))
    (htopLeft : vertices topLeft = (0, 1))
    (hbottom : ∀ v ∈ bottom, ∃ x : ℝ, vertices v = (x, 0))
    (hright : ∀ v ∈ right, ∃ y : ℝ, vertices v = (1, y))
    (htop : ∀ v ∈ top, ∃ x : ℝ, vertices v = (x, 1))
    (hleft : ∀ v ∈ left, ∃ y : ℝ, vertices v = (0, y)) :
    Odd ((Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle
        (triangleColorsOfVertices (realTwoAdicColor ∘ vertices) (triangles i)).1
        (triangleColorsOfVertices (realTwoAdicColor ∘ vertices) (triangles i)).2.1
        (triangleColorsOfVertices (realTwoAdicColor ∘ vertices) (triangles i)).2.2).card) := by
  exact trichromatic_count_odd_from_edge_parity triangles (realTwoAdicColor ∘ vertices)
    (oddEdgeRedGreenCount_odd_of_realSquareBoundaryVertexChain vertices triangles
      bottom right top left bottomLeft bottomRight topRight topLeft
      hboundary hnodup hbottomLeft hbottomRight htopRight htopLeft
      hbottom hright htop hleft)

/--
Existence form of the preceding Sperner conclusion, with the boundary oddness
computed from the real unit-square side constraints.
-/
theorem exists_trichromatic_of_realSquareBoundaryVertexChain
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (bottom right top left : List α) (bottomLeft bottomRight topRight topLeft : α)
    (hboundary : ∀ e : Sym2 α,
      Odd (edgeMultiplicity triangles e) ↔
        e ∈ (squareBoundaryEdgeList bottom right top left
          bottomLeft bottomRight topRight topLeft).toFinset)
    (hnodup : (squareBoundaryEdgeList bottom right top left
      bottomLeft bottomRight topRight topLeft).Nodup)
    (hbottomLeft : vertices bottomLeft = (0, 0))
    (hbottomRight : vertices bottomRight = (1, 0))
    (htopRight : vertices topRight = (1, 1))
    (htopLeft : vertices topLeft = (0, 1))
    (hbottom : ∀ v ∈ bottom, ∃ x : ℝ, vertices v = (x, 0))
    (hright : ∀ v ∈ right, ∃ y : ℝ, vertices v = (1, y))
    (htop : ∀ v ∈ top, ∃ x : ℝ, vertices v = (x, 1))
    (hleft : ∀ v ∈ left, ∃ y : ℝ, vertices v = (0, y)) :
    ∃ i : Fin n,
      TrichromaticTriangle
        (triangleColorsOfVertices (realTwoAdicColor ∘ vertices) (triangles i)).1
        (triangleColorsOfVertices (realTwoAdicColor ∘ vertices) (triangles i)).2.1
        (triangleColorsOfVertices (realTwoAdicColor ∘ vertices) (triangles i)).2.2 := by
  exact chapter20_from_edge_parity triangles (realTwoAdicColor ∘ vertices)
    (oddEdgeRedGreenCount_odd_of_realSquareBoundaryVertexChain vertices triangles
      bottom right top left bottomLeft bottomRight topRight topLeft
      hboundary hnodup hbottomLeft hbottomRight htopRight htopLeft
      hbottom hright htop hleft)

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
Area version of `no_odd_equalArea_realization_of_monskyCertificate`: the
geometric input is the ordinary triangle area `1 / n`, not a pre-oriented
double-area alternative.
-/
theorem no_odd_equalArea_realization_of_monskyCertificate_area {n : ℕ} (hn : Odd n)
    (triangles : Fin n → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ))
    (cert : MonskyCertificate n)
    (hcolors : ∀ i : Fin n, cert.triangleColors i =
      (realTwoAdicColor (triangles i).1,
       realTwoAdicColor (triangles i).2.1,
       realTwoAdicColor (triangles i).2.2))
    (harea : ∀ i : Fin n,
      realTriangleArea (triangles i).1 (triangles i).2.1 (triangles i).2.2 =
        (((1 : ℚ) / n : ℚ) : ℝ)) : False := by
  obtain ⟨i, hi⟩ := chapter20 cert
  have htri : TrichromaticTriangle (realTwoAdicColor (triangles i).1)
      (realTwoAdicColor (triangles i).2.1) (realTwoAdicColor (triangles i).2.2) := by
    simpa [hcolors i] using hi
  exact not_real_triangleArea_eq_one_div_odd_of_trichromatic hn htri (harea i)

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
Finite-vertex area version: after the Sperner boundary parity is established,
ordinary equal triangle area `1 / n` is already enough for the 2-adic
contradiction.
-/
theorem no_odd_equalArea_realization_of_edgeParity_area
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : Odd n)
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (hboundary : Odd (oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices)))
    (harea : ∀ i : Fin n,
      realTriangleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        (((1 : ℚ) / n : ℚ) : ℝ)) : False := by
  let cert : MonskyCertificate n :=
    edgeParityMonskyCertificate triangles (realTwoAdicColor ∘ vertices) hboundary
  exact no_odd_equalArea_realization_of_monskyCertificate_area hn
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
Variant of the boundary bridge stated directly with the explicit unit-square
point-edge chain.  This is the shape produced by a geometric extraction theorem
which identifies the odd-multiplicity triangle boundary edges with the concrete
four-side point list, before reducing that list to the side-chain count.
-/
theorem oddEdgeRedGreenCount_odd_of_squareBoundaryPointEdgeList
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (bottom right top left : List ℝ)
    (hboundary : oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices) =
      listEdgeRGCount (realTwoAdicSquareBoundaryPointEdgeList bottom right top left)
        realTwoAdicColor) :
    Odd (oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices)) := by
  rw [hboundary]
  exact realTwoAdicSquareBoundaryPointEdgeList_RGCount_odd bottom right top left

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

/--
Area version of the square-boundary-incidence frontier: once the extracted
boundary red-green count is the unit-square side-chain count, an ordinary
equal-area realization with odd `n` is impossible.
-/
theorem no_odd_equalArea_realization_of_squareBoundaryIncidence_area
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : Odd n)
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (bottom right top left : List ℝ)
    (hboundary : oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices) =
      realTwoAdicSquareBoundaryRGChainCount bottom right top left)
    (harea : ∀ i : Fin n,
      realTriangleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        (((1 : ℚ) / n : ℚ) : ℝ)) : False := by
  exact no_odd_equalArea_realization_of_edgeParity_area hn vertices triangles
    (oddEdgeRedGreenCount_odd_of_squareBoundaryIncidence vertices triangles bottom right top left
      hboundary)
    harea

/--
Same contradiction with the boundary assumption phrased using the explicit
unit-square point-edge list rather than the already-simplified side-chain
count.
-/
theorem no_odd_equalArea_realization_of_squareBoundaryPointEdgeList_abs
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : Odd n)
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (bottom right top left : List ℝ)
    (hboundary : oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices) =
      listEdgeRGCount (realTwoAdicSquareBoundaryPointEdgeList bottom right top left)
        realTwoAdicColor)
    (harea : ∀ i : Fin n,
      doubleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        (((2 : ℚ) / n : ℚ) : ℝ) ∨
      doubleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        -(((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  exact no_odd_equalArea_realization_of_edgeParity_abs hn vertices triangles
    (oddEdgeRedGreenCount_odd_of_squareBoundaryPointEdgeList vertices triangles
      bottom right top left hboundary)
    harea

/--
Area version with the boundary assumption phrased by the explicit unit-square
point-edge list.
-/
theorem no_odd_equalArea_realization_of_squareBoundaryPointEdgeList_area
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : Odd n)
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (bottom right top left : List ℝ)
    (hboundary : oddEdgeRedGreenCount triangles (realTwoAdicColor ∘ vertices) =
      listEdgeRGCount (realTwoAdicSquareBoundaryPointEdgeList bottom right top left)
        realTwoAdicColor)
    (harea : ∀ i : Fin n,
      realTriangleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        (((1 : ℚ) / n : ℚ) : ℝ)) : False := by
  exact no_odd_equalArea_realization_of_edgeParity_area hn vertices triangles
    (oddEdgeRedGreenCount_odd_of_squareBoundaryPointEdgeList vertices triangles
      bottom right top left hboundary)
    harea

/--
Finite-vertex square-boundary-chain version of the Monsky contradiction.  This
is closer to a genuine triangulation extraction than the count-equality
frontier above: the remaining geometric input identifies odd-multiplicity
triangle edges with an explicit finite boundary vertex chain, proves that the
chain vertices lie on the four sides of the unit square, and supplies oriented
equal-area alternatives.
-/
theorem no_odd_equalArea_realization_of_realSquareBoundaryVertexChain_abs
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : Odd n)
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (bottom right top left : List α) (bottomLeft bottomRight topRight topLeft : α)
    (hboundary : ∀ e : Sym2 α,
      Odd (edgeMultiplicity triangles e) ↔
        e ∈ (squareBoundaryEdgeList bottom right top left
          bottomLeft bottomRight topRight topLeft).toFinset)
    (hnodup : (squareBoundaryEdgeList bottom right top left
      bottomLeft bottomRight topRight topLeft).Nodup)
    (hbottomLeft : vertices bottomLeft = (0, 0))
    (hbottomRight : vertices bottomRight = (1, 0))
    (htopRight : vertices topRight = (1, 1))
    (htopLeft : vertices topLeft = (0, 1))
    (hbottom : ∀ v ∈ bottom, ∃ x : ℝ, vertices v = (x, 0))
    (hright : ∀ v ∈ right, ∃ y : ℝ, vertices v = (1, y))
    (htop : ∀ v ∈ top, ∃ x : ℝ, vertices v = (x, 1))
    (hleft : ∀ v ∈ left, ∃ y : ℝ, vertices v = (0, y))
    (harea : ∀ i : Fin n,
      doubleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        (((2 : ℚ) / n : ℚ) : ℝ) ∨
      doubleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        -(((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  exact no_odd_equalArea_realization_of_edgeParity_abs hn vertices triangles
    (oddEdgeRedGreenCount_odd_of_realSquareBoundaryVertexChain vertices triangles
      bottom right top left bottomLeft bottomRight topRight topLeft
      hboundary hnodup hbottomLeft hbottomRight htopRight htopLeft
      hbottom hright htop hleft)
    harea

/--
Finite-vertex square-boundary-chain area version.  This is the current closest
formal statement to the book argument: finite triangle data, exact
odd-multiplicity boundary chain, unit-square side constraints, and ordinary
equal triangle area `1 / n` contradict odd `n`.
-/
theorem no_odd_equalArea_realization_of_realSquareBoundaryVertexChain_area
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (hn : Odd n)
    (vertices : α → ℝ × ℝ) (triangles : Fin n → α × α × α)
    (bottom right top left : List α) (bottomLeft bottomRight topRight topLeft : α)
    (hboundary : ∀ e : Sym2 α,
      Odd (edgeMultiplicity triangles e) ↔
        e ∈ (squareBoundaryEdgeList bottom right top left
          bottomLeft bottomRight topRight topLeft).toFinset)
    (hnodup : (squareBoundaryEdgeList bottom right top left
      bottomLeft bottomRight topRight topLeft).Nodup)
    (hbottomLeft : vertices bottomLeft = (0, 0))
    (hbottomRight : vertices bottomRight = (1, 0))
    (htopRight : vertices topRight = (1, 1))
    (htopLeft : vertices topLeft = (0, 1))
    (hbottom : ∀ v ∈ bottom, ∃ x : ℝ, vertices v = (x, 0))
    (hright : ∀ v ∈ right, ∃ y : ℝ, vertices v = (1, y))
    (htop : ∀ v ∈ top, ∃ x : ℝ, vertices v = (x, 1))
    (hleft : ∀ v ∈ left, ∃ y : ℝ, vertices v = (0, y))
    (harea : ∀ i : Fin n,
      realTriangleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
          (vertices (triangles i).2.2) =
        (((1 : ℚ) / n : ℚ) : ℝ)) : False := by
  exact no_odd_equalArea_realization_of_edgeParity_area hn vertices triangles
    (oddEdgeRedGreenCount_odd_of_realSquareBoundaryVertexChain vertices triangles
      bottom right top left bottomLeft bottomRight topRight topLeft
      hboundary hnodup hbottomLeft hbottomRight htopRight htopLeft
      hbottom hright htop hleft)
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

/-! ### Linear-algebra bridge for `doubleArea`

The signed double-area `doubleArea a b c` is the determinant of the linear map
on `ℝ²` whose standard-basis images are the edge vectors `b - a` and `c - a`.
This rephrasing is the foundation for connecting the chapter's combinatorial
oriented area to Mathlib's `addHaar_image_linearMap` change-of-variables
formula — the route by which a future geometric dissection of the unit square
will deliver the boundary edge-parity (`hboundary`) needed to remove the
remaining `MonskyCertificate` escape.
-/

/-- `doubleArea a b c` equals the determinant of the 2×2 matrix whose columns
are the edge vectors `b - a` and `c - a`. -/
theorem doubleArea_eq_det_fin_two (a b c : ℝ × ℝ) :
    doubleArea a b c =
      (!![b.1 - a.1, c.1 - a.1;
          b.2 - a.2, c.2 - a.2] : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.det_fin_two_of]
  unfold doubleArea
  ring

/-- The real (unsigned) triangle area equals half the absolute value of the
determinant of the edge-vector matrix.  This is the form that pairs directly
with `MeasureTheory.Measure.addHaar_image_linearMap` (which computes the
Lebesgue measure of a linear-map image as `|det| · μ(source)`). -/
theorem realTriangleArea_eq_half_abs_det (a b c : ℝ × ℝ) :
    realTriangleArea a b c =
      |(!![b.1 - a.1, c.1 - a.1;
           b.2 - a.2, c.2 - a.2] : Matrix (Fin 2) (Fin 2) ℝ).det| / 2 := by
  rw [realTriangleArea, doubleArea_eq_det_fin_two]

/-! ### Structural properties of `doubleArea`

Translation invariance, vertex-permutation symmetries, and the collinearity
equivalence — small structural lemmas needed for any future geometric work
on triangle dissections of the unit square (Monsky's remaining frontier).
-/

/-- `doubleArea` is invariant under translation of all three vertices. -/
theorem doubleArea_translate (a b c v : ℝ × ℝ) :
    doubleArea (a + v) (b + v) (c + v) = doubleArea a b c := by
  unfold doubleArea
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- `doubleArea` based at the origin reduces to the determinant of the two
edge vectors. -/
theorem doubleArea_zero_left (b c : ℝ × ℝ) :
    doubleArea (0, 0) b c = b.1 * c.2 - c.1 * b.2 := by
  unfold doubleArea
  simp

/-- Reduce `doubleArea` based at `a` to the origin by translating `-a`. -/
theorem doubleArea_eq_zero_left_sub (a b c : ℝ × ℝ) :
    doubleArea a b c = doubleArea (0, 0) (b - a) (c - a) := by
  rw [show (b - a) = b + (-a) from by ring, show (c - a) = c + (-a) from by ring,
      show ((0, 0) : ℝ × ℝ) = a + (-a) from by simp]
  exact (doubleArea_translate a b c (-a)).symm

/-- `doubleArea` is antisymmetric under swapping the last two vertices. -/
theorem doubleArea_swap_right (a b c : ℝ × ℝ) :
    doubleArea a c b = - doubleArea a b c := by
  unfold doubleArea
  ring

/-- `doubleArea` is invariant under cyclic permutation of the three vertices. -/
theorem doubleArea_cycle (a b c : ℝ × ℝ) :
    doubleArea b c a = doubleArea a b c := by
  unfold doubleArea
  ring

/-- A triple of points in `ℝ²` is collinear iff its signed double-area is zero. -/
theorem doubleArea_eq_zero_iff_collinear (a b c : ℝ × ℝ) :
    doubleArea a b c = 0 ↔
      (b.1 - a.1) * (c.2 - a.2) = (c.1 - a.1) * (b.2 - a.2) := by
  rw [doubleArea, sub_eq_zero]

/-- `realTriangleArea` is invariant under translation. -/
theorem realTriangleArea_translate (a b c v : ℝ × ℝ) :
    realTriangleArea (a + v) (b + v) (c + v) = realTriangleArea a b c := by
  rw [realTriangleArea, realTriangleArea, doubleArea_translate]

/-- `realTriangleArea` is symmetric under any permutation of the three vertices
(unlike the signed `doubleArea`, the unsigned area depends only on the set). -/
theorem realTriangleArea_swap_right (a b c : ℝ × ℝ) :
    realTriangleArea a c b = realTriangleArea a b c := by
  rw [realTriangleArea, realTriangleArea, doubleArea_swap_right, abs_neg]

theorem realTriangleArea_cycle (a b c : ℝ × ℝ) :
    realTriangleArea b c a = realTriangleArea a b c := by
  rw [realTriangleArea, realTriangleArea, doubleArea_cycle]

/-! ### Affine parametrization of the triangle by the filled 2-simplex

The triangle with vertices `a, b, c` is the image, under the affine map
`(s, t) ↦ a + s • (b - a) + t • (c - a)`, of the filled standard 2-simplex
`{(s, t) | 0 ≤ s, 0 ≤ t, s + t ≤ 1}`.  We define the parametrization and
prove the forward containment (image ⊆ convex hull).  Pairing this with the
2-dimensional Lebesgue volume formula for linear-map images is the route to
`volume (convexHull ℝ {a, b, c}) = realTriangleArea a b c`.
-/

/-- The affine parametrization of the triangle: `(s, t) ↦ a + s • (b - a) + t • (c - a)`. -/
def triangleAffine (a b c : ℝ × ℝ) (st : ℝ × ℝ) : ℝ × ℝ :=
  a + st.1 • (b - a) + st.2 • (c - a)

@[simp] theorem triangleAffine_zero (a b c : ℝ × ℝ) :
    triangleAffine a b c (0, 0) = a := by
  simp [triangleAffine]

@[simp] theorem triangleAffine_e1 (a b c : ℝ × ℝ) :
    triangleAffine a b c (1, 0) = b := by
  simp [triangleAffine]

@[simp] theorem triangleAffine_e2 (a b c : ℝ × ℝ) :
    triangleAffine a b c (0, 1) = c := by
  simp [triangleAffine]

/-- The parametrization expressed as the standard convex combination of the
three vertices with weights `(1 - s - t, s, t)`. -/
theorem triangleAffine_eq_combo (a b c : ℝ × ℝ) (s t : ℝ) :
    triangleAffine a b c (s, t) = (1 - s - t) • a + s • b + t • c := by
  show a + s • (b - a) + t • (c - a) = (1 - s - t) • a + s • b + t • c
  rw [smul_sub, smul_sub]
  match_scalars <;> ring

/-- The set of filled standard 2-simplex parameters: `{(s, t) | 0 ≤ s, 0 ≤ t, s + t ≤ 1}`. -/
def filled2Simplex : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

theorem filled2Simplex_mem_iff (s t : ℝ) :
    (s, t) ∈ filled2Simplex ↔ 0 ≤ s ∧ 0 ≤ t ∧ s + t ≤ 1 := by
  simp [filled2Simplex]

/-- Forward direction: every point in the affine image of the filled 2-simplex
is a convex combination of `a, b, c` and therefore lies in their convex hull. -/
theorem triangleAffine_mem_convexHull (a b c : ℝ × ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1) :
    triangleAffine a b c (s, t) ∈ convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  rw [triangleAffine_eq_combo]
  set S : Set (ℝ × ℝ) := {a, b, c} with hS
  have ha : a ∈ convexHull ℝ S := subset_convexHull _ _ (by simp [hS])
  have hb : b ∈ convexHull ℝ S := subset_convexHull _ _ (by simp [hS])
  have hc : c ∈ convexHull ℝ S := subset_convexHull _ _ (by simp [hS])
  have hconv : Convex ℝ (convexHull ℝ S) := convex_convexHull _ _
  -- Apply Convex.sum_mem with Fin 3, weights (1-s-t, s, t), points (a, b, c).
  have hsum :
      (∑ i : Fin 3, (![(1 - s - t), s, t] : Fin 3 → ℝ) i •
        (![a, b, c] : Fin 3 → ℝ × ℝ) i) ∈ convexHull ℝ S := by
    refine hconv.sum_mem (w := ![(1 - s - t), s, t]) (z := ![a, b, c]) ?_ ?_ ?_
    · intro i _; fin_cases i
      · show (0 : ℝ) ≤ 1 - s - t; linarith
      · show (0 : ℝ) ≤ s; exact hs
      · show (0 : ℝ) ≤ t; exact ht
    · rw [Fin.sum_univ_three]
      show (1 - s - t) + s + t = 1
      ring
    · intro i _; fin_cases i
      · exact ha
      · exact hb
      · exact hc
  -- Reduce the Fin 3 sum to the explicit three-term form.
  simpa [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using hsum

/-- The image of the filled 2-simplex under `triangleAffine a b c` is a subset
of the convex hull of `{a, b, c}`. -/
theorem triangleAffine_image_subset_convexHull (a b c : ℝ × ℝ) :
    triangleAffine a b c '' filled2Simplex ⊆
      convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) := by
  rintro p ⟨⟨s, t⟩, hst, rfl⟩
  exact triangleAffine_mem_convexHull a b c hst.1 hst.2.1 hst.2.2

/-! ### Brick 1: volume of the filled 2-simplex

The 2-dimensional Lebesgue measure of `filled2Simplex` equals `1/2`.
Direct Fubini route: slice the simplex at fixed `x`, identify the slice
with `Icc 0 (1-x)`, and integrate the linear height. -/

/-- The filled 2-simplex is a closed (and hence measurable) subset of `ℝ × ℝ`. -/
theorem isClosed_filled2Simplex : IsClosed filled2Simplex := by
  have h1 : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have h2 : IsClosed {p : ℝ × ℝ | 0 ≤ p.2} :=
    isClosed_le continuous_const continuous_snd
  have h3 : IsClosed {p : ℝ × ℝ | p.1 + p.2 ≤ 1} :=
    isClosed_le (continuous_fst.add continuous_snd) continuous_const
  have hclosed :
      IsClosed ({p : ℝ × ℝ | 0 ≤ p.1} ∩
        ({p : ℝ × ℝ | 0 ≤ p.2} ∩ {p : ℝ × ℝ | p.1 + p.2 ≤ 1})) :=
    h1.inter (h2.inter h3)
  exact hclosed

theorem measurableSet_filled2Simplex : MeasurableSet filled2Simplex :=
  isClosed_filled2Simplex.measurableSet

/-- The volume of the slice of `filled2Simplex` at a fixed `x` coordinate
equals `ENNReal.ofReal (1 - x)` when `x ∈ Icc 0 1`, and zero otherwise. -/
theorem volume_filled2Simplex_slice (x : ℝ) :
    MeasureTheory.volume (Prod.mk x ⁻¹' filled2Simplex) =
      (Set.Icc (0 : ℝ) 1).indicator (fun x => ENNReal.ofReal (1 - x)) x := by
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hx]
    have heq : (Prod.mk x ⁻¹' filled2Simplex : Set ℝ) = Set.Icc 0 (1 - x) := by
      ext y
      simp only [filled2Simplex, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_Icc]
      refine ⟨fun ⟨_, hy, hxy⟩ => ⟨hy, by linarith⟩,
              fun ⟨hy, hyx⟩ => ⟨hx.1, hy, by linarith⟩⟩
    rw [heq, Real.volume_Icc, sub_zero]
  · rw [Set.indicator_of_notMem hx]
    have hempty : (Prod.mk x ⁻¹' filled2Simplex : Set ℝ) = ∅ := by
      ext y
      simp only [filled2Simplex, Set.mem_preimage, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false]
      rintro ⟨hx0, hy, hxy⟩
      apply hx
      exact ⟨hx0, by linarith⟩
    rw [hempty, MeasureTheory.measure_empty]

/-- The 2-D Lebesgue volume of the filled standard 2-simplex equals `1/2`. -/
theorem volume_filled2Simplex :
    MeasureTheory.volume filled2Simplex = ENNReal.ofReal (1 / 2) := by
  rw [MeasureTheory.Measure.volume_eq_prod,
      MeasureTheory.Measure.prod_apply measurableSet_filled2Simplex]
  simp_rw [volume_filled2Simplex_slice]
  rw [MeasureTheory.lintegral_indicator measurableSet_Icc]
  -- ∫⁻ x in Icc 0 1, ofReal (1 - x) ∂volume = ofReal (1/2)
  have hint : MeasureTheory.IntegrableOn (fun x : ℝ => 1 - x)
      (Set.Icc (0 : ℝ) 1) MeasureTheory.volume :=
    (continuous_const.sub continuous_id).continuousOn.integrableOn_Icc
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)]
      (fun x : ℝ => 1 - x) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
    have hx1 : x ≤ 1 := hx.2
    show (0 : ℝ) ≤ 1 - x
    linarith
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  -- ∫ x in Icc 0 1, (1 - x) ∂volume = 1/2
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ 1)]
  -- ∫ x in 0..1, (1 - x) = 1/2
  rw [intervalIntegral.integral_sub
        (intervalIntegral.intervalIntegrable_const)
        (intervalIntegral.intervalIntegrable_id),
      intervalIntegral.integral_const, integral_id]
  -- (1 - 0) • 1 - (1^2 - 0^2) / 2 = 1/2
  simp; ring

/-! ### Brick 2: convex hull ⊆ triangleAffine image

The reverse inclusion `convexHull ℝ {a, b, c} ⊆ triangleAffine '' filled2Simplex`
combined with `triangleAffine_image_subset_convexHull` gives set equality. -/

/-- The filled standard 2-simplex is convex. -/
theorem convex_filled2Simplex : Convex ℝ filled2Simplex := by
  rintro ⟨s₁, t₁⟩ ⟨hs₁, ht₁, hst₁⟩ ⟨s₂, t₂⟩ ⟨hs₂, ht₂, hst₂⟩ μ ν hμ hν hμν
  refine ⟨?_, ?_, ?_⟩
  · show 0 ≤ μ * s₁ + ν * s₂
    nlinarith
  · show 0 ≤ μ * t₁ + ν * t₂
    nlinarith
  · show μ * s₁ + ν * s₂ + (μ * t₁ + ν * t₂) ≤ 1
    have key : μ * (s₁ + t₁) + ν * (s₂ + t₂) ≤ μ * 1 + ν * 1 := by
      have h1 : μ * (s₁ + t₁) ≤ μ * 1 := by nlinarith
      have h2 : ν * (s₂ + t₂) ≤ ν * 1 := by nlinarith
      linarith
    nlinarith [hμν]

/-- The affine parametrization `triangleAffine a b c` sends a convex combination
of `(s, t)`-parameters to the corresponding convex combination of vertex images. -/
theorem triangleAffine_convex_combo (a b c : ℝ × ℝ) (p q : ℝ × ℝ)
    {μ ν : ℝ} (hμν : μ + ν = 1) :
    triangleAffine a b c (μ • p + ν • q) =
      μ • triangleAffine a b c p + ν • triangleAffine a b c q := by
  obtain ⟨ps, pt⟩ := p
  obtain ⟨qs, qt⟩ := q
  show a + (μ • (ps, pt) + ν • (qs, qt)).1 • (b - a) +
        (μ • (ps, pt) + ν • (qs, qt)).2 • (c - a) =
      μ • (a + ps • (b - a) + pt • (c - a)) +
        ν • (a + qs • (b - a) + qt • (c - a))
  have h1 : ((μ • (ps, pt) + ν • (qs, qt)).1 : ℝ) = μ * ps + ν * qs := by
    simp [Prod.smul_def]
  have h2 : ((μ • (ps, pt) + ν • (qs, qt)).2 : ℝ) = μ * pt + ν * qt := by
    simp [Prod.smul_def]
  rw [h1, h2]
  ext
  · show a.1 + (μ * ps + ν * qs) * (b.1 - a.1) + (μ * pt + ν * qt) * (c.1 - a.1) =
        μ * (a.1 + ps * (b.1 - a.1) + pt * (c.1 - a.1)) +
        ν * (a.1 + qs * (b.1 - a.1) + qt * (c.1 - a.1))
    linear_combination -a.1 * hμν
  · show a.2 + (μ * ps + ν * qs) * (b.2 - a.2) + (μ * pt + ν * qt) * (c.2 - a.2) =
        μ * (a.2 + ps * (b.2 - a.2) + pt * (c.2 - a.2)) +
        ν * (a.2 + qs * (b.2 - a.2) + qt * (c.2 - a.2))
    linear_combination -a.2 * hμν

/-- The image of the filled 2-simplex under `triangleAffine a b c` is convex. -/
theorem convex_triangleAffine_image (a b c : ℝ × ℝ) :
    Convex ℝ (triangleAffine a b c '' filled2Simplex) := by
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ μ ν hμ hν hμν
  refine ⟨μ • p + ν • q, convex_filled2Simplex hp hq hμ hν hμν, ?_⟩
  exact triangleAffine_convex_combo a b c p q hμν

/-- Reverse direction: every point in the convex hull of `{a, b, c}` is of the
form `triangleAffine a b c (s, t)` for some `(s, t)` in the filled 2-simplex. -/
theorem convexHull_subset_triangleAffine_image (a b c : ℝ × ℝ) :
    convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) ⊆
      triangleAffine a b c '' filled2Simplex := by
  apply convexHull_min ?_ (convex_triangleAffine_image a b c)
  intro p hp
  rcases hp with rfl | hp
  · exact ⟨(0, 0), by simp [filled2Simplex], by simp⟩
  rcases hp with rfl | hp
  · exact ⟨(1, 0), by simp [filled2Simplex], by simp⟩
  · rcases hp with rfl
    exact ⟨(0, 1), by simp [filled2Simplex], by simp⟩

/-- The convex hull of `{a, b, c}` equals the affine image of the filled 2-simplex. -/
theorem convexHull_eq_triangleAffine_image (a b c : ℝ × ℝ) :
    convexHull ℝ ({a, b, c} : Set (ℝ × ℝ)) = triangleAffine a b c '' filled2Simplex :=
  le_antisymm (convexHull_subset_triangleAffine_image a b c)
    (triangleAffine_image_subset_convexHull a b c)

/-! ### Brick 3: glue to `volume_convexHull_triangle`

The measure-theoretic bridge for Monsky's chapter 20:
`volume (convexHull ℝ {a, b, c}) = ENNReal.ofReal (realTriangleArea a b c)`. -/

/-- The linear part of `triangleAffine a b c`: `(s, t) ↦ s • (b - a) + t • (c - a)`. -/
noncomputable def triangleEdgeMap (a b c : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun st := st.1 • (b - a) + st.2 • (c - a)
  map_add' u v := by
    show (u + v).1 • (b - a) + (u + v).2 • (c - a) =
        u.1 • (b - a) + u.2 • (c - a) + (v.1 • (b - a) + v.2 • (c - a))
    ext
    · show ((u + v).1 * (b - a).1 + (u + v).2 * (c - a).1 : ℝ) =
          u.1 * (b - a).1 + u.2 * (c - a).1 + (v.1 * (b - a).1 + v.2 * (c - a).1)
      simp [Prod.add_def]; ring
    · show ((u + v).1 * (b - a).2 + (u + v).2 * (c - a).2 : ℝ) =
          u.1 * (b - a).2 + u.2 * (c - a).2 + (v.1 * (b - a).2 + v.2 * (c - a).2)
      simp [Prod.add_def]; ring
  map_smul' r v := by
    show (r • v).1 • (b - a) + (r • v).2 • (c - a) =
        r • (v.1 • (b - a) + v.2 • (c - a))
    ext
    · show ((r • v).1 * (b - a).1 + (r • v).2 * (c - a).1 : ℝ) =
          r * (v.1 * (b - a).1 + v.2 * (c - a).1)
      simp [Prod.smul_def]; ring
    · show ((r • v).1 * (b - a).2 + (r • v).2 * (c - a).2 : ℝ) =
          r * (v.1 * (b - a).2 + v.2 * (c - a).2)
      simp [Prod.smul_def]; ring

theorem triangleEdgeMap_apply (a b c st : ℝ × ℝ) :
    triangleEdgeMap a b c st = st.1 • (b - a) + st.2 • (c - a) := rfl

theorem triangleAffine_eq_add_triangleEdgeMap (a b c st : ℝ × ℝ) :
    triangleAffine a b c st = a + triangleEdgeMap a b c st := by
  show a + st.1 • (b - a) + st.2 • (c - a) = a + (st.1 • (b - a) + st.2 • (c - a))
  rw [add_assoc]

/-- The determinant of `triangleEdgeMap a b c` equals `doubleArea a b c`. -/
theorem det_triangleEdgeMap (a b c : ℝ × ℝ) :
    LinearMap.det (triangleEdgeMap a b c) = doubleArea a b c := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), doubleArea_eq_det_fin_two]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr]
  fin_cases j <;> fin_cases i <;>
    simp [triangleEdgeMap_apply, Module.Basis.finTwoProd_zero,
          Module.Basis.finTwoProd_one]

/-- Translation invariance of the 2-D Lebesgue measure. -/
theorem volume_image_add_left (a : ℝ × ℝ) (s : Set (ℝ × ℝ)) :
    MeasureTheory.volume ((fun x : ℝ × ℝ => a + x) '' s) = MeasureTheory.volume s := by
  simp

/-- The image of the filled 2-simplex under the affine triangle map has
2-D Lebesgue measure `|doubleArea a b c| · (1/2)`. -/
theorem volume_triangleAffine_image_filled2Simplex (a b c : ℝ × ℝ) :
    MeasureTheory.volume (triangleAffine a b c '' filled2Simplex) =
      ENNReal.ofReal |doubleArea a b c| * ENNReal.ofReal (1 / 2) := by
  have hcomp : (triangleAffine a b c : (ℝ × ℝ) → (ℝ × ℝ)) =
      (fun x : ℝ × ℝ => a + x) ∘ (triangleEdgeMap a b c) := by
    funext st
    exact triangleAffine_eq_add_triangleEdgeMap a b c st
  rw [hcomp, Set.image_comp, volume_image_add_left,
      MeasureTheory.Measure.addHaar_image_linearMap MeasureTheory.volume
        (triangleEdgeMap a b c) filled2Simplex,
      det_triangleEdgeMap, volume_filled2Simplex]

/-- **The Monsky measure bridge.** The 2-D Lebesgue measure of the triangle
`convexHull ℝ {a, b, c}` equals its Euclidean area `realTriangleArea a b c`. -/
theorem volume_convexHull_triangle (a b c : ℝ × ℝ) :
    MeasureTheory.volume (convexHull ℝ ({a, b, c} : Set (ℝ × ℝ))) =
      ENNReal.ofReal (realTriangleArea a b c) := by
  rw [convexHull_eq_triangleAffine_image, volume_triangleAffine_image_filled2Simplex,
      realTriangleArea,
      show (|doubleArea a b c| / 2 : ℝ) = |doubleArea a b c| * (1 / 2) from by ring,
      ENNReal.ofReal_mul (abs_nonneg _)]

/-! ### Packaged triangulation API

A `RealEqualAreaUnitSquareTriangulation α n` bundles the finite-vertex data
the Monsky frontier theorem
`no_odd_equalArea_realization_of_realSquareBoundaryVertexChain_area` consumes.
This is a refactoring layer: every hypothesis the existing theorem takes is
folded into a single named field, so downstream callers only need to construct
one structure instead of supplying twenty-plus arguments. -/

structure RealEqualAreaUnitSquareTriangulation
    (α : Type*) [Fintype α] [DecidableEq α] (n : ℕ) where
  vertices : α → ℝ × ℝ
  triangles : Fin n → α × α × α
  bottom : List α
  right : List α
  top : List α
  left : List α
  bottomLeft : α
  bottomRight : α
  topRight : α
  topLeft : α
  hboundary : ∀ e : Sym2 α,
    Odd (edgeMultiplicity triangles e) ↔
      e ∈ (squareBoundaryEdgeList bottom right top left
        bottomLeft bottomRight topRight topLeft).toFinset
  hnodup : (squareBoundaryEdgeList bottom right top left
    bottomLeft bottomRight topRight topLeft).Nodup
  hbottomLeft : vertices bottomLeft = (0, 0)
  hbottomRight : vertices bottomRight = (1, 0)
  htopRight : vertices topRight = (1, 1)
  htopLeft : vertices topLeft = (0, 1)
  hbottom : ∀ v ∈ bottom, ∃ x : ℝ, vertices v = (x, 0)
  hright : ∀ v ∈ right, ∃ y : ℝ, vertices v = (1, y)
  htop : ∀ v ∈ top, ∃ x : ℝ, vertices v = (x, 1)
  hleft : ∀ v ∈ left, ∃ y : ℝ, vertices v = (0, y)
  harea : ∀ i : Fin n,
    realTriangleArea (vertices (triangles i).1) (vertices (triangles i).2.1)
      (vertices (triangles i).2.2) = (((1 : ℚ) / n : ℚ) : ℝ)

/-- **Monsky's theorem (packaged form).** An equal-area triangulation of the
unit square into an odd number of triangles is impossible. -/
theorem RealEqualAreaUnitSquareTriangulation.not_odd_size
    {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (T : RealEqualAreaUnitSquareTriangulation α n) (hn : Odd n) : False :=
  no_odd_equalArea_realization_of_realSquareBoundaryVertexChain_area hn
    T.vertices T.triangles T.bottom T.right T.top T.left
    T.bottomLeft T.bottomRight T.topRight T.topLeft
    T.hboundary T.hnodup
    T.hbottomLeft T.hbottomRight T.htopRight T.htopLeft
    T.hbottom T.hright T.htop T.hleft T.harea

/-! ### Concrete witness: the diagonal split

The unit square can be split into two triangles of area 1/2 each by the main
diagonal — a constructive `RealEqualAreaUnitSquareTriangulation (Fin 4) 2`.
This is also a non-vacuity check on the packaged API: the structure can be
inhabited, just not for odd `n`. -/

namespace RealEqualAreaUnitSquareTriangulation

/-- The 4-vertex, 2-triangle equal-area triangulation of the unit square obtained
by drawing the main diagonal from `(0,0)` to `(1,1)`.

Vertices are indexed `0 = (0,0)`, `1 = (1,0)`, `2 = (1,1)`, `3 = (0,1)`; the
two triangles are `(0,1,2)` (bottom-right) and `(0,2,3)` (top-left). -/
def diagonalSplit : RealEqualAreaUnitSquareTriangulation (Fin 4) 2 where
  vertices := ![(0, 0), (1, 0), (1, 1), (0, 1)]
  triangles := ![(0, 1, 2), (0, 2, 3)]
  bottom := []
  right := []
  top := []
  left := []
  bottomLeft := 0
  bottomRight := 1
  topRight := 2
  topLeft := 3
  hboundary := by
    classical
    intro e
    -- The boundary edge list reduces to [s(0,1), s(1,2), s(2,3), s(3,0)].
    -- Triangle edges: (0,1), (1,2), (2,0) from triangle 0;
    --                 (0,2), (2,3), (3,0) from triangle 1.
    -- Edge s(0,2) = s(2,0) is shared (mult 2 — even);
    -- all four boundary edges have multiplicity 1 (odd).
    simp only [squareBoundaryEdgeList, consecutiveEdges, List.nil_append,
      List.cons_append, List.toFinset_cons,
      List.toFinset_nil, Finset.mem_insert]
    -- Decide the iff by cases on `e`: the edge multiplicity is a finite sum
    -- over (Fin 2 × Fin 3) of indicator (triangleEdge ... = e).
    refine Sym2.inductionOn e ?_
    intro a b
    fin_cases a <;> fin_cases b <;> decide
  hnodup := by decide
  hbottomLeft := rfl
  hbottomRight := rfl
  htopRight := rfl
  htopLeft := rfl
  hbottom := by simp
  hright := by simp
  htop := by simp
  hleft := by simp
  harea := by
    intro i
    fin_cases i
    · -- triangle (0, 1, 2): vertices (0,0), (1,0), (1,1)
      show realTriangleArea (0, 0) (1, 0) (1, 1) = (((1 : ℚ) / 2 : ℚ) : ℝ)
      simp [realTriangleArea, doubleArea]
    · -- triangle (0, 2, 3): vertices (0,0), (1,1), (0,1)
      show realTriangleArea (0, 0) (1, 1) (0, 1) = (((1 : ℚ) / 2 : ℚ) : ℝ)
      simp [realTriangleArea, doubleArea]

/-- The 5-vertex, 4-triangle equal-area triangulation of the unit square
obtained by drawing both diagonals (the "X" pattern); they meet at the
center `(1/2, 1/2)`.

Vertices: `0 = (0,0)`, `1 = (1,0)`, `2 = (1,1)`, `3 = (0,1)`, `4 = (1/2,1/2)`.
The center is an interior vertex, not on any side. The four triangles are
`(0,1,4)`, `(1,2,4)`, `(2,3,4)`, `(3,0,4)` — bottom, right, top, left of center. -/
noncomputable def centerSplit : RealEqualAreaUnitSquareTriangulation (Fin 5) 4 where
  vertices := ![(0, 0), (1, 0), (1, 1), (0, 1), (1/2, 1/2)]
  triangles := ![(0, 1, 4), (1, 2, 4), (2, 3, 4), (3, 0, 4)]
  bottom := []
  right := []
  top := []
  left := []
  bottomLeft := 0
  bottomRight := 1
  topRight := 2
  topLeft := 3
  hboundary := by
    classical
    intro e
    simp only [squareBoundaryEdgeList, consecutiveEdges, List.nil_append,
      List.cons_append, List.toFinset_cons,
      List.toFinset_nil, Finset.mem_insert]
    refine Sym2.inductionOn e ?_
    intro a b
    fin_cases a <;> fin_cases b <;> decide
  hnodup := by decide
  hbottomLeft := rfl
  hbottomRight := rfl
  htopRight := rfl
  htopLeft := rfl
  hbottom := by simp
  hright := by simp
  htop := by simp
  hleft := by simp
  harea := by
    intro i
    fin_cases i
    · show realTriangleArea (0, 0) (1, 0) (1/2, 1/2) = (((1 : ℚ) / 4 : ℚ) : ℝ)
      simp [realTriangleArea, doubleArea]; norm_num
    · show realTriangleArea (1, 0) (1, 1) (1/2, 1/2) = (((1 : ℚ) / 4 : ℚ) : ℝ)
      simp [realTriangleArea, doubleArea]; norm_num
    · show realTriangleArea (1, 1) (0, 1) (1/2, 1/2) = (((1 : ℚ) / 4 : ℚ) : ℝ)
      simp [realTriangleArea, doubleArea]; norm_num
    · show realTriangleArea (0, 1) (0, 0) (1/2, 1/2) = (((1 : ℚ) / 4 : ℚ) : ℝ)
      simp [realTriangleArea, doubleArea]; norm_num

end RealEqualAreaUnitSquareTriangulation

end ProofsInTheBook.Chapter20
