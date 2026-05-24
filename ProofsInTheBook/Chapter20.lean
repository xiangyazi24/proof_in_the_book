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

Gap to the full book theorem: the missing work is the analytic/algebraic
input that constructs the certificate from an equal-area triangulation of the
unit square.  With the valuation-extension existence now available, the
remaining work is to choose one such extension, define the induced Monsky
coloring on all points of `ℝ²`, prove the color constraints on square corners
and triangle vertices, connect a geometric finite triangulation model to the
abstract Sperner parity count, and prove the area-valuation contradiction for
an odd equal-area subdivision.  Mathlib has valuation and geometry components,
but not this assembled polygonal Sperner/Monsky triangulation package.
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

/-- A chosen valuation subring of `ℝ` extending the 2-adic valuation on `ℚ`. -/
noncomputable def realTwoAdicSubring : ValuationSubring ℝ :=
  Classical.choose exists_real_twoAdic_extension

/-- The corresponding chosen real-valued-field valuation for Monsky coloring. -/
noncomputable def realTwoAdicValuation : Valuation ℝ realTwoAdicSubring.ValueGroup :=
  realTwoAdicSubring.valuation

theorem realTwoAdic_hasExtension :
    (Rat.padicValuation 2).HasExtension realTwoAdicValuation :=
  Classical.choose_spec exists_real_twoAdic_extension

/-- The chosen Monsky 2-adic coloring on the real plane. -/
noncomputable def realTwoAdicColor (p : ℝ × ℝ) : MonskyColor :=
  valuationColor realTwoAdicValuation p

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
edge count is odd. This is the part that requires 2-adic extension to ℝ
(via transcendence basis / Hahn series, not in Mathlib). -/
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

/- Tier 2 work (deferred): given a hypothetical equal-area triangulation of
the unit square into an ODD number of triangles, construct a MonskyCertificate
by:
1. Using Hahn series / transcendence basis to extend the 2-adic valuation
   v₂ : ℚ → ℤ to v₂' : ℝ → ℤ.
2. Color each point (x, y) ∈ ℝ² by:
   - red if v₂'(x) > 0 ∧ v₂'(y) > 0
   - green if v₂'(x) ≤ 0 ∧ v₂'(x) ≤ v₂'(y)
   - blue if v₂'(y) < 0 ∧ v₂'(y) < v₂'(x)
3. Verify the unit square corners (0,0), (1,0), (0,1), (1,1) get 3 distinct
   colors with odd boundary RG count.
4. The "total RG = boundary RG mod 2" identity follows from double-counting
   per Sperner.
The 2-adic extension to ℝ is non-trivial in Lean — likely needs Mathlib's
HahnSeries / WellOrderedExtension machinery. -/

/-- Chapter 20 (Monsky's theorem, Tier 1 conditional):
Given a Monsky 2-adic coloring certificate (which packages the 2-adic
extension construction + the double-counting parity result + the odd-boundary
witness), there exists a trichromatic triangle — corresponding to the
contradiction that closes the proof (such a triangle has area with 2-adic
valuation incompatible with 1/(odd integer)).
-/
theorem chapter20 {n : ℕ} (cert : MonskyCertificate n) :
    ∃ i : Fin n,
      TrichromaticTriangle (cert.triangleColors i).1
        (cert.triangleColors i).2.1 (cert.triangleColors i).2.2 :=
  exists_trichromatic_of_odd_boundary n cert.triangleColors
    cert.boundaryRGCount cert.totalRG cert.htotal cert.hparity cert.hodd

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
