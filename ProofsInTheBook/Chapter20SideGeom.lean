import ProofsInTheBook.Chapter20

/-!
# Chapter 20 (Monsky) — side collinearity

The geometric fact behind the per-side E3 bridge: any three points lying on a
common segment `[P, Q]` are collinear, i.e. their signed double area vanishes.
Used to feed `exists_two_colors_of_collinear_list` for each subdivided triangle
side.  Engine-independent (raw points), instantiated later with vertex coords.
-/

namespace ProofsInTheBook.Chapter20

/-- Three points weakly between `P` and `Q` (i.e. on the segment `[P,Q]`) have
vanishing signed double area: they are collinear. -/
theorem doubleArea_eq_zero_of_wbtw {P Q a b c : ℝ × ℝ}
    (ha : Wbtw ℝ P a Q) (hb : Wbtw ℝ P b Q) (hc : Wbtw ℝ P c Q) :
    doubleArea a b c = 0 := by
  obtain ⟨ta, _, rfl⟩ := ha
  obtain ⟨tb, _, rfl⟩ := hb
  obtain ⟨tc, _, rfl⟩ := hc
  simp only [AffineMap.lineMap_apply, doubleArea, Prod.fst_add, Prod.snd_add,
    Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_vsub, Prod.snd_vsub, vsub_eq_sub, vadd_eq_add]
  ring

end ProofsInTheBook.Chapter20
