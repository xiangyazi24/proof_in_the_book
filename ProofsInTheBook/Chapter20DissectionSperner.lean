import ProofsInTheBook.Chapter20

/-!
# Chapter 20 (Monsky) — Sperner→contradiction spine

The engine-independent capstone spine: given a finite family of real triangles
each of area `1/n` (`n` odd) and the parity fact that the summed corner
red–green count is odd, Monsky's coloring forces a rainbow triangle whose area
cannot be `1/n` — contradiction.  This packages
`exists_trichromatic_of_odd_boundary` with
`not_real_triangleArea_eq_one_div_odd_of_trichromatic`, leaving the dissection
engine only to supply the parity hypothesis (`hparity`).

Depends only on `Chapter20`.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

/-- **Monsky contradiction from the Sperner parity.**  If `n` is odd, each of the
`n` triangles `tri i` has real area `1/n`, and the sum over triangles of the
corner red–green counts (under the 2-adic colouring) is odd, then `False`. -/
theorem monsky_false_of_odd_corner_parity
    {n : ℕ} (hn : Odd n) (tri : Fin n → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ))
    (harea : ∀ i, realTriangleArea (tri i).1 (tri i).2.1 (tri i).2.2 =
      (((1 : ℚ) / n : ℚ) : ℝ))
    (hodd : Odd (∑ i : Fin n, triangleLocalRGCount
      (realTwoAdicColor (tri i).1, realTwoAdicColor (tri i).2.1,
        realTwoAdicColor (tri i).2.2))) :
    False := by
  classical
  set tc : Fin n → MonskyColor × MonskyColor × MonskyColor :=
    fun i => (realTwoAdicColor (tri i).1, realTwoAdicColor (tri i).2.1,
      realTwoAdicColor (tri i).2.2) with htc
  set total : ℕ := ∑ i : Fin n, triangleLocalRGCount (tc i) with htotaldef
  -- `exists_trichromatic_of_odd_boundary` with boundary count = total (parity trivial)
  have htotal : total = ∑ i : Fin n,
      ((if RedGreenEdge (tc i).1 (tc i).2.1 then 1 else 0) +
       (if RedGreenEdge (tc i).2.1 (tc i).2.2 then 1 else 0) +
       (if RedGreenEdge (tc i).2.2 (tc i).1 then 1 else 0)) := by
    rw [htotaldef]; rfl
  obtain ⟨i, htri⟩ := exists_trichromatic_of_odd_boundary n tc total total htotal rfl
    (by rw [htotaldef]; exact hodd)
  exact not_real_triangleArea_eq_one_div_odd_of_trichromatic hn htri (harea i)

end ProofsInTheBook.Chapter20
