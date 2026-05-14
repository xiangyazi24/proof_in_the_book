import Mathlib

/-!
# Chapter 36: How to guard a museum

From "Proofs from THE BOOK":

**Art gallery theorem** (Chvátal): ⌊n/3⌋ guards suffice to watch
any simple polygon with n vertices.

The book presents Fisk's elegant proof via triangulation and
3-coloring: any triangulation of a simple polygon is 3-colorable,
and the smallest color class has ≤ ⌊n/3⌋ vertices.
-/

namespace ProofsInTheBook.Chapter36

/-!
### The final counting step in Fisk's proof

After triangulating and 3-coloring a polygon, placing guards on the smallest
color class gives at most `⌊n/3⌋` guards.  This is the arithmetic part of that
argument.
-/

theorem min_three_color_classes_le_div_three (red green blue : ℕ) :
    min red (min green blue) ≤ (red + green + blue) / 3 := by
  by_contra h
  have hred : (red + green + blue) / 3 < red :=
    lt_of_not_ge fun hred => h (le_trans (min_le_left _ _) hred)
  have hgreen : (red + green + blue) / 3 < green :=
    lt_of_not_ge fun hgreen =>
      h (le_trans (le_trans (min_le_right _ _) (min_le_left _ _)) hgreen)
  have hblue : (red + green + blue) / 3 < blue :=
    lt_of_not_ge fun hblue =>
      h (le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hblue)
  omega

theorem chapter36 (red green blue : ℕ) :
    min red (min green blue) ≤ (red + green + blue) / 3 :=
  min_three_color_classes_le_div_three red green blue

end ProofsInTheBook.Chapter36
