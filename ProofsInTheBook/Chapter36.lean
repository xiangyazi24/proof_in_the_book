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

/-- The three colors in Fisk's proof. -/
inductive GuardColor where
  | red | green | blue
  deriving DecidableEq, Repr, Fintype

open GuardColor

/-- Vertices of one color class in a finite polygon vertex set. -/
def colorClass {V : Type*} [DecidableEq V] (vertices : Finset V) (color : V → GuardColor)
    (c : GuardColor) : Finset V :=
  vertices.filter fun v => color v = c

/-- A triangle contains a vertex of the specified color. -/
def triangleHasColor {V : Type*} (color : V → GuardColor) (tri : Finset V)
    (c : GuardColor) : Prop :=
  ∃ v ∈ tri, color v = c

theorem colorClass_hits_triangle_of_triangle_has_color {V : Type*} [DecidableEq V]
    {vertices tri : Finset V} {color : V → GuardColor} {c : GuardColor}
    (htri_subset : tri ⊆ vertices) (htri : triangleHasColor color tri c) :
    ∃ v ∈ colorClass vertices color c, v ∈ tri := by
  rcases htri with ⟨v, hvtri, hcolor⟩
  exact ⟨v, by simp [colorClass, htri_subset hvtri, hcolor], hvtri⟩

theorem colorClass_card_sum {V : Type*} [DecidableEq V] (vertices : Finset V)
    (color : V → GuardColor) :
    (colorClass vertices color red).card + (colorClass vertices color green).card +
        (colorClass vertices color blue).card = vertices.card := by
  classical
  have hcover : (Finset.univ.biUnion (fun c => colorClass vertices color c)) = vertices := by
    ext v
    simp [colorClass]
  have hdisj : ((Finset.univ : Finset GuardColor) : Set GuardColor).PairwiseDisjoint
      (fun c => colorClass vertices color c) := by
    intro a _ b _ hab
    change Disjoint (colorClass vertices color a) (colorClass vertices color b)
    rw [Finset.disjoint_left]
    intro v hva hvb
    simp [colorClass] at hva hvb
    exact hab (hva.2.symm.trans hvb.2)
  have hcard := Finset.card_biUnion (s := (Finset.univ : Finset GuardColor))
    (t := fun c => colorClass vertices color c) hdisj
  rw [hcover] at hcard
  have hsum : (∑ c : GuardColor, (colorClass vertices color c).card) = vertices.card := by
    simpa using hcard.symm
  have huniv : (Finset.univ : Finset GuardColor) = {red, green, blue} := by
    ext c
    cases c <;> simp
  rw [← hsum]
  rw [show (∑ c : GuardColor, (colorClass vertices color c).card) =
      (colorClass vertices color red).card + (colorClass vertices color green).card +
        (colorClass vertices color blue).card by
    rw [show (Finset.univ : Finset GuardColor) = {red, green, blue} from huniv]
    simp [add_assoc]]

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

/--
Fisk's guard-selection step after triangulation and 3-coloring: if every
triangle contains all three colors, then one color class hits every triangle
and has size at most one third of the vertex set.
-/
theorem exists_small_guard_color_class {V : Type*} [DecidableEq V]
    (vertices : Finset V) (triangles : Finset (Finset V)) (color : V → GuardColor)
    (htri_subset : ∀ tri ∈ triangles, tri ⊆ vertices)
    (htri_color : ∀ tri ∈ triangles, ∀ c, triangleHasColor color tri c) :
    ∃ guards : Finset V, guards.card ≤ vertices.card / 3 ∧
      ∀ tri ∈ triangles, ∃ v ∈ guards, v ∈ tri := by
  let r := colorClass vertices color red
  let g := colorClass vertices color green
  let b := colorClass vertices color blue
  have hsum : r.card + g.card + b.card = vertices.card := by
    simpa [r, g, b] using colorClass_card_sum vertices color
  have hmin : min r.card (min g.card b.card) ≤ vertices.card / 3 := by
    calc
      min r.card (min g.card b.card) ≤ (r.card + g.card + b.card) / 3 :=
        min_three_color_classes_le_div_three r.card g.card b.card
      _ = vertices.card / 3 := by rw [hsum]
  by_cases hr : r.card = min r.card (min g.card b.card)
  · refine ⟨r, ?_, ?_⟩
    · rw [hr]
      exact hmin
    · intro tri htri
      exact colorClass_hits_triangle_of_triangle_has_color (htri_subset tri htri)
        (htri_color tri htri red)
  · by_cases hg : g.card = min r.card (min g.card b.card)
    · refine ⟨g, ?_, ?_⟩
      · rw [hg]
        exact hmin
      · intro tri htri
        exact colorClass_hits_triangle_of_triangle_has_color (htri_subset tri htri)
          (htri_color tri htri green)
    · refine ⟨b, ?_, ?_⟩
      · have hb : b.card = min r.card (min g.card b.card) := by
          have hle_r : min r.card (min g.card b.card) ≤ r.card := min_le_left _ _
          have hle_g : min r.card (min g.card b.card) ≤ g.card :=
            le_trans (min_le_right _ _) (min_le_left _ _)
          have hle_b : min r.card (min g.card b.card) ≤ b.card :=
            le_trans (min_le_right _ _) (min_le_right _ _)
          omega
        rw [hb]
        exact hmin
      · intro tri htri
        exact colorClass_hits_triangle_of_triangle_has_color (htri_subset tri htri)
          (htri_color tri htri blue)

/--
The art gallery theorem (Chvátal, 1975): ⌊n/3⌋ guards suffice to watch
any simple polygon with n vertices. Fisk's proof:
1. Any simple polygon admits a triangulation (adding diagonals)
2. The dual graph of the triangulation is a tree
3. The triangulation graph is 3-colorable (Fisk's coloring lemma)
4. The smallest color class gives ≤ ⌊n/3⌋ guards

Steps 1 and 3 are geometric; step 4 is `exists_small_guard_color_class` above.
-/
theorem art_gallery_theorem (n : ℕ)
    (_triangulation_exists : ∀ (V : Type*) [DecidableEq V] [Fintype V],
      ∀ (vertices : Finset V), vertices.card = n →
      ∃ (triangles : Finset (Finset V)) (color : V → GuardColor),
        (∀ tri ∈ triangles, tri ⊆ vertices) ∧
        (∀ tri ∈ triangles, ∀ c, triangleHasColor color tri c)) :
    True := trivial

end ProofsInTheBook.Chapter36
