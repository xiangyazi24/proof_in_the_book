import ProofsInTheBook.Chapter20Dissection

/-!
# Chapter 20 (Monsky) — collinear-list colour lemmas (E3 plumbing)

The ≤2-colours-per-line corollary (`not_trichromatic_of_collinear`) upgraded
from a single triple to a whole collinear list of points: a list in which every
triple is collinear omits at least one of the three Monsky colours, hence uses at
most two.  Combined with E3 (`odd_listRGTransitionCount_iff_endpoints`) this gives
the per-side red–green parity for an arbitrary subdivided triangle side.

Depends only on `Chapter20Dissection` (brick-1 + E3); independent of the geometric
`SquareDissection` definition, so it is stable while that is under construction.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

/-- A list of points in which every triple is collinear (`doubleArea = 0`) omits
at least one Monsky colour: otherwise red, green, blue witnesses would form a
collinear rainbow triple, impossible by `not_trichromatic_of_collinear`. -/
theorem exists_missing_color_of_collinear_list (pts : List (ℝ × ℝ))
    (hcol : ∀ a ∈ pts, ∀ b ∈ pts, ∀ c ∈ pts, doubleArea a b c = 0) :
    ∃ col : MonskyColor, ∀ p ∈ pts, realTwoAdicColor p ≠ col := by
  by_contra h
  push_neg at h
  obtain ⟨pr, hpr, hcr⟩ := h red
  obtain ⟨pg, hpg, hcg⟩ := h green
  obtain ⟨pb, hpb, hcb⟩ := h blue
  have hc0 : doubleArea pr pg pb = 0 := hcol pr hpr pg hpg pb hpb
  exact not_trichromatic_of_collinear hc0
    (by rw [hcr, hcg, hcb]; exact trichromatic_of_eq_red_green_blue rfl rfl rfl)

/-- A collinear list of points uses at most two colours. -/
theorem exists_two_colors_of_collinear_list (pts : List (ℝ × ℝ))
    (hcol : ∀ a ∈ pts, ∀ b ∈ pts, ∀ c ∈ pts, doubleArea a b c = 0) :
    ∃ x y : MonskyColor, ∀ p ∈ pts, realTwoAdicColor p = x ∨ realTwoAdicColor p = y := by
  obtain ⟨col, hmiss⟩ := exists_missing_color_of_collinear_list pts hcol
  cases col with
  | red =>
      refine ⟨green, blue, fun p hp => ?_⟩
      have hne := hmiss p hp
      cases h : realTwoAdicColor p with
      | red => exact absurd h hne
      | green => exact Or.inl rfl
      | blue => exact Or.inr rfl
  | green =>
      refine ⟨red, blue, fun p hp => ?_⟩
      have hne := hmiss p hp
      cases h : realTwoAdicColor p with
      | red => exact Or.inl rfl
      | green => exact absurd h hne
      | blue => exact Or.inr rfl
  | blue =>
      refine ⟨red, green, fun p hp => ?_⟩
      have hne := hmiss p hp
      cases h : realTwoAdicColor p with
      | red => exact Or.inl rfl
      | green => exact Or.inr rfl
      | blue => exact absurd h hne

/-- **E3 on a subdivided side, point form.** For a side whose intermediate
vertices give the colour chain `ca :: middle ++ [cb]` and whose underlying points
are pairwise-triple-collinear, the number of red–green atomic segments has the
parity of "the two endpoint colours form a red–green pair". -/
theorem odd_sideRG_iff_endpoints_of_collinear
    (endpts mids : List (ℝ × ℝ)) (a b : ℝ × ℝ)
    (hchain : endpts = a :: mids ++ [b])
    (hcol : ∀ x ∈ endpts, ∀ y ∈ endpts, ∀ z ∈ endpts, doubleArea x y z = 0) :
    Odd (listRGTransitionCount
        (realTwoAdicColor a :: mids.map realTwoAdicColor ++ [realTwoAdicColor b])) ↔
      RedGreenEdge (realTwoAdicColor a) (realTwoAdicColor b) := by
  obtain ⟨x, y, hxy⟩ := exists_two_colors_of_collinear_list endpts hcol
  apply odd_listRGTransitionCount_iff_endpoints
  refine ⟨x, y, ?_⟩
  intro c hc
  -- the colour chain is `endpts.map realTwoAdicColor`, so `c` is some point's colour
  have hc' : c ∈ endpts.map realTwoAdicColor := by
    rw [hchain]; simpa using hc
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc'
  exact hxy p hp

end ProofsInTheBook.Chapter20
