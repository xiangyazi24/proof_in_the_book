import ProofsInTheBook.Chapter20

/-!
# Chapter 20 (Monsky) — faithful dissection front end

`Chapter20.lean` proves Monsky's theorem **conditional on** the structure field
`RealEqualAreaUnitSquareTriangulation.hboundary`, which states that an unordered
*full* triangle edge `s(p, r) : Sym2 α` has odd triangle-multiplicity iff it lies
on the square boundary.  That is the *edge-to-edge* (simplicial) special case:
it fails for a genuine dissection in which a triangle side `p–r` is subdivided by
a "T-vertex" `m` belonging to neighbouring triangles, because then `s(p, r)` has
multiplicity `1` (odd) yet is interior.

Monsky's theorem is about **arbitrary** dissections.  The book (Aigner–Ziegler,
Ch. 20, Lemma 2) counts *atomic segments between consecutive vertices* and uses
"every red–green segment in the interior is counted twice".  This file builds
that faithful atomic-segment front end on top of the proved valuation / Sperner
engine in `Chapter20.lean`.

Sub-facts (book Lemma 2):
* **E2** each interior atomic segment lies on exactly two triangle boundaries,
  each boundary atomic segment on exactly one  *(the geometric core)*;
* **E3** on any straight side, the number of red–green atomic segments has the
  parity of `[endpoints are red&green]`, from the ≤2-colors-per-line corollary;
* **E5** the bottom side carries an odd number of red–green atomic segments and
  the other three sides carry none.

This file currently establishes the **≤2-colors-per-line corollary** to Lemma 1,
the foundation E3 rests on.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

/-- **Lemma 1, valuation form, any rainbow ordering.** For a trichromatic triple
in the plane (one red, one green, one blue vertex, in any order), the 2-adic
valuation of the signed double area is at least `1`.  The red–green–blue case is
`valuation_doubleArea_red_green_blue`; the other five vertex orderings reduce to
it because `doubleArea` only changes sign under a transposition and the valuation
is sign-blind (`v (-t) = v t`). -/
theorem one_le_realTwoAdicValuation_doubleArea_of_trichromatic {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c)) :
    1 ≤ realTwoAdicValuation (doubleArea a b c) := by
  have base : ∀ x y z : ℝ × ℝ,
      realTwoAdicColor x = red → realTwoAdicColor y = green →
      realTwoAdicColor z = blue →
      1 ≤ realTwoAdicValuation (doubleArea x y z) := by
    intro x y z hx hy hz
    exact valuation_doubleArea_red_green_blue realTwoAdicValuation hx hy hz
  have vneg : ∀ t : ℝ, realTwoAdicValuation (-t) = realTwoAdicValuation t :=
    fun t => realTwoAdicValuation.map_neg t
  rcases htri with ⟨hab, hbc, hca⟩
  rcases hA : realTwoAdicColor a with _ | _ | _ <;>
    rcases hB : realTwoAdicColor b with _ | _ | _ <;>
      rcases hC : realTwoAdicColor c with _ | _ | _ <;>
        (try rw [hA] at hab hca) <;> (try rw [hB] at hab hbc) <;>
        (try rw [hC] at hbc hca) <;>
        first
          | exact absurd rfl hab
          | exact absurd rfl hbc
          | exact absurd rfl hca
          | exact base a b c hA hB hC
          | (rw [show doubleArea a b c = -(doubleArea a c b) by
                unfold doubleArea; ring, vneg]
             exact base a c b hA hC hB)
          | (rw [show doubleArea a b c = -(doubleArea b a c) by
                unfold doubleArea; ring, vneg]
             exact base b a c hB hA hC)
          | (rw [show doubleArea a b c = doubleArea b c a by
                unfold doubleArea; ring]
             exact base b c a hB hC hA)
          | (rw [show doubleArea a b c = doubleArea c a b by
                unfold doubleArea; ring]
             exact base c a b hC hA hB)
          | (rw [show doubleArea a b c = -(doubleArea c b a) by
                unfold doubleArea; ring, vneg]
             exact base c b a hC hB hA)

/-- **Corollary to Lemma 1 (≤ 2 colors per line).** Three collinear points of the
plane cannot form a rainbow triangle.  Their signed double area is `0`, but a
rainbow triple has `realTwoAdicValuation (doubleArea …) ≥ 1 > 0 = v 0`.  This is
the fact that on any straight line at most two of the three Monsky colors occur,
which drives the per-side parity bookkeeping (E3). -/
theorem not_trichromatic_of_collinear {a b c : ℝ × ℝ}
    (hcol : doubleArea a b c = 0) :
    ¬ TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
        (realTwoAdicColor c) := by
  intro htri
  have h1 := one_le_realTwoAdicValuation_doubleArea_of_trichromatic htri
  rw [hcol, map_zero] at h1
  exact one_ne_zero (le_antisymm h1 zero_le_one)

/-! ### E3 — per-side red–green parity (general, from ≤2 colors per line)

Along one straight side of a triangle the dissection vertices form a chain
`a :: middle ++ [b]` lying on a single line, so by the ≤2-colors corollary the
chain uses at most two of the three colors.  In that situation the number of
red–green atomic segments along the chain has exactly the parity of "the two
endpoints `a, b` form a red–green pair".  This upgrades the proved
`listRGTransitionCount_*` side lemmas (which fix the colors per side) to an
arbitrary side of an arbitrary triangle. -/

theorem odd_listRGTransitionCount_iff_endpoints
    (a b : MonskyColor) (middle : List MonskyColor)
    (h2 : ∃ x y : MonskyColor, ∀ c ∈ a :: middle ++ [b], c = x ∨ c = y) :
    Odd (listRGTransitionCount (a :: middle ++ [b])) ↔ RedGreenEdge a b := by
  have hamem : a ∈ a :: middle ++ [b] := by simp
  have hbmem : b ∈ a :: middle ++ [b] := by simp
  by_cases hr : red ∈ a :: middle ++ [b]
  · by_cases hg : green ∈ a :: middle ++ [b]
    · -- both red and green occur; a third colour blue would give three colours
      -- in a chain that uses at most two, so blue is absent and the chain is
      -- entirely red/green.
      have hblue : blue ∉ a :: middle ++ [b] := by
        intro hbl
        obtain ⟨x, y, hxy⟩ := h2
        have hsub : ({red, green, blue} : Finset MonskyColor) ⊆ {x, y} := by
          intro c hc
          have hcxy : c = x ∨ c = y := by
            fin_cases hc
            · exact hxy red hr
            · exact hxy green hg
            · exact hxy blue hbl
          rcases hcxy with rfl | rfl <;> simp
        have hcard := Finset.card_le_card hsub
        have h3 : ({red, green, blue} : Finset MonskyColor).card = 3 := by decide
        have h2card : ({x, y} : Finset MonskyColor).card ≤ 2 := by
          apply le_trans (Finset.card_insert_le _ _); simp
        omega
      have hall : ∀ c ∈ a :: middle ++ [b], colorIsRedGreen c := by
        intro c hc
        cases c with
        | red => exact Or.inl rfl
        | green => exact Or.inr rfl
        | blue => exact absurd hc hblue
      have hz := listRGTransitionCount_cons_append_zmod (a := a) (b := b) middle hall
      rw [← ZMod.natCast_eq_one_iff_odd, hz]
      have ha : colorIsRedGreen a := hall a hamem
      have hb : colorIsRedGreen b := hall b hbmem
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide
    · -- green absent ⇒ chain is red/blue ⇒ no red–green segments
      have hall : ∀ c ∈ a :: middle ++ [b], colorIsRedBlue c := by
        intro c hc
        cases c with
        | red => exact Or.inl rfl
        | green => exact absurd hc hg
        | blue => exact Or.inr rfl
      have hzero := listRGTransitionCount_eq_zero_of_redBlue _ hall
      rw [hzero]
      have ha : colorIsRedBlue a := hall a hamem
      have hb : colorIsRedBlue b := hall b hbmem
      constructor
      · intro h; exact absurd h (by decide)
      · intro h; exact absurd h (not_redGreenEdge_of_redBlue ha hb)
  · -- red absent ⇒ chain is green/blue ⇒ no red–green segments
    have hall : ∀ c ∈ a :: middle ++ [b], colorIsGreenBlue c := by
      intro c hc
      cases c with
      | red => exact absurd hc hr
      | green => exact Or.inl rfl
      | blue => exact Or.inr rfl
    have hzero := listRGTransitionCount_eq_zero_of_greenBlue _ hall
    rw [hzero]
    have ha : colorIsGreenBlue a := hall a hamem
    have hb : colorIsGreenBlue b := hall b hbmem
    constructor
    · intro h; exact absurd h (by decide)
    · intro h; exact absurd h (not_redGreenEdge_of_greenBlue ha hb)

end ProofsInTheBook.Chapter20
