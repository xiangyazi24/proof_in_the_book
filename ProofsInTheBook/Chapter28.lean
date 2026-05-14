import Mathlib

/-!
# Chapter 28: Three famous theorems on finite sets

From "Proofs from THE BOOK":

1. **Sperner's theorem**: The largest antichain in 𝒫([n]) has C(n,⌊n/2⌋) sets.
2. **Erdős-Ko-Rado**: For n ≥ 2k, a k-uniform intersecting family has ≤ C(n-1,k-1) sets.
3. **Dilworth's theorem**: min chain cover = max antichain.

The book proves Sperner via the **LYM inequality**: for an antichain 𝒜 ⊆ 𝒫([n]),
  ∑_{A ∈ 𝒜} 1/C(n,|A|) ≤ 1.
Since each C(n,|A|) ≤ C(n,⌊n/2⌋), this gives |𝒜| ≤ C(n,⌊n/2⌋).
-/

namespace ProofsInTheBook.Chapter28

open Finset

/-!
### Sperner's theorem via LYM

An antichain in the power set of a finite type α (ordered by ⊆)
has at most C(|α|, ⌊|α|/2⌋) elements.
-/

theorem chapter28_sperner {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 : Finset (Finset α))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) :=
  by
    have hmiddle_pos : 0 < ((Fintype.card α).choose (Fintype.card α / 2) : ℚ≥0) :=
      Nat.cast_pos.2 <| Nat.choose_pos (Nat.div_le_self _ _)
    have hlym := calc
      ∑ s ∈ 𝒜, ((Fintype.card α).choose (Fintype.card α / 2) : ℚ≥0)⁻¹
        ≤ ∑ s ∈ 𝒜, ((Fintype.card α).choose #s : ℚ≥0)⁻¹ := by
          gcongr with s hs
          · exact mod_cast Nat.choose_pos s.card_le_univ
          · exact Nat.choose_le_middle _ _
      _ ≤ 1 := Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose h𝒜
    simpa [mul_inv_le_iff₀' hmiddle_pos] using hlym

theorem chapter28 {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 : Finset (Finset α))
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) :=
  chapter28_sperner 𝒜 h𝒜

end ProofsInTheBook.Chapter28
