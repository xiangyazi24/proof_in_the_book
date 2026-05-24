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

Formalization status:
* Sperner is proved below from Mathlib's LYM inequality.
* Erdős-Ko-Rado is proved by calling Mathlib's Kruskal-Katona based theorem.
* Mathlib has no ready-made Dilworth/Kőnig chain-cover theorem in this checkout.
  This file proves the universal lower bound `antichain.card ≤ chainPartition.card`;
  the reverse chain-partition construction remains the honest missing part of
  Dilworth rather than being hidden behind an axiom or a theorem-shaped premise.
-/

namespace ProofsInTheBook.Chapter28

open Finset

/-!
### Erdős-Ko-Rado

Mathlib already contains the Kruskal-Katona proof of Erdős-Ko-Rado for
families of `r`-subsets of `Fin n`.  The book's hypothesis `2r ≤ n` is
converted to Mathlib's `r ≤ n / 2`.
-/

theorem chapter28_erdos_ko_rado {n r : ℕ} (𝒜 : Finset (Finset (Fin n)))
    (h𝒜 : (𝒜 : Set (Finset (Fin n))).Intersecting)
    (hr : (𝒜 : Set (Finset (Fin n))).Sized r) (hn : 2 * r ≤ n) :
    𝒜.card ≤ (n - 1).choose (r - 1) := by
  exact Finset.erdos_ko_rado h𝒜 hr (by omega)

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

/-!
### Dilworth's theorem

The definitions below use chain partitions of a finite set.  For a partition
of the ground set into chains, any antichain meets each part in at most one
point, so the antichain size is bounded by the number of chains.  The reverse
inequality is the hard half of Dilworth.
-/

structure ChainPartitionOn {α : Type*} [LE α] (P : Finset α) where
  parts : Finset (Finset α)
  chain' : ∀ C ∈ parts, IsChain (· ≤ ·) (C : Set α)
  disjoint' : ∀ C ∈ parts, ∀ D ∈ parts, C ≠ D → Disjoint C D
  covers' : ∀ x, x ∈ P ↔ ∃ C ∈ parts, x ∈ C

namespace ChainPartitionOn

variable {α : Type*} [LE α] {P : Finset α}

theorem part_subset (𝒞 : ChainPartitionOn P) {C : Finset α} (hC : C ∈ 𝒞.parts) : C ⊆ P := by
  intro x hx
  exact (𝒞.covers' x).2 ⟨C, hC, hx⟩

theorem exists_part (𝒞 : ChainPartitionOn P) {x : α} (hx : x ∈ P) :
    ∃ C ∈ 𝒞.parts, x ∈ C :=
  (𝒞.covers' x).1 hx

theorem part_eq_of_mem {𝒞 : ChainPartitionOn P} {C D : Finset α} (hC : C ∈ 𝒞.parts)
    (hD : D ∈ 𝒞.parts) {x : α} (hxC : x ∈ C) (hxD : x ∈ D) : C = D := by
  by_contra hne
  exact Finset.disjoint_left.mp (𝒞.disjoint' C hC D hD hne) hxC hxD

end ChainPartitionOn

theorem antichain_card_le_chainPartition_card {α : Type*} [PartialOrder α] [DecidableEq α]
    {P A : Finset α} (hAP : A ⊆ P) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (𝒞 : ChainPartitionOn P) :
    A.card ≤ 𝒞.parts.card := by
  classical
  choose part hpart_mem hpart_x using fun x : A => 𝒞.exists_part (hAP x.2)
  let partOf : A → 𝒞.parts := fun x => ⟨part x, hpart_mem x⟩
  have hpart_inj : Function.Injective partOf := by
    intro x y hxy
    have hx_mem : (x : α) ∈ part x := hpart_x x
    have hpart_eq : part x = part y := congrArg Subtype.val hxy
    have hy_mem : (y : α) ∈ part x := by simpa [hpart_eq] using hpart_x y
    by_cases h : (x : α) = y
    · exact Subtype.ext h
    have hchain := 𝒞.chain' (part x) (hpart_mem x)
    rcases hchain hx_mem hy_mem h with hle | hge
    · exact Subtype.ext (hA.eq x.2 y.2 hle)
    · exact Subtype.ext (hA.eq' x.2 y.2 hge)
  simpa [partOf] using Fintype.card_le_of_injective partOf hpart_inj

/--
The easy half of **Dilworth's theorem**: every chain partition of a finite
poset has at least as many parts as any antichain has elements.
-/
theorem chapter28_dilworth_lower_bound {α : Type*} [Fintype α] [PartialOrder α]
    [DecidableEq α] (A : Finset α) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (𝒞 : ChainPartitionOn (univ : Finset α)) :
    A.card ≤ 𝒞.parts.card :=
  antichain_card_le_chainPartition_card (by intro x _; simp) hA 𝒞

/--
Chapter 28 currently contains complete formal proofs of Sperner and
Erdős-Ko-Rado, plus the chain-partition lower bound used in Dilworth.  The
remaining Dilworth upper-bound construction is recorded in the module
docstring rather than hidden behind an axiom.
-/
theorem chapter28 :
    (∀ {α : Type*} [Fintype α] [DecidableEq α], ∀ 𝒜 : Finset (Finset α),
        IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α)) →
          𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2)) ∧
      (∀ {n r : ℕ}, ∀ 𝒜 : Finset (Finset (Fin n)),
        (𝒜 : Set (Finset (Fin n))).Intersecting →
          (𝒜 : Set (Finset (Fin n))).Sized r → 2 * r ≤ n →
            𝒜.card ≤ (n - 1).choose (r - 1)) ∧
      (∀ {α : Type*} [Fintype α] [PartialOrder α] [DecidableEq α],
        ∀ A : Finset α, IsAntichain (· ≤ ·) (A : Set α) →
          ∀ 𝒞 : ChainPartitionOn (univ : Finset α), A.card ≤ 𝒞.parts.card) := by
  refine ⟨?_, ?_, ?_⟩
  · intro α _ _ 𝒜 h𝒜
    exact chapter28_sperner 𝒜 h𝒜
  · intro n r 𝒜 h𝒜 hr hn
    exact chapter28_erdos_ko_rado 𝒜 h𝒜 hr hn
  · intro α _ _ _ A hA 𝒞
    exact chapter28_dilworth_lower_bound A hA 𝒞

end ProofsInTheBook.Chapter28
