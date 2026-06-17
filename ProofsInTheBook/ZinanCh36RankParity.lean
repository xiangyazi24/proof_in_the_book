import ProofsInTheBook.ZinanCh36Comb

/-!
# `ZinanCh36RankParity` — the rank-parity proof of the Ch36 alternation master theorem

This file closes `alt_of_twoSide_noncrossing_cycle`, the pure-combinatorics master theorem that
the whole Ch36 alternation pipeline consumes, via the **rank-parity** design.

Reused (banked, clean-3) from `ZinanCh36Comb`: `TauInterleaves`, `alt_map_of_chain`,
`iterate_mem`, `sigma_iterate`, `even_of_reaches_same_sign`, `side_of_adjacent`.

The mathematical heart is `inside_card_even_of_chord`: along every ν-edge `(a, ν a)`, the number of
elements strictly τ-between `a` and `ν a` is even.  This holds because `ν` restricts to a bijection
from the `σ = +1` inside vertices to the `σ = -1` inside vertices (same-colour chords never
interleave, so a same-colour mate of an inside vertex cannot escape the interval).  Even interior
count makes every ν-edge flip τ-rank parity; the single-cycle hypothesis then forces alternation.
-/

namespace ProofsInTheBook
namespace ZinanCh36RankParity

open ProofsInTheBook.ZinanCh36Comb
open ProofsInTheBook.PolygonWindingBound (Alt)

section Defs
variable {ι : Type*} [DecidableEq ι]

/-- The τ-rank of `a` inside `S`: how many elements of `S` are strictly τ-below `a`. -/
noncomputable def rank (S : Finset ι) (τ : ι → ℝ) (a : ι) : ℕ :=
  (S.filter fun z => τ z < τ a).card

/-- The open τ-interval of `S` strictly between the chord endpoints `a` and `b`. -/
noncomputable def Inside (S : Finset ι) (τ : ι → ℝ) (a b : ι) : Finset ι :=
  S.filter fun z => min (τ a) (τ b) < τ z ∧ τ z < max (τ a) (τ b)

variable {S : Finset ι} {τ : ι → ℝ} {z a b : ι}

theorem mem_inside_iff :
    z ∈ Inside S τ a b ↔
      z ∈ S ∧ min (τ a) (τ b) < τ z ∧ τ z < max (τ a) (τ b) := by
  simp [Inside, Finset.mem_filter]

theorem mem_inside (hz : z ∈ S) (h1 : min (τ a) (τ b) < τ z)
    (h2 : τ z < max (τ a) (τ b)) : z ∈ Inside S τ a b :=
  mem_inside_iff.2 ⟨hz, h1, h2⟩

theorem inside_mem (hz : z ∈ Inside S τ a b) : z ∈ S := (mem_inside_iff.1 hz).1

/-- Inside is the *open* interval, so the endpoints are excluded (using τ-injectivity). -/
theorem not_endpoint_of_mem_inside
    (hz : z ∈ Inside S τ a b) :
    z ≠ a ∧ z ≠ b := by
  obtain ⟨hzS, h1, h2⟩ := mem_inside_iff.1 hz
  constructor
  · intro heq
    rw [heq] at h1 h2
    rcases le_total (τ a) (τ b) with h | h
    · rw [min_eq_left h] at h1; exact (lt_irrefl _ h1)
    · rw [max_eq_left h] at h2; exact (lt_irrefl _ h2)
  · intro heq
    rw [heq] at h1 h2
    rcases le_total (τ a) (τ b) with h | h
    · rw [max_eq_right h] at h2; exact (lt_irrefl _ h2)
    · rw [min_eq_right h] at h1; exact (lt_irrefl _ h1)

end Defs

/-! ## ν is a permutation of `S` (surjectivity from cycle-return, then bijectivity) -/

section Perm
variable {ι : Type*} [DecidableEq ι]
variable {S : Finset ι} {ν : ι → ι}

/-- Surjectivity of `ν` on `S`: every `b ∈ S` has a ν-preimage in `S`.  From the cycle hypothesis,
`ν^[m+1] b = b` for some `m`, so `ν^[m] b ∈ S` is a preimage. -/
theorem nu_surjOn_of_cycle
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b) :
    ∀ b ∈ S, ∃ a ∈ S, ν a = b := by
  intro b hb
  obtain ⟨m, hm⟩ := hcycle (ν b) (hνmem b hb) b hb
  refine ⟨ν^[m] b, iterate_mem hνmem hb m, ?_⟩
  -- hm : ν^[m] (ν b) = b.  Rewrite ν (ν^[m] b) = ν^[m+1] b = ν^[m] (ν b).
  have h1 : ν (ν^[m] b) = ν^[m + 1] b := (Function.iterate_succ_apply' ν m b).symm
  have h2 : ν^[m + 1] b = ν^[m] (ν b) := Function.iterate_succ_apply ν m b
  rw [h1, h2, hm]

/-- `ν` maps `S` into `S` as a `Set.MapsTo`. -/
theorem nu_mapsTo (hνmem : ∀ a ∈ S, ν a ∈ S) : Set.MapsTo ν (S : Set ι) S :=
  fun a ha => hνmem a ha

/-- `ν` is a bijection on `S` (from surjectivity + finiteness). -/
theorem nu_bijOn_of_cycle
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b) :
    Set.BijOn ν (S : Set ι) S := by
  have hfin : (S : Set ι).Finite := S.finite_toSet
  have hmaps : Set.MapsTo ν (S : Set ι) S := nu_mapsTo hνmem
  rw [← Set.Finite.surjOn_iff_bijOn_of_mapsTo hfin hmaps]
  intro b hb
  obtain ⟨a, ha, hab⟩ := nu_surjOn_of_cycle hνmem hcycle b hb
  exact ⟨a, ha, hab⟩

/-- Injectivity of `ν` on `S`. -/
theorem nu_injOn_of_cycle
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b) :
    ∀ a ∈ S, ∀ b ∈ S, ν a = ν b → a = b := by
  have hbij := nu_bijOn_of_cycle hνmem hcycle
  intro a ha b hb h
  exact hbij.injOn ha hb h

/-- A ν-predecessor function: returns a chosen preimage when one exists. -/
noncomputable def nuPred (S : Finset ι) (ν : ι → ι) (b : ι) : ι :=
  if h : ∃ a ∈ S, ν a = b then h.choose else b

theorem nuPred_spec
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    {b : ι} (hb : b ∈ S) :
    nuPred S ν b ∈ S ∧ ν (nuPred S ν b) = b := by
  have hex : ∃ a ∈ S, ν a = b := nu_surjOn_of_cycle hνmem hcycle b hb
  rw [nuPred, dif_pos hex]
  exact hex.choose_spec

theorem nuPred_mem
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    {b : ι} (hb : b ∈ S) : nuPred S ν b ∈ S :=
  (nuPred_spec hνmem hcycle hb).1

theorem nu_nuPred
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    {b : ι} (hb : b ∈ S) : ν (nuPred S ν b) = b :=
  (nuPred_spec hνmem hcycle hb).2

end Perm

/-! ## Same-colour mates stay inside (the interleaving obstruction)

`mate_together_pos`: for a `+1`-start chord `(a, ν a)` and a *distinct* `+1` element `u`, the two
endpoints `u` and `ν u` are τ-inside `(a, ν a)` together or not at all.  Were one inside and one
outside, the two same-colour chords would `TauInterleave`, contradicting `hposNI`. -/

section Mate
variable {ι : Type*} [DecidableEq ι]
variable {S : Finset ι} {τ : ι → ℝ} {σ : ι → ℤ} {ν : ι → ι}

/-- An element whose value is not in the open interval and differs from both endpoints is strictly
outside. -/
theorem outside_of_not_inside {α β γ : ℝ}
    (hα : γ ≠ α) (hβ : γ ≠ β)
    (h : ¬ (min α β < γ ∧ γ < max α β)) :
    γ < min α β ∨ max α β < γ := by
  push_neg at h
  rcases lt_trichotomy γ (min α β) with hlt | heq | hgt
  · exact Or.inl hlt
  · exfalso
    rcases min_choice α β with hm | hm
    · rw [hm] at heq; exact hα heq
    · rw [hm] at heq; exact hβ heq
  · right
    have hle := h hgt
    rcases lt_or_eq_of_le hle with h1 | h1
    · exact h1
    · exfalso
      rcases max_choice α β with hm | hm
      · rw [hm] at h1; exact hα h1.symm
      · rw [hm] at h1; exact hβ h1.symm

/-- Geometric core: given the open interval `(min(α,β), max(α,β))`, and a chord
`{c,d}` with `c` strictly inside but `d` strictly outside, the chords τ-interleave. -/
private theorem interleave_of_one_in_one_out
    {α β c d : ℝ}
    (hcin1 : min α β < c) (hcin2 : c < max α β)
    (hdout : d < min α β ∨ max α β < d) :
    (min α β < min c d ∧ min c d < max α β ∧ max α β < max c d) ∨
    (min c d < min α β ∧ min α β < max c d ∧ max c d < max α β) := by
  rcases hdout with hbelow | habove
  · right
    have hmin : min c d = d := min_eq_right (by linarith)
    have hmax : max c d = c := max_eq_left (by linarith)
    rw [hmin, hmax]
    exact ⟨hbelow, hcin1, hcin2⟩
  · left
    have hmin : min c d = c := min_eq_left (by linarith)
    have hmax : max c d = d := max_eq_right (by linarith)
    rw [hmin, hmax]
    exact ⟨hcin1, hcin2, habove⟩

/-- The "endpoints together" lemma for `+1`-start chords. -/
theorem mate_together_pos
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = 1 → σ b = 1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    {a u : ι}
    (ha : a ∈ S) (hσa : σ a = 1)
    (hu : u ∈ S) (hσu : σ u = 1) (hua : u ≠ a) :
    (u ∈ Inside S τ a (ν a)) ↔ (ν u ∈ Inside S τ a (ν a)) := by
  have hνaS : ν a ∈ S := hνmem a ha
  have hνuS : ν u ∈ S := hνmem u hu
  have hσνa : σ (ν a) = -1 := by rw [hflip a ha, hσa]
  have hσνu : σ (ν u) = -1 := by rw [hflip u hu, hσu]
  -- u ≠ ν a (signs), ν u ≠ a (signs), ν u ≠ ν a (injectivity ⇒ u = a, contra).
  have huνa : u ≠ ν a := fun h => by rw [h, hσνa] at hσu; norm_num at hσu
  have hνua : ν u ≠ a := fun h => by rw [h, hσa] at hσνu; norm_num at hσνu
  have hνuνa : ν u ≠ ν a :=
    fun h => hua (nu_injOn_of_cycle hνmem hcycle u hu a ha h)
  -- τ-distinctness
  have hτua : τ u ≠ τ a := fun h => hua (hτinj u hu a ha h)
  have hτuνa : τ u ≠ τ (ν a) := fun h => huνa (hτinj u hu (ν a) hνaS h)
  have hτνua : τ (ν u) ≠ τ a := fun h => hνua (hτinj (ν u) hνuS a ha h)
  have hτνuνa : τ (ν u) ≠ τ (ν a) := fun h => hνuνa (hτinj (ν u) hνuS (ν a) hνaS h)
  constructor
  · -- u inside ⇒ ν u inside
    intro hin
    by_contra hout
    obtain ⟨_, hu1, hu2⟩ := mem_inside_iff.1 hin
    rw [mem_inside_iff] at hout
    have hνu_out : τ (ν u) < min (τ a) (τ (ν a)) ∨ max (τ a) (τ (ν a)) < τ (ν u) :=
      outside_of_not_inside hτνua hτνuνa (fun hp => hout ⟨hνuS, hp⟩)
    have : TauInterleaves τ a (ν a) u (ν u) :=
      interleave_of_one_in_one_out hu1 hu2 hνu_out
    exact hposNI a ha u hu (Ne.symm hua) hσa hσu this
  · -- ν u inside ⇒ u inside
    intro hin
    by_contra hout
    obtain ⟨_, hνu1, hνu2⟩ := mem_inside_iff.1 hin
    rw [mem_inside_iff] at hout
    have hu_out : τ u < min (τ a) (τ (ν a)) ∨ max (τ a) (τ (ν a)) < τ u :=
      outside_of_not_inside hτua hτuνa (fun hp => hout ⟨hu, hp⟩)
    -- interleaving with roles c := ν u (inside), d := u (outside): same chord {u, ν u}
    have hinter : TauInterleaves τ a (ν a) (ν u) u :=
      interleave_of_one_in_one_out hνu1 hνu2 hu_out
    -- TauInterleaves is symmetric in swapping the two endpoints of the second chord
    have : TauInterleaves τ a (ν a) u (ν u) := by
      rw [TauInterleaves] at hinter ⊢
      rwa [min_comm (τ (ν u)) (τ u), max_comm (τ (ν u)) (τ u)] at hinter
    exact hposNI a ha u hu (Ne.symm hua) hσa hσu this

/-- The "endpoints together" lemma for `-1`-start chords (mirror of `mate_together_pos`). -/
theorem mate_together_neg
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hnegNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = -1 → σ b = -1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    {a u : ι}
    (ha : a ∈ S) (hσa : σ a = -1)
    (hu : u ∈ S) (hσu : σ u = -1) (hua : u ≠ a) :
    (u ∈ Inside S τ a (ν a)) ↔ (ν u ∈ Inside S τ a (ν a)) := by
  have hνaS : ν a ∈ S := hνmem a ha
  have hνuS : ν u ∈ S := hνmem u hu
  have hσνa : σ (ν a) = 1 := by rw [hflip a ha, hσa]; ring
  have hσνu : σ (ν u) = 1 := by rw [hflip u hu, hσu]; ring
  have huνa : u ≠ ν a := fun h => by rw [h, hσνa] at hσu; norm_num at hσu
  have hνua : ν u ≠ a := fun h => by rw [h, hσa] at hσνu; norm_num at hσνu
  have hνuνa : ν u ≠ ν a :=
    fun h => hua (nu_injOn_of_cycle hνmem hcycle u hu a ha h)
  have hτua : τ u ≠ τ a := fun h => hua (hτinj u hu a ha h)
  have hτuνa : τ u ≠ τ (ν a) := fun h => huνa (hτinj u hu (ν a) hνaS h)
  have hτνua : τ (ν u) ≠ τ a := fun h => hνua (hτinj (ν u) hνuS a ha h)
  have hτνuνa : τ (ν u) ≠ τ (ν a) := fun h => hνuνa (hτinj (ν u) hνuS (ν a) hνaS h)
  constructor
  · intro hin
    by_contra hout
    obtain ⟨_, hu1, hu2⟩ := mem_inside_iff.1 hin
    rw [mem_inside_iff] at hout
    have hνu_out : τ (ν u) < min (τ a) (τ (ν a)) ∨ max (τ a) (τ (ν a)) < τ (ν u) :=
      outside_of_not_inside hτνua hτνuνa (fun hp => hout ⟨hνuS, hp⟩)
    have : TauInterleaves τ a (ν a) u (ν u) :=
      interleave_of_one_in_one_out hu1 hu2 hνu_out
    exact hnegNI a ha u hu (Ne.symm hua) hσa hσu this
  · intro hin
    by_contra hout
    obtain ⟨_, hνu1, hνu2⟩ := mem_inside_iff.1 hin
    rw [mem_inside_iff] at hout
    have hu_out : τ u < min (τ a) (τ (ν a)) ∨ max (τ a) (τ (ν a)) < τ u :=
      outside_of_not_inside hτua hτuνa (fun hp => hout ⟨hu, hp⟩)
    have hinter : TauInterleaves τ a (ν a) (ν u) u :=
      interleave_of_one_in_one_out hνu1 hνu2 hu_out
    have : TauInterleaves τ a (ν a) u (ν u) := by
      rw [TauInterleaves] at hinter ⊢
      rwa [min_comm (τ (ν u)) (τ u), max_comm (τ (ν u)) (τ u)] at hinter
    exact hnegNI a ha u hu (Ne.symm hua) hσa hσu this

end Mate

/-! ## Even interior count for every ν-edge (the master brick) -/

section MasterBrick
variable {ι : Type*} [DecidableEq ι]
variable {S : Finset ι} {τ : ι → ℝ} {σ : ι → ℤ} {ν : ι → ι}

/-- For a `+1`-start chord `(a, ν a)`, `ν` is a bijection from the `+1` inside vertices to the
`-1` inside vertices, so the inside count is even. -/
theorem inside_card_even_of_pos_chord
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = 1 → σ b = 1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    {a : ι} (ha : a ∈ S) (hσa : σ a = 1) :
    Even (Inside S τ a (ν a)).card := by
  classical
  set I := Inside S τ a (ν a) with hI
  set Ipos := I.filter (fun z => σ z = 1) with hIpos
  set Ineg := I.filter (fun z => σ z = -1) with hIneg
  -- I is the disjoint union of Ipos and Ineg.
  have hsplit : I.card = Ipos.card + Ineg.card := by
    rw [hIpos, hIneg, ← Finset.card_union_of_disjoint]
    · congr 1
      ext z
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hz
        rcases hpm z (inside_mem hz) with h | h
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, h⟩
      · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    · rw [Finset.disjoint_filter]
      intro z _ h1 h2
      rw [h1] at h2; norm_num at h2
  -- ν : Ipos → Ineg is a bijection ⇒ card Ipos = card Ineg.
  have hbij : Ipos.card = Ineg.card := by
    apply Finset.card_bij (fun z _ => ν z)
    · -- maps into Ineg
      intro z hz
      rw [hIpos, Finset.mem_filter] at hz
      obtain ⟨hzI, hσz⟩ := hz
      have hza : z ≠ a := (not_endpoint_of_mem_inside hzI).1
      rw [hIneg, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (mate_together_pos hτinj hνmem hcycle hpm hflip hposNI ha hσa
          (inside_mem hzI) hσz hza).1 hzI
      · rw [hflip z (inside_mem hzI), hσz]
    · -- injective
      intro z1 h1 z2 h2 heq
      rw [hIpos, Finset.mem_filter] at h1 h2
      exact nu_injOn_of_cycle hνmem hcycle z1 (inside_mem h1.1) z2 (inside_mem h2.1) heq
    · -- surjective via predecessor
      intro w hw
      rw [hIneg, Finset.mem_filter] at hw
      obtain ⟨hwI, hσw⟩ := hw
      have hwS : w ∈ S := inside_mem hwI
      have hp := nuPred_mem hνmem hcycle hwS
      have hνp := nu_nuPred hνmem hcycle hwS
      -- σ (nuPred w) = 1
      have hσp : σ (nuPred S ν w) = 1 := by
        have := hflip (nuPred S ν w) hp
        rw [hνp, hσw] at this; linarith
      -- nuPred w ≠ a (else w = ν a, excluded from Inside)
      have hpa : nuPred S ν w ≠ a := by
        intro h
        rw [h] at hνp
        exact (not_endpoint_of_mem_inside hwI).2 hνp.symm
      refine ⟨nuPred S ν w, ?_, hνp⟩
      rw [hIpos, Finset.mem_filter]
      refine ⟨?_, hσp⟩
      -- nuPred w ∈ I:  its mate ν(nuPred w) = w is inside, so by mate_together it is inside.
      have hgoal : ν (nuPred S ν w) ∈ Inside S τ a (ν a) := by rw [hνp]; exact hwI
      exact (mate_together_pos hτinj hνmem hcycle hpm hflip hposNI ha hσa
        hp hσp hpa).2 hgoal
  rw [hsplit, ← hbij]
  exact ⟨Ipos.card, by ring⟩

/-- Mirror: for a `-1`-start chord, the inside count is even. -/
theorem inside_card_even_of_neg_chord
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hnegNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = -1 → σ b = -1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    {a : ι} (ha : a ∈ S) (hσa : σ a = -1) :
    Even (Inside S τ a (ν a)).card := by
  classical
  set I := Inside S τ a (ν a) with hI
  set Ineg := I.filter (fun z => σ z = -1) with hIneg
  set Ipos := I.filter (fun z => σ z = 1) with hIpos
  have hsplit : I.card = Ineg.card + Ipos.card := by
    rw [hIneg, hIpos, ← Finset.card_union_of_disjoint]
    · congr 1
      ext z
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hz
        rcases hpm z (inside_mem hz) with h | h
        · exact Or.inr ⟨hz, h⟩
        · exact Or.inl ⟨hz, h⟩
      · rintro (⟨hz, _⟩ | ⟨hz, _⟩) <;> exact hz
    · rw [Finset.disjoint_filter]
      intro z _ h1 h2
      rw [h1] at h2; norm_num at h2
  -- ν : Ineg → Ipos is a bijection.
  have hbij : Ineg.card = Ipos.card := by
    apply Finset.card_bij (fun z _ => ν z)
    · intro z hz
      rw [hIneg, Finset.mem_filter] at hz
      obtain ⟨hzI, hσz⟩ := hz
      have hza : z ≠ a := (not_endpoint_of_mem_inside hzI).1
      rw [hIpos, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (mate_together_neg hτinj hνmem hcycle hpm hflip hnegNI ha hσa
          (inside_mem hzI) hσz hza).1 hzI
      · rw [hflip z (inside_mem hzI), hσz]; ring
    · intro z1 h1 z2 h2 heq
      rw [hIneg, Finset.mem_filter] at h1 h2
      exact nu_injOn_of_cycle hνmem hcycle z1 (inside_mem h1.1) z2 (inside_mem h2.1) heq
    · intro w hw
      rw [hIpos, Finset.mem_filter] at hw
      obtain ⟨hwI, hσw⟩ := hw
      have hwS : w ∈ S := inside_mem hwI
      have hp := nuPred_mem hνmem hcycle hwS
      have hνp := nu_nuPred hνmem hcycle hwS
      have hσp : σ (nuPred S ν w) = -1 := by
        have := hflip (nuPred S ν w) hp
        rw [hνp, hσw] at this; linarith
      have hpa : nuPred S ν w ≠ a := by
        intro h
        rw [h] at hνp
        exact (not_endpoint_of_mem_inside hwI).2 hνp.symm
      refine ⟨nuPred S ν w, ?_, hνp⟩
      rw [hIneg, Finset.mem_filter]
      refine ⟨?_, hσp⟩
      have hgoal : ν (nuPred S ν w) ∈ Inside S τ a (ν a) := by rw [hνp]; exact hwI
      exact (mate_together_neg hτinj hνmem hcycle hpm hflip hnegNI ha hσa
        hp hσp hpa).2 hgoal
  rw [hsplit, hbij]
  exact ⟨Ipos.card, by ring⟩

/-- **The master brick.**  Along every ν-edge `(a, ν a)`, the number of elements strictly
τ-between `a` and `ν a` is even. -/
theorem inside_card_even_of_chord
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = 1 → σ b = 1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    (hnegNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = -1 → σ b = -1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    {a : ι} (ha : a ∈ S) :
    Even (Inside S τ a (ν a)).card := by
  rcases hpm a ha with hpos | hneg
  · exact inside_card_even_of_pos_chord hτinj hνmem hcycle hpm hflip hposNI ha hpos
  · exact inside_card_even_of_neg_chord hτinj hνmem hcycle hpm hflip hnegNI ha hneg

end MasterBrick

/-! ## Rank arithmetic and parity along ν -/

section Rank
variable {ι : Type*} [DecidableEq ι]
variable {S : Finset ι} {τ : ι → ℝ} {σ : ι → ℤ} {ν : ι → ι}

/-- When `τ a < τ b`, `Inside S τ a b = S.filter (τ a < τ· ∧ τ· < τ b)`. -/
theorem inside_eq_of_lt {a b : ι} (hab : τ a < τ b) :
    Inside S τ a b = S.filter (fun z => τ a < τ z ∧ τ z < τ b) := by
  rw [Inside, min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab)]

/-- **Rank-difference formula.**  For τ-comparable `a < b`, the rank gains `1` (for `a` itself) plus
the number of elements strictly between. -/
theorem rank_eq_rank_add_inside_left
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    {a b : ι} (ha : a ∈ S) (hb : b ∈ S) (hab : τ a < τ b) :
    rank S τ b = rank S τ a + 1 + (Inside S τ a b).card := by
  classical
  rw [rank, rank, inside_eq_of_lt hab]
  -- partition  {z ∈ S : τz < τb}  =  {z : τz<τa}  ⊎  {a}  ⊎  {z : τa<τz<τb}
  have hdecomp :
      S.filter (fun z => τ z < τ b) =
        (S.filter (fun z => τ z < τ a)) ∪ ({a} ∪ S.filter (fun z => τ a < τ z ∧ τ z < τ b)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hzS, hzb⟩
      rcases lt_trichotomy (τ z) (τ a) with h | h | h
      · exact Or.inl ⟨hzS, h⟩
      · exact Or.inr (Or.inl (hτinj z hzS a ha h))
      · exact Or.inr (Or.inr ⟨hzS, h, hzb⟩)
    · rintro (⟨hzS, h⟩ | h | ⟨hzS, h1, h2⟩)
      · exact ⟨hzS, lt_trans h hab⟩
      · subst h; exact ⟨ha, hab⟩
      · exact ⟨hzS, h2⟩
  rw [hdecomp]
  rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, Finset.card_singleton]
  · ring
  · -- {a} disjoint from inside
    rw [Finset.disjoint_singleton_left, Finset.mem_filter]
    rintro ⟨_, h, _⟩; exact lt_irrefl _ h
  · -- lower part disjoint from ({a} ∪ inside)
    rw [Finset.disjoint_union_right]
    constructor
    · rw [Finset.disjoint_singleton_right, Finset.mem_filter]
      rintro ⟨_, h⟩; exact lt_irrefl _ h
    · rw [Finset.disjoint_filter]
      intro z _ h1 h2; exact lt_irrefl _ (lt_trans h2.1 h1)

/-- For τ-adjacent `a < b` (nothing strictly between), `Inside` is empty, so rank increments by 1. -/
theorem rank_eq_succ_of_adjacent
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    {a b : ι} (ha : a ∈ S) (hb : b ∈ S) (hab : τ a < τ b)
    (hgap : ∀ z ∈ S, ¬ (τ a < τ z ∧ τ z < τ b)) :
    rank S τ b = rank S τ a + 1 := by
  have hempty : (Inside S τ a b).card = 0 := by
    rw [Finset.card_eq_zero]
    rw [inside_eq_of_lt hab]
    rw [Finset.filter_eq_empty_iff]
    intro z hz
    exact hgap z hz
  rw [rank_eq_rank_add_inside_left hτinj ha hb hab, hempty]

/-- **Rank parity flips along every ν-edge.** -/
theorem rank_parity_flip_of_chord
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = 1 → σ b = 1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    (hnegNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = -1 → σ b = -1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    {a : ι} (ha : a ∈ S) :
    rank S τ (ν a) % 2 ≠ rank S τ a % 2 := by
  have hνaS : ν a ∈ S := hνmem a ha
  -- ν a ≠ a since σ flips and σ a = ±1
  have hflipa := hflip a ha
  have hne : ν a ≠ a := by
    intro h; rw [h] at hflipa
    rcases hpm a ha with hp | hp <;> rw [hp] at hflipa <;> norm_num at hflipa
  -- τ a ≠ τ (ν a)
  have hτne : τ a ≠ τ (ν a) := fun h => hne (hτinj (ν a) hνaS a ha h.symm)
  have heven := inside_card_even_of_chord hτinj hνmem hcycle hpm hflip hposNI hnegNI ha
  rcases lt_or_gt_of_ne hτne with hlt | hgt
  · -- τ a < τ (ν a)
    have := rank_eq_rank_add_inside_left hτinj ha hνaS hlt
    obtain ⟨m, hm⟩ := heven
    omega
  · -- τ (ν a) < τ a ⇒ use the formula with roles swapped
    have hInside_symm : (Inside S τ (ν a) a).card = (Inside S τ a (ν a)).card := by
      rw [Inside, Inside]; rw [min_comm, max_comm]
    have := rank_eq_rank_add_inside_left hτinj hνaS ha hgt
    rw [hInside_symm] at this
    obtain ⟨m, hm⟩ := heven
    omega

/-- Rank parity after `k` ν-steps. -/
theorem rank_parity_iterate
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = 1 → σ b = 1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    (hnegNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = -1 → σ b = -1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    {a : ι} (ha : a ∈ S) :
    ∀ k : ℕ, rank S τ (ν^[k] a) % 2 = (rank S τ a + k) % 2 := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      have hmem : ν^[n] a ∈ S := iterate_mem hνmem ha n
      have hflipp := rank_parity_flip_of_chord hτinj hνmem hcycle hpm hflip hposNI hnegNI hmem
      rw [Function.iterate_succ_apply']
      -- rank (ν (ν^[n] a)) parity = 1 - rank (ν^[n] a) parity, and rank (ν^[n]a) % 2 = (rank a + n)%2
      omega

end Rank

/-! ## The no-adjacency lemma and the final master theorem -/

section Final
variable {ι : Type*} [DecidableEq ι]
variable {S : Finset ι} {τ : ι → ℝ} {σ : ι → ℤ} {ν : ι → ι}

/-- **No two τ-adjacent elements share a sign.** -/
theorem no_same_sign_of_tau_adjacent
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = 1 → σ b = 1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    (hnegNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = -1 → σ b = -1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    {a b : ι} (ha : a ∈ S) (hb : b ∈ S) (hab : τ a < τ b)
    (hgap : ∀ z ∈ S, ¬ (τ a < τ z ∧ τ z < τ b)) :
    σ a ≠ σ b := by
  intro hσeq
  obtain ⟨k, hk⟩ := hcycle a ha b hb
  -- same sign ⇒ k even (banked)
  have heven : Even k := even_of_reaches_same_sign hνmem hflip ha (hpm a ha) hσeq hk
  -- rank parity: rank b = rank a + 1 (adjacent) and rank (ν^[k] a) = rank b
  have hrank := rank_eq_succ_of_adjacent hτinj ha hb hab hgap
  have hpar := rank_parity_iterate hτinj hνmem hcycle hpm hflip hposNI hnegNI ha k
  rw [hk] at hpar
  -- hpar : rank b % 2 = (rank a + k) % 2 ; hrank : rank b = rank a + 1
  obtain ⟨m, hm⟩ := heven
  omega

/-- **THE Ch36 alternation master theorem.**  A single ν-cycle on a finite τ-labelled set, with a
sign `σ` flipping along ν and same-colour chords that never τ-interleave, has alternating signs read
off in τ-sorted order. -/
theorem alt_of_twoSide_noncrossing_cycle
    (hτinj : ∀ a ∈ S, ∀ b ∈ S, τ a = τ b → a = b)
    (hνmem : ∀ a ∈ S, ν a ∈ S)
    (hcycle : ∀ a ∈ S, ∀ b ∈ S, ∃ k : ℕ, ν^[k] a = b)
    (hpm : ∀ a ∈ S, σ a = 1 ∨ σ a = -1)
    (hflip : ∀ a ∈ S, σ (ν a) = -σ a)
    (hposNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = 1 → σ b = 1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    (hnegNI : ∀ a ∈ S, ∀ b ∈ S,
      a ≠ b → σ a = -1 → σ b = -1 →
      ¬ TauInterleaves τ a (ν a) b (ν b))
    {L : List ι}
    (hnd : L.Nodup)
    (hmem : ∀ a, a ∈ L ↔ a ∈ S)
    (hsort : L.Pairwise (fun a b => τ a < τ b)) :
    Alt (L.map σ) := by
  apply alt_map_of_chain
  -- Use the infix chain `[x,y] <:+: L` and convert each adjacent pair to a sign inequality.
  have hbase : List.IsChain (fun x y => [x, y] <:+: L) L := List.isChain_isInfix L
  refine hbase.imp ?_
  intro x y hinfix
  obtain ⟨l₁, l₂, hsplit⟩ := hinfix
  -- L = l₁ ++ [x,y] ++ l₂.  Extract membership, τ x < τ y, and the gap.
  have hxL : x ∈ L := by rw [← hsplit]; simp
  have hyL : y ∈ L := by rw [← hsplit]; simp
  have hxS : x ∈ S := (hmem x).1 hxL
  have hyS : y ∈ S := (hmem y).1 hyL
  -- Decompose sortedness over the split  L = (l₁ ++ [x,y]) ++ l₂.
  have hpwL : List.Pairwise (fun a b => τ a < τ b) (l₁ ++ [x, y] ++ l₂) := hsplit ▸ hsort
  rw [List.pairwise_append] at hpwL
  -- hpwL : Pairwise (l₁++[x,y]) ∧ Pairwise l₂ ∧ (∀ a ∈ l₁++[x,y], ∀ b ∈ l₂, τ a < τ b)
  obtain ⟨hpwFront, hpwL2, hcrossOut⟩ := hpwL
  rw [List.pairwise_append] at hpwFront
  obtain ⟨hpwl1, hpwxy, hcrossIn⟩ := hpwFront
  -- τ x < τ y from sortedness: x precedes y adjacently.
  have hxy : τ x < τ y := by
    rw [List.pairwise_cons] at hpwxy
    exact hpwxy.1 y (by simp)
  -- gap: any z ∈ S with τ x < τ z < τ y is in L; locate it in the split and contradict.
  have hgap : ∀ z ∈ S, ¬ (τ x < τ z ∧ τ z < τ y) := by
    intro z hzS hz
    obtain ⟨hzx, hzy⟩ := hz
    have hzL : z ∈ L := (hmem z).2 hzS
    rw [← hsplit] at hzL
    simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hzL
    rcases hzL with (hz1 | hzmid) | hz2
    · -- z ∈ l₁ : then τ z < τ x (cross l₁ [x,y]), contradicts τ x < τ z
      have hcross := hcrossIn z hz1 x (by simp)
      exact lt_asymm hzx hcross
    · -- z = x or z = y
      rcases hzmid with rfl | rfl
      · exact lt_irrefl _ hzx
      · exact lt_irrefl _ hzy
    · -- z ∈ l₂ : then τ y < τ z (cross (l₁++[x,y]) l₂), contradicts τ z < τ y
      have hcross := hcrossOut y (by simp) z hz2
      exact lt_asymm hzy hcross
  exact no_same_sign_of_tau_adjacent hτinj hνmem hcycle hpm hflip hposNI hnegNI
    hxS hyS hxy hgap

end Final

section Audit
open ProofsInTheBook.ZinanCh36RankParity
#print axioms alt_of_twoSide_noncrossing_cycle
#print axioms inside_card_even_of_chord
end Audit

end ZinanCh36RankParity
end ProofsInTheBook
