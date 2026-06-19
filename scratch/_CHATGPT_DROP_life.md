# Ch13 Route B helper: cyclic-unimodal sublevels are cyclic intervals

This is the cleanest Lean target I would use for a `CyclicIntervalOnVertex` bridge.  The key design choice is to **not** make the core theorem depend on `List.rotate` bookkeeping.  Instead, the core theorem works directly on a cyclic enumeration

```lean
step s t = s + (t : ZMod n)
```

and defines a cyclic interval by saying that, from some start `s`, membership is exactly `t < k` for `0 ≤ t < n`.  This is equivalent to the more extensional predicate

```lean
∀ i, P i ↔ ∃ t < k, i = s + t
```

using `ZMod.exists` / `ZMod.natCast_zmod_surjective` and uniqueness of representatives when `t < n`; in downstream code the enumeration form is much easier to use.

The theorem below uses the **block-structure** form of “the difference signs have at most two alternations”: there is a cyclic start and a peak index `p` such that the lifted sequence is nondecreasing on `[0,p]` and nonincreasing on `[p,n]`.  This is the transitive form of “a run of nonnegative consecutive differences followed by a run of nonpositive consecutive differences”; it is the right target for a small outer parser from a sorted list plus `List.rotate`/`List.Chain` facts.

Important implementation notes:

* `ZMod.natCast_self`, `Nat.cast_add`, and `simp [step]` do the wrap arithmetic.
* `Nat.find_spec` and `Nat.find_min` build the first threshold cut on the rising side and the first threshold cut on the falling side.
* `omega` handles the remaining natural-number inequalities.
* The raw list adapter should prove the block-structure hypothesis from a rotated difference-sign list using `List.Chain` over the two runs.  I would keep that parser outside this theorem; the theorem below is the reusable kernel.

```lean
import Mathlib

open scoped BigOperators

namespace Cauchy.Ch13.CyclicUnimodal

/-- The cyclic walk starting at `s`.  This is the only place where modular
arithmetic enters the core theorem. -/
def step {n : ℕ} (s : ZMod n) (t : ℕ) : ZMod n :=
  s + (t : ZMod n)

/-- Lean-friendly cyclic interval predicate: from a start `s`, membership is
exactly the first `k` entries of the cyclic enumeration `s, s+1, ..., s+n-1`.

This avoids quotient-representative noise in the main proof.  It is equivalent,
for `k ≤ n`, to `∀ i, P i ↔ ∃ t < k, i = s + t`. -/
def IsCyclicIntervalFrom {n : ℕ} [NeZero n]
    (P : ZMod n → Prop) (s : ZMod n) (k : ℕ) : Prop :=
  k ≤ n ∧ ∀ t : ℕ, t < n → (P (step s t) ↔ t < k)

/-- A predicate on the cyclic index set is a cyclic interval if it is an initial
block after some cyclic rotation. -/
def IsCyclicInterval {n : ℕ} [NeZero n] (P : ZMod n → Prop) : Prop :=
  ∃ s : ZMod n, ∃ k : ℕ, IsCyclicIntervalFrom P s k

/-- Block-structure form of cyclic unimodality.

There is a cyclic start `s` and a peak index `p` such that the lifted sequence
`t ↦ a (s+t)` is nondecreasing on `[0,p]` and nonincreasing on `[p,n]`.
This is the transitive form of a run of nonnegative consecutive differences
followed by a run of nonpositive consecutive differences. -/
def CyclicallyUnimodal {n : ℕ} [NeZero n] (a : ZMod n → ℝ) : Prop :=
  ∃ s : ZMod n, ∃ p : ℕ,
    p ≤ n ∧
    (∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ p → a (step s i) ≤ a (step s j)) ∧
    (∀ ⦃i j : ℕ⦄, p ≤ i → i ≤ j → j ≤ n → a (step s j) ≤ a (step s i))

/-- The definition to use as the output of a raw `List`/`rotate` parser saying
that the consecutive difference signs have at most two alternations.

In downstream code, prove this from a rotated list of signs: one `List.Chain`
proof for the nonnegative run, one `List.Chain` proof for the nonpositive run,
then fold chains into the transitive inequalities in `CyclicallyUnimodal`. -/
abbrev DiffSignsAtMostTwoAlternations {n : ℕ} [NeZero n]
    (a : ZMod n → ℝ) : Prop :=
  CyclicallyUnimodal a

/-- Parser helper: after converting the raw sign-alternation/list statement to
the block-structure predicate, this is just projection. -/
theorem cyclicallyUnimodal_of_diffSignsAtMostTwoAlternations
    {n : ℕ} [NeZero n] {a : ZMod n → ℝ}
    (h : DiffSignsAtMostTwoAlternations a) :
    CyclicallyUnimodal a :=
  h

private lemma prefix_cut_of_mono_of_last_not
    {b : ℕ → ℝ} {p : ℕ} {c : ℝ}
    (hmono : ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ p → b i ≤ b j)
    (hlast : ¬ b p < c) :
    ∃ lo : ℕ, lo ≤ p ∧ ∀ t : ℕ, t ≤ p → (b t < c ↔ t < lo) := by
  classical
  let q : ℕ → Prop := fun t => t ≤ p ∧ ¬ b t < c
  have hq : ∃ t : ℕ, q t := ⟨p, le_rfl, hlast⟩
  let lo : ℕ := Nat.find hq
  have hloq : q lo := Nat.find_spec hq
  refine ⟨lo, hloq.1, ?_⟩
  intro t ht
  constructor
  · intro htlt
    by_contra hnot
    have hlo_le_t : lo ≤ t := le_of_not_gt hnot
    have hb_lo_lt : b lo < c := lt_of_le_of_lt (hmono hlo_le_t ht) htlt
    exact hloq.2 hb_lo_lt
  · intro ht_lo
    by_contra hnot_lt
    have hfind_le : lo ≤ t := Nat.find_min hq ⟨ht, hnot_lt⟩
    exact (Nat.not_le_of_gt ht_lo) hfind_le

private lemma suffix_cut_of_antitone_of_last
    {b : ℕ → ℝ} {p n : ℕ} {c : ℝ}
    (hp : p ≤ n)
    (hanti : ∀ ⦃i j : ℕ⦄, p ≤ i → i ≤ j → j ≤ n → b j ≤ b i)
    (hlast : b n < c) :
    ∃ hi : ℕ, p ≤ hi ∧ hi ≤ n ∧
      ∀ t : ℕ, p ≤ t → t ≤ n → (b t < c ↔ hi ≤ t) := by
  classical
  let q : ℕ → Prop := fun t => p ≤ t ∧ t ≤ n ∧ b t < c
  have hq : ∃ t : ℕ, q t := ⟨n, hp, le_rfl, hlast⟩
  let hi : ℕ := Nat.find hq
  have hhiq : q hi := Nat.find_spec hq
  refine ⟨hi, hhiq.1, hhiq.2.1, ?_⟩
  intro t hpt htn
  constructor
  · intro htlt
    exact Nat.find_min hq ⟨hpt, htn, htlt⟩
  · intro hhi_t
    exact lt_of_le_of_lt (hanti hhiq.1 hhi_t htn) hhiq.2.2

/-- Main bridge: every strict sublevel set of a cyclically unimodal cyclic
sequence is a contiguous cyclic interval. -/
theorem sublevel_isCyclicInterval_of_cyclicallyUnimodal
    {n : ℕ} [NeZero n] (a : ZMod n → ℝ) (c : ℝ)
    (ha : CyclicallyUnimodal a) :
    IsCyclicInterval (fun i : ZMod n => a i < c) := by
  classical
  rcases ha with ⟨s, p, hp, hinc, hdec⟩
  let b : ℕ → ℝ := fun t => a (step s t)
  have hperiod : b n = b 0 := by
    simp [b, step, ZMod.natCast_self]
  have hmono : ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ p → b i ≤ b j := by
    intro i j hij hjp
    simpa [b] using hinc (i := i) (j := j) hij hjp
  have hanti : ∀ ⦃i j : ℕ⦄, p ≤ i → i ≤ j → j ≤ n → b j ≤ b i := by
    intro i j hpi hij hjn
    simpa [b] using hdec (i := i) (j := j) hpi hij hjn

  by_cases hSome : ∃ t : ℕ, t < n ∧ b t < c
  · by_cases hAll : ∀ t : ℕ, t < n → b t < c
    · refine ⟨s, n, le_rfl, ?_⟩
      intro t ht
      constructor
      · intro _
        exact ht
      · intro _
        simpa [b] using hAll t ht
    · have hSomeFalse : ∃ t : ℕ, t < n ∧ ¬ b t < c := by
        by_contra hNoFalse
        apply hAll
        intro t ht
        by_contra htlt
        exact hNoFalse ⟨t, ht, htlt⟩
      rcases hSome with ⟨tTrue, htTrue, hTrue⟩
      rcases hSomeFalse with ⟨tFalse, htFalse, hFalse⟩

      -- The cyclic start is a minimum, so if anything is below `c`, then
      -- the start itself is below `c`.
      have h0 : b 0 < c := by
        have hb0_le : b 0 ≤ b tTrue := by
          by_cases htlep : tTrue ≤ p
          · simpa [b] using hinc (i := 0) (j := tTrue) (Nat.zero_le tTrue) htlep
          · have hpt : p ≤ tTrue := Nat.le_of_not_ge htlep
            have htn : tTrue ≤ n := Nat.le_of_lt htTrue
            have hbn_le : b n ≤ b tTrue := by
              simpa [b] using hdec (i := tTrue) (j := n) hpt htn le_rfl
            simpa [hperiod] using hbn_le
        exact lt_of_le_of_lt hb0_le hTrue

      -- The peak is not below `c`, because some point is not below `c` and
      -- every point lies below the peak in the bitonic order.
      have hPeakNot : ¬ b p < c := by
        have hb_false_le_peak : b tFalse ≤ b p := by
          by_cases htfp : tFalse ≤ p
          · simpa [b] using hinc (i := tFalse) (j := p) htfp le_rfl
          · have hptf : p ≤ tFalse := Nat.le_of_not_ge htfp
            have htfn : tFalse ≤ n := Nat.le_of_lt htFalse
            simpa [b] using hdec (i := p) (j := tFalse) le_rfl hptf htfn
        have hc_le_false : c ≤ b tFalse := le_of_not_gt hFalse
        exact not_lt_of_ge (le_trans hc_le_false hb_false_le_peak)

      rcases prefix_cut_of_mono_of_last_not (b := b) (p := p) (c := c)
          hmono hPeakNot with ⟨lo, hlo_le_p, hlo_prop⟩
      have hn_last : b n < c := by
        simpa [hperiod] using h0
      rcases suffix_cut_of_antitone_of_last (b := b) (p := p) (n := n) (c := c)
          hp hanti hn_last with ⟨hi, hp_le_hi, hhi_le_n, hhi_prop⟩

      have hlo_pos : 0 < lo := by
        exact (hlo_prop 0 (Nat.zero_le p)).mp h0
      have hp_lt_hi : p < hi := by
        have hnot_hi_le_p : ¬ hi ≤ p := by
          intro hle
          exact hPeakNot ((hhi_prop p hp le_rfl).mpr hle)
        exact lt_of_le_of_ne hp_le_hi (by
          intro hEq
          apply hnot_hi_le_p
          simpa [hEq])
      have hlo_le_hi : lo ≤ hi := le_trans hlo_le_p hp_le_hi

      -- Combine the two one-sided threshold cuts into a single two-cut
      -- description in the original enumeration from `s`.
      have hTwoCut : ∀ r : ℕ, r < n →
          (b r < c ↔ r < lo ∨ hi ≤ r) := by
        intro r hrn
        by_cases hrp : r ≤ p
        · have hpre := hlo_prop r hrp
          constructor
          · intro hr
            exact Or.inl (hpre.mp hr)
          · intro h
            cases h with
            | inl hrl => exact hpre.mpr hrl
            | inr hhir =>
                have hi_le_p : hi ≤ p := le_trans hhir hrp
                exact False.elim ((Nat.not_le_of_gt hp_lt_hi) hi_le_p)
        · have hpr : p ≤ r := Nat.le_of_not_ge hrp
          have hsuf := hhi_prop r hpr (Nat.le_of_lt hrn)
          constructor
          · intro hr
            exact Or.inr (hsuf.mp hr)
          · intro h
            cases h with
            | inl hrlo =>
                have hlo_le_r : lo ≤ r := le_trans hlo_le_p hpr
                exact False.elim ((Nat.not_lt_of_ge hlo_le_r) hrlo)
            | inr hhir => exact hsuf.mpr hhir

      -- Rotate the cyclic interval so it starts at the descending-side cut `hi`.
      let start : ZMod n := step s hi
      let k : ℕ := n - hi + lo
      have hk : k ≤ n := by
        dsimp [k]
        omega
      refine ⟨start, k, hk, ?_⟩
      intro t ht
      by_cases hNoWrap : hi + t < n
      · have ht_lt_n_sub_hi : t < n - hi := by omega
        have htk : t < k := by
          dsimp [k]
          omega
        have hstep : step start t = step s (hi + t) := by
          simp [start, step, Nat.cast_add, add_assoc]
        have hP : a (step start t) < c := by
          have hb : b (hi + t) < c :=
            (hTwoCut (hi + t) hNoWrap).mpr (Or.inr (by omega))
          simpa [b, hstep] using hb
        constructor
        · intro _
          exact htk
        · intro _
          exact hP
      · let r : ℕ := hi + t - n
        have hwrap : n ≤ hi + t := Nat.le_of_not_gt hNoWrap
        have hr_lt_hi : r < hi := by
          dsimp [r]
          omega
        have hr_lt_n : r < n := by
          dsimp [r]
          omega
        have hcast : ((hi + t : ℕ) : ZMod n) = (r : ZMod n) := by
          have hnat : hi + t = n + r := by
            dsimp [r]
            omega
          rw [hnat]
          simp [Nat.cast_add, ZMod.natCast_self]
        have hstep : step start t = step s r := by
          calc
            step start t = s + ((hi + t : ℕ) : ZMod n) := by
              simp [start, step, Nat.cast_add, add_assoc]
            _ = s + (r : ZMod n) := by rw [hcast]
            _ = step s r := by simp [step]
        have hP_iff : a (step start t) < c ↔ r < lo := by
          have hbase := hTwoCut r hr_lt_n
          have hnot_hi_le_r : ¬ hi ≤ r := Nat.not_le_of_gt hr_lt_hi
          constructor
          · intro hpst
            have hb : b r < c := by simpa [b, hstep] using hpst
            rcases hbase.mp hb with hrlo | hhir
            · exact hrlo
            · exact False.elim (hnot_hi_le_r hhir)
          · intro hrlo
            have hb : b r < c := hbase.mpr (Or.inl hrlo)
            simpa [b, hstep] using hb
        have htk_iff : t < k ↔ r < lo := by
          dsimp [k, r]
          omega
        constructor
        · intro hpst
          exact htk_iff.mpr (hP_iff.mp hpst)
        · intro htk
          exact hP_iff.mpr (htk_iff.mp htk)
  · refine ⟨s, 0, Nat.zero_le n, ?_⟩
    intro t ht
    constructor
    · intro htlt
      exact False.elim (hSome ⟨t, ht, by simpa [b] using htlt⟩)
    · intro ht0
      exact False.elim ((Nat.not_lt_zero t) ht0)

/-- Direct corollary with the requested name: strict sublevels of a cyclic
sequence whose difference signs have at most two alternations are cyclic
intervals. -/
theorem sublevel_isCyclicInterval_of_diffSignsAtMostTwoAlternations
    {n : ℕ} [NeZero n] (a : ZMod n → ℝ) (c : ℝ)
    (ha : DiffSignsAtMostTwoAlternations a) :
    IsCyclicInterval (fun i : ZMod n => a i < c) :=
  sublevel_isCyclicInterval_of_cyclicallyUnimodal a c
    (cyclicallyUnimodal_of_diffSignsAtMostTwoAlternations ha)

end Cauchy.Ch13.CyclicUnimodal
```

## How to connect this to a raw sorted list / `List.rotate` statement

For the list-level statement, I would not put `List.rotate` into the geometric bridge theorem.  I would prove a separate parser lemma whose target is `DiffSignsAtMostTwoAlternations` above.

A good shape is:

```lean
-- Schematic outer adapter; keep it separate from the kernel above.
theorem diffSignsAtMostTwoAlternations_of_rotated_chain
    {n : ℕ} [NeZero n]
    (a : ZMod n → ℝ)
    (s : ZMod n) (p : ℕ) (hp : p ≤ n)
    -- first run: all consecutive differences are nonnegative
    (hup : ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ p →
      a (step s i) ≤ a (step s j))
    -- second run: all consecutive differences are nonpositive
    (hdown : ∀ ⦃i j : ℕ⦄, p ≤ i → i ≤ j → j ≤ n →
      a (step s j) ≤ a (step s i)) :
    DiffSignsAtMostTwoAlternations a := by
  exact ⟨s, p, hp, hup, hdown⟩
```

If the data really arrives as a `List` of signed consecutive differences, prove `hup` and `hdown` from `List.Chain` over the two rotated runs.  The parser is finite-list plumbing; the theorem above is the part that should be reused in convex-geometry code.
