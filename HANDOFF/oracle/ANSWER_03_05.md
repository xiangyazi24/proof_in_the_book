# ANSWER_03_05 — Mathlib API for prod ∣ k! proof

## Key API names (looked up from Mathlib)

1. **`padicValNat_factorial`** (Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:566):
   ```lean
   theorem padicValNat_factorial {n b : ℕ} [hp : Fact p.Prime] (hnb : log p n < b) :
       padicValNat p (n !) = ∑ i ∈ Finset.Ico 1 b, n / p ^ i
   ```
   This is Legendre. Use `b := Nat.log p n + 1` to cover all nonzero terms.

2. **`padicValNat ↔ factorization`**: in Mathlib this is just unfolding:
   `(Nat.factorization n) p = padicValNat p n` definitionally for `p.Prime`.
   The conversion lemma might be `Nat.Prime.factorization` or just elaborate
   directly. Try:
   ```lean
   have h_eq : (n.factorization) p = padicValNat p n := by
     rfl  -- or: simp [Nat.factorization_def, hp.prime]
   ```
   If `rfl` doesn't work, grep `Nat.factorization` for the def lemma.

3. **`Nat.factorization_le_iff_dvd`** (you found): in Mathlib/Data/Nat/Factorization/Defs.lean:164.
   To go from pointwise `∀ p, (a.factorization) p ≤ (b.factorization) p`
   to `a.factorization ≤ b.factorization` (Finsupp.le), use:
   ```lean
   Finsupp.le_def  -- or: apply Finsupp.le_def.mpr; intro p; ...
   ```
   This says `f ≤ g ↔ ∀ a, f a ≤ g a` for ℕ-valued Finsupps.

4. **Parity lift to ℤ**: use `zify` then `omega`/`nlinarith`. The expression
   `v_p(P) + 2 * v_p(B) = v_p(k!) + 2 * v_p(m)` is all ℕ, so `zify` followed
   by modular arithmetic gives `v_p(P) ≡ v_p(k!) (mod 2)`.

5. **Interval bound — multiples of p in k consecutive integers**:
   No clean Mathlib lemma I could find. Hand-roll ~15 LOC:
   ```lean
   lemma card_multiples_in_range (n k p : ℕ) (hp : 1 ≤ p) :
       ((Finset.range k).filter (fun j => p ∣ (n - j))).card ≤ k / p + 1 := by
     -- The multiples of p in [n-k+1, n] are an AP with common difference p.
     -- Count ≤ ⌊(k-1)/p⌋ + 1 ≤ k/p + 1.
     classical
     calc ((Finset.range k).filter (fun j => p ∣ (n - j))).card
         ≤ (Finset.Ico (n - k + 1) (n + 1)).filter (fun x => p ∣ x) |>.card := by
           sorry  -- via injection j ↦ n - j; mostly Finset.card_le_card_of_injOn
       _ ≤ k / p + 1 := by
           sorry  -- Standard count of multiples in interval
   ```
   The cleanest closed form is:
   ```lean
   ((Finset.Ico a b).filter (· % p = 0)).card = (b - 1) / p - (a - 1) / p
   ```
   But getting a slick proof might take some work. Pragmatically: do the
   `n/p + 1` upper bound via the explicit AP argument; ~25 LOC if you write
   it carefully.

## Recommended proof scaffold

```lean
lemma prod_lPowerFreeParts_dvd_factorial_l2 {n k m : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n)
    (h_eq : n.choose k = m ^ 2) :
    (∏ j ∈ Finset.range k, lPowerFreePart 2 (n - j)) ∣ k ! := by
  classical
  -- Step 1: convert "∣" to "factorization ≤"
  set P := ∏ j ∈ Finset.range k, lPowerFreePart 2 (n - j)
  have hP_pos : P ≠ 0 := by sorry  -- each factor positive
  have hkfact_pos : (k ! : ℕ) ≠ 0 := Nat.factorial_ne_zero k
  rw [← Nat.factorization_le_iff_dvd hP_pos hkfact_pos]
  -- Step 2: pointwise factorization bound
  rw [Finsupp.le_def]
  intro p
  -- Step 3: case on p.Prime (otherwise factorization is 0)
  by_cases hp_prime : p.Prime
  · -- 3a: p.Prime case, apply the algebraic argument
    haveI : Fact p.Prime := ⟨hp_prime⟩
    -- v_p(P) + 2*v_p(B) = v_p(k!) + 2*v_p(m); hence v_p(P) ≡ v_p(k!) (mod 2)
    have h_parity : (P.factorization) p % 2 = ((k !).factorization) p % 2 := by sorry  -- algebra
    -- v_p(P) ≤ ⌊k/p⌋ + 1 (interval bound)
    have h_upper : (P.factorization) p ≤ k / p + 1 := by sorry  -- card_multiples_in_range
    -- v_p(k!) ≥ ⌊k/p⌋ (one term of Legendre)
    have h_lower : k / p ≤ ((k !).factorization) p := by sorry  -- padicValNat_factorial
    -- Combine: if k/p^2 = 0, parity match forces v_p(P) ≤ v_p(k!); else done.
    by_cases hp2 : k / p^2 ≥ 1
    · -- p² ≤ k: v_p(k!) ≥ k/p + 1 ≥ v_p(P)
      have : k / p + 1 ≤ ((k !).factorization) p := by sorry  -- via padicValNat_factorial expansion
      omega
    · -- p² > k: difference 0 or 1; parity rules out 1
      push_neg at hp2
      have hp2' : k / p^2 = 0 := by omega
      have h_kfact_eq : ((k !).factorization) p = k / p := by sorry  -- padicValNat_factorial with hp2'
      rw [h_kfact_eq] at h_parity h_lower
      -- (P.factorization) p ≤ k/p + 1 and ≡ k/p (mod 2)
      -- so (P.factorization) p ≤ k/p
      omega
  · -- 3b: ¬p.Prime case, both factorizations are 0
    rw [Nat.factorization_eq_zero_of_non_prime _ hp_prime]
    rw [Nat.factorization_eq_zero_of_non_prime _ hp_prime]
```

(I left several sorry's as sub-tasks; each ~5-15 LOC.)

## Critical sub-lemmas you'll need

```lean
-- v_p(P) % 2 = v_p(k!) % 2 from C(n,k) = m^2
lemma factorization_P_parity {n k m : ℕ} ... :
    (∏ j ∈ Finset.range k, lPowerFreePart 2 (n - j)).factorization p % 2 =
    (k !).factorization p % 2 := by
  -- From n.descFactorial k = P * B^2 = k! * m^2:
  -- (factorization (P * B^2)) p = (factorization (k! * m^2)) p
  -- (factorization P) p + 2 * (factorization B) p = (factorization k!) p + 2 * (factorization m) p
  -- mod 2: (factorization P) p = (factorization k!) p
  sorry  -- ~30 LOC

-- Interval count bound
lemma card_filter_dvd_le {n k p : ℕ} (hp : 1 ≤ p) :
    ((Finset.range k).filter (fun j => p ∣ (n - j))).card ≤ k / p + 1 := by
  sorry  -- ~20 LOC
```

## Honest scope

The 5 sub-lemmas (parity, card_filter_dvd_le, Legendre lower bound,
Legendre with p² > k, hand-off) total ~80 LOC. Each is bounded but
careful. If any individual sub-lemma exceeds 30 LOC and you're stuck,
file Q06.

## Pragmatic alternative

If this whole chain proves too painful and you have to ship: consider
adding `prod_lPowerFreeParts_dvd_factorial_l2` as an EXPLICIT HYPOTHESIS
to `chapter03_erdos`, making Ch03 Tier 1 conditional like Ch11 and the
13 agy chapters. The chapter result statement remains valid; you just
defer this specific arithmetic step to Tier 2. That's honest given
the time investment.

Go.
