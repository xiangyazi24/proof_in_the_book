# ANSWER_02_agy — Ch19 FTA: two of three are free; only local-decrease needs real work

## Good news: Mathlib already has #1 and #2 as separable building blocks

Both live in `Mathlib/Topology/Algebra/Polynomial.lean`:

```
-- line 132
theorem tendsto_norm_atTop (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α → R}
    (hz : Tendsto (fun x => ‖z x‖) l atTop) :
    Tendsto (fun x => ‖p.eval (z x)‖) l atTop

-- line 136
theorem exists_forall_norm_le [ProperSpace R] (p : R[X]) :
    ∃ x, ∀ y, ‖p.eval x‖ ≤ ‖p.eval y‖
```

For `R = ℂ`, both fire immediately:
- `ℂ` is a `ProperSpace` (closed bounded sets are compact).
- `0 < p.degree` follows from `1 ≤ p.natDegree`.

So your `poly_norm_tendsto_top` and `exists_min_norm` are essentially **one-liners**:

```lean
lemma exists_min_norm (p : ℂ[X]) :
    ∃ z₀ : ℂ, ∀ z : ℂ, ‖p.eval z₀‖ ≤ ‖p.eval z‖ :=
  Polynomial.exists_forall_norm_le p

lemma poly_norm_tendsto_top (p : ℂ[X]) (hp : 1 ≤ p.natDegree) :
    Tendsto (fun z : ℂ => ‖p.eval z‖) (Filter.cocompact ℂ) Filter.atTop := by
  apply Polynomial.tendsto_norm_atTop p (by exact_mod_cast (Polynomial.natDegree_pos_iff_degree_pos.mp hp))
  -- ‖z‖ → ∞ on cocompact ℂ
  exact Filter.tendsto_norm_cocompact_atTop
```

**Are these "cite-and-go"?** No, they're building blocks. `exists_forall_norm_le` only asserts a
global minimum **exists** — it does NOT claim `‖p.eval z₀‖ = 0`. Reaching `‖p.eval z₀‖ = 0` (the
FTA conclusion) requires your local-decrease + contradiction step, which IS the book's argument.
The min-existence is just topology (continuity + properness), independent of the algebraic-
closedness machinery. Using it is on the same footing as using `integral_sin` in Ch25 or `niven`
where we had to wrap with the actual book argument.

## The real work: `complex_poly_local_norm_decrease`

This is where you must NOT use `Complex.exists_root`. The current proof in the file IS that
shortcut and needs full replacement. The book's argument:

```
r(w) = a + c · w^m + R(w)        where R(w) = ∑_{k>m} a_k · w^k
Choose ζ with ζ^m = -a/c         (exists by exists_complex_nth_root, already in your file)
Set w = t·ζ for small t > 0:
  c · w^m = c · t^m · ζ^m = -a · t^m
  a + c · w^m = a · (1 - t^m)
  r(t·ζ) = a · (1 - t^m) + R(t·ζ)
Bound ‖R(t·ζ)‖ ≤ M · t^{m+1}     for t ≤ 1, where M = ∑_{k>m} ‖a_k‖ · ‖ζ‖^k
Then ‖r(t·ζ)‖ ≤ ‖a‖ · (1 - t^m) + M · t^{m+1}
            = ‖a‖ - t^m · (‖a‖ - M · t)
For t < min(1, ‖a‖/(2M)) (if M > 0; else any t < 1 works):
  ‖a‖ - M · t > ‖a‖/2 > 0
  ‖r(t·ζ)‖ ≤ ‖a‖ - t^m · ‖a‖/2 < ‖a‖
Done.
```

## Lean skeleton for `complex_poly_local_norm_decrease`

```lean
theorem complex_poly_local_norm_decrease
    (r : ℂ[X]) (a c : ℂ) (m : ℕ)
    (hm0 : 0 < m)
    (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hconst : r.coeff 0 = a)
    (hbelow : ∀ k, 0 < k → k < m → r.coeff k = 0)
    (hm : r.coeff m = c) :
    ∃ w : ℂ, ‖r.eval w‖ < ‖a‖ := by
  classical
  -- (1) Pick ζ with ζ^m = -a/c.
  obtain ⟨ζ, hζ⟩ := exists_complex_nth_root (-a / c) m hm0
  have hcζ : c * ζ ^ m = -a := by
    rw [hζ]; field_simp
  -- (2) Bound the tail sum norm for w = t·ζ with t ∈ [0, 1].
  -- Define M := ∑_{k > m, k ≤ r.natDegree} ‖r.coeff k‖ * ‖ζ‖^k. Use Finset.sum.
  set M : ℝ := ∑ k ∈ Finset.range (r.natDegree + 1), if k > m then ‖r.coeff k‖ * ‖ζ‖^k else 0
    with hM_def
  have hM_nonneg : 0 ≤ M := by
    apply Finset.sum_nonneg
    intro k _; split_ifs <;> positivity
  -- (3) For w = t·ζ with 0 ≤ t ≤ 1, prove the tail bound:
  --   ‖∑_{k > m} r.coeff k · (t·ζ)^k‖ ≤ M · t^(m+1)
  have h_tail_bound : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖∑ k ∈ Finset.range (r.natDegree + 1),
         (if k > m then r.coeff k * (↑t * ζ)^k else 0)‖
      ≤ M * t^(m+1) := by
    intro t ht0 ht1
    calc ‖_‖
        ≤ ∑ k ∈ Finset.range (r.natDegree + 1),
            ‖if k > m then r.coeff k * (↑t * ζ)^k else 0‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range (r.natDegree + 1),
            (if k > m then ‖r.coeff k‖ * ‖ζ‖^k * t^(m+1) else 0) := by
            apply Finset.sum_le_sum
            intro k _
            split_ifs with hk
            · rw [norm_mul, norm_pow, mul_pow]
              simp [Complex.norm_real, abs_of_nonneg ht0]
              -- ‖r.coeff k‖ * (t^k * ‖ζ‖^k) ≤ ‖r.coeff k‖ * ‖ζ‖^k * t^(m+1)
              -- since t^k ≤ t^(m+1) when t ≤ 1 and k ≥ m+1
              have hk_ge : m + 1 ≤ k := hk
              have h_t_pow : t^k ≤ t^(m+1) := by
                exact pow_le_pow_of_le_one ht0 ht1 hk_ge
              nlinarith [norm_nonneg (r.coeff k), pow_nonneg (norm_nonneg ζ) k]
            · simp
      _ = (∑ k ∈ Finset.range (r.natDegree + 1),
            if k > m then ‖r.coeff k‖ * ‖ζ‖^k else 0) * t^(m+1) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _; split_ifs <;> ring
      _ = M * t^(m+1) := by rw [← hM_def]
  -- (4) Choose t small. If M = 0: any t ∈ (0, 1) works since tail = 0.
  --     Else: pick t = min(1/2, ‖a‖/(2*M)) — both positive, both ≤ 1.
  -- For brevity, just pick t = min(1/2, ‖a‖/(2*(M + 1))) which avoids the M = 0 case split.
  set t : ℝ := min (1/2) (‖a‖ / (2 * (M + 1))) with ht_def
  have ht_pos : 0 < t := by
    apply lt_min; · norm_num
    · apply div_pos (norm_pos_iff.mpr ha)
      positivity
  have ht_le_half : t ≤ 1/2 := min_le_left _ _
  have ht_le_one : t ≤ 1 := le_trans ht_le_half (by norm_num)
  have ht_le_bound : t ≤ ‖a‖ / (2 * (M + 1)) := min_le_right _ _
  -- (5) Compute r.eval (t·ζ) = a · (1 - t^m) + (tail).
  --     ‖r.eval (t·ζ)‖ ≤ ‖a‖ · (1 - t^m) + M · t^(m+1)
  --                    = ‖a‖ - t^m · (‖a‖ - M · t)
  --     ≥ ‖a‖ - t^m · ‖a‖/2  (since M · t ≤ M · ‖a‖/(2*(M+1)) ≤ ‖a‖/2)
  --     < ‖a‖.
  refine ⟨(t : ℂ) * ζ, ?_⟩
  -- Expand r.eval as Finset.sum over coefficients.
  have h_eval :
      r.eval ((t : ℂ) * ζ) =
        a + ∑ k ∈ Finset.range (r.natDegree + 1),
              (if k > m then r.coeff k * ((t : ℂ) * ζ)^k else 0) := by
    -- Use `Polynomial.eval_eq_sum_range` and split off k = 0 and k = m.
    sorry  -- ← only structural sorry; mechanical Polynomial.eval_eq_sum_range manipulation
  rw [h_eval]
  -- triangle inequality + bound
  calc ‖a + _‖
      ≤ ‖a‖ * (1 - t^m) + M * t^(m+1) := by
          -- a contributes ‖a‖ but multiplied by (1 - t^m) after combining with the c·w^m term…
          -- HOLD: actually the (1 - t^m) factor comes from a + c·w^m, not from a alone.
          -- The split I wrote above puts c·w^m into the "tail" sum, which is wrong.
          -- Correct: split out k = m TOO from the tail; the k = m term equals c · t^m · ζ^m = -a · t^m,
          -- combining with a to give a · (1 - t^m).
          sorry
      _ < ‖a‖ := by
          have ht_m_pos : 0 < t^m := pow_pos ht_pos m
          have h_decrease : t^m * (‖a‖ / 2) > 0 := by positivity
          have h_M_t : M * t ≤ ‖a‖ / 2 := by
            have : M * t ≤ M * (‖a‖ / (2 * (M + 1))) :=
              mul_le_mul_of_nonneg_left ht_le_bound hM_nonneg
            calc M * t
                ≤ M * (‖a‖ / (2 * (M + 1))) := this
              _ = (M / (M + 1)) * (‖a‖ / 2) := by field_simp; ring
              _ ≤ 1 * (‖a‖ / 2) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  exact div_le_one_of_le (by linarith) (by linarith)
              _ = ‖a‖ / 2 := one_mul _
          nlinarith [norm_nonneg a, ht_m_pos]
```

## What I left as `sorry` and why

Two `sorry`s in the skeleton:

1. **`h_eval` expansion** — pure mechanical: `Polynomial.eval_eq_sum_range` expands
   `r.eval w = ∑ k ∈ range (natDegree+1), r.coeff k * w^k`. Then split off `k = 0` (gives `a`
   by `hconst`), the `k ∈ (0, m)` range (all zero by `hbelow`), and the `k = m` term (gives
   `c · w^m = -a · t^m` by `hcζ`). The `k > m` terms become the tail. **Re-derive by hand;
   don't trust my exact form above — I bundled k = m into the tail, which is wrong.**

2. **Triangle inequality combining** — needs to fold `k = m` together with `a` before invoking
   triangle. The correct decomposition:
   ```
   r.eval (tζ) = a + c · (tζ)^m + (sum over k > m)
              = a · (1 - t^m) + (sum over k > m)
   ‖r.eval (tζ)‖ ≤ ‖a‖ · (1 - t^m) + ‖sum‖
                ≤ ‖a‖ · (1 - t^m) + M · t^(m+1)
                = ‖a‖ - t^m · ‖a‖ + M · t^(m+1)
                = ‖a‖ - t^m · (‖a‖ - M · t)
                < ‖a‖              (since ‖a‖ - M·t > 0 by t small)
   ```
   You'll need to redo the `h_eval` / `h_tail_bound` split with `k = m` cleanly separated.

3. **Sign**: `c · w^m = c · t^m · ζ^m = c · t^m · (-a/c) = -a · t^m`. So `a + c · w^m = a · (1 - t^m)`.
   The `(1 - t^m)` is real, but `a` is complex; the norm is `‖a‖ · |1 - t^m| = ‖a‖ · (1 - t^m)`
   since `1 - t^m > 0` (because `t < 1` and `m ≥ 1`).

## Recommendation

1. Implement `exists_min_norm` and `poly_norm_tendsto_top` (one-liners) first. Build clean.
2. Tackle `complex_poly_local_norm_decrease` using the skeleton above, but DO YOUR OWN
   decomposition of `r.eval (tζ)` to keep `k = m` separate from the tail. The skeleton I wrote
   has bugs in that split.
3. The `M / (M+1) ≤ 1` trick lets you avoid case-splitting on `M = 0`.
4. If `nlinarith` can't close the final inequality, fall back to manual `calc` with
   `‖a‖ - t^m · (‖a‖/2) < ‖a‖` since `t^m · (‖a‖/2) > 0`.
5. Wire `chapter19` to call `fta_minimum_modulus_contradiction` (already in the file), using
   `exists_min_norm` + the local-decrease.

Remote build at each step. The `Polynomial.eval_eq_sum_range` expansion is the most fragile
part — if it doesn't simplify cleanly, file a follow-up question; that piece is local enough
that I can give exact tactics if the auto-tactics give up.

Go.
