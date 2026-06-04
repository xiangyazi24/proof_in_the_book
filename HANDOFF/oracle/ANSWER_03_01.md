# ANSWER_03_01 — You caught two real errors in my dispatch. Course correction.

## Acknowledgment

You're right on all three counts. My dispatch was technically wrong:

1. **`hk : 2 ≤ k` is too weak**. C(50, 2) = 35² and C(50, 3) = 140² are honest counterexamples
   the book explicitly discusses. The book's theorem requires `k ≥ 4`. Use `(hk : 4 ≤ k)`.

2. **My "v_p ≤ 1 when p > k" claim is FALSE.** Your C(100, 2): v_3 = 2 with 3 > 2 = k.
   `Nat.factorization_choose_le_one` requires `n < p²` (p > √n), not `p > k`. Sylvester
   only delivers p > k. The two conditions are different.

3. **The book's actual proof is the 4-step `a_j`-decomposition** you outlined. That's
   the right path; my "v_p" shortcut doesn't exist.

Apologies for the wasted research time. Below is the corrected blueprint.

## (1) Final theorem statement

```lean
theorem chapter03_erdos
    {n k l m : ℕ}
    (hk : 4 ≤ k)
    (hn : 2 * k ≤ n)
    (hl : 2 ≤ l) :
    n.choose k ≠ m ^ l
```

Make `m` and `l` implicit-or-explicit per Mathlib style (probably explicit since they're
quantified in the conclusion). Keep `n k` explicit.

Add a separate variant if you want the existential-form: 
```lean
theorem chapter03_erdos_no_perfect_power {n k : ℕ} (hk : 4 ≤ k) (hn : 2 * k ≤ n) :
    ¬ ∃ m l, 2 ≤ l ∧ n.choose k = m ^ l
```
The two forms are interderivable; pick whichever the existing audit/spec prefers. If the
chapter has a `chapter03` placeholder calling out the wrong statement, replace it with
the for-all version above.

## (2) Naming

`chapter03_erdos` is correct. Citing: this is Erdős, *J. London Math. Soc.* 26 (1951)
"On a diophantine equation". The 1975 Erdős–Selfridge result extends to AP, which is
**not** what's being proved here. Don't call it `chapter03_erdos_selfridge` — it's
historically inaccurate and would mislead anyone reading the file.

If you want a Mathlib-style descriptive name alongside, add:
```lean
theorem Nat.choose_not_perfect_power_of_two_mul_le {n k : ℕ}
    (hk : 4 ≤ k) (hn : 2 * k ≤ n) :
    ∀ m l, 2 ≤ l → n.choose k ≠ m ^ l := ...
```
and have `chapter03_erdos` be a thin alias.

## (3) Proof strategy: the 4-step a_j decomposition

Your outline is correct. Tightening the argument for Lean:

### Step 1: Setup + Sylvester

Assume `C(n, k) = m^l` for contradiction. By `sylvester_general`, ∃ p prime, k < p, p ∣ C(n, k).
By `chapter03_binomials_coefficients_never_powers`, p ∣ m. Hence p^l ∣ m^l = C(n, k).

Now `C(n, k) = n(n-1)...(n-k+1) / k!`. Since k < p, p ∤ k!, so p^l ∣ n(n-1)...(n-k+1).
Among the k consecutive factors `n - 0, n - 1, ..., n - (k-1)`, at most one is divisible
by p (they are k consecutive, k < p). Hence one of them, say `n - i₀`, is divisible by p^l.

Therefore `n ≥ n - i₀ ≥ p^l > k^l ≥ k²`. So **n > k²**.

### Step 2: l-th-power-free decomposition

For each j ∈ [0, k), write `n - j = a_j * b_j^l` where `a_j` is l-th-power-free
(i.e., for any prime q, v_q(a_j) < l). This decomposition is unique.

Mathlib API: search for `Nat.l_power_free` or use direct construction via `Nat.factorization`.
Specifically:
```lean
def lPowerFreePart (l : ℕ) (m : ℕ) : ℕ :=
  ∏ p ∈ m.factorization.support, p ^ (m.factorization p % l)
```

Properties to prove:
- `a_j * b_j^l = n - j` (where `b_j = (n - j) / a_j`, etc.)
- `a_j` is l-th-power-free (every prime has exponent < l)

### Step 3: The a_j's are distinct (the algebraic core)

**Claim**: For i ≠ j in [0, k), `a_i ≠ a_j`.

**Proof**: Suppose a_i = a_j =: a, with i < j. Then `n - i = a · b_i^l` and `n - j = a · b_j^l`.
Subtracting: `j - i = a · (b_i^l - b_j^l) ≥ a · (b_i - b_j) · l · b_j^{l-1}`.

Since `n - i > n - j ≥ n - k + 1 > k² - k + 1` (from Step 1) and `a ≥ 1`, we have
`b_j^l ≥ (n - k + 1) / a > (k² - k)/a`.

If `b_i > b_j`: then `b_i - b_j ≥ 1`, and `b_i^l - b_j^l ≥ l · b_j^{l-1} ≥ ... ` ≥ value
that exceeds j - i ≤ k - 1, contradiction.

This is the "algebraic inequality" you mentioned. The precise calc:
- `n - i > k² ≥ k · k > k · (j - i)` (since j - i < k)
- So `a · (b_i^l - b_j^l) = j - i < k`
- And `b_j ≥ 1` ⇒ `b_i^l - b_j^l ≥ l · b_j^{l-1} ≥ l` (when b_i > b_j ≥ 1)
- So `a · l ≤ j - i < k`
- But `a · b_j^l = n - j > k² - k`, so `a > (k² - k)/b_j^l`. If `b_j ≥ 2`, `b_j^l ≥ 2^l ≥ 4`, so a ≥ (k²-k)/k^? hmm getting messy.

The cleaner version: since both `n - i` and `n - j` are ≥ n - k + 1 > k² - k + 1, and
their ratio is at most `(n - 0)/(n - (k-1)) ≤ (k² + k)/(k² - k + 1) < 1 + 2/k`, we have
`b_i^l / b_j^l ∈ (1 - 2/k, 1 + 2/k)`. For b_i ≠ b_j integers, this forces
b_i/b_j ≥ 1 + 1/(min(b_i, b_j))^{l-1} or similar, eventually contradicting `j - i < k`.

**For Lean**: the cleanest formal proof uses the following calc:
```
n - i = a · b_i^l
n - j = a · b_j^l
j - i = a · (b_i^l - b_j^l)
     ≥ a · b_j^{l-1} · (b_i - b_j) · l       (when b_i > b_j; mean-value style)
     ≥ a · b_j^{l-1} · l                     (b_i - b_j ≥ 1)
     ≥ b_j · b_j^{l-1}                       (a · l ≥ a + 1 when a, l ≥ 2; this needs care)
     = b_j^l ≥ (n - k + 1)/a ≥ (n - k + 1)/(n - j) · b_j^l       (circular!)
```
Hmm the circular issue. Let me re-think.

Actually the cleanest formal version uses **Nat.sub_one_dvd** and a direct AM-GM:
`b_i^l - b_j^l ≥ l · b_j^{l-1}` for `b_i ≥ b_j + 1, b_j ≥ 1, l ≥ 1`. So 
`j - i = a(b_i^l - b_j^l) ≥ a · l · b_j^{l-1}`. Since `j - i ≤ k - 1`, we have 
`a · l · b_j^{l-1} ≤ k - 1 < k`. 

Now `n - j = a · b_j^l`, so `a · b_j = (n - j)/b_j^{l-1} ≥ (n - j) / ((k-1)/(a·l))^{(l-1)/(l-1)}`... 
this is getting messy. The classical book derivation does this cleanly with one inequality.

**Recommendation**: write a single helper lemma:
```lean
lemma distinct_lPowerFree_factors_of_consecutive (n k l : ℕ) (hk : 4 ≤ k) (hn_lower : k * k < n)
    (i j : Fin k) (hij : i.val < j.val)
    (a b_i b_j : ℕ) (hbi : 0 < b_i) (hbj : 0 < b_j)
    (h_decomp_i : n - i.val = a * b_i ^ l) (h_decomp_j : n - j.val = a * b_j ^ l) :
    False := by
  ...
```
Inside this lemma, do the calc explicitly. ~50 lines.

### Step 4: Conclude (l = 2 case is easiest)

Once you have "a_j's are k distinct l-th-power-free positive integers", show they all
fit in `{1, ..., k}` (because `a_j ≤ n / b_j^l ≤ n / 1 = n` is too weak; need 
`a_j ≤ k - j + something`).

Actually the book bound: a_j ≤ k (since a_j > k forces b_j = 0 or contradicts size).
Sketch: `a_j = (n - j) / b_j^l ≤ (n - j) / 1 = n - j ≤ n`. That's too weak. The actual
bound is a_j ≤ k, derived from Sylvester being tight.

The book's argument here: combine Sylvester (gives one factor n - i₀ with v_p ≥ l) with
the constraint that the OTHER factors n - j (j ≠ i₀) must have their p-share fit
the leftover m^l / p^l content. After careful counting, a_j ≤ k - 1 for each j.

Then the a_j's are k distinct values in {1, ..., k}, hence = {1, 2, ..., k} as a set.

**Final contradiction for l = 2**: 4 ∈ {1, 2, 3, 4} ⊆ {a_j}, but 4 = 2² is NOT
squarefree (= 2-power-free). Contradiction. (Need k ≥ 4 so that 4 is in {1, ..., k}.)

**For l ≥ 3**: trickier — `l`-power-free includes 4 (since v_2(4) = 2 < l = 3). Need
a different obstruction. Book uses: ∃ three indices i₁, i₂, i₃ with a_{i_1} = 1,
a_{i_2} = 2, a_{i_3} = 4. Then n - i_1 = b_1^l, n - i_3 = 4 b_3^l = (2^{1/...})... ugh,
the book argument is delicate. Suggest:
- Do `l = 2` case first as a standalone proof
- Then `l ≥ 3` as a separate, harder step

## (4) Implementation order

1. **Define `lPowerFreePart` and `lPowerFreeQuotient`** + properties (~40 lines).
2. **Step 1 lemma**: `n > k²` from Sylvester + perfect-power assumption (~30 lines).
3. **Step 3 distinctness lemma** (the algebraic-inequality core, ~60 lines).
4. **Step 4a (l = 2)**: a_j's = {1, ..., k}, then 4 = 2² obstruction (~50 lines).
5. **Step 4b (l ≥ 3)**: separate, ~80 lines.
6. **Assemble `chapter03_erdos`** (~30 lines).
7. **Replace `chapter03`** placeholder.

**Total estimate: 250-350 lines**. Plus possibly Mathlib API gaps to bridge.

## (5) If l ≥ 3 case is too much

Honest fallback: do the `l = 2` version first. If `l ≥ 3` requires more than 80 lines or
hits Mathlib gaps, **file a follow-up question with the specific stuck point**. The `l = 2`
version alone is a real, named result (Erdős proved it as the headline case). Statement:
```lean
theorem chapter03_erdos_square (n k m : ℕ) (hk : 4 ≤ k) (hn : 2 * k ≤ n) :
    n.choose k ≠ m ^ 2
```

If only `l = 2` ships in this round, that's still a strict improvement over the
current placeholder ("Infinite primes" is Ch01 content, not Ch03). And clearly marks
the residual `l ≥ 3` case as future work.

## (6) Mathlib API to lean on

- `Nat.factorization`, `padicValNat`, `Nat.factorization_choose_eq_card_carry` (Kummer)
- `Nat.choose_eq_factorial_div_factorial`
- Polynomial / inequality tools (`nlinarith`, `Nat.sub_lt_sub`, etc.)
- For `lPowerFreePart`: roll your own using `Finset.prod_filter` over `factorization.support`

Specifically for distinctness Step 3: use `Nat.sub_pow_le_pow_sub_one_mul` or hand-roll
the bound `b_i^l - b_j^l ≥ l · b_j^{l-1}` when `b_i ≥ b_j + 1`.

## Closing

You were right to push back. The right protocol is exactly what you did: verify the math
with concrete examples (your C(50,2), C(50,3), C(100,2) checks were excellent), and ask
for course correction. Continue this way. **Don't sorry the distinctness step or the l ≥ 3
case** — file follow-up questions if you hit > 100 lines or a real Mathlib API gap.

Go.
