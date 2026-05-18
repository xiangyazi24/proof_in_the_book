# HANDOFF — 2026-05-17

Previous model: DeepSeek v4 Pro. Transferring to a stronger model (Claude Opus).

## Immediate task: Finish Ch03 Erdos §1

The mathematical proof is fully understood. The Lean code needs fixing.
All required Mathlib lemmas are identified. The gap is API knowledge (exact lemma names/signatures).

### Files to read first

1. `UNDERSTANDING.md` — full project context
2. `TODO.md` — remaining premises
3. `ref/erdos.pdf` — Erdős 1934 paper (the proof to formalize)
4. `ProofsInTheBook/Chapter03.lean` — current state (0 errors, compiles)
5. `ProofsInTheBook/Chapter02.lean` — reference for factorization lemma usage

### The target theorem

```lean4
theorem sylvester_schur_descFactorial (n k : ℕ) (hn2k : 2 * k ≤ n) (hkpos : 0 < k) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ n.descFactorial k :=
```

This should replace `sylvester_general`'s `hsmooth` premise. The lemma above directly states
Sylvester-Schur: n·(n-1)·...·(n-k+1) has a prime divisor > k when n ≥ 2k.

### Pieces that are complete (but in separate attempts, not assembled)

1. **`two_mul_primeCounting_lt`** — complete and verified:
```lean4
lemma two_mul_primeCounting_lt (k : ℕ) (hk : 8 < k) : 2 * Nat.primeCounting k < k
```
Proved by induction + parity analysis via `Nat.primesLE` API.

2. **`erdos_case1_real_contradiction`** — complete ℝ algebra chain (not yet compiled):
   Squares both sides, clears denominator, derives n^{k+1} < k^{2k},
   with k² ≤ n gives k^{2k+2} < k^{2k} → contradiction.

3. **Factorization upper bound** — structure from ChatGPT, needs API fixes:
   `choose_le_pow_primeCounting_of_no_large_prime`

### Key Mathlib lemmas (verified to exist)

```
pow_factorization_choose_le (hn : 0 < n) : p ^ (choose n k).factorization p ≤ n
prod_pow_factorization_choose (n k) (hkn : k ≤ n) : C(n,k) = product over p≤n
Nat.primesLE k : Finset ℕ  — set of primes ≤ k
Nat.primesLE_card_eq_primeCounting : |primesLE k| = primeCounting k
Nat.dvd_of_factorization_pos {n p} (h : n.factorization p ≠ 0) : p ∣ n
Nat.factorization_eq_zero_of_not_prime (a) (h : ¬ p.Prime) : ...
```

### What needs to be written

**Lemma: `choose_gt_div_pow_real`** — lower bound C(n,k) > (n/k)^k in ℝ for n ≥ 2k, k ≥ 1.
Standard proof: C(n,k) = ∏_{i=0}^{k-1} (n-i)/(k-i), each factor ≥ n/k.

### Attack plan

1. Fix the factorization lemma API calls in `choose_le_pow_primeCounting_of_no_large_prime`
2. Write `choose_gt_div_pow_real` (use ℝ product identity or induction)
3. Assemble `sylvester_schur_case1` from pieces 1-3
4. For §§2-4 (k > √n) and k ≤ 8: mark as `sorry` for now — these need the Erdos refined decomposition
5. Wire `sylvester_schur_descFactorial` to call `sylvester_schur_case1` for the covered range

## Ch33 — Done ✅

`ProofsInTheBook/Chapter33.lean` — Hall's premise eliminated via double counting.
Uses `P : Fin n → Fin n → Option (Fin n)` partial Latin square representation.

## Repo state

- Branch: `main`
- Remote: `origin` → https://github.com/xiangyazi24/proof_in_the_book.git
- Clean working tree (only untracked `.DS_Store`)
- Both Ch03 and Ch33 compile with 0 errors

## Remote build

```bash
scripts/remote-build.sh  # runs lake build on uisai1 (32C/251GB)
```

Local `lake env lean File.lean` for single-file checks (do NOT run `lake build` locally).

## ChatGPT bridge

```bash
~/repos/chatgpt-bridge/ask-chatgpt.sh --pipe --channel ssem2 --no-channel-guard --stdin
```

## Build SOP update — 2026-05-17

Full local `lake build` is forbidden on the Mac mini: it can exhaust memory and hang.

Use local single-file checks only:

```bash
lake env lean ProofsInTheBook/Chapter03.lean
```

Use the workspace-level remote build script for full builds:

```bash
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh $(basename $PWD)
```

For this repository, from inside `~/repos/proof_in_the_book`, this expands to:

```bash
/Users/huangx/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book
```

The script rsyncs the local repo to `uisai1`, checks/installs the Lean toolchain as needed, runs
`lake build` remotely with 32-core parallelism, and returns output. `uisai1` cannot directly reach
GitHub; the script handles this through the Mac mini relay.

## Current Ch03 direction — 2026-05-17

Xiang clarified that Ch03 must prove the full Sylvester-Schur theorem, including Erdős §§2-4;
§§2-4 must not be left as `sorry` or postponed.

Current investigation:

- Mathlib does not appear to contain a ready-made Sylvester-Schur theorem.
- `mo271/FormalBook` also leaves Sylvester's theorem as `sorry`/TODO in Chapter 3.
- A simple lcm-based proof works only under the stronger hypothesis `start >= lcm(1..k)`, so it
  does not replace Sylvester-Schur under the desired `n >= 2*k` hypothesis.
- Useful Mathlib building blocks found so far:
  - `Nat.pow_factorization_choose_le`
  - `Nat.prod_pow_factorization_choose`
  - `Nat.factorization_choose_of_lt_three_mul`
  - Bertrand upper-bound pattern in `Mathlib/NumberTheory/Bertrand.lean`
  - Chebyshev `theta`, `psi`, and `lcmUpto` infrastructure in `Mathlib/NumberTheory/Chebyshev.lean`

ChatGPT bridge queries have been submitted on channels `ssem2` and `ssem` for proof-strategy help,
but the work should proceed independently rather than waiting on them.

## Chapter03 progress — 2026-05-18

Implemented and pushed a Lean-checked estimate spine toward full Sylvester-Schur:

- `NoLargePrimeFactor` and equivalence with `¬ HasPrimeFactorAbove`.
- Valuation vanishing for primes above `k` under no-large assumption.
- Choose/descFactorial divisibility bridges in both directions where applicable.
- Base case `k = 1` for descFactorial.
- No-large choose upper bound via factorization support:
  `choose_le_pow_primeCounting_of_noLargePrimeFactor`.
- Erdős-style §§2-4 upper-bound skeleton:
  `choose_factorization_le_min_third_of_noLargePrimeFactor` and
  `choose_le_sqrt_mul_four_pow_min_third_of_noLargePrimeFactor`.
  This uses `factorization_choose_of_lt_three_mul`,
  `factorization_choose_le_one`, and `primorial_le_four_pow`.
- Product lower bound:
  `pow_le_pow_mul_choose`, giving `n^k <= k^k * C(n,k)`.
- Log upper/lower bounds and sandwich:
  `log_choose_le_sqrt_log_add_min_third_log_four_of_noLargePrimeFactor`,
  `mul_log_sub_mul_log_le_log_choose`, and
  `erdos_log_sandwich_of_noLargePrimeFactor`.
- Gap-to-prime interface:
  `exists_large_prime_factor_choose_of_erdos_log_gap`.

Current missing mathematical core:

- A pure real/numeric gap lemma proving
  `sqrt(n) log n + min(k,n/3) log 4 < k log n - k log k`
  in the intended large range, or a stronger entropy lower bound replacing
  `k(log n - log k)`.
- Finite certificate for the remaining bounded cases.

The bridge responses (`0dc2cefd`, `10e3ddde`) recommend the same route:
upper-bound factorization + entropy lower bound + standalone real gap + finite certificate.
No bridge response supplied a complete proof of the hard real/finite parts.
