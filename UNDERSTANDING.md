# UNDERSTANDING.md — Proofs in the Book Formalization

## Project overview

Full-book formalization of *Proofs from THE BOOK* (Aigner & Ziegler) in Lean 4.
40 chapters, each formalizing one "book proof."

**Current status after Ch33 fix (2026-05-17, DeepSeek v4 Pro session):**

- 40 chapters compile with 0 `sorry` and 0 `axiom`
- 7 chapters have explicit premises (function parameters) marking difficult math
- 1 premise eliminated (Ch33 Hall's condition)
- Ch03 partial work done (Erdős 1934 paper located and analyzed, §1 proof scaffold built)

## Premises to eliminate (from TODO.md)

| Chapter | Premise | Difficulty | Status |
|---------|---------|------------|--------|
| Ch33 | Hall's condition | Easy | ✅ DONE |
| Ch03 | Sylvester smoothness | Medium-Hard | ⬜ Partial |
| Ch31 | Prüfer encoding | Medium | ⬜ |
| Ch34 | Kernel-perfect extension | Medium-Hard | ⬜ |
| Ch11 | Rotating calipers | Medium | ⬜ |
| Ch09 | arccos(1/3) irrationality | Hard | ⬜ |
| Ch10 | Gallai geometry | Hard | ⬜ |
| Ch39 | Kneser lower bound | Very Hard | ⬜ |

## Ch33 — Hall's condition (DONE)

**What changed**: Eliminated `hHall_verified` premise from `latin_square_completion_step`.

**Approach**: Introduced `P : Fin n → Fin n → Option (Fin n)` representing a partial Latin square.
The Hall condition is proved via double counting: symbols common to all columns of a set S,
times |S|, ≤ total filled cells ≤ n-1. If Hall failed, the product would be ≥ n, contradiction.

**Key lemma**: `hall_from_partial_square` — proves Hall from `filledCells P ≤ n-1` and `hused_witness`.

**Note**: The ChatGPT ssem2 channel contributed an alternative approach using `hSparse`
(total used symbols across any set of columns ≤ n-1). Either works. The committed approach
uses the P-representation.

## Ch03 — Sylvester-Schur (PARTIAL)

### What the book says

The book states Sylvester's theorem but does NOT prove it. It says:
> In 1934, Erdős gave a short and elementary Book Proof of Sylvester's result,
> running along the lines of his proof of Bertrand's postulate.

Then references: P. Erdős, J. London Math. Soc. 9 (1934), 282-288.

The rest of Ch03 uses Sylvester as a lemma for "binomial coefficients are almost never powers."

### Erdős 1934 proof structure

The paper is at `ref/erdos.pdf`. The proof has two main cases:

**§1 (8 < k ≤ √n)**: 
- Lemma: p^{v_p(C(n,k))} ≤ n (proved via Legendre's formula, each term in the sum is 0 or 1)
- Under assumption "no prime > k divides C(n,k)": C(n,k) = ∏_{p≤k} p^{v_p} ≤ ∏_{p≤k} n = n^{π(k)}
- π(k) < k/2 for k > 8 (proved by counting even composites + odd composite 9)
- C(n,k) > (n/k)^k (standard lower bound)
- Chain: (n/k)^k < C(n,k) ≤ n^{π(k)} < n^{k/2}
- → n < k², contradiction with k ≤ √n (i.e., k² ≤ n)

**§§2-4 (k > √n)**:
More refined product decomposition. Not yet formalized.

### What was built (not yet compiling)

Three complete pieces exist:

1. **`two_mul_primeCounting_lt`** (complete, provided by Xiang):
   Induction proof that 2·π(k) < k for k > 8, using `Nat.primesLE` API.

2. **`erdos_case1_real_contradiction`** (complete, DeepSeek):
   ℝ-algebra chain: square both sides → clear denominator → n^{k+1} < k^{2k}.
   With k² ≤ n gives k^{2k+2} ≤ n^{k+1} < k^{2k} → k² < 1, impossible.

3. **`choose_le_pow_primeCounting_of_no_large_prime`** (from ChatGPT):
   Factorization product bound using `prod_pow_factorization_choose`,
   `pow_factorization_choose_le`, `Nat.primesLE`. The core of the Erdos §1 upper bound.

4. **Lower bound `choose_gt_div_pow_real`** (NOT DONE):
   Need to prove C(n,k) > (n/k)^k in ℝ for n ≥ 2k, k ≥ 1.
   Standard proof: C(n,k) = ∏_{i=0}^{k-1} (n-i)/(k-i), each factor ≥ n/k.

### Key Mathlib lemmas needed

- `pow_factorization_choose_le (hn : 0 < n)` — p^{v_p(C(n,k))} ≤ n
- `prod_pow_factorization_choose n k hkn` — C(n,k) = ∏_{p≤n} p^{v_p}
- `Nat.primesLE k` — set of primes ≤ k
- `Nat.primesLE_card_eq_primeCounting` — |primesLE k| = π(k)
- `Nat.dvd_of_factorization_pos hne` — v_p(m) > 0 → p | m
- `Nat.factorization_eq_zero_of_not_prime` — not prime → v_p = 0

### Why the Lean code didn't compile

The factorization/product lemmas require precise knowledge of Mathlib4 API:
- `∏` vs `Finset.prod` syntax
- `factorization_eq_zero_of_not_prime` method call syntax (it's a method on `Nat`, takes `a` as argument)
- `Nat.dvd_of_factorization_pos` signature
- Typeclass issues with `simp` and `positivity`
- `mod_cast` with ℝ ↔ ℕ powers

A stronger model (Claude Opus) with better Mathlib4 knowledge should fix these in one pass.

### What the current file has

`ProofsInTheBook/Chapter03.lean` is the original WORKING version (0 errors):
- `sylvester_general (n k) (hn2k) (hkpos) (hsmooth)` — takes `hsmooth` as premise
- `hsmooth : n.descFactorial k ∉ (k+1).smoothNumbers` — the Sylvester-Schur conclusion
- All subsidiary lemmas about `HasPrimeFactorAbove`, `smoothNumbers` are complete

## Ch31 — Prüfer encoding (NOT STARTED)

Premise: `hCayley : Fintype.card (LabeledTree n) ≤ n ^ (n-2)`

Task: Construct the actual Prüfer encoding algorithm (repeatedly remove smallest leaf,
record neighbor) to produce an injective map `LabeledTree n → Fin (n-2) → Fin n`.

This is algorithmic graph theory. Key lemmas needed:
- `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial` (leaf extraction)
- Well-founded recursion on tree size
- Injectivity: different trees → different Prüfer sequences

## Ch34 — Kernel-perfect orientation

Premise: `hextension : ∀ colored partialColor, ... → ∃ v c, ...`

The book uses kernel-perfect orientations of row-column bipartite graphs.
Needs Galvin's theorem / kernel-perfect lemma.

## Ch11 — Rotating calipers (slopes count)

Premise: `hslopes : points.card - 1 ≤ slopesDeterminedBy points`.card

Ungar's rotating-calipers argument. Needs convex hull infrastructure.

## Working style notes

- Remote build: `scripts/remote-build.sh` on uisai1 (32 cores / 251GB RAM).
  Local Mac mini cannot handle `lake build`.
- `lake env lean File.lean` works locally for single-file checks.
- Commit often, use `git diff --check` before committing (whitespace rule from CLAUDE.md).
- The ChatGPT bridge at `~/repos/chatgpt-bridge/` is available for collaboration.
  Channel `ssem2` has extended thinking (ChatGPT Pro).
  Use `--pipe --channel ssem2 --no-channel-guard` for queries.
- The Erdos paper is at `ref/erdos.pdf`.

## Key commit history

```
39bb8ea add Erdős 1934 Sylvester-Schur original paper (ref/erdos.pdf)
0cb83b6 Chapter03: add book citation and formalization status annotation
c660f88 TODO: mark Ch33 premise as done
81088fa Chapter33: PROVE Hall condition internally — 1st premise eliminated
c2322c1 add TODO.md (8 premises to prove) + update UNDERSTANDING.md
```
