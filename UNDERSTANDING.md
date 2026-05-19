# UNDERSTANDING.md — Proofs in the Book Formalization

## Project overview

Full-book formalization of *Proofs from THE BOOK* (Aigner & Ziegler) in Lean 4.
40 chapters, each formalizing one "book proof."

**Current status after Ch11 reduction work (2026-05-19):**

- 40 chapters compiled before the current Ch11 push; Ch11 is currently
  remote single-file checked with no `sorry`/`admit` and no axioms. The Ungar
  theorem still has a geometric rotating-sweep premise, now narrowed to a
  concrete cyclic generalized allowable-sequence certificate.
- Ch31 Cayley upper bound has been eliminated via Joyal's endofunction injection.
- Ch34 Dinitz/Galvin premise has been eliminated via kernel-perfect orientation
  and stable-matching kernels.
- Ch33 Hall's condition premise eliminated.
- Ch03 Sylvester-Schur premise eliminated; `sylvester_general` now proves the binomial coefficient form directly from `2 * k ≤ n` and `0 < k`.
- Next target: Ch11 rotating calipers / slopes count.

## Premises to eliminate (from TODO.md)

| Chapter | Premise | Difficulty | Status |
|---------|---------|------------|--------|
| Ch33 | Hall's condition | Easy | ✅ DONE |
| Ch03 | Sylvester smoothness | Medium-Hard | ✅ DONE |
| Ch31 | Joyal/Cayley upper bound | Medium | ✅ DONE |
| Ch34 | Kernel-perfect extension | Medium-Hard | ✅ DONE |
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

## Ch03 — Sylvester-Schur (DONE)

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

### Current file status

`ProofsInTheBook/Chapter03.lean` now proves:

```lean
theorem sylvester_general (n k : ℕ) (hn : 2 * k ≤ n) (hk : 0 < k) :
    ∃ p, k < p ∧ p.Prime ∧ p ∣ n.choose k
```

The proof combines Erdős-style factorization bounds, entropy/Stirling lower bounds,
Chebyshev estimates, and finite certificates. See `CHAPTER03_EXPERIENCE.md`.

## Ch31 — Cayley upper bound / Joyal encoding (DONE)

Premise eliminated: `hCayley : Fintype.card (LabeledTree n) ≤ n ^ (n-2)`.

Approach: formalized Joyal's injection from doubly rooted labeled trees to
endofunctions on `Fin n`. Since there are `n^n` endofunctions and `n^2` root
choices, this gives `Fintype.card (LabeledTree n) ≤ n^(n-2)` in the required
range.

Key theorem:

```lean
theorem joyal_tree_adj_iff_recovered (X : DoublyRootedLabeledTree n) (u v : Fin n) :
    X.1.1.Adj u v ↔ joyalRecoveredAdj X u v
```

This reconstructs all original tree edges from the Joyal endofunction data.
The final proof is remote-build checked and has no `sorry`.

## Ch34 — Kernel-perfect orientation (DONE)

Premise: `hextension : ∀ colored partialColor, ... → ∃ v c, ...`

The current premise is mathematically too strong: a partial proper coloring of
an `n × n` Dinitz array with lists of size `n` need not be extendable by coloring
one additional arbitrary-uncolored cell. The correct proof is not greedy over
arbitrary partial colorings. It has been replaced by Galvin's proof:

1. Prove list-colorability from a kernel-perfect orientation with
   `|C(v)| > outdegree(v)` for every vertex.
2. Construct the Dinitz orientation from a Latin square order.
3. Prove every induced subgraph has a kernel via the stable-matching lemma.

The committed proof uses the cyclic Latin value orientation. Kernel existence
is proved directly on finite induced cell sets by the row-max/column-max
stable-matching argument: if row-maximal cells are independent, they form a
kernel; otherwise a same-column conflicting pair lets one delete a column-maximum
cell and lift the inductive kernel back.

## Ch11 — Rotating calipers (slopes count)

Premise: Ungar's direction lower bound for non-collinear finite point sets.

Important correction: the fixed-coordinate statement
`points.card - 1 ≤ (slopesDeterminedBy points).card` is false because
`slopesDeterminedBy` intentionally excludes vertical directions. The book's
"slope" count includes the vertical parallel class. The correct target in Lean
is therefore phrased using `directionsDeterminedBy`.

Current progress:

- Proved finite slopes embed into directions.
- Proved directions have at most one more element than finite slopes.
- Proved subset monotonicity for slopes/directions and non-collinearity.
- Proved the book's reduction from all sets to the even-cardinality direction
  theorem, including the `n = 3` base case.
- Formalized Ungar's final numerical counting endpoint as
  `UngarCountingCertificate.length_lower_bound`.
- Added `CountedGeneralizedAllowableSequence.length_lower_bound_from_gaps`,
  reducing the counted-sequence endpoint to the two T/O/C gap inequalities
  on ordered crossing moves.
- Added central-barrier windows and offset-pair switch lemmas in Ch11:
  crossing steps are increasing/decreasing on the whole central window, and
  every offset `s < min(d_i,d_j)` between consecutive crossings has a
  noncrossing switch witness.
- Proved the finite counted-sequence fact that if no crossing move has full
  order `k`, then there are at least two crossing moves; also connected the
  existing unit-order consecutive gap lemma to the ordered `crossingIdx`
  interface used by `toMoveSchedule`.
- Added central-window monotonicity, restriction lemmas for increasing/decreasing
  states, and the block-intersection fact needed for the T/O/C persistence
  proof: in a state decreasing on a central window, an increasing reversal
  block intersects that window in at most one position.
- Proved the T/O/C persistence facts: across a noncrossing range, a decreasing
  (respectively increasing, backwards) central window loses at most one layer
  per move.  This removes the `gap_between` assumption for adjacent crossing
  moves: `ConcreteGeneralizedAllowableSequence.gap_between_crossingIdx` now
  proves the general `d_i + d_{i+1} - 1` lower bound.  The counted-sequence
  endpoint is reduced to the cyclic first/last `gap_ends` condition plus the
  no-full-crossing condition.
- Added `CyclicEndGapWitness`, matching Ungar's periodic-extension argument
  for the first/last crossing pair, and connected concrete cyclic sequences
  back to the even direction bound via
  `even_direction_bound_of_concrete_cyclic_sequence`.
- Added `directions_lower_bound_of_even_concrete_cyclic_sequences`, so the
  book reduction now accepts a concrete cyclic allowable-sequence certificate
  for every even non-collinear set, rather than a raw sweep-counting
  certificate.
- The public `ungar_directions_lower_bound` now uses
  `EvenConcreteCyclicSequencePremise`; the older
  `EvenUngarSweepCertificatePremise` interface remains available only as a
  coarser compatibility layer.
- Added `ConcreteGeneralizedAllowableSequence.NoDirectFullMove` and proved
  `moveOrder < k` from it: a crossing step of order `k` would have source
  equal to the identity and target equal to the full reverse permutation.
  Thus the geometric no-full condition can be proved as "no sweep direction
  collapses all points into one reversing block."
- Added the point-set geometry lemma
  `not_all_pair_directions_eq_of_noncollinearSet`: a non-collinear set cannot
  have all distinct point pairs determining one common projective direction.
- Added `FullMoveForcesCommonDirection` and
  `EvenGeometricConcreteCyclicSequencePremise`; non-collinearity now turns this
  geometric explanation of a full reversal into `NoDirectFullMove`, then into
  the `moveOrder < k` condition needed by the counting proof.

Remaining core: construct `EvenConcreteCyclicSequencePremise` from the
rotating projection sweep of every even non-collinear point set.  The adjacent
T/O/C gaps are proved; the remaining geometric content is the actual sweep
construction, no-direct-full property, and cyclic first/last crossing witness.

Current premise:

```lean
abbrev EvenConcreteCyclicSequencePremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
    NoncollinearSet S →
      ∃ A : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card,
        ∃ _hnoFull :
          ∀ j : Fin (directionsDeterminedBy S).card,
            A.toCountedGeneralizedAllowableSequence.IsCrossing j →
              A.toCountedGeneralizedAllowableSequence.moveOrder j < k,
          Nonempty (A.CyclicEndGapWitness
            (A.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk))
```

This is the only intended Ch11 gap after the reductions. Proving it removes
the rotating-calipers premise from the public `ungar_directions_lower_bound`.

## Working style notes

- Remote build/check only.  Do not run Lean locally on the Mac mini, including
  single-file `lake env lean` checks.
- Single-file check:
  `/Users/huangx/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book --file ProofsInTheBook/Chapter11.lean`
- Full build:
  `/Users/huangx/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book`
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
