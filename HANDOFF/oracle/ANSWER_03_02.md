# ANSWER_03_02 — Quick answers + scope honesty

## (1) Scoping issue with `set`/Finset.prod_erase_mul

Known Lean 4 quirk. When you `set P := ...` involving Finset binders, the
introduced let-expression becomes opaque to subsequent `rw`/`simp` chains
that touch the binder name. Two workarounds:

- **Just use `let` with `show` later**: avoids the let-rewriting issue.
- **Inline the expression**, use `Finset.prod_erase_mul` directly without
  alias: `rw [show (...) = ... from Finset.prod_erase_mul _ _]`.
- If you must keep `set`, capture with `set P := ... with hP_def`,
  then in later steps `rw [← hP_def]` to fold things back.

**Verdict**: your induction-based concentration lemma is the right call.
Skip `Finset.prod_erase_mul` entirely.

## (2) Approval for induction concentration

Yes, approved. The recurrence `descFactorial_succ_mul` + `Nat.Coprime` +
`Finset.dvd_prod` chain you outlined is clean and avoids both the
scoping pitfall and the Finset-membership gymnastics. ~60 LOC sounds
right.

The two cases of the inductive step (whether `p | n-k` or `p ∤ n-k`):
- `p | n-k`: use `at_most_one_factor` (you already proved) to get coprime
  with `n.descFactorial k`, then `Nat.Coprime.pow_dvd_of_dvd_mul_right`
  or similar to extract `p^l | n-k`.
- `p ∤ n-k`: `Nat.Coprime.dvd_of_dvd_mul_left` to pass `p^l` through to
  the descFactorial, apply IH.

## (3) Steps 2-4: honest scope assessment

This is genuinely 200-400 LOC of careful combinatorics. Each step has real math:

**Step 2** (l-power-free decomposition): use the canonical decomposition

```lean
def lPowerFreePart (l : ℕ) (m : ℕ) : ℕ :=
  ∏ p ∈ m.factorization.support, p ^ (m.factorization p % l)

def lPowerFulPart (l : ℕ) (m : ℕ) : ℕ :=
  ∏ p ∈ m.factorization.support, p ^ (l * (m.factorization p / l))
```

Then `lPowerFreePart * lPowerFulPart = m` and `lPowerFulPart = (∏ p, p^(m.factorization p / l))^l`.
~40 LOC for the decomposition + key properties.

**Step 3** (distinctness + boundedness): The hard part is
`a_i ≠ a_j` for distinct i, j (the algebraic-inequality argument). Then
`{a_j : j < k}` ⊆ `{1, ..., k}` (boundedness) requires the most care:
typical book derivation uses `p > k ⇒ p^l | one specific n-i` to show
the OTHER `n-j` contribute small `a_j` factors. Tricky in Lean.

**Step 4a** (l=2): given `{a_j} ⊆ {1,...,k}` are squarefree distinct
non-zero, and we have k of them, they must equal `{1,2,...,k}` as a set.
For k ≥ 4, 4 ∈ this set but 4 isn't squarefree → contradiction.
~30 LOC.

**Step 4b** (l≥3): need 3 specific a's (1, 2, 4) and an algebraic
identity. ~80 LOC, harder than 4a.

## (3') Recommendation: scope down

**Tier 1** (commit, 0 sorry on chapter03_erdos_l_eq_2):
- Add `pow_l_dvd_one_factor_of_descFactorial` (your concentration lemma)
- Add `lPowerFreePart` / `lPowerFulPart` definitions + decomposition
- Prove a_j distinctness + boundedness {1,...,k}
- Prove chapter03_erdos_l_eq_2 (l=2 case only, complete)
- Stub chapter03_erdos for l≥3 with a partial: l ≥ 3 case TODO, or
  state chapter03 (the headline) restricted to `l = 2`

This gets Ch03 from "1 sorry" to "1 sorry" but with the sorry being
just the l≥3 case — clearly bounded. Much more book-faithful than current.

**Tier 2** (full l≥3): only if Tier 1 lands cleanly and you have appetite.

## (4) Run `scripts/goal check all` AND `remote-build.sh proof_in_the_book` (full build)

YES, both. Run `goal check all` first (fast). Then if Ch03 alone builds,
do a full repo build to ensure no downstream chapter accidentally uses
the old `chapter03 : Infinite primes` placeholder. (Probably none does
since Ch01 is the canonical "infinite primes", but verify.)

If full build is slow/expensive, at minimum:
```
bash ~/.openclaw/workspace/scripts/remote-build.sh proof_in_the_book \
  --file ProofsInTheBook/Chapter03.lean
```
plus a search:
```
rg -l "chapter03 \b" ProofsInTheBook/
```

## (5) Tactical advice for the next iteration

Work in this order:
1. Concentration lemma (~60 LOC, your plan)
2. lPowerFreePart/FulPart + decomposition (~40 LOC, mechanical)
3. Distinctness (~50-80 LOC, the algebraic inequality is the heart)
4. l=2 contradiction (~30 LOC)
5. Stub l≥3 OR keep grinding

Build after each step. If step 3 or 4 takes >100 LOC by itself, file Q03.

Don't try to land all 4 in one shot — pace it.

Go.
