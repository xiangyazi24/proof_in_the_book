# Ch33 normalization — RESOLVED (own derivation, no pbook needed)

The {2,2,0,0,0} obstruction (codex: "no uniquely-occurring symbol") is sidestepped: normalization is
POSITIONAL + uses an UNUSED symbol, with NO single-occurrence condition.

## Crux lemma (clean single induction)
`exists_perm_strictly_above`: for S : Finset (Fin n × Fin n) with S.card < n, there exist
σ τ : Equiv.Perm (Fin n) with ∀ p ∈ S, σ p.1 < τ p.2  (all cells strictly above the main diagonal).

PROOF by strong induction on n:
- n = 0 or S = ∅: take σ = τ = 1 (no cells).
- Else: |S| ≥ 1 and |S| < n so n ≥ 2.
  * ∃ empty column c0 (a col with no cell of S): since the columns used number ≤ |S| < n.
  * ∃ non-empty row r0 (a row with ≥1 cell): since |S| ≥ 1.
  * Build σ, τ sending r0 ↦ 0 and c0 ↦ 0, and on the rest use (IH on the (n-1)×(n-1) grid obtained by
    deleting row r0 and column c0) shifted up by 1.
  * Sub-grid cell count = |S| − deg(r0) ≤ |S| − 1 ≤ n − 2 = (n−1) − 1, so IH applies.
  * Correctness: r0's cells (r0, j), j ≠ c0, satisfy σ(r0)=0 < τ(j) (= subτ+1 ≥ 1); c0 has no cells;
    other cells: σ(i)=subσ(i)+1 < subτ(j)+1=τ(j) ⟺ subσ(i)<subτ(j) (IH).
KEY: peel an empty COLUMN (rank 0) together with a NON-EMPTY ROW (rank 0) — the non-empty row's cells are
automatically satisfied, and deleting it strictly reduces the cell count. No strict/weak alternation.

## Normalization of the exact case (using the crux lemma)
Given P : order-n partial Latin square, exactly n-1 filled cells.
1. By exists_perm_strictly_above on the filled-cell set, permute rows & columns so all n-1 filled cells lie
   strictly above the main diagonal (i < j).
2. Reverse the column order (j ↦ (n-1)-j): now all filled cells lie in the region i + j < n-1 (above the
   anti-diagonal) — exactly smetBackPartial's "copied" region.
3. Choose an UNUSED symbol s* (exists: n-1 cells use ≤ n-1 < n symbols), relabel it to be the new symbol N=n-1.
   The anti-diagonal i+j=n-1 will carry N in the back-diagonal partial.
4. Reduce to order n-1: the order-(n-1) partial square R (delete the anti-diagonal slot and re-index) has
   ≤ n-2 cells, completes by IH (Evans at order n-1) to L0; then smetBackPartial L0 extends the normalized P,
   and smetBackDiagonal_completable (PROVEN) completes it. Undo the relabeling/permutations to complete P.

This closes EvansExactCardinalityCase (hence chapter33_unconditional) — the switching is already proven.

## CORRECTION (codex adversarial check, 2026-06-04): the above has a COUNTING GAP
The unused-symbol route puts NO filled cell on the back-diagonal, so the order-(n-1) shrink retains all
n-1 cells — exceeding the Evans IH at order n-1 (which handles ≤ n-2). The singleton-symbol invariant existed
precisely so the shrink deletes one filled cell (the special diagonal cell). So:
- exists_perm_strictly_above (PROVEN) is still necessary/useful, but NOT sufficient.
- The genuine remaining design question (for the literature / relay): how does Smetaniuk's actual proof handle
  the no-singleton-symbol case ({2,2,0,0,0})? Candidates: (a) a case split with a separate argument when every
  used symbol occurs ≥2 (few distinct symbols); (b) a STRENGTHENED triangular completion statement at order N
  allowing N cells when all are strictly above the diagonal (the triangular structure compensating the +1);
  (c) a strengthened Smetaniuk core with extra row/column constraints. (b) looks most plausible — the classic
  n-cell non-completable examples are not triangular.
STATUS: Ch33 = switching PROVEN + permutation crux PROVEN + this one design question open.
