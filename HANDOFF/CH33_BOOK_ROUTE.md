# CH33 BOOK ROUTE — the authoritative Aigner–Ziegler Chapter 32 proof (NO improper squares needed)

DISCOVERY: the book's actual proof avoids the improper-Latin-square machinery entirely.
The off-by-one is resolved by: (i) Lemma 2 handles "few distinct elements"; (ii) otherwise a
SINGLETON element exists, its cell is renamed to the fresh symbol and placed ON the diagonal,
then REMOVED before the inductive call (=> card <= N-1 at order N, exactly E_N); the proven
extension theorem puts the fresh symbol on the WHOLE back diagonal, so the removed cell is
restored automatically.

Existing inventory in this repo (verify exact statements yourself):
- latin_rectangle_extend_one (Chapter33.lean:245)  = book Lemma 1 (Hall), with
  hall_system_of_distinct_representatives + hall_condition_of_regular_family.
- SmetBackDiagonalCompletableCore (Chapter33Smetaniuk.lean:2180): for 3<=N, proper L0 of order N,
  EXISTS L completing smetBackPartial L0 — where smetBackPartial prescribes omega=Fin.last N on the
  ENTIRE back diagonal {i+j=N}, castSucc(L0 i j) on {i+j<N}, free above.
- smetMainShrink_step1 (needs hdiag : P last last = some last — generalize or re-derive: note
  smetShrink uses dropLastSymbol, so ANY cell containing the last symbol is erased BY SYMBOL).
- exists_perm_strictly_above (line 994): S.card < n => sigma/tau with all cells strictly above.
- relabelPartial + completion_exists_relabelPartial_iff + filledCells_relabelPartial_card:
  full row/column/ELEMENT relabeling transfer (line ~1110).
- reverseColumnsPartial; smetaniuk_exact_normalized_of_IH; SmetaniukExactNormalizedStatement.
- chapter33_order_le_three; the padding reduction to exact cardinality.

WORK ITEMS (book page references are to the verbatim text below):
(A) Lemma 2 [NEW FILE Chapter33Ryser.lean]: any partial Latin square of order n with at most n-1
    filled cells and at most n/2 distinct ELEMENTS completes. Proof = conjugacy (swap the roles of
    elements and rows in the (R,C,E) line array; for function-typed squares: the conjugate square
    has cell (e,c) = some r iff P r c = some e; well-defined by column-injectivity) reduces to
    "entries in at most n/2 ROWS"; then sort rows by fill count f1>=...>=fr, complete rows 1..r
    one by one via Hall (inequality (1) and the quadratic inequality (2), full text below), then
    finish with latin_rectangle_extend_one iterated.
(B) Singleton pigeonhole: if a partial Latin square has <= n-1 cells and MORE than n/2 distinct
    elements, some element occurs exactly once.
(C) Normalization: card <= N cells at order N+1, an element occurring exactly once => exists row
    perm sigma, col perm tau, element perm pi such that the relabeled square has: the singleton cell
    AT (d,d) on the main diagonal with value Fin.last, every OTHER cell strictly above {i<j}, and
    NO other occurrence of Fin.last. Book construction: sort rows by fill count descending, place
    row s_i at index f1+...+f_i (1-indexed), pack filled cells left, singleton ordered last in its
    row => lands on the diagonal; transpose to match the strictly-above convention of this repo.
    (Generalizes exists_perm_strictly_above — reuse its peeling-induction idea or the explicit
    sorted construction.)
(D) Glue (the main induction, replacing the improper conditional route):
    order N+1, card <= N. If card <= N-1+... split: <= n/2 distinct elements -> (A);
    else (B) gives singleton -> (C) normalize -> reverse columns -> erase the omega cell via the
    symbol-dropping shrink (cells with omega vanish; card drops to <= N-1) -> IH E_N gives L0 ->
    SmetBackDiagonalCompletableCore -> the completion covers the omega cell because it lies on the
    back diagonal after reversal ((d,d) -> (d, N-d), d+(N-d)=N) and ALL back-diagonal cells are
    prescribed omega -> transfer back through relabeling. CHECK the existing smetShrink/ShiftedCompletes
    conventions carefully and reconcile (there appear to be both a shifted-column convention and a
    back-diagonal identity convention in the file; pick what composes).
    Endpoint: theorem chapter33_unconditional : forall n, LatinSquareCompletionTheorem n  (no hypotheses).

=== VERBATIM BOOK TEXT (Aigner-Ziegler ch. 32, the complete proof) ===

Lemma 1. Any (r × n)-Latin rectangle, r < n, can be extended to an
                                       ((r+1)×n)-Latin rectangle and hence can be completed to a Latin square.
                                        Proof. We apply Hall’s theorem (see Chapter 27). Let Aj be the set
                                       of numbers that do not appear in column j. An admissible (r + 1)-st row
                                       corresponds then precisely to a system of distinct representatives for the
                                       collection A1 , . . . , An . To prove the lemma we therefore have to verify
                                       Hall’s condition (H). Every set Aj has size n − r, and every element is in
                                       precisely n − r sets Aj (since it appears r times in the rectangle). Any m
                                       of the sets Aj contain together m(n − r) elements and therefore at least m
                                       different ones, which is just condition (H).                             

                                       Lemma 2. Let P be a partial Latin square of order n with at most n − 1
                                       cells filled and at most n2 distinct elements, then P can be completed to a
                                       Latin square of order n.
Completing Latin squares                                                                                                    215

 Proof. We first transform the problem into a more convenient form.
By the conjugacy principle discussed above, we may replace the condi-
tion “at most n2 distinct elements” by the condition that the entries appear
in at most n2 rows, and we may further assume that these rows are the top
rows. So let the rows with filled cells be the rows 1, 2, . . . , r, with fi filled
                                        r
cells in row i, where r ≤ n2 and i=1 fi ≤ n − 1. By permuting the rows,
we may assume that f1 ≥ f2 ≥ . . . ≥ fr . Now we complete the rows
1, . . . , r step by step until we reach an (r × n)-rectangle which can then be
extended to a Latin square by Lemma 1.
Suppose we have already filled rows 1, 2, . . . ,  − 1. In row  there are f
filled cells which we may assume to be at the end. The current situation is
depicted in the figure, where the shaded part indicates the filled cells.
The completion of row  is performed by another application of Hall’s
theorem, but this time it is quite subtle. Let X be the set of elements that          A situation for n = 8, with  = 3, f1 =
do not appear in row , thus |X| = n − f , and for j = 1, . . . , n − f             f2 = f3 = 2, f4 = 1. The dark squares
let Aj denote the set of those elements in X which do not appear in                   represent the pre-filled cells, the lighter
column j (neither above nor below row ). Hence in order to complete                  ones show the cells that have been filled
row  we must verify condition (H) for the collection A1 , . . . , An−f .            in the completion process.
First we claim

                 n − f −  + 1 >  − 1 + f+1 + . . . + fr .                  (1)
                                            r
The case  = 1 is clear. Otherwise          i=1 fi < n,     f1 ≥ . . . ≥ fr and
1 <  ≤ r together imply
                       
                       r
                n >          fi ≥ ( − 1)f−1 + f + . . . + fr .
                       i=1

Now either f−1 ≥ 2 (in which case (1) holds) or f−1 = 1. In the latter
case, (1) reduces to n > 2( − 1) + r −  + 1 = r +  − 1, which is true
because of  ≤ r ≤ n2 .
Let us now take m sets Aj , 1 ≤ m ≤ n − f , and let B be their union.
We must show |B| ≥ m. Consider the number c of cells in the m columns
corresponding to the Aj ’s which contain elements of X. There are at most
( − 1)m such cells above row  and at most f+1 + . . . + fr below row ,
and thus
                    c ≤ ( − 1)m + f+1 + . . . + fr .
On the other hand, each element x ∈ X\B appears in each of the m
columns, hence c ≥ m(|X| − |B|), and therefore (with |X| = n − f )
                 1                        1
     |B| ≥ |X| − m c ≥ n − f − ( − 1) − m (f+1 + . . . + fr ).

It follows that |B| ≥ m if
                                 1
              n − f − ( − 1) − m (f+1 + . . . + fr ) > m − 1,

that is, if

                 m(n − f −  + 2 − m) > f+1 + . . . + fr .                   (2)
216                                                                                 Completing Latin squares

                              Inequality (2) is true for m = 1 and for m = n−f −+1 by (1), and hence
                              for all values m between 1 and n − f −  + 1, since the left-hand side is
                              a quadratic function in m with leading coefficient −1. The remaining case
                              is m > n − f −  + 1. Since any element x of X is contained in at most
                               − 1 + f+1 + . . . + fr rows, it can also appear in at most that many
                              columns. Invoking (1) once more, we find that x is in one of the sets Aj , so
                              in this case B = X, |B| = n − f ≥ m, and the proof is complete.           

                              Let us finally prove Smetaniuk’s theorem.
                              Theorem. Any partial Latin square of order n with at most n − 1 filled
                              cells can be completed to a Latin square of the same order.

                               Proof. We use induction on n, the cases n ≤ 2 being trivial. Thus we
s1        2           7
                              now study a partial Latin square of order n ≥ 3 with at most n − 1 filled
s2            5       4       cells. With the notation used above these cells lie in r ≤ n − 1 different
                              rows numbered s1 , . . . , sr , which contain f1 , . . . , fr > 0 filled cells, with
                                 r
                                 i=1 fi ≤ n − 1. By Lemma 2 we may assume that there are more than
s3                5           n
                               2 different elements; thus there is an element that appears only once: after
                              renumbering and permutation of rows (if necessary) we may assume that
                              the element n occurs only once, and this is in row s1 .
s4        4                   In the next step we want to permute the rows and columns of the partial
                              Latin square such that after the permutations all the filled cells lie below
                              the diagonal — except for the cell filled with n, which will end up on the
                              diagonal. (The diagonal consists of the cells (k, k) with 1 ≤ k ≤ n.) We
                              achieve this as follows: First we permute row s1 into the position f1 . By
                              permutation of columns we move all the filled cells to the left, so that n
      2   7                   occurs as the last element in its row, on the diagonal. Next we move row
                              s2 into position 1 + f1 + f2 , and again the filled cells as far to the left
                              as possible. In general, for 1 < i ≤ r we move the row si into position
                              1 + f1 + f2 + . . . + fi and the filled cells as far left as possible. This clearly
                              gives the desired set-up. The drawing to the left shows an example, with
          4   5
                              n = 7: the rows s1 = 2, s2 = 3, s3 = 5 and s4 = 7 with f1 = f2 = 2
                  5           and f3 = f4 = 1 are moved into the rows numbered 2, 5, 6 and 7, and the
                              columns are permuted “to the left” so that in the end all entries except for
      4
                              the single 7 come to lie below the diagonal, which is marked by •s.
                              In order to be able to apply induction we now remove the entry n from
                              the diagonal and ignore the first row and the last column (which do not
                              not contain any filled cells): thus we are looking at a partial Latin square
      2   3   4   1   6   5   of order n − 1 with at most n − 2 filled cells, which by induction can be
                              completed to a Latin square of order n − 1. The margin shows one (of
      5   6   1   4   2   3   many) completions of the partial Latin square that arises in our example.
      1   2   3   6   5   4   In the figure, the original entries are printed bold. They are already final,
                              as are all the elements in shaded cells; some of the other entries will be
      6   4   5   2   3   1   changed in the following, in order to complete the Latin square of order n.
      3   1   6   5   4   2   In the next step we want to move the diagonal elements of the square to
                              the last column and put entries n onto the diagonal in their place. How-
      4   5   2   3   1   6
                              ever, in general we cannot do this, since the diagonal elements need not
Completing Latin squares                                                                                         217

be distinct. Thus we proceed more carefully and perform successively, for
k = 2, 3, . . . , n − 1 (in this order), the following operation:
Put the value n into the cell (k, n). This yields a correct partial Latin
square. Now exchange the value xk in the diagonal cell (k, k) with the
value n in the cell (k, n) in the last column.
If the value xk did not already occur in the last column, then our job for the
current k is completed. After this, the current elements in the k-th column
will not be changed any more.
In our example this works without problems for k = 2, 3 and 4, and the
corresponding diagonal elements 3, 1 and 6 move to the last column. The
following three figures show the corresponding operations.



  2   3    4    1    6   5    7               2   7    4    1    6   5    3      2   7   4     1    6    5   3
  5   6    1    4    2   3                    5   6    1    4    2   3    7      5   6   7     4    2    3   1
  1   2    3    6    5   4                    1   2    3    6    5   4           1   2   3     6    5    4   7
  6   4    5    2    3   1                    6   4    5    2    3   1           6   4   5     2    3    1
  3   1    6    5    4   2                    3   1    6    5    4   2           3   1   6     5    4    2
  4   5    2    3    1   6                    4   5    2    3    1   6           4   5   2     3    1    6

Now we have to treat the case in which there is already an element xk in
the last column. In this case we proceed as follows:
If there is already an element xk in a cell (j, n) with 2 ≤ j < k, then we
exchange in row j the element xk in the n-th column with the element xk
in the k-th column. If the element xk also occurs in a cell (j , n), then we
also exchange the elements in the j -th row that occur in the n-th and in the
k-th columns, and so on.                                                                            k        n
If we proceed like this there will never be two equal entries in a row. Our
exchange process ensures that there also will never be two equal elements in
a column. So we only have to verify that the exchange process between the                           xk       xk j
k-th and the n-th column does not lead to an infinite loop. This can be seen
from the following bipartite graph Gk : Its vertices correspond to the cells
(i, k) and (j, n) with 2 ≤ i, j ≤ k whose elements might be exchanged.                              xk       xk j
There is an edge between (i, k) and (j, n) if these two cells lie in the same
row (that is, for i = j), or if the cells before the exchange process contain                       xk       n   k
the same element (which implies i = j). In our sketch the edges for i = j
are dotted, the others are not. All vertices in Gk have degree 1 or 2. The
cell (k, n) corresponds to a vertex of degree 1; this vertex is the beginning
of a path which leads to column k on a horizontal edge, then possibly on a
sloped edge back to column n, then horizontally back to column k and so                      Gk :
on. It ends in column k at a value that does not occur in column n. Thus the
exchange operations will end at some point with a step where we move a
new element into the last column. Then the work on column k is completed,
and the elements in the cells (i, k) for i ≥ 2 are fixed for good.
218                                                                                    Completing Latin squares

                                  In our example the “exchange case” happens for k = 5: the element x5 = 3
                                  does already occur in the last column, so that entry has to be moved back
                                  to column k = 5. But the exchange element x5 = 6 is not new either, it is
                                  exchanged by x5 = 5, and this one is new.



                                    2    7    4    1    6    5   3                2    7    4    1    3    5    6
                                    5    6    7    4    2    3   1                5    6    7    4    2    3    1
                                    1    2    3    7    5    4   6                1    2    3    7    6    4    5
                                    6    4    5    2    3    1   7                6    4    5    2    7    1    3
                                    3    1    6    5    4    2                    3    1    6    5    4    2
                                    4    5    2    3    1    6                    4    5    2    3    1    6

                                  Finally, the exchange for k = 6 = n − 1 poses no problem, and after that
                                  the completion of the Latin square is unique:

                                                                                  7    3    1    6    4    2    4
      2   7   4   1   3   5   6     2   7    4    1    3    5    6                2    7    4    1    3    5    6
      5   6   7   4   2   3   1     5   6    7    4    2    3    1                5    6    7    4    2    3    1
      1   2   3   7   6   4   5     1   2    3    7    6    4    5                1    2    3    7    6    4    5
      6   4   5   2   7   1   3     6   4    5    2    7    1    3                6    4    5    2    7    1    3
      3   1   6   5   4   2   7     3   1    6    5    4    7    2                3    1    6    5    4    7    2
      4   5   2   3   1   6         4   5    2    3    1    6                     4    5    2    3    1    6    7

                                  . . . and the same occurs in general: We put an element n into the cell (n, n),
                                  and after that the first row can be completed by the missing elements of the
                                  respective columns (see Lemma 1), and this completes the proof. In order
                                  to get explicitly a completion of the original partial Latin square of order n,
                                  we only have to reverse the element, row and column permutations of the
                                  first two steps of the proof.                                                


                                  