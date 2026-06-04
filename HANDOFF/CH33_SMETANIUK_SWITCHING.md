I’ll focus only on the exact-cardinality normalized Smetaniuk step. I need to be careful here because the usual “diagonal” description hides a nontrivial strengthened induction invariant; I’ll make that invariant explicit rather than pretending the bare statement inducts directly.

There is a normalization mismatch to fix: Smetaniuk’s construction does not use “bottom-right plus arbitrary other cells.” It uses one occurrence of the new symbol on a diagonal and all other prescribed cells in the strict triangular region on one side of that diagonal. I’ll state the exact strengthened normalized theorem; without that triangular hypothesis, the requested construction is not the actual inductive step.

There is one correction: the statement as written is not the Smetaniuk normalized induction step unless your normalization also proves the triangular condition. The Smetaniuk step needs:


$$P(n-1,n-1)=n-1,$$


the symbol $n-1$ occurs exactly once, and every other filled cell lies in the strict upper triangle:


$$i<j.$$


Equivalently, after deleting the special cell, all remaining prescribed cells are above the main diagonal. This is the column-reversed version of Smetaniuk’s usual “back diagonal” setup. Smetaniuk’s proof first normalizes one uniquely occurring symbol onto the diagonal and all other entries above it; Burton’s exposition states exactly this normalization and then removes the unique symbol to reduce to order $n-1$. people.smp.uq.edu.au+1
Below is the formalization-ready version.

Target strengthened induction statement
Use this as the induction theorem:
leanTheorem SmetaniukTriangular n :  4 ≤ n →  ∀ P : PartialLatinSquare (Fin n),    cardFilled P ≤ n - 1 →    P.Valid →    (∃! c, P c = some (last n)) →    P (last n, last n) = some (last n) →    (∀ i j s,      P (i,j) = some s →      s ≠ last n →      i < j) →    ∃ L : LatinSquare (Fin n), Extends L P
For your exact-cardinality case, add:
leancardFilled P = n - 1
but the proof only needs ≤ n - 1.
The induction hypothesis should be the general Evans statement for order n-1:
leanIH :  ∀ R : PartialLatinSquare (Fin (n-1)),    cardFilled R ≤ (n-1) - 1 →    R.Valid →    ∃ L0 : LatinSquare (Fin (n-1)), Extends L0 R
This is important: the smaller square is not necessarily normalized; it is just a partial Latin square with at most $n-2$ entries.

Step 1: delete the special cell and reduce to order $n-1$
Let $N := n-1$. Assume:
leanP (N,N) = some N∀ filled (i,j,s), s ≠ N → i < j
Remove the special entry:
leanQ(i,j) :=  if (i,j) = (N,N) then none else P(i,j)
Because every other filled cell satisfies i < j, row N is empty in Q.
Also column 0 is empty in Q, because no filled cell can have i < 0.
So remove row N and column 0.
Define the smaller partial square $R$ of order $n-1$ by:


$$R(i,j)=Q(i,j+1).$$


In Lean, with i j : Fin (n-1):
leanR i j := Q (castUp i, succ j)
where:
leancastUp : Fin (n-1) → Fin nsucc   : Fin (n-1) → Fin nsucc j = j + 1
The triangular condition transfers:


$$i < j+1 \iff i \le j.$$


So all entries of $R$ lie on or above the main diagonal.
Cardinality:
leancardFilled R = cardFilled P - 1
Hence, since cardFilled P = n - 1,
leancardFilled R = n - 2 = (n-1) - 1.
Latin validity of R follows by restriction of rows, columns, and symbols from P.
Apply IH:
leanobtain ⟨L0, hL0_extends_R⟩ := IH R hcardR hvalidR
Here $L_0$ is a Latin square of order $n-1$.

Step 2: define the Smetaniuk partial expansion $S(L_0)$
Define a partial square $S$ of order $n$ as follows.
For $i,j : \mathrm{Fin}\ n$:


$$S(i,j)=
\begin{cases}
N, & i=j,\\
L_0(i,j-1), & i<j,\\
\emptyset, & i>j.
\end{cases}$$


In Lean shape:
leandef smetPartial (L0 : LatinSquare (Fin (n-1))) :    PartialLatinSquare (Fin n) :=fun i j =>  if hdiag : i = j then    some (last n)  else if hlt : i < j then    some (embedSymbol (L0 ⟨i, proof_i_lt_n_minus_one⟩ ⟨j-1, proof⟩))  else    none
The embedding of old symbols is:
leanembedSymbol : Fin (n-1) → Fin nembedSymbol x := ⟨x.val, Nat.lt_trans x.isLt (Nat.sub_lt ... )⟩
Important domain facts for i < j:
leani < j → i < n - 1i < j → 0 < ji < j → j - 1 < n - 1
So L0 i (j-1) is well-defined.
S extends P:


At (N,N), both contain N.


If P(i,j)=s≠N, then i<j.


Its image in R is R(i,j-1)=s.


Since L0 extends R, L0(i,j-1)=s.


Therefore S(i,j)=s.


Thus:
leanlemma P_extends_smetPartial :  ExtendsPartial (smetPartial L0) P

Step 3: complete $S(L_0)$
The remaining nontrivial theorem is Smetaniuk’s switching completion:
leantheorem smetPartial_completable  (L0 : LatinSquare (Fin (n-1))) :  ∃ L : LatinSquare (Fin n), Extends L (smetPartial L0)
This is Smetaniuk’s diagonal/switching construction. It is independent of the original $P$.
The usual proof completes columns one by one. In the column-reversed main-diagonal version, it is cleaner to complete from left to right after using the original back-diagonal theorem. For Lean, I recommend proving the back-diagonal version first, then deriving the main-diagonal version by column reversal.

Back-diagonal version of the switching theorem
Let $m=n-1$. Given a Latin square $L_0$ of order $m$, define $B(L_0)$ of order $m+1=n$:


$$B(i,j)=
\begin{cases}
N, & i+j=N,\\
L_0(i,j), & i+j<N,\\
\emptyset, & i+j>N.
\end{cases}$$


This is exactly Smetaniuk’s $P(L)$: back diagonal filled with the new symbol, above the back diagonal copied from $L_0$, below empty. people.smp.uq.edu.au
Then prove:
leantheorem smetBackDiagonal_completable  (L0 : LatinSquare (Fin (n-1))) :  ∃ L : LatinSquare (Fin n), Extends L (smetBackPartial L0)
The proof uses the following invariant.

Cunning extension invariant
Suppose columns 0, …, k-1 are complete, where $1 \le k \le n-1$.
For each row $r<n-1$, let:


$$M_r(k)=\{\text{symbols in row } r \text{ of } M \text{ in columns }0,\dots,k-1\}.$$


Let:


$$L_r(k)=\{\text{symbols in row } r \text{ of } L_0 \text{ in columns }0,\dots,k-1\}.$$


The invariant is:


$$\forall r\ge n-k+1,\quad M_r(k)\setminus\{N\}\subseteq L_r(k).$$


In Lean:
leandef Cunning (M : PartialLatinSquare (Fin n)) (k : Nat) : Prop :=  ColumnsComplete M k ∧  ExtendsPartial M (smetBackPartial L0) ∧  ∀ r : Fin (n-1),    n - k + 1 ≤ r.val →      (rowSymbols M r k \ {last n}) ⊆ rowSymbolsL L0 r k
Base case k=1: true vacuously. Only the first column is complete because the back diagonal puts N in the bottom-left cell and all cells above it are copied from $L_0$.
This matches Smetaniuk’s “cunning extension” invariant. people.smp.uq.edu.au

Column extension step
Assume Cunning M k for 1 ≤ k ≤ n-2. Fill column k.
For each old symbol $x<N$, define a row sequence.
Use 0-based notation.
Row sequence for symbol $x$
If $x$ does not occur in the last row of $M$, define:


$$\sigma(x)=[].$$


Otherwise let $c_0$ be the column where $M(N,c_0)=x$. Let $r_0$ be the row where:


$$L_0(r_0,c_0)=x.$$


If $x$ does not occur in row $r_0$ of $M$, stop. Otherwise let $c_1$ be the column where $M(r_0,c_1)=x$, and let $r_1$ be the row where:


$$L_0(r_1,c_1)=x.$$


Continue.
This gives a finite list:


$$\sigma(x)=[r_0,r_1,\dots,r_t].$$


Lemmas:
leanlemma rowSeq_rows_old :  r ∈ rowSeq M L0 x → r < n-1lemma rowSeq_nodup :  (rowSeq M L0 x).Noduplemma rowSeq_finite :  True
Finiteness follows from Nodup in a finite type.
Also:
leanlemma rowSeq_cells_below_diagonal :  if r_i uses column c_i, then r_i + c_i > n-1lemma rowSeq_columns_lt_k :  every c_i < k
These are exactly the “row sequence” facts in Smetaniuk’s proof. people.smp.uq.edu.au

Starting row
Define:


$$\rho(x)=
\begin{cases}
N, & \sigma(x)=[],\\
\text{last element of }\sigma(x), & \sigma(x)\ne[].
\end{cases}$$


Then:
leanlemma startRow_missing :  x ∉ rowSymbols M (ρ x)lemma startRow_low :  ρ x ≥ n - k
and the key injectivity property:
leanlemma startRow_eq :  ρ x = ρ y →  x = y ∨ ρ x = last n
This is the critical no-collision lemma.

Value sequence
Let:


$$x_0=L_0(n-k-1,k).$$


Then recursively:


$$x_{t+1}=L_0(\rho(x_t),k)$$


as long as $\rho(x_t)\ne N$. Stop when $\rho(x_t)=N$.
The resulting list is:


$$\nu=[x_0,x_1,\dots,x_q].$$


Lemmas:
leanlemma valueSeq_nodup :  ν.Noduplemma valueSeq_startRows_nodup :  (ν.map ρ).Noduplemma valueSeq_ends_lastRow :  ρ (ν.getLast _) = last n
This is the “value sequence” part. people.smp.uq.edu.au

Fill column $k$
Define $M'$:
For column $k$:


If row $r=\rho(x)$ for some $x\in\nu$, set:




$$M'(r,k)=x.$$




Otherwise set:




$$M'(r,k)=L_0(r,k)$$


for old rows $r<N$.
All other cells equal $M$.
In Lean:
leandef fillNextColumn  (M : PartialLatinSquare (Fin n))  (hM : Cunning L0 M k) :  PartialLatinSquare (Fin n) :=fun r c =>  if hc : c.val = k then    if h : ∃ x ∈ valueSeq M L0 k, startRow M L0 x = r then      some (Classical.choose h)    else if hr : r.val < n-1 then      some (embed (L0 ⟨r.val, hr⟩ ⟨k, hk⟩))    else      none  else    M r c
The final none case cannot occur for the last row, because the value sequence ends with start row N, so the last row is filled by step 1.
Prove:
leanlemma fillNextColumn_no_overwritelemma fillNextColumn_column_completelemma fillNextColumn_validlemma fillNextColumn_cunning :  Cunning L0 M k →  Cunning L0 (fillNextColumn M hM) (k+1)
Validity splits into:
Row Latin
Step-1 entries are safe because:
leanstartRow_missing : x ∉ rowSymbols M (ρ x)
Step-2 entries are safe because cunning says the old row symbols, except N, are already among the first k symbols of the same row in L0, while $L_0(r,k)$ is not among those.
Column Latin
Step-1 values are distinct by valueSeq_nodup.
Step-2 values are distinct because they come from a column of $L_0$.
No value appears in both step 1 and step 2 by the definition of the value sequence.
No new value duplicates an old value in column $k$ by the “below diagonal” and “columns < k” row-sequence lemmas.
This is the core switching argument.

Finish the completion
Iterate fillNextColumn until columns 0,…,n-2 are complete.
Then delete any entries in the last column, obtaining a Latin rectangle with first $n-1$ columns complete and last column empty.
Invoke your already-proven Latin-rectangle extension theorem:
leanlatinRectangle_extend :  IsLatinRectangle r n Q →  ∃ L : LatinSquare (Fin n), Extends L Q
Here r = n, and the rectangle has n rows and n-1 filled columns.
The missing entry in each row of the last column is forced, so the resulting Latin square also restores any deleted last-column entries.
Thus:
leantheorem smetBackDiagonal_completable :  ∃ L : LatinSquare (Fin n), Extends L (smetBackPartial L0)
Then obtain the main-diagonal version by column reversal:
leanmainDiag = reverseColumns backDiag
So:
leantheorem smetPartial_completable :  ∃ L : LatinSquare (Fin n), Extends L (smetPartial L0)

Final proof of the normalized exact case
Given normalized $P$:


Remove (N,N)=N.


Remove row N and column 0.


Get $R$ of order $n-1$ with at most $n-2$ filled cells.


Complete $R$ by IH to $L_0$.


Build smetPartial L0.


Prove smetPartial L0 extends $P$.


Complete smetPartial L0 by Smetaniuk switching.


Therefore complete $P$.



Lean lemma order
lean-- triangular normalizationdef StrictUpperTriangledef MainDiagonalNewSymbollemma normalized_row_last_empty_after_deletelemma normalized_col_zero_empty_after_delete-- reductiondef removeSpecialdef shrinkRemoveLastRowFirstCollemma shrink_validlemma shrink_cardFilled :  cardFilled R = cardFilled P - 1lemma shrink_card_le :  cardFilled R ≤ (n-1) - 1-- induction usetheorem IH_complete_smaller :  ∃ L0, Extends L0 R-- Smetaniuk partial expansiondef smetBackPartiallemma smetBackPartial_validtheorem smetBackDiagonal_completabledef smetMainPartiallemma smetMainPartial_eq_reverse_backtheorem smetMainPartial_completable-- extension of original Plemma smetMainPartial_extends_P :  ExtendsPartial (smetMainPartial L0) P-- final theoremtheorem smetaniuk_exact_normalized :  4 ≤ n →  cardFilled P = n - 1 →  Valid P →  P (last,last) = some last →  OccursExactlyOnce P last →  (∀ i j s, P(i,j)=some s → s≠last → i<j) →  ∃ L, LatinSquare L ∧ Extends L P
That is the faithful Smetaniuk construction. The indispensable strengthened hypothesis is the triangular one; the bare condition “bottom-right contains $n-1$” is not the Smetaniuk induction step.