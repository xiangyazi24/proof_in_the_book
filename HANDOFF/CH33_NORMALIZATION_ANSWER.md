The missing move is not a no-singleton case split and not a proper-completion induction with $N$ cells. Smetaniuk’s proof handles the off-by-one by strengthening the intermediate induction target to improper completion.
The clean dependency chain is:


$$\boxed{E_N \Longrightarrow I_N \Longrightarrow E_{N+1}}$$


where:


$$E_N:\quad \text{every partial Latin square of order }N\text{ with }\le N-1\text{ cells completes properly;}$$




$$I_N:\quad \text{every partial Latin square of order }N\text{ with }\le N\text{ cells has an improper completion.}$$


For the Smetaniuk shrink you only need $I_N$ for weakly-upper-triangular partial squares, but the usual proof gives the stronger arbitrary-position version.
So the answer to your three alternatives is:


No, Smetaniuk does not need a special “every used symbol occurs at least twice” case split. The count $\le (n-1)/2$ is not the key invariant.


Almost, but not properly. The strengthened statement is not “$N$ strictly-above-diagonal cells complete properly.” That kind of statement is false. The actual strengthened statement is:
$N$ cells at order $N$ are allowed, but only for improper completion.


A cell is removed only temporarily. In the $I_N$ proof, delete an arbitrary cell, complete the remaining $N-1$ cells by $E_N$, then restore the deleted cell by a signed $2\times2$ improper trade. The later Smetaniuk diagonal/back-diagonal extension converts that improper completion into a proper Latin square of order $N+1$.


Here is the formalization-ready version.

1. Improper Latin squares
Use a syntactic signed-cell type:


$$\operatorname{cell} ::= [x]\quad\text{or}\quad [x+y-z].$$


Interpretation for row/column balance is by signed coefficients:


$$[x] \leadsto +x,
\qquad
[x+y-z]\leadsto +x + y - z.$$


A signed array $L$ of order $N$ is an improper Latin square if every row and every column has net coefficient $1$ for every symbol, and all but at most one cell are proper singleton cells.
A partial Latin square $P$ is improperly extended by $L$ if, for every filled cell $(r,c,a)\in P$, the signed cell $L(r,c)$ contains $a$ as a positive summand. Thus $[a]$, $[a+x-y]$, and $[x+a-y]$ all satisfy the prescribed entry $a$.
For formalization, do not quotient the syntax of $[a+b-b]$ to $[a]$ before checking “contains positively.” Row/column balance uses net coefficients; extension of the partial square uses positive syntactic occurrence.

2. The improper-restoration lemma: $E_N\Rightarrow I_N$
Assume $E_N$: every order-$N$ partial Latin square with at most $N-1$ entries completes properly.
Let $P$ be an order-$N$ partial Latin square with $|P|\le N$.
If $|P|\le N-1$, apply $E_N$ directly. A proper Latin square is also an improper Latin square with zero improper cells.
Now suppose $|P|=N$. Pick any filled cell


$$e=(r,c,a)\in P.$$


Let


$$P^- = P\setminus\{e\}.$$


By $E_N$, choose a proper Latin square $L$ completing $P^-$.
If


$$L(r,c)=a,$$


then $L$ already completes $P$ properly.
Otherwise let


$$b=L(r,c),\qquad b\ne a.$$


Let $c_a$ be the unique column in row $r$ with


$$L(r,c_a)=a,$$


and let $r_a$ be the unique row in column $c$ with


$$L(r_a,c)=a.$$


Since $L(r,c)=b\ne a$, we have $c_a\ne c$ and $r_a\ne r$.
Let


$$d=L(r_a,c_a).$$


Inside $L$ the relevant $2\times2$ pattern is


$$\begin{array}{c|cc}
 & c & c_a\\
\hline
r   & b & a\\
r_a & a & d
\end{array}$$


Replace it by the signed pattern


$$\begin{array}{c|cc}
 & c & c_a\\
\hline
r   & a & b\\
r_a & b & a+d-b
\end{array}$$


and leave every other cell unchanged.
Call the resulting signed array $L'$.
Row/column balance check
Row $r$ changed from


$$b+a$$


to


$$a+b.$$


Row $r_a$ changed from


$$a+d$$


to


$$b+(a+d-b)=a+d.$$


Column $c$ changed from


$$b+a$$


to


$$a+b.$$


Column $c_a$ changed from


$$a+d$$


to


$$b+(a+d-b)=a+d.$$


All other rows and columns are unchanged. Therefore every row and column still has net coefficient $1$ for every symbol. Hence $L'$ is an improper Latin square.
Extension check
The deleted cell $e=(r,c,a)$ is now restored properly, because


$$L'(r,c)=a.$$


The two cells $(r,c_a)$ and $(r_a,c)$ cannot have been prescribed in $P^-$. Indeed, $L(r,c_a)=a$; if $(r,c_a)$ were prescribed in $P^-$, then $P$ would contain symbol $a$ twice in row $r$, once at $e$ and once at $(r,c_a)$. Similarly, $(r_a,c)$ cannot be prescribed, because that would put symbol $a$ twice in column $c$.
The only other changed cell is $(r_a,c_a)$. If it was prescribed in $P^-$, its prescribed value was $d$, because $L$ completed $P^-$. In $L'$, that cell is


$$a+d-b,$$


which contains $d$ positively. So it still improperly extends the prescribed entry.
Thus $L'$ improperly completes $P$.
This proves:


$$E_N \Longrightarrow I_N.$$


No triangularity and no singleton-symbol hypothesis is used here.

3. The Smetaniuk shrink/extension step: $I_N\Rightarrow E_{N+1}$
Now prove $E_{N+1}$, assuming $I_N$.
Let $P$ be a partial Latin square of order $N+1$ with


$$|P|\le N.$$


By the row/column permutation lemma you already have, permute rows and columns so that every filled cell of $P$ lies strictly above the main diagonal:


$$(r,c,a)\in P \implies r<c.$$


Because $|P|\le N$ but there are $N+1$ symbols, choose a symbol $\omega$ not used in $P$. This is the symbol inserted on the Smetaniuk diagonal/back-diagonal.
Define the shrink $P^\downarrow$ of order $N$ by


$$P^\downarrow
=
\{(r,c-1,a):(r,c,a)\in P\}.$$


Since $r<c$, we have


$$r\le c-1,$$


so $P^\downarrow$ is weakly above the main diagonal. It has the same number of filled cells:


$$|P^\downarrow|=|P|\le N.$$


Also, $P^\downarrow$ is still a partial Latin square: shifting all columns down by one is injective on columns, and row-symbol and column-symbol uniqueness are preserved.
By $I_N$, choose an improper Latin square $L^\ast$ of order $N$ improperly completing $P^\downarrow$.
Now apply the improper Smetaniuk extension lemma:

If $Q$ is a weakly-upper partial Latin square of order $N$, $L^\ast$ is an improper Latin square of order $N$ improperly completing $Q$, and $\omega$ is fresh, then the Smetaniuk diagonal/back-diagonal extension of $L^\ast$ with new symbol $\omega$ has a proper Latin completion of order $N+1$ extending


$$Q^\uparrow=\{(r,c+1,a):(r,c,a)\in Q\}.$$



Apply this to $Q=P^\downarrow$. Since


$$(P^\downarrow)^\uparrow=P,$$


we get a proper Latin square of order $N+1$ completing $P$. Undo the row and column permutations.
Thus:


$$I_N \Longrightarrow E_{N+1}.$$


Together with the previous section:


$$E_N \Longrightarrow I_N \Longrightarrow E_{N+1}.$$


That is the actual induction.

4. What must be strengthened in your current formalization
Your current theorem


$$\texttt{smetBackDiagonal\_completable}$$


apparently has the shape:

the Smetaniuk back-diagonal partial square over any proper Latin square $L_0$ of order $N$ completes to order $N+1$.

For the full Evans/Smetaniuk proof, the needed theorem is the improper version:


$$\texttt{smetBackDiagonal\_improperCompletable}$$


with shape:

the Smetaniuk back-diagonal partial square over any improper Latin square $L^\ast$ of order $N$, with a marked positive occurrence for each prescribed weak-upper cell, completes properly to order $N+1$.

The proper theorem is the special case where the improper Latin square has no improper cell.
This is exactly where the “extra” retained cell goes. It is not deleted in the shrink. It is absorbed as the unique improper defect in $L^\ast$, and the Smetaniuk switching removes that defect when passing to order $N+1$.

5. Why the tempting proper strengthened statements are false
A proper statement like


$$\text{“every weakly-upper order-}N\text{ partial Latin square with }N\text{ cells completes”}$$


is false.
For $N=3$, take


$$(1,1)=1,\qquad (1,2)=2,\qquad (2,3)=3.$$


This is weakly above the diagonal and has $N=3$ cells. It has no proper completion: row $1$ already contains $1,2$, so $(1,3)$ would have to be $3$, but column $3$ already contains $3$ at $(2,3)$.
Even the strictly-above version with $N$ cells is not generally true. For $N=4$, take


$$(1,2)=1,\qquad
(1,3)=2,\qquad
(2,4)=3,\qquad
(3,4)=4.$$


Row $1$ must place $3$ and $4$ in columns $1$ and $4$, but column $4$ already contains both $3$ and $4$. So no proper completion exists.
Thus the strengthened induction cannot be a proper-completion theorem with $N$ cells. It must be an improper-completion theorem.

6. Final dependency order
Formalize in this order:


Signed cells


$$[x],\quad [x+y-z].$$




Net coefficient


$$\operatorname{coeff}([x],s),\qquad
\operatorname{coeff}([x+y-z],s).$$




Positive occurrence


$$\operatorname{pos}([x],s)\iff s=x,$$




$$\operatorname{pos}([x+y-z],s)\iff s=x\text{ or }s=y.$$




Improper Latin square
every row and column has net coefficient $1$ for every symbol, with at most one syntactically improper cell.


Improper extension
every prescribed entry of $P$ occurs positively in its cell.


Improper $2\times2$ restore lemma
From a proper completion of $P\setminus\{(r,c,a)\}$, construct an improper completion of $P$ using


$$\begin{array}{cc}
b & a\\
a & d
\end{array}
\mapsto
\begin{array}{cc}
a & b\\
b & a+d-b.
\end{array}$$




Evans-to-improper


$$E_N\Rightarrow I_N.$$




Strict-to-weak shrink


$$(r,c,a)\mapsto(r,c-1,a),
\qquad r<c\Rightarrow r\le c-1.$$




Improper Smetaniuk extension


$$I_N\Rightarrow E_{N+1}$$


for shrunk weak-upper configurations.


Main induction


$$E_N\Rightarrow I_N\Rightarrow E_{N+1}.$$




So the sharpened gap is closed by replacing the order-$(n-1)$ Evans IH call with an order-$(n-1)$ improper-completion IH call. The no-singleton case needs no separate combinatorial argument.
