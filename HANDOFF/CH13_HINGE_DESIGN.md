I will be blunt about the crux, because it is the point that decides the formalization:


$$\boxed{
\text{From ordinary strict spherical convexity alone, the terminal-first claim is false.}
}$$


The genuine determinant admissible set gives:


$$\boxed{
\text{target reached}\quad\text{or}\quad\text{some mixed support determinant is tight.}
}$$


It does not identify the tight determinant as


$$[q_2,q_1,q_n^*]=0.$$


To get the book’s stated branch, one must either add a stronger hypothesis, or prove an additional “terminal visibility” theorem not contained in the usual strict-convex-arm definition. In particular, admissibility defined only by the terminal closing determinant plus the target bound is not sufficient: other mixed convexity inequalities do not follow from the terminal one.
Below is the dependency-ordered chain in the unit-vector $\det_3$/Gram language.

0. Sign convention and basic notation
Write


$$[a,b,c]:=\det_3(a,b,c)=a\cdot(b\times c).$$


All points are unit vectors in $S^2\subset\mathbb R^3$.
For a cyclically oriented strictly convex spherical polygonal arm


$$(x_1,\dots,x_n),$$


with $x_{n+1}=x_1$, use the support-sign convention


$$[x_i,x_{i+1},x_k]>0$$


for every cyclic edge $x_ix_{i+1}$ and every nonincident vertex $x_k\notin\{x_i,x_{i+1}\}$.
If your file uses the opposite orientation, replace every $>0$ by $<0$. The zero/tightness statements are unchanged.
For the opening at $q_2$, let


$$x_1(t)=q_1,\qquad x_2(t)=q_2,\qquad x_k(t)=R_tq_k\quad(3\le k\le n),$$


where $R_t$ is the Rodrigues rotation about the axis $q_2$. Also set


$$a_t:=R_{-t}q_1.$$


Then


$$R_tq_2=q_2$$


and


$$[R_tu,R_tv,R_tw]=[u,v,w].$$



1. Determinant/rotation layer
Lemma 1.1 — cyclic and skew determinant identities
For all $a,b,c\in\mathbb R^3$,


$$[a,b,c]=[b,c,a]=[c,a,b],$$


and


$$[a,c,b]=-[a,b,c].$$


These are just the alternating multilinearity of the determinant.

Lemma 1.2 — rotation invariance of $\det_3$
If $R\in SO(3)$, then


$$[Ra,Rb,Rc]=[a,b,c].$$


Proof:


$$[Ra,Rb,Rc]
=
\det(R)\,[a,b,c]
=
[a,b,c],$$


because $\det(R)=1$.
For Rodrigues rotations about $q_2$, this gives in particular


$$R_tq_2=q_2$$


and


$$[R_tu,R_tv,R_tw]=[u,v,w].$$



Lemma 1.3 — inverse-head rewrite
For


$$a_t:=R_{-t}q_1,$$


one has


$$[R_tq_i,R_tq_{i+1},q_1]
=
[q_i,q_{i+1},a_t],$$


and


$$[R_tq_n,q_1,R_tq_k]
=
[q_n,a_t,q_k].$$


Proof: apply $R_{-t}$ simultaneously to all three entries and use Lemma 1.2.

2. Strict convexity support layer
Lemma 2.1 — edge-support definition
A cyclic arm


$$(x_1,\dots,x_n)$$


is strictly convex if, for every cyclic edge $x_ix_{i+1}$ and every nonincident vertex $x_k$,


$$[x_i,x_{i+1},x_k]>0,$$


with all side lengths lying in $(0,\pi)$, and with the vertices in a common open hemisphere.
The weak version replaces $>0$ by $\ge0$.

Lemma 2.2 — support signs imply a hemisphere witness
If


$$[x_i,x_{i+1},x_k]>0$$


for all nonincident $k$, define


$$H:=\sum_{i=1}^n x_i\times x_{i+1}.$$


Then


$$H\cdot x_k
=
\sum_i [x_i,x_{i+1},x_k].$$


The two adjacent terms vanish:


$$[x_{k-1},x_k,x_k]=0,
\qquad
[x_k,x_{k+1},x_k]=0.$$


All remaining terms are positive. Hence


$$H\cdot x_k>0$$


for every $k$. So the vertices lie in the open hemisphere


$$H\cdot x>0.$$


This is often the cleanest way to remove a separate hemisphere witness from the strict predicate.

Lemma 2.3 — edge supports imply cyclic triple signs
For a strictly convex cyclic arm, every cyclically ordered triple has the same positive orientation:


$$i<j<k
\quad\Longrightarrow\quad
[x_i,x_j,x_k]>0,$$


after choosing the cyclic indexing convention appropriately.
Proof sketch in determinant language:
Fix $i<j$. The edge-support inequalities place every vertex strictly on the same oriented side of every edge. Equivalently, the spherical polygon is the boundary of an intersection of positive hemispheres


$$\bigcap_i\{y:[x_i,x_{i+1},y]\ge0\}.$$


The geodesic diagonal $x_ix_j$ lies inside this convex spherical polygon. Therefore every vertex $x_k$ cyclically between $x_j$ and $x_i$ lies on the positive side of the oriented diagonal $x_ix_j$, giving


$$[x_i,x_j,x_k]>0.$$


For formalization, this lemma is usually proved by induction on $j-i$ using diagonal containment and the strict support signs. Once available, it is the workhorse for all cut and subsequence arguments.

Lemma 2.4 — cyclic subsequence strict convexity
Every cyclic subsequence of a strictly convex cyclic arm is strictly convex.
Proof:
Let


$$(y_1,\dots,y_m)$$


be a cyclic subsequence of


$$(x_1,\dots,x_n).$$


Every support determinant of the subsequence has the form


$$[y_r,y_{r+1},y_s].$$


These are cyclic triple determinants of the original sequence. By Lemma 2.3 they are strictly positive. Hence the subsequence is strictly convex.
The hemisphere condition is inherited either because the old hemisphere contains all vertices, or by applying Lemma 2.2 to the subsequence.

3. Mixed support classification for the opened arm
Let


$$X(t)=(q_1,q_2,R_tq_3,\dots,R_tq_n).$$


The support determinants of $X(t)$ fall into invariant and genuinely mixed families.

Lemma 3.1 — invariant support determinants
All support determinants involving only


$$q_2,R_tq_3,\dots,R_tq_n$$


are invariant under the opening.
For $2\le i\le n-1$ and $k\ge2$,


$$[x_i(t),x_{i+1}(t),x_k(t)]
=
[q_i,q_{i+1},q_k].$$


Also,


$$[R_tq_n,q_2,R_tq_k]
=
[q_n,q_2,q_k].$$


Proof: $q_2=R_tq_2$, so all three entries are jointly rotated by $R_t$. Apply Lemma 1.2.

Lemma 3.2 — genuinely theta-dependent supports
The theta-dependent support determinants are precisely the following.
First-edge supports


$$A_k(t):=[q_1,q_2,R_tq_k],
\qquad 3\le k\le n.$$


These are the supports of the edge $q_1q_2$ against the rotated tail.
Rotated-tail-edge supports against the fixed head vertex


$$B_i(t):=[R_tq_i,R_tq_{i+1},q_1]
       =[q_i,q_{i+1},a_t],
\qquad 2\le i\le n-1.$$


These are the supports of the edge $R_tq_i\,R_tq_{i+1}$ against $q_1$.
Closing-edge supports, if the arm is treated cyclically


$$C_2(t):=[R_tq_n,q_1,q_2],$$


and


$$C_k(t):=[R_tq_n,q_1,R_tq_k]
       =[q_n,a_t,q_k],
\qquad 3\le k\le n-1.$$


The book’s terminal stuck determinant


$$[q_2,q_1,R_tq_n]$$


is the same zero condition as


$$C_2(t)=0,$$


up to a fixed sign/cyclic permutation.
Thus the full mixed family is


$$\mathcal F_{\mathrm{mix}}
=
\{A_k:3\le k\le n\}
\cup
\{B_i:2\le i\le n-1\}
\cup
\{C_2\}
\cup
\{C_k:3\le k\le n-1\}.$$


If your strict arm predicate is open-chain rather than cyclic, remove the $C$-family. The $A$- and $B$-families remain mandatory.

4. Convex persistence through the admissible interval
Lemma 4.1 — continuity of mixed supports
Every


$$F(t)\in\mathcal F_{\mathrm{mix}}$$


is continuous.
Proof:
$t\mapsto R_tq_i$ is continuous. The determinant is a polynomial in the coordinates of its three inputs. Therefore every determinant support function is continuous.

Lemma 4.2 — correct admissible predicate
Let $T$ be the target opening parameter.
Define


$$\operatorname{Adm}(u)$$


by


$$0\le u\le T$$


and


$$F(t)\ge0
\quad\text{for every }F\in\mathcal F_{\mathrm{mix}}
\quad\text{and every }t\in[0,u],$$


together with the chosen hemisphere constraints on $[0,u]$, if they are stored separately.
Equivalently, since the family is finite and continuous,


$$\min_{F\in\mathcal F_{\mathrm{mix}}}F(t)\ge0
\quad\text{for all }t\in[0,u].$$


Then


$$\operatorname{Adm}(u)
\Longrightarrow
X(t)\text{ is weakly convex for every }t\in[0,u].$$


If all support inequalities are strict on $[0,u]$, then $X(t)$ is strictly convex on $[0,u]$.
This is the answer to part (1): persistence is not an extra monotonicity theorem. It is obtained by building the genuine theta-dependent support constraints into admissibility.

Lemma 4.3 — closedness and sup admissibility
The set


$$\mathcal A:=\{u:\operatorname{Adm}(u)\}$$


is closed in $[0,T]$.
Proof:
If $u_m\to u$ and every $u_m$ is admissible, then for any $t\in[0,u]$, approximate $t$ by some $t_m\in[0,u_m]$. Continuity gives


$$F(t)=\lim_m F(t_m)\ge0$$


for every mixed support $F$. The hemisphere constraints are identical.
Therefore


$$s:=\sup\mathcal A$$


belongs to $\mathcal A$.

Lemma 4.4 — genuine reach-or-support-tight
Let


$$s:=\sup\mathcal A.$$


Then either


$$s=T,$$


or there exists a mixed support or hemisphere constraint $G$ such that


$$G(s)=0.$$


Proof:
Assume $s<T$ and every constraint is strict at $s$. Since there are finitely many constraints and each is continuous, there exists $\varepsilon>0$ such that all constraints remain nonnegative on $[s,s+\varepsilon]$. This makes $s+\varepsilon/2$ admissible, contradicting maximality of $s$.
Thus some constraint is tight.
This is the strongest theorem obtained from the genuine support-family admissible set.

5. The crux: why terminal-first does not follow
The desired theorem would be:


$$s<T
\Longrightarrow
[q_2,q_1,R_sq_n]=0.$$


Equivalently, among all mixed supports, the first tight one must be the terminal closing support.
That is not implied by strict convexity.
The tempting argument

opening at $q_2$ moves the tail away from the head region, so all interior supports move inward

fails because the mixed determinants


$$B_i(t)=[R_tq_i,R_tq_{i+1},q_1]$$


and


$$C_k(t)=[R_tq_n,q_1,R_tq_k]$$


are not monotone in the favorable direction in general.
Using the inverse-head rewrite,


$$B_i(t)=[q_i,q_{i+1},a_t],$$


so the question is whether the backward-moving head point $a_t=R_{-t}q_1$ stays strictly inside all original tail supports until the terminal ray is reached. Ordinary convexity gives no such implication.

6. Explicit determinant counterexample
This counterexample lives in the positive affine chart $z=1$. Then it is also a spherical counterexample after radial normalization, because replacing


$$v_i$$


by


$$q_i=\frac{v_i}{\|v_i\|}$$


multiplies every determinant by a positive factor and hence preserves signs and zeros.
Take unnormalised vectors


$$v_1=(-2,0,1),$$




$$v_2=(0,0,1),$$




$$v_3=(0,2,1),$$




$$v_4=(-2,2,1),$$




$$v_5=(-3,1,1),$$




$$v_6=\left(-\frac{21}{10},\frac1{100},1\right).$$


In the affine chart $z=1$, these are the planar points


$$(-2,0),\quad
(0,0),\quad
(0,2),\quad
(-2,2),\quad
(-3,1),\quad
\left(-\frac{21}{10},\frac1{100}\right).$$


They form a strictly convex cyclic polygon.
The relevant edge-support determinants are all positive:


$$\begin{array}{c|c}
\text{oriented edge} & \text{nonincident support determinants} \\
\hline
v_1v_2 & 4,\ 4,\ 2,\ \frac1{50} \\
v_2v_3 & 4,\ 4,\ 6,\ \frac{21}{5} \\
v_3v_4 & 4,\ 4,\ 2,\ \frac{199}{50} \\
v_4v_5 & 2,\ 4,\ 2,\ \frac{189}{100} \\
v_5v_6 & \frac9{100},\ \frac{207}{100},\ \frac{387}{100},\ \frac{189}{100} \\
v_6v_1 & \frac1{50},\ \frac{11}{50},\ \frac15,\ \frac9{100}
\end{array}$$


Thus the starting arm is strictly convex in determinant-support language.
Now rotate the tail


$$v_3,\dots,v_6$$


clockwise about


$$v_2=e_3.$$


Equivalently, keep the tail fixed and move the head backwards by the opposite rotation:


$$a(t)=R_t v_1=(-2\cos t,-2\sin t,1).$$


Consider the mixed support for the tail edge $v_5v_6$ against the fixed head point:


$$D(t):=[v_5,v_6,a(t)].$$


A direct determinant expansion gives


$$D(t)
=
\frac{207}{100}
-\frac{99}{50}\cos t
-\frac95\sin t.$$


At $t=0$,


$$D(0)=\frac9{100}>0.$$


But for $t=0.052$,


$$D(t)<0.$$


So there is some


$$t_0\in(0,0.052)$$


such that


$$D(t_0)=0.$$


Equivalently,


$$[R_{-t_0}v_5,R_{-t_0}v_6,v_1]=0.$$


Thus a nonterminal mixed support becomes tight.
Now compare the desired terminal support. Up to the fixed sign convention, the terminal determinant is


$$E(t):=[R_{-t}v_6,v_1,v_2].$$


A direct expansion gives


$$E(t)
=
\frac{21}{5}\sin t+\frac1{50}\cos t.$$


For every


$$0\le t\le0.052,$$


one has


$$E(t)>0.$$


Therefore, when the nonterminal support first becomes tight,


$$[R_{-t_0}v_6,v_1,v_2]\ne0.$$


Equivalently,


$$[q_2,q_1,R_{-t_0}q_6]\ne0.$$


So the first tight support need not be


$$[q_2,q_1,q_n^*]=0.$$


This disproves the unrestricted terminal-first statement.

7. What theorem would recover the book’s terminal stuck branch
The missing theorem is a visibility statement.
Let


$$C_{\mathrm{term}}(t):=[R_tq_n,q_1,q_2],$$


or, in your sign convention,


$$[q_2,q_1,R_tq_n].$$


The needed additional lemma is:


$$\boxed{
C_{\mathrm{term}}(t)>0
\Longrightarrow
F(t)>0
\quad
\text{for every }
F\in\mathcal F_{\mathrm{mix}}\setminus\{C_{\mathrm{term}}\}.
}$$


Expanded, this is:


$$[q_1,q_2,R_tq_k]>0
\qquad(3\le k<n),$$




$$[R_tq_i,R_tq_{i+1},q_1]>0
\qquad(2\le i\le n-1),$$


and, in the cyclic version,


$$[R_tq_n,q_1,R_tq_k]>0
\qquad(3\le k\le n-1),$$


whenever the terminal closing support remains positive.
Call this lemma terminal_visibility.
With it, one may define the simpler admissible set


$$\operatorname{Adm}_{\mathrm{term}}(u)$$


by


$$0\le u\le T$$


and


$$C_{\mathrm{term}}(t)\ge0
\quad\text{for all }t\in[0,u].$$


Then the proof is:


Let


$$s:=\sup\{u:\operatorname{Adm}_{\mathrm{term}}(u)\}.$$




If


$$s=T,$$


the target angle is reached.


If


$$s<T$$


and


$$C_{\mathrm{term}}(s)>0,$$


continuity gives $C_{\mathrm{term}}>0$ on a slightly larger interval, contradicting maximality.


Hence


$$C_{\mathrm{term}}(s)=0.$$




By terminal_visibility, every other mixed support remains strict up to $s$.


This is the exact logical shape required for the book’s sentence. Without terminal_visibility, the terminal-only admissible set is not valid.

8. What ordinary pivot fan-order does prove
There is one useful monotonicity that is true, but it controls only the first-edge supports.
Strict convexity gives the cyclic tangent order around $q_2$:


$$q_3,\ q_4,\ \dots,\ q_n,\ q_1$$


in the opening direction.
Consequently, as long as the terminal support


$$[q_1,q_2,R_tq_n]$$


has not vanished, the intermediate first-edge supports remain positive:


$$[q_1,q_2,R_tq_k]>0
\qquad(3\le k<n).$$


In the notation above,


$$A_n(t)>0
\Longrightarrow
A_k(t)>0
\qquad(3\le k<n).$$


Proof idea:
At $q_2$, project every vertex $u\ne\pm q_2$ to the tangent plane


$$T_{q_2}S^2$$


by


$$\tau_{q_2}(u)
=
u-(u\cdot q_2)q_2.$$


The sign


$$[q_2,u,v]$$


is the oriented area determinant of


$$\tau_{q_2}(u),\tau_{q_2}(v).$$


Strict convexity gives the cyclic order of the tangent rays. The opening rotates all tail tangent rays rigidly. The terminal ray $R_tq_n$ is the last tail ray before the fixed head ray $q_1$. Therefore, if $R_tq_n$ has not crossed the head ray, none of $R_tq_3,\dots,R_tq_{n-1}$ has crossed it.
This proves the $A$-family implication.
But it says nothing about


$$B_i(t)=[R_tq_i,R_tq_{i+1},q_1]$$


or


$$C_k(t)=[R_tq_n,q_1,R_tq_k],\quad k\ge3.$$


Those are exactly where the counterexample fails.
So the book’s informal phrase “the tail moves away from the head” is insufficient unless upgraded to the full terminal_visibility statement.

9. Stuck-cut bookkeeping, assuming genuine terminal stuck
Now assume the terminal stuck branch really has been obtained:


$$[q_2,q_1,q_n^*]=0,
\qquad
q_n^*:=R_sq_n,$$


and all other support inequalities remain strict.
The stuck configuration is


$$(q_1,q_2,R_sq_3,\dots,R_sq_n).$$


The book replaces it by the shorter arm


$$(q_2,R_sq_3,\dots,R_sq_n).$$


Call this shorter arm


$$Y=(y_1,\dots,y_{n-1}),$$


where


$$y_1=q_2,
\qquad
y_j=R_sq_{j+1}\quad(2\le j\le n-1).$$



Lemma 9.1 — inherited tail supports
For $2\le i\le n-1$ and relevant $k$,


$$[R_sq_i,R_sq_{i+1},R_sq_k]
=
[q_i,q_{i+1},q_k].$$


These are strict by the original strict convexity of the tail portion.

Lemma 9.2 — new closing supports of the shorter arm
The new cyclic closing edge of $Y$ is


$$R_sq_n\to q_2.$$


For $3\le k\le n-1$,


$$[R_sq_n,q_2,R_sq_k]
=
[R_sq_n,R_sq_2,R_sq_k]
=
[q_n,q_2,q_k].$$


This determinant is a cyclic triple determinant of the original arm. By Lemma 2.3,


$$[q_n,q_2,q_k]>0.$$


Therefore every support for the shorter arm is strict.

Lemma 9.3 — hemisphere for the shorter arm
The shorter arm lies in an open hemisphere.
If the original hemisphere witness $h$ still contains all opened points, this is immediate.
Alternatively define


$$H_Y:=\sum_j y_j\times y_{j+1}.$$


Then


$$H_Y\cdot y_k
=
\sum_j [y_j,y_{j+1},y_k].$$


Adjacent summands vanish and all nonadjacent summands are positive by Lemmas 9.1 and 9.2. Hence


$$H_Y\cdot y_k>0$$


for all $k$.
Thus


$$Y=(q_2,R_sq_3,\dots,R_sq_n)$$


is strictly convex.

10. Betweenness extraction at the stuck triple
Terminal stuck gives collinearity:


$$[q_2,q_1,q_n^*]=0.$$


Let


$$a=q_2,\qquad b=q_1,\qquad c=q_n^*.$$


Assume


$$a\ne\pm c.$$


Set


$$\Delta:=1-(a\cdot c)^2>0.$$


Because


$$[a,b,c]=0,$$


the vector $b$ lies in the plane spanned by $a,c$:


$$b=\lambda a+\mu c.$$


The Gram coefficients are


$$\lambda
=
\frac{(b\cdot a)-(a\cdot c)(b\cdot c)}
     {1-(a\cdot c)^2},$$


and


$$\mu
=
\frac{(b\cdot c)-(a\cdot c)(b\cdot a)}
     {1-(a\cdot c)^2}.$$


Then


$$b\in \operatorname{span}_{\mathbb R_{\ge0}}\{a,c\}$$


if and only if


$$\lambda\ge0,\qquad \mu\ge0.$$


Equivalently, $q_1$ lies on the minor spherical segment from $q_2$ to $q_n^*$.
In metric form, this is


$$d(q_2,q_n^*)=
d(q_2,q_1)+d(q_1,q_n^*).$$


The determinant equality


$$[q_2,q_1,q_n^*]=0$$


alone gives only coplanarity on a common great circle. It does not decide which point lies between the other two.
So the stuck-cut needs one more branch fact:


$$q_1\in \operatorname{span}_{\mathbb R_{\ge0}}\{q_2,q_n^*\}.$$


A convenient sufficient form is the following ray lemma.

Lemma 10.1 — oriented-ray betweenness
Let $a,b,c\in S^2$, with


$$0<A<C<\pi.$$


Suppose there is a unit tangent vector $u\perp a$ such that


$$b=\cos A\,a+\sin A\,u,$$


and


$$c=\cos C\,a+\sin C\,u.$$


Then


$$b
=
\frac{\sin(C-A)}{\sin C}\,a
+
\frac{\sin A}{\sin C}\,c.$$


Both coefficients are positive. Hence


$$b\in\operatorname{span}_{\mathbb R_{\ge0}}\{a,c\}.$$


Therefore


$$b$$


lies between


$$a
\quad\text{and}\quad
c$$


on the minor great-circle arc.
Applied to


$$a=q_2,\quad b=q_1,\quad c=q_n^*,$$


this gives the betweenness needed for the stuck inequality string.
The branch information must come from the way the terminal contact is reached, or from an explicit side-length/angle hypothesis. It is not supplied by the support signs alone.

11. Equal-angle cut
Now consider the equal-angle case.
Suppose two arms $Q=(q_1,\dots,q_n)$ and $P=(p_1,\dots,p_n)$ have corresponding side lengths equal, and for some interior index $i$,


$$\angle(q_{i-1},q_i,q_{i+1})
=
\angle(p_{i-1},p_i,p_{i+1}).$$


The diagonal cut replaces


$$q_{i-1}q_i,\ q_iq_{i+1}$$


by


$$q_{i-1}q_{i+1},$$


and similarly for $P$.

Lemma 11.1 — diagonal lengths agree
By the spherical cosine rule,


$$\cos d(q_{i-1},q_{i+1})
=
\cos d(q_{i-1},q_i)\cos d(q_i,q_{i+1})$$




$$+
\sin d(q_{i-1},q_i)\sin d(q_i,q_{i+1})
\cos\angle(q_{i-1},q_i,q_{i+1}).$$


The corresponding expression for


$$d(p_{i-1},p_{i+1})$$


has the same two side lengths and the same included angle. Therefore


$$d(q_{i-1},q_{i+1})
=
d(p_{i-1},p_{i+1}),$$


assuming all relevant side lengths lie in $(0,\pi)$, so distance is recovered from its cosine.

Lemma 11.2 — convexity of the cut arms
The two cut arms are


$$Q^-=(q_1,\dots,q_{i-1},q_{i+1})$$


and


$$Q^+=(q_{i-1},q_{i+1},q_{i+2},\dots,q_n).$$


Similarly define $P^-$ and $P^+$.
For $Q^-$, all old support edges inherit their determinant signs directly.
The only new edge is


$$q_{i-1}q_{i+1}.$$


A support determinant for this new edge has the form


$$[q_{i-1},q_{i+1},q_k].$$


This is a cyclic triple determinant of the original arm $Q$. By Lemma 2.3,


$$[q_{i-1},q_{i+1},q_k]>0$$


for every relevant retained vertex $q_k$.
Therefore $Q^-$ is strictly convex.
The same argument proves $Q^+$ strictly convex. The only new edge in $Q^+$ is the same diagonal, with support determinants again inherited from cyclic triple signs of $Q$.
The $P$-cut arms are handled identically.
Thus the convexity of the smaller arms uses:


$$\text{old edge supports}
+
\text{cyclic triple signs for the new diagonal}.$$



Lemma 11.3 — which angle inequalities are inherited
Angles away from the cut are inherited unchanged.
The only vertices requiring rederivation are


$$q_{i-1}
\quad\text{and}\quad
q_{i+1}.$$


At $q_{i-1}$, convexity puts the diagonal ray $q_{i-1}q_{i+1}$ inside the old tangent cone between the rays to $q_i$ and the next retained neighbor. Thus one has the tangent-angle decomposition


$$\angle(q_{i-2},q_{i-1},q_i)
=
\angle(q_{i-2},q_{i-1},q_{i+1})
+
\angle(q_{i+1},q_{i-1},q_i).$$


At $q_{i+1}$,


$$\angle(q_i,q_{i+1},q_{i+2})
=
\angle(q_i,q_{i+1},q_{i-1})
+
\angle(q_{i-1},q_{i+1},q_{i+2}).$$


The small spherical triangles


$$(q_{i-1},q_i,q_{i+1})$$


and


$$(p_{i-1},p_i,p_{i+1})$$


are congruent by SAS, so the corner angles


$$\angle(q_{i+1},q_{i-1},q_i),
\qquad
\angle(q_i,q_{i+1},q_{i-1})$$


equal their corresponding $P$-triangle corner angles.
Therefore subtracting the same corner angle on both sides gives the required angle inequalities for the cut arms.
In determinant language, the “diagonal ray lies inside the tangent cone” facts are supplied by strict cyclic signs such as


$$[q_{i-1},q_i,q_{i+1}]>0$$


together with the neighboring cyclic triple signs involving


$$q_{i-2},q_{i-1},q_i,q_{i+1}$$


and


$$q_i,q_{i+1},q_{i+2}.$$


So the cut-corner proof uses:


$$\text{SAS for diagonal length}
+
\text{cyclic triple signs for diagonal support}
+
\text{tangent-angle additivity from ray order}.$$



12. Final dependency-ordered theorem list
Here is the full formal chain in the order I would implement it.
Block A — algebra


det3_cyclic


$$[a,b,c]=[b,c,a]=[c,a,b].$$




det3_swap


$$[a,c,b]=-[a,b,c].$$




det3_rot


$$[Ra,Rb,Rc]=[a,b,c]
\quad(R\in SO(3)).$$




mixed_inverse_head


$$[R_tq_i,R_tq_{i+1},q_1]=[q_i,q_{i+1},R_{-t}q_1].$$





Block B — convexity signs


strictConvex_supports


$$[x_i,x_{i+1},x_k]>0.$$




supportSigns_openHemisphere


$$H=\sum_i x_i\times x_{i+1},
\quad
H\cdot x_k>0.$$




strictConvex_cyclicTriple


$$i<j<k
\Longrightarrow
[x_i,x_j,x_k]>0.$$




strictConvex_subsequence
every cyclic subsequence is strictly convex.



Block C — opening support bookkeeping


opened_tail_support_invariant


$$[R_tq_i,R_tq_{i+1},R_tq_k]=[q_i,q_{i+1},q_k].$$




opened_mixed_supports_complete


The complete moving family is


$$A_k(t)=[q_1,q_2,R_tq_k],$$




$$B_i(t)=[R_tq_i,R_tq_{i+1},q_1],$$


and cyclically


$$C_k(t)=[R_tq_n,q_1,R_tq_k].$$




mixed_support_continuous
every $A_k,B_i,C_k$ is continuous.



Block D — admissibility


openedAdm_def




$$\operatorname{Adm}(u)
\Longleftrightarrow
0\le u\le T
\text{ and all mixed supports are }\ge0
\text{ on }[0,u].$$




openedAdm_convex_persistence




$$\operatorname{Adm}(u)
\Longrightarrow
X(t)\text{ weakly convex for }0\le t\le u.$$




openedAdm_closed




$$\mathcal A=\{u:\operatorname{Adm}(u)\}
\text{ is closed}.$$




openedAdm_sup_admissible




$$s=\sup\mathcal A\in\mathcal A.$$




openedReach_or_someSupport




$$s=T
\quad\text{or}\quad
\exists F\in\mathcal F_{\mathrm{mix}},\ F(s)=0.$$


This is the unconditional result.

Block E — optional terminal-first strengthening


terminal_visibility — additional required lemma/hypothesis:




$$C_{\mathrm{term}}(t)>0
\Longrightarrow
F(t)>0
\quad(F\ne C_{\mathrm{term}}).$$




openedReach_or_terminalStuck


Assuming terminal_visibility,


$$s=T
\quad\text{or}\quad
[q_2,q_1,R_sq_n]=0.$$


Without item 17, item 18 is false.

Block F — stuck cut


terminalStuck_collinear




$$[q_2,q_1,q_n^*]=0.$$




stuck_shorterArm_strictConvex




$$(q_2,R_sq_3,\dots,R_sq_n)$$


is strictly convex, using tail invariance and inherited cyclic triple signs for the new closing edge.


Gram_decomp_collinear


If


$$[a,b,c]=0,$$


then


$$b=\lambda a+\mu c$$


with


$$\lambda
=
\frac{(b\cdot a)-(a\cdot c)(b\cdot c)}
     {1-(a\cdot c)^2},$$




$$\mu
=
\frac{(b\cdot c)-(a\cdot c)(b\cdot a)}
     {1-(a\cdot c)^2}.$$




Gram_nonneg_betweenness




$$\lambda,\mu\ge0
\Longleftrightarrow
b\in\operatorname{span}_{\mathbb R_{\ge0}}\{a,c\}$$


and hence


$$d(a,c)=d(a,b)+d(b,c).$$




terminal_ray_branch


Supplies the missing nonnegativity


$$q_1\in\operatorname{span}_{\mathbb R_{\ge0}}\{q_2,q_n^*\}.$$



Block G — equal-angle cut


equalAngle_SAS_diagonal


Equal included angle and equal adjacent sides imply equal diagonal:


$$d(q_{i-1},q_{i+1})
=
d(p_{i-1},p_{i+1}).$$




diagonalCut_convex_left




$$(q_1,\dots,q_{i-1},q_{i+1})$$


is strictly convex.


diagonalCut_convex_right




$$(q_{i-1},q_{i+1},q_{i+2},\dots,q_n)$$


is strictly convex.


cutCorner_angle_subtraction_left


The only new angle inequality at $q_{i-1}$ follows by tangent-angle additivity and SAS equality of the removed small triangle.


cutCorner_angle_subtraction_right


The only new angle inequality at $q_{i+1}$ follows similarly.

13. Bottom line for OpenedArmReachOrStuck
The formally correct unconditional theorem is:


$$\boxed{
\operatorname{OpenedArmReachOrStuck}_{\mathrm{honest}}:
\quad
\text{target reached}
\ \lor\
\exists F\in\mathcal F_{\mathrm{mix}},\ F(s)=0.
}$$


The book’s desired theorem


$$\boxed{
\text{target reached}
\ \lor\
[q_2,q_1,q_n^*]=0
}$$


requires the extra lemma


$$\boxed{
\text{terminal closing support positive}
\Longrightarrow
\text{all other mixed supports positive}.
}$$


That implication is not true for a general strictly convex spherical arm. The precise obstruction is the $B_i$-family:


$$[R_tq_i,R_tq_{i+1},q_1],$$


and, in the cyclic version, also the nonterminal $C_k$-family:


$$[R_tq_n,q_1,R_tq_k].$$


These can become tight before the terminal determinant. Therefore the safe implementation path is to formalize the honest reach-or-some-support theorem, and only derive the book’s terminal stuck branch under an explicit terminal_visibility/no_nonterminal_first_tight hypothesis.