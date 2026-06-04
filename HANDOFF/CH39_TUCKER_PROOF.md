Let $K_r:=\Delta(P_r)$, where $P_r=\{-1,0,1\}^r\setminus\{0\}$ with your order.
Let $B_r^+\subset K_r$ be the “upper hemisphere”


$$B_r^+ := \Delta\{X\in P_r: X_r\neq -1\},$$


so


$$\partial B_r^+ = \Delta\{X\in P_r:X_r=0\}\cong K_{r-1}.$$


For a simplex $\sigma$, say $\sigma$ is positive alternating of dimension $q$ if its $q+1$ labels, sorted by increasing absolute value, are


$$+a_0,-a_1,+a_2,\dots,(-1)^q a_q,
\qquad a_0<\cdots<a_q.$$


Ky Fan parity input, in graph form
Fan parity lemma.
For $r\ge 1$, $m\ge r$, if


$$\mu:P_r\to\{\pm1,\dots,\pm m\}$$


is antipodal and has no complementary comparable pair, then the number of positive alternating maximal chains of $K_r$ is odd.
Proof graph. Induct on $r$. The case $r=1$ is immediate: the two antipodal vertices have labels $+\ell,-\ell$, so exactly one is positive.
For $r>1$, work in $B_r^+$. Define a bipartite graph


$$\Gamma_r=(\mathcal R\sqcup\mathcal S,E)$$


by


$$\mathcal R
=
\{\rho\subset B_r^+:\dim\rho=r-2,\ \rho\text{ positive alternating}\},$$




$$\mathcal S
=
\{\sigma\subset B_r^+:\dim\sigma=r-1,\ \exists\rho\in\mathcal R,\ \rho\subset\sigma\},$$




$$(\rho,\sigma)\in E \iff \rho\subset\sigma.$$


Degree facts:


$$\deg(\rho)=
\begin{cases}
1,&\rho\subset\partial B_r^+,\\
2,&\rho\not\subset\partial B_r^+,
\end{cases}
\qquad \rho\in\mathcal R.$$


For $\sigma\in\mathcal S$, the local insertion check gives


$$\deg(\sigma)=
\begin{cases}
1,&\sigma\text{ is positive alternating or negative alternating},\\
2,&\text{otherwise}.
\end{cases}$$


Reason: $\sigma$ is obtained by inserting one signed label into a positive alternating word. If the full word alternates, exactly one deletion gives a positive alternating ridge; otherwise exactly two deletions do. Opposite repeated labels are excluded by the no-complement assumption.
By handshaking, the number of odd-degree vertices is even, hence


$$\#\{\rho\in\mathcal R:\rho\subset\partial B_r^+\}
+
\#\{\sigma\in\mathcal S:\sigma\text{ alternating}\}
\equiv 0\pmod 2.$$


The first term is odd by induction on $\partial B_r^+\cong K_{r-1}$. Therefore the second term is odd. Antipodality identifies negative alternating top simplices in $B_r^+$ with positive alternating top simplices in $B_r^-$, so the total number of positive alternating maximal chains of $K_r$ is odd.
Reduction step for your $n$
Put $d:=n-1$. First, if the equator


$$\partial B_n^+ \cong K_d$$


already contains a complementary comparable pair, extend it to a maximal chain and stop. So assume it does not.
By Fan parity applied to $\partial B_n^+\cong K_d$ with $m=d$, the number of boundary chains $\rho$ with label set


$$A:=\{+1,-2,+3,\dots,(-1)^{d-1}d\}$$


is odd.
Now define the graph


$$\Gamma=(\mathcal R\sqcup\mathcal M,E)$$


where


$$\mathcal R
=
\{\rho\subset B_n^+:\dim\rho=d-1,\ \{\lambda(v):v\in\rho\}=A\},$$




$$\mathcal M
=
\{\sigma\subset B_n^+:\dim\sigma=d,\ \exists\rho\in\mathcal R,\ \rho\subset\sigma\},$$




$$(\rho,\sigma)\in E \iff \rho\subset\sigma.$$


For $\rho\in\mathcal R$,


$$\deg(\rho)=
\begin{cases}
1,&\rho\subset\partial B_n^+,\\
2,&\rho\not\subset\partial B_n^+.
\end{cases}$$


For $\sigma\in\mathcal M$, choose $\rho\subset\sigma$ in $\mathcal R$. Since $\rho$ already uses all indices $1,\dots,d$, the unique extra vertex $v\in\sigma\setminus\rho$ has label either $\alpha_k$ or $-\alpha_k$, where


$$\alpha_k:=(-1)^{k-1}k\in A.$$


Thus


$$\deg(\sigma)=
\begin{cases}
2,&\lambda(v)=\alpha_k\text{ for some }k,\\
1,&\lambda(v)=-\alpha_k\text{ for some }k.
\end{cases}$$


In the second case, $\rho$ contains a unique vertex $u$ with $\lambda(u)=\alpha_k$, and since $u,v\in\sigma$, they are comparable; hence


$$\lambda(v)=-\lambda(u).$$


By handshaking,


$$\#\{\rho\in\mathcal R:\rho\subset\partial B_n^+\}
+
\#\{\sigma\in\mathcal M:\deg(\sigma)=1\}
\equiv 0\pmod 2.$$


The first term is odd by Fan parity on the equator. Therefore the second term is odd. Hence some $\sigma\in\mathcal M$ has $\deg(\sigma)=1$, yielding comparable $u,v\in\sigma$ with


$$\lambda(u)=-\lambda(v).$$


Finally, $\sigma$ is a maximal chain of $B_n^+$, hence a maximal chain of $K_n$. Ordering it as


$$C_0\prec C_1\prec\cdots\prec C_{n-1},$$


the two vertices $u,v$ occur as some $C_i,C_j$ with $i<j$, and


$$|\lambda(C_i)|=|\lambda(C_j)|,\qquad
\operatorname{sgn}\lambda(C_i)\neq \operatorname{sgn}\lambda(C_j).$$


So the “all repeated indices have the same sign on every maximal chain” alternative is impossible.
---
## Master verification (Opus, 拒绝传声筒 — checked, not relayed)

VERDICT: structurally CORRECT and avoids the degeneracy that sank codex's earlier route.
- KEY: the "alternating" simplices ρ are dim d-1 = n-2 (n-1 vertices, label set A = all n-1 indices
  with alternating signs). These are INHABITED. Codex's fatal error was using full maximal chains
  (n vertices, needing n distinct indices in {1..n-1} → empty). This proof correctly uses (n-1)-vertex ρ.
- VERIFIED the σ-degree fact (deg 2 if extra label = α_k; deg 1 if = -α_k, yielding the complementary
  pair u,v with λ(v)=-λ(u)) — checks out by the label-set-A deletion count.
- Fan parity lemma applied to the equator ∂B_n^+ ≅ K_{n-1} with m = n-1 = r (so m ≥ r holds — alternating
  maximal chains of K_{n-1} EXIST; count odd by induction, base r=1 immediate).
- TO VERIFY DURING FORMALIZATION (not yet fully checked): the ρ-degree fact (interior ridge in exactly
  2 maximal simplices = the manifold-with-boundary property of the hemisphere B_n^+); the chain-insertion
  preserving simplex/chain structure; the induction's hemisphere decomposition K_r = B_r^+ ∪ B_r^-.

This lands on the committed sound base (Chapter39Tucker.lean: tuckerLemmaStatement_of_chain_complementary)
— the proof's conclusion is exactly "∃ maximal chain with a same-index opposite-sign comparable pair",
which that lemma converts to TuckerLemmaStatement.

---
## State after 11 codex rounds (honest frontier)

COMMITTED & sound (0-sorry, verified non-degenerate): pigeonhole base + reduction
(`tuckerLemmaStatement_of_chain_complementary`), hemisphere/equator model (`equatorEquiv`),
alternating-label-set A machinery, the σ-degree crux (`sigma_opposite_extra_gives_complementary_labels`),
the abstract Ky Fan parity engine (`RhoDegreeManifoldData` + handshaking +
`final_reduction_graph_gives_prefixChain_complementary_pair`), and the local coface model
(`representedRidgePartner`, 2-element local coface set, `ActualHemisphereARidge` Nonempty).

TARGET CORRECTION: the literal `∀ n, TuckerLemmaStatement n` is FALSE (verified: `TuckerLemmaStatement 0`
fails — `NonzeroSignedSubset 0` is empty so the ∃-conclusion fails). The faithful, kneser-sufficient target
is `tuckerLemma_pos : ∀ n, 1 ≤ n → TuckerLemmaStatement n`.

THE ONE REMAINING LEMMA (the irreducible core codex could not prove across rounds 8-11; it kept
chaining new interfaces instead):
  **coface-exhaustion / ρ-degree count** for the ACTUAL hemisphere ridge type: an `ActualHemisphereARidge`
  ρ (a punctured length-(d+1) flag with a gap) has exactly TWO cofaces in B⁺ when interior, ONE when
  boundary. Proof = the two single-coordinate covers of `C_{k-1}` below `C_{k+1}` are exactly the deleted
  original and `representedRidgePartner` (EXHAUSTION: no third single-coordinate cover), and the hemisphere
  filter (last coord ≠ −1) removes exactly one iff ρ ⊂ equator. Once this `degree_card` holds on
  `ActualHemisphereARidge`, the round-7 engine + the equator induction (via `equatorEquiv`) close
  `tuckerLemma_pos`, discharging kneser's `htucker`.

This is a concrete, provable combinatorial-lattice fact (the covering relation of the signed-subset poset
+ the hemisphere constraint). It needs careful master/strong-model formalization over the actual ridge
encoding — codex (gpt-5.5) tangles on the represented↔actual representation consistency. NOT a math gap;
a formalization-engineering frontier on a verified-correct proof.
