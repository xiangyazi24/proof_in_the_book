I’ll give the proof in the exact Gurvits form, but one constant in your prompt needs correction: the capacity reduction factor is $\bigl((k-1)/k\bigr)^{k-1}$, not $(k-1)^{k-1}/k^k$. The latter would telescope to $1/n^n$, missing the factorial.

You are right about the overall Gurvits route, but the reduction constant should be


$$G(k)=\left(\frac{k-1}{k}\right)^{k-1}$$


with $G(1)=1$, not $(k-1)^{k-1}/k^k$.
The latter misses a factor $k$.

1. Capacity
For a homogeneous polynomial $p\in \mathbb R[x_1,\dots,x_m]$ of total degree $m$,


$$\operatorname{Cap}(p)
=
\inf_{x_i>0}
\frac{p(x)}{x_1x_2\cdots x_m}.$$


Lean-friendly version:
leandef PosVec (m : Nat) := {x : Fin m → ℝ // ∀ i, 0 < x i}def prodCoord (x : Fin m → ℝ) : ℝ :=  ∏ i, x idef capacity (p : MvPolynomial (Fin m) ℝ) : ℝ :=  sInf {r : ℝ | ∃ x : PosVec m, r = eval x.val p / prodCoord x.val}
But for formalization, avoid sInf as long as possible. Use a lower-bound predicate:
leandef CapLB (p : MvPolynomial (Fin m) ℝ) (C : ℝ) : Prop :=  ∀ x : Fin m → ℝ,    (∀ i, 0 < x i) →    C * (∏ i, x i) ≤ eval x p
Then:
leanCapLB p C  ↔  C ≤ capacity p
under the usual nonempty/bounded-below conditions.
For Gurvits, prove everything with CapLB.

2. Stability input
A polynomial $p$ is real stable if


$$p(z_1,\dots,z_m)\ne 0$$


whenever all $z_i$ have positive imaginary part.
For the row-linear polynomial


$$p_A(x)=\prod_{i=1}^n \sum_j A_{ij}x_j$$


with $A_{ij}\ge0$, each linear form has positive imaginary part on the upper half-plane, hence is nonzero. Therefore $p_A$ is stable.
Needed closure lemmas:
leanlemma stable_of_nonneg_linear_productlemma stable_specialize_zerolemma stable_partial_derivative
The reduction uses:


$$q(x_1,\dots,x_{m-1})
=
\left.\frac{\partial p}{\partial x_m}\right|_{x_m=0}.$$


Stability of $q$ follows from derivative + specialization closure.

3. Single-variable Gurvits lemma
This is the analytic crux.
Let


$$R(t)=a_0+a_1t+\cdots+a_kt^k$$


have nonnegative coefficients and all roots real and nonpositive. Then:


$$a_1
\ge
G(k)\inf_{t>0}\frac{R(t)}{t},
\qquad
G(k)=\left(\frac{k-1}{k}\right)^{k-1}.$$


For $k=1$, $G(1)=1$.
Proof for $k\ge2$:
Since $R$ has nonnegative coefficients and real nonpositive roots,


$$R(t)=R(0)\prod_{\ell=1}^k(1+\lambda_\ell t)$$


with $\lambda_\ell\ge0$, padding with $\lambda_\ell=0$ if needed.
Then


$$a_1=R'(0)=R(0)\sum_\ell\lambda_\ell.$$


Let


$$S=\sum_\ell\lambda_\ell.$$


By AM-GM,


$$\prod_{\ell=1}^k(1+\lambda_\ell t)
\le
\left(1+\frac{St}{k}\right)^k.$$


Hence


$$\frac{R(t)}t
\le
R(0)\frac{(1+St/k)^k}{t}.$$


Choose


$$t=\frac{k}{S(k-1)}.$$


Then


$$\inf_{t>0}\frac{R(t)}t
\le
a_1\left(\frac{k}{k-1}\right)^{k-1}.$$


Therefore


$$a_1
\ge
\left(\frac{k-1}{k}\right)^{k-1}
\inf_{t>0}\frac{R(t)}t.$$


Lean lemma:
leanlemma univariate_gurvits  (R : Polynomial ℝ)  (hk : R.natDegree ≤ k)  (hcoeff_nonneg : ∀ i, 0 ≤ R.coeff i)  (hrealrooted : all_roots_real_nonpos R)  (h1 : 1 ≤ k) :  coeff R 1 ≥ G k * sInf {y | ∃ t > 0, y = R.eval t / t}
Better lower-bound form:
leanlemma univariate_gurvits_LB  (R : Polynomial ℝ)  (hk : R.natDegree ≤ k)  (hcoeff_nonneg : ∀ i, 0 ≤ R.coeff i)  (hrealrooted : all_roots_real_nonpos R)  (C : ℝ)  (hC : ∀ t > 0, C * t ≤ R.eval t) :  G k * C ≤ R.coeff 1
This avoids sInf.

4. Capacity reduction step
Let $p$ be homogeneous stable of degree $m$ in $m$ variables, with nonnegative coefficients. Suppose


$$\deg_{x_m}(p)\le k.$$


Define


$$q(x_1,\dots,x_{m-1})
=
\left.\frac{\partial p}{\partial x_m}\right|_{x_m=0}.$$


Then


$$\operatorname{Cap}(q)
\ge
G(k)\operatorname{Cap}(p).$$


Lean lower-bound version:
leantheorem gurvits_capacity_step_LB  (p : MvPolynomial (Fin m) ℝ)  (q : MvPolynomial (Fin (m-1)) ℝ)  (hp_stable : RealStable p)  (hp_nonneg : CoeffNonneg p)  (hp_hom : Homogeneous p m)  (hdeg : degreeOf p (last m) ≤ k)  (hq : q = reduceLastByDerivative p)  (hC : CapLB p C) :  CapLB q (G k * C)
Proof:
Fix $x_1,\dots,x_{m-1}>0$. Define


$$R(t)=p(x_1,\dots,x_{m-1},t).$$


Then:


$R$ has nonnegative coefficients.


$\deg R\le k$.


Stability of $p$ implies $R$ has only real nonpositive roots.


Since CapLB p C,




$$C\cdot x_1\cdots x_{m-1}\cdot t
\le
R(t)$$


for all $t>0$.
Apply the single-variable lemma:


$$G(k)\,C\,x_1\cdots x_{m-1}
\le
R'(0).$$


But


$$R'(0)=q(x_1,\dots,x_{m-1}).$$


Thus


$$\operatorname{Cap}(q)\ge G(k)C.$$



5. Iteration
Start with


$$p_n=p_A.$$


For $m=n,n-1,\dots,2$, define


$$p_{m-1}
=
\left.\frac{\partial p_m}{\partial x_m}\right|_{x_m=0}.$$


Then $p_m$ is homogeneous stable of degree $m$ in $m$ variables.
Since total degree is $m$,


$$\deg_{x_m}(p_m)\le m.$$


Therefore:


$$\operatorname{Cap}(p_{m-1})
\ge
G(m)\operatorname{Cap}(p_m).$$


So


$$\operatorname{Cap}(p_1)
\ge
\operatorname{Cap}(p_n)\prod_{m=2}^n G(m).$$


Now


$$G(m)=\left(\frac{m-1}{m}\right)^{m-1}.$$


Thus


$$\prod_{m=2}^nG(m)
=
\prod_{m=2}^n
\frac{(m-1)^{m-1}}{m^{m-1}}
=
\frac{n!}{n^n}.$$


Lean lemma:
leanlemma gurvits_product_telescopes :  (∏ m in Finset.Icc 2 n, G m) = (Nat.factorial n : ℝ) / (n : ℝ)^n

6. Final coefficient identification
After all reductions,


$$p_1(x_1)=c\,x_1,$$


where


$$c=[x_1x_2\cdots x_n]p.$$


So:


$$\operatorname{Cap}(p_1)=c.$$


Therefore:


$$[x_1x_2\cdots x_n]p
\ge
\operatorname{Cap}(p)\frac{n!}{n^n}.$$


If $\operatorname{Cap}(p)\ge1$, then


$$[x_1x_2\cdots x_n]p
\ge
\frac{n!}{n^n}.$$


For $p=p_A$, the squarefree coefficient is exactly


$$\operatorname{perm}(A).$$



7. Final theorem
leantheorem gurvits_core  {n : Nat}  (hn : 1 ≤ n)  (p : MvPolynomial (Fin n) ℝ)  (hp_stable : RealStable p)  (hp_nonneg : CoeffNonneg p)  (hp_hom : Homogeneous p n)  (hcap : CapLB p 1) :  ((p.coeff (squarefreeMonomial n)) : ℝ)    ≥ (Nat.factorial n : ℝ) / (n : ℝ)^n
Specialized to row-linear products:
leantheorem van_der_waerden_core  {n : Nat}  (hn : 3 ≤ n)  (A : Matrix (Fin n) (Fin n) ℝ)  (hA_nonneg : ∀ i j, 0 ≤ A i j)  (hcap : CapLB (rowLinearProduct A) 1) :  permanent A ≥ (Nat.factorial n : ℝ) / (n : ℝ)^n

Lemma dependency order
lean-- capacitydef CapLBdef capacitylemma CapLB_iff_le_capacity-- polynomial classesdef CoeffNonnegdef RealStabledef Homogeneouslemma rowLinearProduct_coeff_nonneglemma rowLinearProduct_stablelemma rowLinearProduct_homogeneous-- univariate root structuredef all_roots_real_nonposlemma stable_specialization_univariate_realrootedlemma realrooted_nonneg_factorizationlemma amgm_product_boundlemma univariate_gurvits_LB-- reduction operatordef reduceLastByDerivativelemma reduceLast_coeff_nonneglemma reduceLast_homogeneouslemma reduceLast_stablelemma reduceLast_eval_eq_deriv_eval-- capacity steplemma gurvits_capacity_step_LB-- iterationdef iteratedReductionlemma iteratedReduction_stablelemma iteratedReduction_coeff_nonneglemma iteratedReduction_homogeneouslemma iteratedReduction_cap_bound-- constantsdef Glemma G_onelemma G_monotone_antitonelemma G_deg_le_total :  d ≤ m → G m ≤ G dlemma gurvits_product_telescopes-- final coefficientlemma iteratedReduction_final_coeff_squarefreelemma univariate_capacity_eq_coeff-- core theoremtheorem gurvits_core-- permanent specializationlemma rowLinearProduct_squarefreeCoeff_eq_permtheorem van_der_waerden_core
Only the following parts need real analysis:
leancapacity / sInfunivariate_gurvits_LBstable_specialization_univariate_realrooted
Everything after gurvits_capacity_step_LB is finite algebra and induction.