=== OPTION B FULL ANSWER (   19888 bytes) ===
The newer suffix-lift machinery already contains a usable invariant and step lemma, but it still leaves a nondegeneracy residue that strict first-edge support alone does not supply.

The theorem as restated with only


$$0<\sum_{i\in[0,n)}\rho_i\sin(\theta_i-\theta_0)$$


is still false. That condition makes the total chord nonzero and strictly left of the first edge; it does not rule out a proper suffix closing up. The suffix-lift induction in ZinanFFCT108 already found the real missing condition: every proper suffix chord must be nonzero, and its suffix argument must not be exactly antiparallel to the last edge. The file’s core_of_nondeg proves the desired < 2π bound under precisely that nondegeneracy hypothesis. ZinanFFCT108 ZinanFFCT108
0. The proposed “strict closing only” theorem is refuted by n = 6
Take


$$n=6,\qquad \theta_i=i\frac{\pi}{2},\qquad \rho_i=1.$$


Then


$$\theta_5-\theta_0=\frac{5\pi}{2}>2\pi.$$


All original hypotheses hold:


$$\theta_{m+1}-\theta_m=\frac{\pi}{2}\in(0,\pi),
\qquad
\rho_i>0.$$


The forward supports are


$$\sum_{i=a}^{j-1}\sin(\theta_i-\theta_a)
=
\sum_{r=0}^{j-a-1}\sin\left(r\frac{\pi}{2}\right).$$


For $0\le L\le6$,


$$\sum_{r=0}^{L-1}\sin\left(r\frac{\pi}{2}\right)
=
0,0,1,1,0,0,1,$$


so every forward support is nonnegative.
The backward supports are


$$-\sum_{i=j}^{a-1}\sin(\theta_i-\theta_a)
=
\sum_{r=1}^{a-j}\sin\left(r\frac{\pi}{2}\right).$$


For $0\le L\le5$,


$$\sum_{r=1}^{L}\sin\left(r\frac{\pi}{2}\right)
=
0,1,1,0,0,1,$$


so every backward support is nonnegative.
The new strict condition also holds:


$$\sum_{i=0}^{5}\sin(\theta_i-\theta_0)
=
0+1+0-1+0+1
=
1>0.$$


The “equivalent” strict last-edge form also holds:


$$-\sum_{i=0}^{4}\sin(\theta_i-\theta_5)
=
1>0.$$


But the conclusion fails.
The key degeneracy is the proper suffix chord


$$s_2=\sum_{i=2}^{5}e^{i\theta_i}
=
-1-i+1+i
=
0.$$


So strict first-edge closing only proves $s_0\ne0$, not $s_k\ne0$ for $1\le k\le n-1$. This is exactly the nondegeneracy gap isolated in ZinanFFCT108: for every 1 ≤ k ≤ n-1, one needs chord θ ρ n k ≠ 0 and ((θ (n-1) - θ k) - aang θ ρ n k) ≠ π. ZinanFFCT108
A Lean counterexample to the proposed strict-closing theorem is simpler than the n=5 rectangle counterexample:
leandef θ6 (i : ℕ) : ℝ :=  (i : ℝ) * (Real.pi / 2)def ρ6 (_i : ℕ) : ℝ :=  1
Then instantiate the proposed theorem with n := 6. The support proofs are finite interval_cases using the two tables above, and the strict closing proof is the table value 1 > 0.

1. The actually provable corrected theorem
The clean Lean-ready theorem is:
leantheorem discreteFenchelCore_of_suffix_nondeg    {n : ℕ} (θ ρ : ℕ → ℝ)    (hn : 2 ≤ n)    (hmono : ∀ m : ℕ, m + 1 ≤ n - 1 → θ m < θ (m + 1))    (hgap : ∀ m : ℕ, m + 2 ≤ n → θ (m + 1) - θ m < Real.pi)    (hpos : ∀ i : ℕ, 0 < ρ i)    (hfwd : ∀ a j : ℕ, a + 1 ≤ n → a ≤ j → j ≤ n →      0 ≤ ∑ i ∈ Finset.Ico a j, ρ i * Real.sin (θ i - θ a))    (hbwd : ∀ a j : ℕ, a + 1 ≤ n → j ≤ a →      0 ≤ - ∑ i ∈ Finset.Ico j a, ρ i * Real.sin (θ i - θ a))    (hnd : ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →      chord θ ρ n k ≠ 0 ∧      (θ (n - 1) - θ k) - aang θ ρ n k ≠ Real.pi) :    θ (n - 1) - θ 0 < 2 * Real.pi
This is already exactly core_of_nondeg in ZinanFFCT108. ZinanFFCT108
The strict first-edge closing condition may be added, but it is not used by this theorem except to prove chord θ ρ n 0 ≠ 0, which the final step can already handle by cases.

2. Definitions used by the suffix-lift induction
The repo already has these definitions:
leannoncomputable def edge (θ ρ : ℕ → ℝ) (i : ℕ) : ℂ :=  (ρ i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I)noncomputable def chord (θ ρ : ℕ → ℝ) (n j : ℕ) : ℂ :=  ∑ i ∈ Finset.Ico j n, edge θ ρ inoncomputable def wrot (θ ρ : ℕ → ℝ) (n j : ℕ) : ℂ :=  Complex.exp (-(θ j : ℂ) * Complex.I) * chord θ ρ n jnoncomputable def aang (θ ρ : ℕ → ℝ) (n j : ℕ) : ℝ :=  Complex.arg (wrot θ ρ n j)
These occur in ZinanFFCT108. ZinanFFCT108
Write


$$s_j=\operatorname{chord}(\theta,\rho,n,j)
=
\sum_{i=j}^{n-1}\rho_i e^{i\theta_i},$$




$$w_j=e^{-i\theta_j}s_j,$$




$$a_j=\arg(w_j),$$




$$\Delta_j=\theta_{n-1}-\theta_j,$$




$$b_j=\Delta_j-a_j.$$


The proof works with suffix chords, not prefix displacements. This is important: prefix-displacement range control is still false under strict first-edge closing, as shown by the n=6 example.

3. Exact induction and invariant
The induction is a downward induction on suffix index.
Equivalently, induct on


$$d=n-1-k.$$


For every $1\le k\le n-1$, prove:


$$\boxed{
0\le a_k\le\pi
}$$




$$\boxed{
a_k\le \Delta_k
}$$




$$\boxed{
b_k=\Delta_k-a_k<\pi
}$$


In Lean form:
lean∀ d k, k + d = n - 1 → 1 ≤ k →  aang θ ρ n k ∈ Set.Icc (0 : ℝ) Real.pi ∧  aang θ ρ n k ≤ θ (n - 1) - θ k ∧  (θ (n - 1) - θ k) - aang θ ρ n k < Real.pi
This is exactly the conclusion of aux_inv. ZinanFFCT108
Base case: k = n - 1
Here


$$s_{n-1}=\rho_{n-1}e^{i\theta_{n-1}},$$


so


$$w_{n-1}=e^{-i\theta_{n-1}}s_{n-1}
=
\rho_{n-1}>0.$$


Therefore


$$a_{n-1}=\arg(\rho_{n-1})=0.$$


Also


$$\Delta_{n-1}=0,
\qquad
b_{n-1}=0.$$


Thus


$$a_{n-1}\in[0,\pi],
\qquad
a_{n-1}\le \Delta_{n-1},
\qquad
b_{n-1}<\pi.$$


Lean uses chord_last, chord_last_ne, and aang_last. ZinanFFCT108

4. The induction step
Assume the invariant at j + 1, with j + 1 < n.
Set


$$\delta_j=\theta_{j+1}-\theta_j.$$


By strict monotonicity and the gap hypothesis,


$$0<\delta_j<\pi.$$


Let


$$r=\|s_{j+1}\|.$$


By the nondegeneracy hypothesis,


$$s_{j+1}\ne0,$$


so


$$r>0.$$


The key algebraic identity is:


$$w_j
=
\rho_j+r e^{i(\delta_j+a_{j+1})}.$$


This is wrot_succ. ZinanFFCT108
Define


$$\varphi_j=\delta_j+a_{j+1}.$$


The step proves the stronger package:


$$a_j\in[0,\pi],$$




$$a_j\le \Delta_j,$$




$$b_j=\Delta_j-a_j\le\pi,$$




$$a_j\le\varphi_j,$$




$$\varphi_j\le\pi.$$


In Lean, this is exactly the conclusion of step: ZinanFFCT108
leanaang θ ρ n j ∈ Set.Icc (0 : ℝ) Real.pi ∧aang θ ρ n j ≤ θ (n - 1) - θ j ∧θ (n - 1) - θ j - aang θ ρ n j ≤ Real.pi ∧aang θ ρ n j ≤ (θ (j + 1) - θ j) + aang θ ρ n (j + 1) ∧(θ (j + 1) - θ j) + aang θ ρ n (j + 1) ≤ Real.pi
Then the nondegeneracy hypothesis
lean(θ (n - 1) - θ j) - aang θ ρ n j ≠ Real.pi
upgrades


$$b_j\le\pi$$


to


$$b_j<\pi.$$


That closes the induction.

4.1 Proving φ_j ≤ π
From wrot_succ,


$$\operatorname{Im}(w_j)
=
r\sin\varphi_j.$$


But by im_rot_chord,


$$\operatorname{Im}(w_j)
=
\sum_{i=j}^{n-1}\rho_i\sin(\theta_i-\theta_j).$$


The forward support with a = j, j = n gives


$$0\le
\sum_{i=j}^{n-1}\rho_i\sin(\theta_i-\theta_j).$$


Since $r>0$,


$$0\le \sin\varphi_j.$$


Also


$$0<\varphi_j$$


because $\delta_j>0$ and $a_{j+1}\ge0$.
If $\varphi_j>\pi$, then because $\delta_j<\pi$ and $a_{j+1}\le\pi$,


$$0<\varphi_j-\pi<\pi.$$


Hence


$$\sin(\varphi_j-\pi)>0,$$


so


$$\sin\varphi_j
=
-\sin(\varphi_j-\pi)<0,$$


contradiction. Therefore


$$\varphi_j\le\pi.$$


This is the hφπ block in step. ZinanFFCT108

4.2 Cone argument: proving 0 ≤ a_j ≤ φ_j
Use the elementary lemma:
leantheorem cone_arg    (ρ r φ : ℝ)    (h0 : 0 < φ)    (hπ : φ ≤ Real.pi)    (hρ : 0 ≤ ρ)    (hr : 0 ≤ r) :    0 ≤ Complex.arg ((ρ : ℂ) + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) ∧    Complex.arg ((ρ : ℂ) + (r : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) ≤ φ
This says: a nonnegative real vector plus a vector in the cone [0, φ] has argument in [0, φ].
Apply it to


$$w_j=\rho_j+r e^{i\varphi_j}.$$


Since $\rho_j>0$, $r>0$, $0<\varphi_j$, and $\varphi_j\le\pi$,


$$0\le a_j\le \varphi_j.$$


Then, since $\varphi_j\le\pi$,


$$a_j\in[0,\pi].$$


And since


$$a_{j+1}\le \Delta_{j+1},$$


we have


$$\varphi_j
=
\delta_j+a_{j+1}
\le
\delta_j+\Delta_{j+1}
=
\theta_{j+1}-\theta_j+\theta_{n-1}-\theta_{j+1}
=
\Delta_j.$$


So


$$a_j\le\Delta_j.$$


The repo has cone_arg already. ZinanFFCT108

4.3 Proving b_j ≤ π
Now


$$b_j=\Delta_j-a_j\ge0$$


because $a_j\le\Delta_j$.
First prove


$$b_j<2\pi.$$


Using the induction hypothesis


$$b_{j+1}
=
\Delta_{j+1}-a_{j+1}
<\pi,$$


we get


$$\Delta_{j+1}<\pi+a_{j+1}.$$


Therefore


$$b_j
=
\delta_j+\Delta_{j+1}-a_j
<
\delta_j+a_{j+1}+\pi-a_j
=
\varphi_j+\pi-a_j.$$


Since


$$\varphi_j\le\pi,
\qquad
a_j\ge0,$$


we get


$$b_j<2\pi.$$


Next use the backward support at the last edge. The repo lemma im_end_chord gives:


$$\operatorname{Im}\left(e^{-i\theta_{n-1}}s_j\right)
=
-\|s_j\|\sin b_j.$$


The backward support with a = n - 1 gives


$$\sum_{i=j}^{n-1}\rho_i\sin(\theta_i-\theta_{n-1})\le0.$$


The last term is zero, so this is the same as the original backward support over [j,n-1).
Combining,


$$-\|s_j\|\sin b_j\le0.$$


Since $s_j\ne0$,


$$\|s_j\|>0,$$


so


$$0\le\sin b_j.$$


Now use the real sine range lemma:
leantheorem sin_helper    (x : ℝ)    (h0 : 0 ≤ x)    (h2 : x ≤ 2 * Real.pi)    (hs : 0 ≤ Real.sin x) :    x ≤ Real.pi ∨ x = 2 * Real.pi
Because actually $b_j<2\pi$, the second alternative is impossible. Hence


$$b_j\le\pi.$$


This is the second half of step. ZinanFFCT108
Finally, the nondegeneracy assumption excludes equality:


$$b_j\ne\pi.$$


Thus


$$b_j<\pi.$$



5. Final step at j = 0
The induction gives the invariant at k = 1:


$$a_1\in[0,\pi],
\qquad
a_1\le\Delta_1,
\qquad
b_1<\pi.$$


Then handle j = 0.
There are two cases in the existing proof.
Case 1: chord θ ρ n 0 = 0
Then


$$s_0=0.$$


From


$$s_0=e_0+s_1,$$


we get


$$s_1=-e_0.$$


Rotating by $-\theta_1$,


$$w_1
=
e^{-i\theta_1}s_1
=
-\rho_0 e^{-i(\theta_1-\theta_0)}.$$


Since


$$0<\delta_0=\theta_1-\theta_0<\pi,$$


the argument is


$$a_1=\pi-\delta_0.$$


Then


$$b_1
=
\theta_{n-1}-\theta_1-a_1
=
\theta_{n-1}-\theta_1-(\pi-\delta_0)
=
\theta_{n-1}-\theta_0-\pi.$$


The invariant gives


$$b_1<\pi,$$


so


$$\theta_{n-1}-\theta_0-\pi<\pi,$$


hence


$$\theta_{n-1}-\theta_0<2\pi.$$


This is the closed-case branch in core_of_nondeg. ZinanFFCT108
Under the strict first-edge condition, this case is impossible, because im_rot_chord gives


$$\operatorname{Im}(e^{-i\theta_0}s_0)
=
\sum_{i=0}^{n-1}\rho_i\sin(\theta_i-\theta_0)>0.$$


If $s_0=0$, the left side is zero. Contradiction.
But core_of_nondeg does not need this strict condition; it proves the branch directly.
Case 2: chord θ ρ n 0 ≠ 0
Apply step at j = 0.
It gives


$$a_0\in[0,\pi],$$




$$b_0=\theta_{n-1}-\theta_0-a_0\le\pi,$$


and


$$a_0\le\varphi_0
=
\theta_1-\theta_0+a_1
\le\pi.$$


Therefore


$$\theta_{n-1}-\theta_0
=
a_0+b_0
\le
2\pi.$$


To prove strictness, argue by contradiction. Suppose


$$2\pi\le\theta_{n-1}-\theta_0.$$


Since $a_0\le\pi$ and $b_0\le\pi$, and their sum is at least $2\pi$, both must be equalities:


$$a_0=\pi,
\qquad
b_0=\pi.$$


Because


$$a_0\le\varphi_0\le\pi,$$


we also get


$$\varphi_0=\pi.$$


Thus


$$\theta_1-\theta_0+a_1=\pi,$$


so


$$a_1=\pi-(\theta_1-\theta_0).$$


Then


$$b_1
=
\theta_{n-1}-\theta_1-a_1
=
\theta_{n-1}-\theta_1-\pi+\theta_1-\theta_0
=
\theta_{n-1}-\theta_0-\pi.$$


Since


$$2\pi\le\theta_{n-1}-\theta_0,$$


we get


$$\pi\le b_1,$$


contradicting the induction invariant


$$b_1<\pi.$$


Hence


$$\theta_{n-1}-\theta_0<2\pi.$$


This is the open-case branch of core_of_nondeg. ZinanFFCT108

6. Why strict first-edge closing does not give the needed nondegeneracy
The strict condition


$$0<
\sum_{i=0}^{n-1}\rho_i\sin(\theta_i-\theta_0)$$


gives only:


$$s_0\ne0.$$


Lean lemma:
leanlemma chord_zero_ne_of_strict_first    (hstrict0 :      0 < ∑ i ∈ Finset.Ico 0 n,        ρ i * Real.sin (θ i - θ 0)) :    chord θ ρ n 0 ≠ 0 := by  intro hzero  have him := im_rot_chord θ ρ n 0 0  -- him :  -- (Complex.exp (-(θ 0 : ℂ) * Complex.I) * chord θ ρ n 0).im  --   = ∑ i ∈ Finset.Ico 0 n, ρ i * Real.sin (θ i - θ 0)  rw [hzero] at him  simp at him  linarith
It does not prove


$$s_k\ne0
\qquad
(1\le k\le n-1).$$


The n = 6 counterexample has


$$s_2=0$$


but satisfies strict first-edge closing.
It also does not prove


$$b_k\ne\pi.$$


The suffix induction needs both for every 1 ≤ k ≤ n - 1. This is the exact DiscreteFenchelNondeg residue in ZinanFFCT108. ZinanFFCT108

7. A geometric hypothesis that does imply the suffix nondegeneracy
A usable planar strengthening is:
lean(hsuffix_ne : ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →  chord θ ρ n k ≠ 0)(hfinal_strict : ∀ k : ℕ, 1 ≤ k → k ≤ n - 2 →  0 < - ∑ i ∈ Finset.Ico k (n - 1),    ρ i * Real.sin (θ i - θ (n - 1)))
Then hnd follows.
7.1 First half of hnd
Immediate:
leanexact (hsuffix_ne k hk1 hkn).1
or, with the statement above:
leanhave hchord : chord θ ρ n k ≠ 0 :=  hsuffix_ne k hk1 hkn
7.2 Second half of hnd
Suppose


$$b_k=(\theta_{n-1}-\theta_k)-a_k=\pi.$$


By im_end_chord,


$$\sum_{i=k}^{n-1}\rho_i\sin(\theta_i-\theta_{n-1})
=
-\|s_k\|\sin b_k.$$


If $b_k=\pi$, then


$$\sin b_k=0,$$


so


$$\sum_{i=k}^{n-1}\rho_i\sin(\theta_i-\theta_{n-1})=0.$$


The final term is zero:


$$\rho_{n-1}\sin(\theta_{n-1}-\theta_{n-1})=0.$$


Therefore


$$\sum_{i=k}^{n-2}\rho_i\sin(\theta_i-\theta_{n-1})=0.$$


But hfinal_strict says


$$0<
-\sum_{i=k}^{n-2}\rho_i\sin(\theta_i-\theta_{n-1}),$$


equivalently


$$\sum_{i=k}^{n-2}\rho_i\sin(\theta_i-\theta_{n-1})<0.$$


Contradiction.
Lean skeleton:
leanlemma hnd_of_suffix_ne_and_final_strict    (hsuffix_ne : ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →      chord θ ρ n k ≠ 0)    (hfinal_strict : ∀ k : ℕ, 1 ≤ k → k ≤ n - 2 →      0 < - ∑ i ∈ Finset.Ico k (n - 1),        ρ i * Real.sin (θ i - θ (n - 1))) :    ∀ k : ℕ, 1 ≤ k → k ≤ n - 1 →      chord θ ρ n k ≠ 0 ∧      (θ (n - 1) - θ k) - aang θ ρ n k ≠ Real.pi := by  intro k hk1 hkn  refine ⟨hsuffix_ne k hk1 hkn, ?_⟩  intro hbpi  by_cases hk_last : k = n - 1  · subst hk_last    -- b_{n-1} = 0 by aang_last, contradict π    have ha : aang θ ρ n (n - 1) = 0 :=      aang_last θ ρ n (by omega) (hpos (n - 1))    rw [ha] at hbpi    nlinarith [Real.pi_pos]  · have hk_n2 : k ≤ n - 2 := by omega    have hstrict := hfinal_strict k hk1 hk_n2    have him := im_end_chord θ ρ n k    -- rewrite the LHS by im_rot_chord with a = n-1    rw [im_rot_chord θ ρ n k (n - 1)] at him    have hsum_zero :        ∑ i ∈ Finset.Ico k n,          ρ i * Real.sin (θ i - θ (n - 1)) = 0 := by      have hnormpos : 0 < ‖chord θ ρ n k‖ :=        norm_pos_iff.mpr (hsuffix_ne k hk1 hkn)      rw [hbpi, Real.sin_pi, mul_zero, neg_zero] at him      exact him.symm    have hsplit :        ∑ i ∈ Finset.Ico k n,          ρ i * Real.sin (θ i - θ (n - 1))        =        ∑ i ∈ Finset.Ico k (n - 1),          ρ i * Real.sin (θ i - θ (n - 1)) := by      rw [show n = (n - 1) + 1 by omega]      rw [Finset.sum_Ico_succ_top (by omega : k ≤ n - 1)]      rw [sub_self, Real.sin_zero, mul_zero, add_zero]    rw [hsplit] at hsum_zero    linarith
Then the final theorem is one line:
leanexact core_of_nondeg n θ ρ hn hmono hgap hpos hfwd hbwd  (hnd_of_suffix_ne_and_final_strict hpos hsuffix_ne hfinal_strict)
This is the strongest Lean-friendly route: no polygonal Umlaufsatz is needed.

8. What the spherical/opened-arm side must supply
The currently wired opened-WBS planar residue supplies only weak global supports, nonzero cyclic edges, and strict positive consecutive turns. That is visible in OpenedWBSPlanarLiftedTurnSpanExists: it assumes ∀ i j, 0 ≤ det3 (Q i) (Q (i+1)) (Q j), nonzero cyclic edges, and strict consecutive triples. ZinanFFCT97
In openedWBS_gnomonicSingleWind, the gnomonic image obtains exactly weak supports from WeakConvexSphArm and strict consecutive turns from positive joints. ZinanFFCT97
So the statement

an open strictly-convex spherical arm supplies
$0<\sum_{i\in[0,n)}\rho_i\sin(\theta_i-\theta_0)$

is true only if the endpoint $Q_n$ is known to be a strictly nonincident vertex for the first support line:


$$0<\det(Q_0,Q_1,Q_n).$$


That is a stronger geometric fact than the current weak support premise.
In the real sine formulation,


$$\det(Q_0,Q_1,Q_n)>0$$


is exactly


$$0<
\rho_0
\sum_{i=0}^{n-1}
\rho_i\sin(\theta_i-\theta_0)$$


up to the positive frame factor. Since $\rho_0>0$, this gives the strict first-edge condition.
But this still does not imply the suffix nondegeneracy needed by the suffix proof. For that, the spherical side should supply at least:


no nonadjacent endpoint repeats in the gnomonic chain:


$$Q_k\ne Q_n
\quad\text{for }1\le k\le n-1,$$


which gives chord θ ρ n k ≠ 0;


strict final-edge support for every interior earlier vertex:


$$0<\det(Q_{n-1},Q_n,Q_k)
\quad\text{for }1\le k\le n-2,$$


which gives


$$0<
-\sum_{i=k}^{n-2}
\rho_i\sin(\theta_i-\theta_{n-1}).$$




Those two facts imply DiscreteFenchelNondeg, and then core_of_nondeg proves the turn bound.
So the spherical task should not be phrased as “prove only strict closing at the first edge.” It should be:
lean-- From strict opened spherical convexity / no-repeat:∀ k, 1 ≤ k → k ≤ n - 1 → chord θ ρ n k ≠ 0-- From strict final-edge support:∀ k, 1 ≤ k → k ≤ n - 2 →  0 < - ∑ i ∈ Finset.Ico k (n - 1),    ρ i * Real.sin (θ i - θ (n - 1))
Then the analytic residue is gone.

9. Key Lean lemmas needed
Most of these already exist in ZinanFFCT108.
Existing complex/suffix lemmas
leanedgechordwrotaang
Definitions of the edge vector, suffix chord, rotated suffix chord, and principal argument. ZinanFFCT108
leanchord_succchord_lastchord_last_nenorm_wrotchord_polaraang_last
Basic suffix-chord identities and the base case. ZinanFFCT108
leanim_rot_chord
The identity


$$\operatorname{Im}(e^{-i\theta_a}s_j)
=
\sum_{i=j}^{n-1}\rho_i\sin(\theta_i-\theta_a).$$


ZinanFFCT108
leanim_end_chord
The identity


$$\operatorname{Im}(e^{-i\theta_{n-1}}s_j)
=
-\|s_j\|\sin((\theta_{n-1}-\theta_j)-a_j).$$


ZinanFFCT108
leanwrot_succ
The recurrence


$$w_j=\rho_j+\|s_{j+1}\|e^{i(\theta_{j+1}-\theta_j+a_{j+1})}.$$


ZinanFFCT108
leancone_arg
Argument of a vector in the cone. ZinanFFCT108
leansin_helper
If $x\in[0,2\pi]$ and $\sin x\ge0$, then $x\le\pi$ or $x=2\pi$. ZinanFFCT108
leanstepaux_invarg_neg_expcore_of_nondeg
The induction step, downward induction, closed-case argument calculation, and final theorem. ZinanFFCT108 ZinanFFCT108
New small lemmas to add
leanlemma chord_zero_ne_of_strict_first    (hstrict0 :      0 < ∑ i ∈ Finset.Ico 0 n,        ρ i * Real.sin (θ i - θ 0)) :    chord θ ρ n 0 ≠ 0
This is useful but not enough.
leanlemma hnd_of_suffix_ne_and_final_strict    (hpos : ∀ i, 0 < ρ i)    (hsuffix_ne : ∀ k, 1 ≤ k → k ≤ n - 1 →      chord θ ρ n k ≠ 0)    (hfinal_strict : ∀ k, 1 ≤ k → k ≤ n - 2 →      0 < - ∑ i ∈ Finset.Ico k (n - 1),        ρ i * Real.sin (θ i - θ (n - 1))) :    ∀ k, 1 ≤ k → k ≤ n - 1 →      chord θ ρ n k ≠ 0 ∧      (θ (n - 1) - θ k) - aang θ ρ n k ≠ Real.pi
Then:
leantheorem discreteFenchelCore_of_strict_final_support    ...    (hsuffix_ne : ∀ k, 1 ≤ k → k ≤ n - 1 →      chord θ ρ n k ≠ 0)    (hfinal_strict : ∀ k, 1 ≤ k → k ≤ n - 2 →      0 < - ∑ i ∈ Finset.Ico k (n - 1),        ρ i * Real.sin (θ i - θ (n - 1))) :    θ (n - 1) - θ 0 < 2 * Real.pi :=by  exact core_of_nondeg n θ ρ hn hmono hgap hpos hfwd hbwd    (hnd_of_suffix_ne_and_final_strict hpos hsuffix_ne hfinal_strict)
That is the Lean-transcribable analytic closure. The strict first-edge closing condition alone is not a valid corrected theorem.

I’ll first isolate the strict-closing counterexample, then state the sufficient closed/strict support package and connect it to the suffix-lift machinery and spherical provenance.

One
(background)
