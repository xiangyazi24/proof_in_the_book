import Mathlib
import ProofsInTheBook.Chapter22

/-!
# Real-stable polynomials (toward Chapter 22, Gurvits capacity)

A real multivariate polynomial is **real-stable** if it has no zero with all variables in the
open upper half-plane. This is the polynomial class underlying Gurvits's capacity proof. Here we
build the definition and the closure properties that are elementary (product closure, stability of
nonnegative linear forms — hence of the row-linear product `∏ rows`). The hard remaining closure
(`∂/∂xₘ` preserves real-stability — the Lieb–Sokal lemma) is isolated as `DerivPreservesStable`.
-/

namespace ProofsInTheBook.Chapter22Stable

open MvPolynomial

/-- A real multivariate polynomial is real-stable if it is nonzero whenever every variable lies
in the open upper half-plane. -/
def RealStable {m : ℕ} (p : MvPolynomial (Fin m) ℝ) : Prop :=
  ∀ z : Fin m → ℂ, (∀ i, 0 < (z i).im) →
    MvPolynomial.eval z (p.map (algebraMap ℝ ℂ)) ≠ 0

/-- The product of real-stable polynomials is real-stable. -/
lemma RealStable.mul {m : ℕ} {p q : MvPolynomial (Fin m) ℝ}
    (hp : RealStable p) (hq : RealStable q) : RealStable (p * q) := by
  intro z hz
  rw [map_mul, map_mul]
  exact mul_ne_zero (hp z hz) (hq z hz)

/-- A nonempty finite product of real-stable polynomials is real-stable. -/
lemma RealStable.prod {m : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → MvPolynomial (Fin m) ℝ} (hf : ∀ i ∈ s, RealStable (f i)) :
    RealStable (∏ i ∈ s, f i) := by
  intro z hz
  rw [map_prod, map_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun i hi => hf i hi z hz)

/-- A nonnegative linear form `∑ⱼ Cⱼ Xⱼ` with positive total weight is real-stable: its value at
any upper-half-plane point has strictly positive imaginary part. -/
lemma linearForm_stable {m : ℕ} (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hpos : 0 < ∑ j, C j) :
    RealStable (∑ j, MvPolynomial.C (C j) * (X j : MvPolynomial (Fin m) ℝ)) := by
  intro z hz
  have hval : MvPolynomial.eval z
      ((∑ j, MvPolynomial.C (C j) * (X j : MvPolynomial (Fin m) ℝ)).map (algebraMap ℝ ℂ))
      = ∑ j, (C j : ℂ) * z j := by
    rw [map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, eval_C, eval_X]
    simp
  rw [hval]
  have him : (∑ j, (C j : ℂ) * z j).im = ∑ j, C j * (z j).im := by
    rw [Complex.im_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [Complex.mul_im]
  have hExists : ∃ j, 0 < C j := by
    by_contra h
    push_neg at h
    have : ∑ j, C j ≤ 0 := Finset.sum_nonpos (fun j _ => h j)
    linarith
  obtain ⟨j0, hj0⟩ := hExists
  have hpos' : 0 < (∑ j, (C j : ℂ) * z j).im := by
    rw [him]
    apply Finset.sum_pos'
    · intro j _; exact mul_nonneg (hC j) (le_of_lt (hz j))
    · exact ⟨j0, Finset.mem_univ j0, mul_pos hj0 (hz j0)⟩
  intro hz0
  rw [hz0] at hpos'
  simp at hpos'

/-- **The row-linear product is real-stable** (the base of the Gurvits capacity iteration): for a
nonnegative matrix with strictly positive row sums (e.g. doubly stochastic), `∏ᵢ ∑ⱼ Aᵢⱼ Xⱼ` is
real-stable. -/
lemma rowLinearMvPolynomial_realStable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, 0 < ∑ j, A i j) :
    RealStable (ProofsInTheBook.Chapter22.rowLinearMvPolynomial A) := by
  rw [ProofsInTheBook.Chapter22.rowLinearMvPolynomial]
  apply RealStable.prod
  intro i _
  exact linearForm_stable (A i) (fun j => hA i j) (hrow i)

/-!
### Univariate real-rootedness and its derivative closure (the univariate Lieb–Sokal heart)

A univariate real polynomial is real-rooted iff it splits over ℝ — equivalently its root multiset
(with multiplicity) has cardinality equal to its degree. The derivative of a real-rooted polynomial
is again real-rooted (Rolle's theorem / interlacing). This is the one-variable case of the stability
closure; the full multivariate Lieb–Sokal lemma (`∂/∂xₘ` preserves real-stability) lifts it via the
Hurwitz theorem and remains the genuine remaining analytic input for the Gurvits reduction.
-/

open Polynomial in
/-- A univariate real polynomial is real-rooted: all roots real (splits over ℝ), i.e. the root
multiset cardinality equals the degree. -/
def RealRooted (p : ℝ[X]) : Prop := Multiset.card p.roots = p.natDegree

open Polynomial in
/-- **A real polynomial with no root in the open upper half-plane is real-rooted**
(conjugate-pairing: a non-real root would have a conjugate in the upper half-plane). This is the
bridge from univariate real-stability to real-rootedness, used in the Lieb–Sokal lifting. -/
lemma realRooted_of_forall_uhp_ne_zero (q : ℝ[X])
    (h : ∀ w : ℂ, 0 < w.im → Polynomial.aeval w q ≠ 0) : RealRooted q := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [RealRooted]
  rw [RealRooted, ← Polynomial.splits_iff_card_roots]
  apply Polynomial.Splits.of_splits_map_of_injective (i := algebraMap ℝ ℂ)
    (algebraMap ℝ ℂ).injective (IsAlgClosed.splits _)
  intro a ha
  have haroot : Polynomial.aeval a q = 0 := by
    have h2 := (Polynomial.mem_roots'.mp ha).2
    rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at h2
  have him : a.im = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hconj : Polynomial.aeval ((starRingEnd ℂ) a) q = 0 := by
        rw [Polynomial.aeval_conj, haroot, map_zero]
      have hconjim : 0 < ((starRingEnd ℂ) a).im := by
        rw [Complex.conj_im]; linarith
      exact h _ hconjim hconj
    · exact h a hpos haroot
  refine ⟨a.re, ?_⟩
  apply Complex.ext
  · simp
  · simp [him]

open Polynomial in
/-- **The derivative of a real-rooted polynomial is real-rooted** (Rolle interlacing). -/
lemma RealRooted.derivative {p : ℝ[X]} (hp : RealRooted p) :
    RealRooted (Polynomial.derivative p) := by
  unfold RealRooted at hp ⊢
  have h1 : Multiset.card p.roots ≤ Multiset.card (Polynomial.derivative p).roots + 1 :=
    Polynomial.card_roots_le_derivative p
  have h2 : Multiset.card (Polynomial.derivative p).roots ≤ (Polynomial.derivative p).natDegree :=
    Polynomial.card_roots' _
  have h3 : (Polynomial.derivative p).natDegree ≤ p.natDegree - 1 :=
    Polynomial.natDegree_derivative_le p
  omega

open Polynomial in
/-- **Cauchy root bound**: every root of a nonzero complex polynomial satisfies
`‖z‖ ≤ 1 + (Σ_{i<d} ‖coeff i‖) / ‖leadingCoeff‖`. Needed for the compactness step of the
root-continuity (Hurwitz-specialization) argument. -/
lemma norm_root_le_one_add (q : Polynomial ℂ) (hq : q ≠ 0) {z : ℂ} (hz : q.IsRoot z) :
    ‖z‖ ≤ 1 + (∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖) / ‖q.leadingCoeff‖ := by
  set d := q.natDegree with hd
  set L := ‖q.leadingCoeff‖ with hL
  set S := ∑ i ∈ Finset.range d, ‖q.coeff i‖ with hS
  have hLpos : 0 < L := by
    rw [hL]; exact norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hq)
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  by_contra hcon
  push_neg at hcon
  have hz1 : 1 < ‖z‖ := by
    have h0 : 0 ≤ S / L := div_nonneg hSnn (le_of_lt hLpos)
    linarith
  have hzpos : 0 < ‖z‖ := by linarith
  -- a nonzero constant has no root, so d ≥ 1
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with hd0 | hpos
    · exfalso
      have hconst : q.eval z = q.coeff 0 := by
        rw [Polynomial.eval_eq_sum_range, ← hd, hd0]
        simp
      have hc0 : q.coeff 0 = q.leadingCoeff := by
        rw [Polynomial.leadingCoeff, ← hd, hd0]
      have hzero := hz
      rw [Polynomial.IsRoot, hconst, hc0] at hzero
      exact (Polynomial.leadingCoeff_ne_zero.mpr hq) hzero
    · exact hpos
  -- split the evaluation: leading term + lower terms
  have heval := hz
  rw [Polynomial.IsRoot, Polynomial.eval_eq_sum_range, ← hd, Finset.sum_range_succ] at heval
  have hcd : q.coeff d = q.leadingCoeff := by rw [Polynomial.leadingCoeff, hd]
  have h1 : q.leadingCoeff * z ^ d = -(∑ i ∈ Finset.range d, q.coeff i * z ^ i) := by
    rw [← hcd]
    linear_combination heval
  -- norm estimate: L‖z‖^d ≤ S‖z‖^(d-1)
  have hmain : L * ‖z‖ ^ d ≤ S * ‖z‖ ^ (d - 1) := by
    have h2 : ‖q.leadingCoeff * z ^ d‖ = L * ‖z‖ ^ d := by
      rw [norm_mul, norm_pow, hL]
    rw [← h2, h1, norm_neg]
    calc ‖∑ i ∈ Finset.range d, q.coeff i * z ^ i‖
        ≤ ∑ i ∈ Finset.range d, ‖q.coeff i * z ^ i‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.range d, ‖q.coeff i‖ * ‖z‖ ^ i := by
          simp [norm_mul, norm_pow]
      _ ≤ ∑ i ∈ Finset.range d, ‖q.coeff i‖ * ‖z‖ ^ (d - 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hile : i ≤ d - 1 := by
            have := Finset.mem_range.mp hi; omega
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (le_of_lt hz1) hile) (norm_nonneg _)
      _ = S * ‖z‖ ^ (d - 1) := by rw [← Finset.sum_mul, hS]
  -- divide by ‖z‖^(d-1) > 0 to get L‖z‖ ≤ S
  have hpowsplit : ‖z‖ ^ d = ‖z‖ ^ (d - 1) * ‖z‖ := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hpowsplit] at hmain
  have hzd : 0 < ‖z‖ ^ (d - 1) := pow_pos hzpos _
  have hLz : L * ‖z‖ ≤ S := by
    nlinarith [hmain, hzd]
  have hfin : ‖z‖ ≤ S / L := (le_div_iff₀ hLpos).mpr (by linarith)
  linarith

noncomputable section

lemma multiset_enum_toList {α : Type*} (s : Multiset α) {d : ℕ} (hcard : s.card = d) :
    Multiset.map (fun i : Fin d =>
      s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i))
      Finset.univ.val = s := by
  rw [Fin.univ_val_map]
  have hlen : s.toList.length = d := by rw [Multiset.length_toList, hcard]
  change (List.ofFn (fun i : Fin d => s.toList.get (Fin.cast hlen.symm i)) :
    Multiset α) = s
  have hlist :
      List.ofFn (fun i : Fin d => s.toList.get (Fin.cast hlen.symm i)) = s.toList := by
    exact (List.ofFn_congr hlen (s.toList.get)).symm.trans (List.ofFn_get s.toList)
  exact (congrArg (fun l : List α => (l : Multiset α)) hlist).trans (Multiset.coe_toList s)

lemma multiset_enum_toList_mem {α : Type*} (s : Multiset α) {d : ℕ} (hcard : s.card = d)
    (i : Fin d) :
    s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i) ∈ s := by
  have hmem : s.toList.get (Fin.cast (((Multiset.length_toList s).trans hcard).symm) i) ∈
      s.toList := List.get_mem _ _
  rwa [Multiset.mem_toList] at hmem

lemma continuous_esymm_fin (d j : ℕ) :
    Continuous fun v : Fin d → ℂ => (Finset.univ.val.map v).esymm j := by
  have hfun : (fun v : Fin d → ℂ => (Finset.univ.val.map v).esymm j)
      = fun v : Fin d → ℂ => ∑ t ∈ Finset.univ.powersetCard j, ∏ i ∈ t, v i := by
    funext v
    exact Finset.esymm_map_val v Finset.univ j
  rw [hfun]
  exact continuous_finsetSum _ (fun t _ =>
    continuous_finsetProd _ (fun i _ => continuous_apply i))

lemma continuous_prod_roots_coeff_fin {d k : ℕ} (hk : k ≤ d) :
    Continuous fun v : Fin d → ℂ =>
      ((Finset.univ.val.map v).map (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k := by
  have hfun : (fun v : Fin d → ℂ =>
        ((Finset.univ.val.map v).map (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k)
      = fun v : Fin d → ℂ => (-1 : ℂ) ^ (d - k) * (Finset.univ.val.map v).esymm (d - k) := by
    funext v
    rw [Multiset.prod_X_sub_C_coeff]
    · simp
    · simpa using hk
  rw [hfun]
  exact continuous_const.mul (continuous_esymm_fin d (d - k))

lemma roots_im_nonpos_of_tendsto (d : ℕ) (q : ℕ → Polynomial ℂ) (qlim : Polynomial ℂ)
    (hdeg : ∀ n, (q n).natDegree = d) (hdeglim : qlim.natDegree = d) (hlim0 : qlim ≠ 0)
    (hcoeff : ∀ k, Filter.Tendsto (fun n => (q n).coeff k) Filter.atTop (nhds (qlim.coeff k)))
    (hroots : ∀ n, ∀ z ∈ (q n).roots, z.im ≤ 0) :
    ∀ z ∈ qlim.roots, z.im ≤ 0 := by
  classical
  by_cases hd0 : d = 0
  · have hconst : qlim.roots = 0 := by
      have hqconst : qlim = Polynomial.C (qlim.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero (by simpa [hd0] using hdeglim)
      rw [hqconst]
      simp
    intro z hz
    rw [hconst] at hz
    simpa using hz
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
  have hqnz : ∀ n, q n ≠ 0 := by
    intro n hn
    have := hdeg n
    rw [hn, Polynomial.natDegree_zero] at this
    omega
  have hleadlim_ne : qlim.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hlim0
  have hcoefflim_d_ne : qlim.coeff d ≠ 0 := by
    simpa [Polynomial.leadingCoeff, hdeglim] using hleadlim_ne
  have hcard : ∀ n, (q n).roots.card = d := by
    intro n
    exact (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (q n))).trans (hdeg n)
  let r : ℕ → Fin d → ℂ := fun n i =>
    (q n).roots.toList.get
      (Fin.cast (((Multiset.length_toList (q n).roots).trans (hcard n)).symm) i)
  have henum : ∀ n, Finset.univ.val.map (r n) = (q n).roots := by
    intro n
    simpa [r] using multiset_enum_toList ((q n).roots) (hcard n)
  have hrmem : ∀ n i, r n i ∈ (q n).roots := by
    intro n i
    simpa [r] using multiset_enum_toList_mem ((q n).roots) (hcard n) i
  let L : ℝ := ‖qlim.coeff d‖
  have hLpos : 0 < L := by
    simp [L, hcoefflim_d_ne]
  let S : ℝ := ∑ k ∈ Finset.range d, (‖qlim.coeff k‖ + 1)
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun _ _ => by positivity
  let B : ℝ := 1 + S / (L / 2)
  have hhalfpos : 0 < L / 2 := by positivity
  have hBnonneg : 0 ≤ B := by
    have hdiv_nonneg : 0 ≤ S / (L / 2) := div_nonneg hSnonneg hhalfpos.le
    dsimp [B]
    linarith
  have hlead_event : ∀ᶠ n in Filter.atTop, L / 2 ≤ ‖(q n).leadingCoeff‖ := by
    have hnorm : Filter.Tendsto (fun n => ‖(q n).coeff d‖) Filter.atTop (nhds L) := by
      simpa [L] using (hcoeff d).norm
    have hev : ∀ᶠ n in Filter.atTop, L / 2 < ‖(q n).coeff d‖ :=
      hnorm.eventually (lt_mem_nhds (by linarith))
    filter_upwards [hev] with n hn
    have hcd : (q n).coeff d = (q n).leadingCoeff := by
      rw [Polynomial.leadingCoeff, hdeg n]
    rw [← hcd]
    exact le_of_lt hn
  have hlow_event :
      ∀ᶠ n in Filter.atTop, ∀ k ∈ Finset.range d, ‖(q n).coeff k‖ ≤ ‖qlim.coeff k‖ + 1 := by
    rw [Filter.eventually_all_finset]
    intro k _
    have hnorm : Filter.Tendsto (fun n => ‖(q n).coeff k‖) Filter.atTop
        (nhds ‖qlim.coeff k‖) := (hcoeff k).norm
    exact (hnorm.eventually (gt_mem_nhds (by linarith))).mono fun _ hn => le_of_lt hn
  have hbound_event : ∀ᶠ n in Filter.atTop, ∀ i : Fin d, ‖r n i‖ ≤ B := by
    filter_upwards [hlead_event, hlow_event] with n hlead hlow i
    have hroot_isRoot : (q n).IsRoot (r n i) := (Polynomial.mem_roots'.mp (hrmem n i)).2
    have hcauchy := norm_root_le_one_add (q n) (hqnz n) hroot_isRoot
    have hcauchy' :
        ‖r n i‖ ≤
          1 + (∑ k ∈ Finset.range d, ‖(q n).coeff k‖) / ‖(q n).leadingCoeff‖ := by
      simpa [hdeg n] using hcauchy
    have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.range d, ‖(q n).coeff k‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hsum_le : (∑ k ∈ Finset.range d, ‖(q n).coeff k‖) ≤ S := by
      dsimp [S]
      exact Finset.sum_le_sum fun k hk => hlow k hk
    have hfrac :
        (∑ k ∈ Finset.range d, ‖(q n).coeff k‖) / ‖(q n).leadingCoeff‖
          ≤ S / (L / 2) :=
      div_le_div₀ hSnonneg hsum_le hhalfpos hlead
    exact hcauchy'.trans (by dsimp [B]; linarith)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hbound_event
  let box : Set (Fin d → ℂ) := {v | ∀ i : Fin d, ‖v i‖ ≤ B}
  have hbox_bdd : Bornology.IsBounded box := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin d → ℂ)) (r := B)).subset ?_
    intro v hv
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hBnonneg).2 hv
  let x : ℕ → (Fin d → ℂ) := fun n => r (n + N)
  have hxmem : ∀ n, x n ∈ box := by
    intro n i
    exact hN (n + N) (Nat.le_add_left N n) i
  obtain ⟨s, _hs_closure, φ, hφmono, hφlim⟩ := tendsto_subseq_of_bounded hbox_bdd hxmem
  have hs_im_nonpos : ∀ i : Fin d, (s i).im ≤ 0 := by
    intro i
    have him_tendsto :
        Filter.Tendsto (fun n => (r (φ n + N) i).im) Filter.atTop (nhds (s i).im) := by
      simpa [x, Function.comp_def] using
        ((Complex.continuous_im.comp (continuous_apply i)).tendsto s).comp hφlim
    exact le_of_tendsto him_tendsto
      (Filter.Eventually.of_forall fun n =>
        hroots (φ n + N) (r (φ n + N) i) (hrmem (φ n + N) i))
  have hfactor : ∀ n,
      q n = Polynomial.C (q n).leadingCoeff *
        ((Finset.univ.val.map (r n)).map (fun t => Polynomial.X - Polynomial.C t)).prod := by
    intro n
    calc
      q n = Polynomial.C (q n).leadingCoeff *
          (((q n).roots).map (fun t => Polynomial.X - Polynomial.C t)).prod :=
        (IsAlgClosed.splits (q n)).eq_prod_roots
      _ = Polynomial.C (q n).leadingCoeff *
          ((Finset.univ.val.map (r n)).map (fun t => Polynomial.X - Polynomial.C t)).prod := by
        rw [← henum n]
  let pstar : Polynomial ℂ :=
    Polynomial.C qlim.leadingCoeff *
      ((Finset.univ.val.map s).map (fun t => Polynomial.X - Polynomial.C t)).prod
  have hψ_tendsto : Filter.Tendsto (fun n => φ n + N) Filter.atTop Filter.atTop :=
    (Filter.tendsto_add_atTop_nat N).comp hφmono.tendsto_atTop
  have hidentify : qlim = pstar := by
    apply Polynomial.ext
    intro k
    by_cases hk : k ≤ d
    · have hqcoeff_tendsto :
          Filter.Tendsto (fun n => (q (φ n + N)).coeff k) Filter.atTop (nhds (qlim.coeff k)) :=
        (hcoeff k).comp hψ_tendsto
      have hlead_tendsto :
          Filter.Tendsto (fun n => (q (φ n + N)).leadingCoeff) Filter.atTop
            (nhds qlim.leadingCoeff) := by
        have hcd : Filter.Tendsto (fun n => (q (φ n + N)).coeff d) Filter.atTop
            (nhds (qlim.coeff d)) := (hcoeff d).comp hψ_tendsto
        have hcd' : Filter.Tendsto (fun n => (q (φ n + N)).leadingCoeff) Filter.atTop
            (nhds (qlim.coeff d)) := by
          exact hcd.congr (fun n => by rw [Polynomial.leadingCoeff, hdeg (φ n + N)])
        have hlead_eq : qlim.coeff d = qlim.leadingCoeff := by
          rw [Polynomial.leadingCoeff, hdeglim]
        simpa [hlead_eq] using hcd'
      have hprod_tendsto :
          Filter.Tendsto
            (fun n => (((Finset.univ.val.map (r (φ n + N))).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k))
            Filter.atTop
            (nhds (((Finset.univ.val.map s).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k)) := by
        simpa [x, Function.comp_def] using
          (continuous_prod_roots_coeff_fin (d := d) (k := k) hk).tendsto s |>.comp hφlim
      have hmul_tendsto :
          Filter.Tendsto
            (fun n => (q (φ n + N)).leadingCoeff *
              (((Finset.univ.val.map (r (φ n + N))).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k))
            Filter.atTop
            (nhds (qlim.leadingCoeff *
              (((Finset.univ.val.map s).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k))) :=
        hlead_tendsto.mul hprod_tendsto
      have hcoeff_factor : ∀ n,
          (q (φ n + N)).coeff k =
            (q (φ n + N)).leadingCoeff *
              (((Finset.univ.val.map (r (φ n + N))).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k) := by
        intro n
        have h := congrArg (fun p : Polynomial ℂ => p.coeff k) (hfactor (φ n + N))
        simpa [Polynomial.coeff_C_mul] using h
      have hmul_as_q :
          Filter.Tendsto (fun n => (q (φ n + N)).coeff k) Filter.atTop
            (nhds (qlim.leadingCoeff *
              (((Finset.univ.val.map s).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k))) :=
        hmul_tendsto.congr' (Filter.Eventually.of_forall fun n => (hcoeff_factor n).symm)
      have heq :
          qlim.coeff k =
            qlim.leadingCoeff *
              (((Finset.univ.val.map s).map
                (fun t => Polynomial.X - Polynomial.C t)).prod.coeff k) :=
        tendsto_nhds_unique hqcoeff_tendsto hmul_as_q
      dsimp [pstar]
      rw [Polynomial.coeff_C_mul]
      exact heq
    · have hklt : d < k := Nat.lt_of_not_ge hk
      have hleft : qlim.coeff k = 0 := by
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa [hdeglim] using hklt)
      have hprod_natDegree :
          (((Finset.univ.val.map s).map (fun t => Polynomial.X - Polynomial.C t)).prod).natDegree = d := by
        rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]
        simp
      have hprod_coeff0 :
          (((Finset.univ.val.map s).map (fun t => Polynomial.X - Polynomial.C t)).prod).coeff k = 0 := by
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
          rw [hprod_natDegree]
          exact hklt)
      have hright : pstar.coeff k = 0 := by
        dsimp [pstar]
        rw [Polynomial.coeff_C_mul, hprod_coeff0, mul_zero]
      rw [hleft, hright]
  intro z hz
  have hroot_eq : qlim.roots = Finset.univ.val.map s := by
    rw [hidentify]
    dsimp [pstar]
    rw [Polynomial.roots_C_mul _ hleadlim_ne, Polynomial.roots_multiset_prod_X_sub_C]
  rw [hroot_eq] at hz
  rcases Multiset.mem_map.mp hz with ⟨i, _hi, rfl⟩
  exact hs_im_nonpos i

end

end ProofsInTheBook.Chapter22Stable
