import Mathlib

/-!
# Permanent convexity lemmas

This file is independent of `Chapter22`.  It records algebraic permanent
facts used in Van der Waerden-style arguments:

* additivity and affine-linearity in one row or one column;
* bilinearity of the permanent after two rows are singled out;
* the quadratic expansion along a two-row line, and the resulting convexity
  criterion when the mixed quadratic coefficient is nonnegative;
* the discharge of that mixed-coefficient hypothesis for the elementary
  `2 × 2` checkerboard exchange directions;
* the maximal feasible checkerboard exchange step, which keeps the
  doubly-stochastic constraints and forces a boundary zero;
* the elementary `2 × 2` row log-concavity model.

The deep Alexandrov-Fenchel/Falikman-Egorychev/Gurvits log-concavity input is
not hidden here.  The general convexity theorem below states exactly the local
mixed-coefficient nonnegativity hypothesis needed for a two-row slice.
-/

namespace ProofsInTheBook.PermanentConvexity

open Matrix

noncomputable section

variable {n : Type*} [DecidableEq n] [Fintype n]

/-! ## Basic multilinearity -/

variable {R : Type*} [CommSemiring R]

theorem permanent_updateCol_add (M : Matrix n n R) (j : n) (u v : n → R) :
    (M.updateCol j (u + v)).permanent =
      (M.updateCol j u).permanent + (M.updateCol j v).permanent := by
  classical
  simp only [Matrix.permanent, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    Matrix.updateCol_self, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  apply congrArg₂ HAdd.hAdd
  · refine Finset.sum_congr rfl ?_
    intro p _hp
    congr 1
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)]
    rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)]
  · refine Finset.sum_congr rfl ?_
    intro p _hp
    congr 1
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)]
    rw [Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)]

theorem permanent_updateRow_add (M : Matrix n n R) (i : n) (u v : n → R) :
    (M.updateRow i (u + v)).permanent =
      (M.updateRow i u).permanent + (M.updateRow i v).permanent := by
  rw [← Matrix.permanent_transpose, ← Matrix.updateCol_transpose, permanent_updateCol_add]
  simp [Matrix.updateCol_transpose]

theorem permanent_updateCol_linear_comb (M : Matrix n n R) (j : n)
    (a b : R) (u v : n → R) :
    (M.updateCol j (a • u + b • v)).permanent =
      a * (M.updateCol j u).permanent + b * (M.updateCol j v).permanent := by
  rw [permanent_updateCol_add, Matrix.permanent_updateCol_smul,
    Matrix.permanent_updateCol_smul]

theorem permanent_updateRow_linear_comb (M : Matrix n n R) (i : n)
    (a b : R) (u v : n → R) :
    (M.updateRow i (a • u + b • v)).permanent =
      a * (M.updateRow i u).permanent + b * (M.updateRow i v).permanent := by
  rw [permanent_updateRow_add, Matrix.permanent_updateRow_smul,
    Matrix.permanent_updateRow_smul]

theorem permanent_nonneg_of_entrywise_nonneg {A : Matrix n n ℝ}
    (hA : ∀ i j, 0 ≤ A i j) :
    0 ≤ A.permanent := by
  classical
  unfold Matrix.permanent
  exact Finset.sum_nonneg fun σ _hσ =>
    Finset.prod_nonneg fun j _hj => hA (σ j) j

/-! ## Two-row slices -/

/-- Permanent after replacing rows `r` and `s` by `u` and `v`. -/
def twoRowPermanent (M : Matrix n n R) (r s : n) (u v : n → R) : R :=
  ((M.updateRow r u).updateRow s v).permanent

theorem twoRowPermanent_add_left (M : Matrix n n R) {r s : n} (hrs : r ≠ s)
    (u v w : n → R) :
    twoRowPermanent M r s (u + v) w =
      twoRowPermanent M r s u w + twoRowPermanent M r s v w := by
  unfold twoRowPermanent
  rw [Matrix.updateRow_comm M hrs, permanent_updateRow_add]
  rw [← Matrix.updateRow_comm M hrs, ← Matrix.updateRow_comm M hrs]

theorem twoRowPermanent_add_right (M : Matrix n n R) (r s : n) (u v w : n → R) :
    twoRowPermanent M r s u (v + w) =
      twoRowPermanent M r s u v + twoRowPermanent M r s u w := by
  unfold twoRowPermanent
  rw [permanent_updateRow_add]

theorem twoRowPermanent_smul_left (M : Matrix n n R) {r s : n} (hrs : r ≠ s)
    (a : R) (u v : n → R) :
    twoRowPermanent M r s (a • u) v = a * twoRowPermanent M r s u v := by
  unfold twoRowPermanent
  rw [Matrix.updateRow_comm M hrs, Matrix.permanent_updateRow_smul]
  rw [← Matrix.updateRow_comm M hrs]

theorem twoRowPermanent_smul_right (M : Matrix n n R) (r s : n)
    (a : R) (u v : n → R) :
    twoRowPermanent M r s u (a • v) = a * twoRowPermanent M r s u v := by
  unfold twoRowPermanent
  rw [Matrix.permanent_updateRow_smul]

theorem twoRowPermanent_linear_comb_left (M : Matrix n n R) {r s : n}
    (hrs : r ≠ s) (a b : R) (u v w : n → R) :
    twoRowPermanent M r s (a • u + b • v) w =
      a * twoRowPermanent M r s u w + b * twoRowPermanent M r s v w := by
  rw [twoRowPermanent_add_left M hrs, twoRowPermanent_smul_left M hrs,
    twoRowPermanent_smul_left M hrs]

theorem twoRowPermanent_linear_comb_right (M : Matrix n n R) (r s : n)
    (a b : R) (u v w : n → R) :
    twoRowPermanent M r s u (a • v + b • w) =
      a * twoRowPermanent M r s u v + b * twoRowPermanent M r s u w := by
  rw [twoRowPermanent_add_right, twoRowPermanent_smul_right,
    twoRowPermanent_smul_right]

theorem twoRowPermanent_nonneg_of_nonneg {M : Matrix n n ℝ} {r s : n}
    {u v : n → ℝ}
    (hM : ∀ i j, i ≠ r → i ≠ s → 0 ≤ M i j)
    (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) :
    0 ≤ twoRowPermanent M r s u v := by
  apply permanent_nonneg_of_entrywise_nonneg
  intro i j
  by_cases his : i = s
  · subst i
    simp [hv j]
  · by_cases hir : i = r
    · subst i
      simp [his, hu j]
    · simp [his, hir, hM i j hir his]

private theorem sum_piecewise_two {f : n → ℝ} {r s : n} (hrs : r ≠ s) (a b : ℝ) :
    (∑ i, (if i = s then b else if i = r then a else f i)) =
      ∑ i, f i + (a - f r) + (b - f s) := by
  let g : n → ℝ := fun i => if i = s then b else if i = r then a else f i
  have hrs_mem : r ∈ (Finset.univ.erase s : Finset n) := by
    exact Finset.mem_erase.mpr ⟨hrs, Finset.mem_univ r⟩
  have hsum_g : (∑ i, g i) = (∑ i ∈ (Finset.univ.erase s).erase r, f i) + a + b := by
    rw [← Finset.sum_erase_add _ g (Finset.mem_univ s)]
    rw [← Finset.sum_erase_add (Finset.univ.erase s) g hrs_mem]
    have hrest : (∑ x ∈ (Finset.univ.erase s).erase r, g x) =
        ∑ x ∈ (Finset.univ.erase s).erase r, f x := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxr : x ≠ r := Finset.ne_of_mem_erase hx
      have hxs : x ≠ s := by
        exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
      simp [g, hxs, hxr]
    rw [hrest]
    simp [g, hrs]
  have hsum_f : (∑ i, f i) = (∑ i ∈ (Finset.univ.erase s).erase r, f i) + f r + f s := by
    rw [← Finset.sum_erase_add _ f (Finset.mem_univ s)]
    rw [← Finset.sum_erase_add (Finset.univ.erase s) f hrs_mem]
  rw [hsum_g, hsum_f]
  ring

/-! ## Doubly-stochastic two-row perturbations -/

/--
The row-pair perturbation that adds `t • du` to row `r` and `t • dv` to row
`s`.  If the two direction rows have zero row sums and cancel columnwise, this
is the standard line inside the doubly-stochastic affine subspace.
-/
def twoRowPerturbation (M : Matrix n n ℝ) (r s : n) (du dv : n → ℝ) (t : ℝ) :
    Matrix n n ℝ :=
  (M.updateRow r (M r + t • du)).updateRow s (M s + t • dv)

theorem twoRowPermanent_self (M : Matrix n n ℝ) (r s : n) :
    twoRowPermanent M r s (M r) (M s) = M.permanent := by
  unfold twoRowPermanent
  rw [Matrix.updateRow_eq_self, Matrix.updateRow_eq_self]

omit [Fintype n] in
theorem twoRowPerturbation_eq_affineLine (hrs : r ≠ s) (du dv : n → ℝ) (t : ℝ) :
    twoRowPerturbation M r s du dv t =
      (1 - t) • M + t • twoRowPerturbation M r s du dv 1 := by
  ext i j
  by_cases his : i = s
  · subst i
    simp [twoRowPerturbation]
    ring
  · by_cases hir : i = r
    · subst i
      simp [twoRowPerturbation, hrs]
      ring
    · simp [twoRowPerturbation, his, hir]
      ring

omit [Fintype n] in
theorem twoRowPerturbation_nonneg_of_endpoints (hrs : r ≠ s) (du dv : n → ℝ)
    (hM : ∀ i j, 0 ≤ M i j)
    (h1 : ∀ i j, 0 ≤ twoRowPerturbation M r s du dv 1 i j)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∀ i j, 0 ≤ twoRowPerturbation M r s du dv t i j := by
  intro i j
  rw [twoRowPerturbation_eq_affineLine (M := M) (r := r) (s := s) hrs du dv t]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) (hM i j))
    (mul_nonneg ht0 (h1 i j))

theorem twoRowPerturbation_mem_doublyStochastic {M : Matrix n n ℝ} {r s : n}
    (hrs : r ≠ s) (hM : M ∈ doublyStochastic ℝ n)
    {du dv : n → ℝ} (hdu : ∑ j, du j = 0) (hdv : ∑ j, dv j = 0)
    (hcol : ∀ j, du j + dv j = 0)
    {t : ℝ} (hnonneg : ∀ i j, 0 ≤ twoRowPerturbation M r s du dv t i j) :
    twoRowPerturbation M r s du dv t ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨hnonneg, ?_, ?_⟩
  · intro i
    by_cases his : i = s
    · subst i
      simp only [twoRowPerturbation, Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      calc
        (∑ x, (M s x + t * dv x)) = (∑ x, M s x) + t * ∑ x, dv x := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
        _ = 1 := by rw [sum_row_of_mem_doublyStochastic hM s, hdv]; ring
    · by_cases hir : i = r
      · subst i
        simp only [twoRowPerturbation, Matrix.updateRow_ne hrs, Matrix.updateRow_self,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc
          (∑ x, (M r x + t * du x)) = (∑ x, M r x) + t * ∑ x, du x := by
            simp [Finset.sum_add_distrib, Finset.mul_sum]
          _ = 1 := by rw [sum_row_of_mem_doublyStochastic hM r, hdu]; ring
      · simp [twoRowPerturbation, his, hir, sum_row_of_mem_doublyStochastic hM i]
  · intro j
    simp only [twoRowPerturbation, Matrix.updateRow_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [sum_piecewise_two hrs (M r j + t * du j) (M s j + t * dv j)]
    rw [sum_col_of_mem_doublyStochastic hM j]
    have htd : t * du j + t * dv j = 0 := by
      rw [← mul_add, hcol j, mul_zero]
    nlinarith

/-! ## Checkerboard exchange directions -/

/--
The signed direction that adds to column `c` and subtracts from column `d` in
one row.  Paired with its negative in another row, this is the elementary
`2 × 2` exchange direction preserving row and column sums.
-/
def checkerboardDirection (c d : n) : n → ℝ :=
  Pi.single c (1 : ℝ) - Pi.single d (1 : ℝ)

def scaledCheckerboardDirection (a : ℝ) (c d : n) : n → ℝ :=
  a • checkerboardDirection c d

def checkerboardExchangeAmount (M : Matrix n n ℝ) (r s c d : n) : ℝ :=
  min (M r d) (M s c)

theorem sum_checkerboardDirection (c d : n) :
    ∑ j, checkerboardDirection c d j = 0 := by
  simp [checkerboardDirection, Finset.sum_sub_distrib]

omit [DecidableEq n] [Fintype n] in
theorem checkerboardExchangeAmount_nonneg {M : Matrix n n ℝ} {r s c d : n}
    (hM : ∀ i j, 0 ≤ M i j) :
    0 ≤ checkerboardExchangeAmount M r s c d := by
  unfold checkerboardExchangeAmount
  exact le_min (hM r d) (hM s c)

omit [Fintype n] in
theorem checkerboardDirection_cancel (c d : n) (j : n) :
    checkerboardDirection c d j + (-checkerboardDirection c d) j = 0 := by
  simp

theorem twoRowPerturbation_checkerboard_mem_doublyStochastic {M : Matrix n n ℝ}
    {r s c d : n} (hrs : r ≠ s) (hM : M ∈ doublyStochastic ℝ n)
    {t : ℝ}
    (hnonneg : ∀ i j, 0 ≤
      twoRowPerturbation M r s (checkerboardDirection c d)
        (-checkerboardDirection c d) t i j) :
    twoRowPerturbation M r s (checkerboardDirection c d)
        (-checkerboardDirection c d) t ∈ doublyStochastic ℝ n := by
  refine twoRowPerturbation_mem_doublyStochastic hrs hM
    (sum_checkerboardDirection c d) ?_ ?_ hnonneg
  · simp [sum_checkerboardDirection]
  · exact checkerboardDirection_cancel c d

omit [Fintype n] in
theorem scaledCheckerboardPerturbation_one_nonneg {M : Matrix n n ℝ} {r s c d : n}
    (hrs : r ≠ s) (hcd : c ≠ d)
    (hM : ∀ i j, 0 ≤ M i j) {a : ℝ} (ha0 : 0 ≤ a)
    (hrd : a ≤ M r d) (hsc : a ≤ M s c) :
    ∀ i : n, ∀ j : n,
      0 ≤ twoRowPerturbation M r s (scaledCheckerboardDirection (n := n) a c d)
      (-(scaledCheckerboardDirection (n := n) a c d)) 1 i j := by
  intro i j
  by_cases his : i = s
  · subst i
    by_cases hjc : j = c
    · subst j
      simp [twoRowPerturbation, scaledCheckerboardDirection, checkerboardDirection, hcd]
      linarith
    · by_cases hjd : j = d
      · subst j
        simp [twoRowPerturbation, scaledCheckerboardDirection, checkerboardDirection, hcd]
        nlinarith [hM s d, ha0]
      · simp [twoRowPerturbation, scaledCheckerboardDirection, checkerboardDirection, hjc, hjd]
        exact hM s j
  · by_cases hir : i = r
    · subst i
      by_cases hjc : j = c
      · subst j
        simp [twoRowPerturbation, scaledCheckerboardDirection, checkerboardDirection, hrs, hcd]
        nlinarith [hM r c, ha0]
      · by_cases hjd : j = d
        · subst j
          simp [twoRowPerturbation, scaledCheckerboardDirection, checkerboardDirection, hrs, hcd]
          linarith
        · simp [twoRowPerturbation, scaledCheckerboardDirection, checkerboardDirection, his, hjc, hjd]
          exact hM r j
    · simp [twoRowPerturbation, his, hir]
      exact hM i j

theorem twoRowPermanent_same_single_eq_zero (hrs : r ≠ s) (c : n) :
    twoRowPermanent M r s (Pi.single c (1 : ℝ)) (Pi.single c (1 : ℝ)) = 0 := by
  classical
  unfold twoRowPermanent Matrix.permanent
  refine Finset.sum_eq_zero fun σ _hσ => ?_
  have hpre : σ.symm r ≠ σ.symm s := by
    intro h
    apply hrs
    simpa using congrArg σ h
  by_cases hsc : σ.symm s = c
  · have hrc : σ.symm r ≠ c := by
      intro hrc
      exact hpre (by rw [hrc, hsc])
    exact Finset.prod_eq_zero (Finset.mem_univ (σ.symm r)) (by
      simp [Matrix.updateRow_apply, hrc])
  · exact Finset.prod_eq_zero (Finset.mem_univ (σ.symm s)) (by
      simp [Matrix.updateRow_apply, hsc])

theorem checkerboardDirection_quadraticCoeff_eq_crossSum (hrs : r ≠ s) (c d : n) :
    twoRowPermanent M r s (checkerboardDirection c d) (-checkerboardDirection c d) =
      twoRowPermanent M r s (Pi.single c (1 : ℝ)) (Pi.single d (1 : ℝ)) +
        twoRowPermanent M r s (Pi.single d (1 : ℝ)) (Pi.single c (1 : ℝ)) := by
  let ec : n → ℝ := Pi.single c (1 : ℝ)
  let ed : n → ℝ := Pi.single d (1 : ℝ)
  have hp : checkerboardDirection c d = (1 : ℝ) • ec + (-1 : ℝ) • ed := by
    ext j
    simp [checkerboardDirection, ec, ed]
    ring
  have hq : -checkerboardDirection c d = (1 : ℝ) • ed + (-1 : ℝ) • ec := by
    ext j
    simp [checkerboardDirection, ec, ed]
    ring
  rw [hq, hp]
  rw [twoRowPermanent_linear_comb_left M hrs]
  rw [twoRowPermanent_linear_comb_right, twoRowPermanent_linear_comb_right]
  rw [twoRowPermanent_same_single_eq_zero hrs c, twoRowPermanent_same_single_eq_zero hrs d]
  ring

/--
The local mixed-coefficient nonnegativity needed for convexity is elementary
for checkerboard exchange directions: only the two cross terms survive, and
each is a permanent with nonnegative replaced rows.
-/
theorem checkerboardDirection_quadraticCoeff_nonneg (hrs : r ≠ s)
    (hM : ∀ i j, i ≠ r → i ≠ s → 0 ≤ M i j) (c d : n) :
    0 ≤ twoRowPermanent M r s (checkerboardDirection c d)
      (-checkerboardDirection c d) := by
  let ec : n → ℝ := Pi.single c (1 : ℝ)
  let ed : n → ℝ := Pi.single d (1 : ℝ)
  have h_ec_nonneg : ∀ j, 0 ≤ ec j := fun j =>
    (Pi.single_nonneg.mpr zero_le_one : 0 ≤ ec) j
  have h_ed_nonneg : ∀ j, 0 ≤ ed j := fun j =>
    (Pi.single_nonneg.mpr zero_le_one : 0 ≤ ed) j
  have h_ec_ed : 0 ≤ twoRowPermanent M r s ec ed := by
    exact twoRowPermanent_nonneg_of_nonneg hM h_ec_nonneg h_ed_nonneg
  have h_ed_ec : 0 ≤ twoRowPermanent M r s ed ec := by
    exact twoRowPermanent_nonneg_of_nonneg hM h_ed_nonneg h_ec_nonneg
  rw [checkerboardDirection_quadraticCoeff_eq_crossSum (M := M) (r := r) (s := s) hrs c d]
  exact add_nonneg h_ec_ed h_ed_ec

theorem scaledCheckerboardDirection_quadraticCoeff_nonneg {M : Matrix n n ℝ} {r s : n}
    (hrs : r ≠ s)
    (hM : ∀ i j, i ≠ r → i ≠ s → 0 ≤ M i j) (c d : n) (a : ℝ) :
    0 ≤ twoRowPermanent M r s (scaledCheckerboardDirection (n := n) a c d)
      (-(scaledCheckerboardDirection (n := n) a c d)) := by
  have hneg : -(scaledCheckerboardDirection (n := n) a c d) =
      a • (-checkerboardDirection c d) := by
    ext j
    simp [scaledCheckerboardDirection]
  rw [hneg]
  unfold scaledCheckerboardDirection
  rw [twoRowPermanent_smul_left M hrs, twoRowPermanent_smul_right]
  have hq := checkerboardDirection_quadraticCoeff_nonneg
    (M := M) (r := r) (s := s) hrs hM c d
  nlinarith [sq_nonneg a, hq]

/-! ## Quadratic expansion and convexity along a two-row line -/

variable {M : Matrix n n ℝ} {r s : n}

theorem permanent_twoRowLine_eq_quadratic (hrs : r ≠ s)
    (u v du dv : n → ℝ) (t : ℝ) :
    twoRowPermanent M r s (u + t • du) (v + t • dv) =
      twoRowPermanent M r s u v +
        t * (twoRowPermanent M r s du v + twoRowPermanent M r s u dv) +
        t ^ 2 * twoRowPermanent M r s du dv := by
  rw [twoRowPermanent_add_right]
  rw [twoRowPermanent_add_left M hrs]
  rw [twoRowPermanent_smul_left M hrs]
  rw [twoRowPermanent_smul_right]
  rw [twoRowPermanent_add_left M hrs]
  rw [twoRowPermanent_smul_left M hrs]
  ring

/--
Convexity criterion for a two-row permanent slice.

The hypothesis is exactly the local nonnegativity of the mixed quadratic
coefficient.  In a full Van der Waerden proof this is where the relevant
permanent log-concavity/Alexandrov-Fenchel input must enter.
-/
theorem permanent_twoRowLine_convex_on_unit_interval (hrs : r ≠ s)
    (u v du dv : n → ℝ)
    (hquad : 0 ≤ twoRowPermanent M r s du dv)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    twoRowPermanent M r s (u + t • du) (v + t • dv) ≤
      (1 - t) * twoRowPermanent M r s u v +
        t * twoRowPermanent M r s (u + du) (v + dv) := by
  rw [permanent_twoRowLine_eq_quadratic hrs u v du dv t]
  rw [show twoRowPermanent M r s (u + du) (v + dv) =
      twoRowPermanent M r s (u + (1 : ℝ) • du) (v + (1 : ℝ) • dv) by simp]
  rw [permanent_twoRowLine_eq_quadratic hrs u v du dv 1]
  have ht_sq_le : t ^ 2 ≤ t := by
    nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hquad_le : t ^ 2 * twoRowPermanent M r s du dv ≤
      t * twoRowPermanent M r s du dv := by
    exact mul_le_mul_of_nonneg_right ht_sq_le hquad
  nlinarith

theorem permanent_twoRowLine_convex_from_nonnegative_directions (hrs : r ≠ s)
    (u v du dv : n → ℝ)
    (hM : ∀ i j, i ≠ r → i ≠ s → 0 ≤ M i j)
    (hdu : ∀ j, 0 ≤ du j) (hdv : ∀ j, 0 ≤ dv j)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    twoRowPermanent M r s (u + t • du) (v + t • dv) ≤
      (1 - t) * twoRowPermanent M r s u v +
        t * twoRowPermanent M r s (u + du) (v + dv) := by
  exact permanent_twoRowLine_convex_on_unit_interval hrs u v du dv
    (twoRowPermanent_nonneg_of_nonneg hM hdu hdv) ht0 ht1

theorem permanent_twoRowPerturbation_convex_on_unit_interval (hrs : r ≠ s)
    (du dv : n → ℝ)
    (hquad : 0 ≤ twoRowPermanent M r s du dv)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (twoRowPerturbation M r s du dv t).permanent ≤
      (1 - t) * M.permanent +
        t * (twoRowPerturbation M r s du dv 1).permanent := by
  simpa [twoRowPerturbation, twoRowPermanent_self] using
    permanent_twoRowLine_convex_on_unit_interval (M := M) (r := r) (s := s) hrs
      (M r) (M s) du dv hquad ht0 ht1

theorem permanent_checkerboardPerturbation_convex_on_unit_interval (hrs : r ≠ s)
    (hM : ∀ i j, i ≠ r → i ≠ s → 0 ≤ M i j) (c d : n)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (twoRowPerturbation M r s (checkerboardDirection c d)
      (-checkerboardDirection c d) t).permanent ≤
      (1 - t) * M.permanent +
        t * (twoRowPerturbation M r s (checkerboardDirection c d)
          (-checkerboardDirection c d) 1).permanent := by
  exact permanent_twoRowPerturbation_convex_on_unit_interval hrs _ _
    (checkerboardDirection_quadraticCoeff_nonneg hrs hM c d) ht0 ht1

theorem checkerboardPerturbation_mem_and_permanent_convex_between_endpoints
    (hrs : r ≠ s) (hM : M ∈ doublyStochastic ℝ n) (c d : n)
    (h1 : ∀ i j, 0 ≤
      twoRowPerturbation M r s (checkerboardDirection c d)
        (-checkerboardDirection c d) 1 i j)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    twoRowPerturbation M r s (checkerboardDirection c d)
        (-checkerboardDirection c d) t ∈ doublyStochastic ℝ n ∧
      (twoRowPerturbation M r s (checkerboardDirection c d)
        (-checkerboardDirection c d) t).permanent ≤
        (1 - t) * M.permanent +
          t * (twoRowPerturbation M r s (checkerboardDirection c d)
            (-checkerboardDirection c d) 1).permanent := by
  have hnonneg_t : ∀ i j, 0 ≤
      twoRowPerturbation M r s (checkerboardDirection c d)
        (-checkerboardDirection c d) t i j := by
    exact twoRowPerturbation_nonneg_of_endpoints
      (M := M) (r := r) (s := s) hrs _ _
      (fun i j => nonneg_of_mem_doublyStochastic hM) h1 ht0 ht1
  refine ⟨?_, ?_⟩
  · exact twoRowPerturbation_checkerboard_mem_doublyStochastic hrs hM hnonneg_t
  · exact permanent_checkerboardPerturbation_convex_on_unit_interval hrs
      (fun i j _ _ => nonneg_of_mem_doublyStochastic hM) c d ht0 ht1

theorem scaledCheckerboardPerturbation_mem_and_permanent_convex_between_endpoints
    {c d : n} (hrs : r ≠ s) (hcd : c ≠ d) (hM : M ∈ doublyStochastic ℝ n)
    {a : ℝ} (ha0 : 0 ≤ a) (hrd : a ≤ M r d) (hsc : a ≤ M s c)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    twoRowPerturbation M r s (scaledCheckerboardDirection (n := n) a c d)
        (-(scaledCheckerboardDirection (n := n) a c d)) t ∈ doublyStochastic ℝ n ∧
      (twoRowPerturbation M r s (scaledCheckerboardDirection (n := n) a c d)
        (-(scaledCheckerboardDirection (n := n) a c d)) t).permanent ≤
        (1 - t) * M.permanent +
          t * (twoRowPerturbation M r s (scaledCheckerboardDirection (n := n) a c d)
            (-(scaledCheckerboardDirection (n := n) a c d)) 1).permanent := by
  have h1 : ∀ i j, 0 ≤ twoRowPerturbation M r s
      (scaledCheckerboardDirection (n := n) a c d)
      (-(scaledCheckerboardDirection (n := n) a c d)) 1 i j := by
    exact scaledCheckerboardPerturbation_one_nonneg
      (M := M) (r := r) (s := s) (c := c) (d := d) hrs hcd
      (fun i j => nonneg_of_mem_doublyStochastic hM) ha0 hrd hsc
  have hnonneg_t : ∀ i j, 0 ≤ twoRowPerturbation M r s
      (scaledCheckerboardDirection (n := n) a c d)
      (-(scaledCheckerboardDirection (n := n) a c d)) t i j := by
    exact twoRowPerturbation_nonneg_of_endpoints (M := M) (r := r) (s := s) hrs _ _
      (fun i j => nonneg_of_mem_doublyStochastic hM) h1 ht0 ht1
  refine ⟨?_, ?_⟩
  · refine twoRowPerturbation_mem_doublyStochastic hrs hM ?_ ?_ ?_ hnonneg_t
    · simp_rw [scaledCheckerboardDirection, Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum, sum_checkerboardDirection, mul_zero]
    · simp_rw [scaledCheckerboardDirection, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      rw [sum_checkerboardDirection, mul_zero, neg_zero]
    · intro j
      simp
  · exact permanent_twoRowPerturbation_convex_on_unit_interval hrs _ _
      (scaledCheckerboardDirection_quadraticCoeff_nonneg
        (M := M) (r := r) (s := s) hrs
        (fun i j _ _ => nonneg_of_mem_doublyStochastic hM) c d a) ht0 ht1

omit [Fintype n] in
theorem scaledCheckerboardPerturbation_exchangeAmount_endpoint_zero
    {M : Matrix n n ℝ} {r s c d : n} (hrs : r ≠ s) (hcd : c ≠ d) :
    twoRowPerturbation M r s
        (scaledCheckerboardDirection (n := n) (checkerboardExchangeAmount M r s c d) c d)
        (-(scaledCheckerboardDirection (n := n) (checkerboardExchangeAmount M r s c d) c d))
        1 r d = 0 ∨
      twoRowPerturbation M r s
        (scaledCheckerboardDirection (n := n) (checkerboardExchangeAmount M r s c d) c d)
        (-(scaledCheckerboardDirection (n := n) (checkerboardExchangeAmount M r s c d) c d))
        1 s c = 0 := by
  by_cases hle : M r d ≤ M s c
  · left
    simp [twoRowPerturbation, scaledCheckerboardDirection, checkerboardDirection,
      checkerboardExchangeAmount, hrs, hcd, min_eq_left hle]
  · right
    have hle' : M s c ≤ M r d := le_of_lt (lt_of_not_ge hle)
    simp [twoRowPerturbation, scaledCheckerboardDirection, checkerboardDirection,
      checkerboardExchangeAmount, hcd, min_eq_right hle']

theorem checkerboardExchangeAmount_mem_and_permanent_convex_and_endpoint_zero
    {c d : n} (hrs : r ≠ s) (hcd : c ≠ d) (hM : M ∈ doublyStochastic ℝ n)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let a := checkerboardExchangeAmount M r s c d
    twoRowPerturbation M r s (scaledCheckerboardDirection (n := n) a c d)
        (-(scaledCheckerboardDirection (n := n) a c d)) t ∈ doublyStochastic ℝ n ∧
      (twoRowPerturbation M r s (scaledCheckerboardDirection (n := n) a c d)
        (-(scaledCheckerboardDirection (n := n) a c d)) t).permanent ≤
        (1 - t) * M.permanent +
          t * (twoRowPerturbation M r s (scaledCheckerboardDirection (n := n) a c d)
            (-(scaledCheckerboardDirection (n := n) a c d)) 1).permanent ∧
      (twoRowPerturbation M r s (scaledCheckerboardDirection (n := n) a c d)
        (-(scaledCheckerboardDirection (n := n) a c d)) 1 r d = 0 ∨
        twoRowPerturbation M r s (scaledCheckerboardDirection (n := n) a c d)
          (-(scaledCheckerboardDirection (n := n) a c d)) 1 s c = 0) := by
  dsimp only
  have hmain := scaledCheckerboardPerturbation_mem_and_permanent_convex_between_endpoints
    (M := M) (r := r) (s := s) (c := c) (d := d) hrs hcd hM
    (checkerboardExchangeAmount_nonneg
      (M := M) (r := r) (s := s) (c := c) (d := d)
      (fun i j => nonneg_of_mem_doublyStochastic hM))
    (by
      unfold checkerboardExchangeAmount
      exact min_le_left (M r d) (M s c))
    (by
      unfold checkerboardExchangeAmount
      exact min_le_right (M r d) (M s c))
    ht0 ht1
  exact ⟨hmain.1, hmain.2,
    scaledCheckerboardPerturbation_exchangeAmount_endpoint_zero
      (M := M) (r := r) (s := s) (c := c) (d := d) hrs hcd⟩

/-! ## Elementary `2 × 2` log-concavity model -/

/-- The permanent bilinear form for a matrix with rows `u` and `v` in dimension `2`. -/
def twoByTwoRowPermanent (u v : Fin 2 → ℝ) : ℝ :=
  u 0 * v 1 + u 1 * v 0

theorem twoByTwoRowPermanent_self (u : Fin 2 → ℝ) :
    twoByTwoRowPermanent u u = 2 * (u 0 * u 1) := by
  unfold twoByTwoRowPermanent
  ring

theorem twoByTwoRowPermanent_logConcave (u v : Fin 2 → ℝ) :
    twoByTwoRowPermanent u u * twoByTwoRowPermanent v v ≤
      twoByTwoRowPermanent u v ^ 2 := by
  unfold twoByTwoRowPermanent
  nlinarith [sq_nonneg (u 0 * v 1 - u 1 * v 0)]

end

end ProofsInTheBook.PermanentConvexity
