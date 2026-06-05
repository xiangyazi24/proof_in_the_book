import ProofsInTheBook.TetPearls

/-!
# Volume of a tetrahedron: `volume T.carrier = |det edgeMatrix| / 6`

This file discharges the single named-statement gap left open in `TetPearls.lean`, namely
`VolumeTetFormula`.  Mathlib has no off-the-shelf simplex-volume lemma, so we build the missing
ingredient — the volume of the *corner simplex* `{x : 0 ≤ xᵢ, ∑ xᵢ ≤ c}` is `cⁿ / n!` — by a
clean induction on the dimension, using the volume-preserving `Fin (n+1) ≃ ℝ × Fin n` split and
Tonelli.  Then:

* the corner simplex in `Fin 3 → ℝ` has volume `1/6`;
* transporting along the volume-preserving `WithLp.toLp` identifies it with the standard simplex in
  `EuclideanSpace ℝ (Fin 3)`;
* the tetrahedron carrier is the image of that standard simplex under the affine map
  `x ↦ v 0 + ∑ xᵢ • (v (i.succ) − v 0)`, whose linear part is `Matrix.toEuclideanLin edgeMatrixᵀ`;
* `addHaar_image_linearMap` scales volume by `|det|`, translation is measure invariant, and
  `det edgeMatrixᵀ = det edgeMatrix`.

The end result `volumeTetFormula : VolumeTetFormula` is proved with **no** `sorry`/`axiom`/`admit`.
-/

noncomputable section

open scoped Classical ENNReal Matrix
open MeasureTheory Set

namespace ProofsInTheBook.TetVolume

/-! ## The corner simplex in `Fin n → ℝ` and its volume `cⁿ / n!` -/

/-- The closed *corner simplex* of "size" `c` in `Fin n → ℝ`:
`{x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ c}`. -/
def cornerSimplex (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ c}

theorem measurableSet_cornerSimplex (n : ℕ) (c : ℝ) :
    MeasurableSet (cornerSimplex n c) := by
  have h1 : MeasurableSet {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    have : {x : Fin n → ℝ | ∀ i, 0 ≤ x i} = ⋂ i, {x : Fin n → ℝ | 0 ≤ x i} := by
      ext x; simp [Set.mem_iInter]
    rw [this]
    refine MeasurableSet.iInter (fun i => ?_)
    exact measurableSet_le measurable_const (measurable_pi_apply i)
  have h2 : MeasurableSet {x : Fin n → ℝ | ∑ i, x i ≤ c} := by
    refine measurableSet_le ?_ measurable_const
    exact Finset.univ.measurable_sum (fun i _ => measurable_pi_apply i)
  exact h1.inter h2

/-- The corner simplex is empty when its size is negative (for every dimension, including `0`:
the empty sum `0` already violates `∑ ≤ c < 0`). -/
theorem cornerSimplex_eq_empty_of_neg {n : ℕ} {c : ℝ} (hc : c < 0) :
    cornerSimplex n c = (∅ : Set (Fin n → ℝ)) := by
  ext x
  simp only [cornerSimplex, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hpos, hsum⟩
  have : (0 : ℝ) ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hpos i)
  linarith

/-- Volume of the corner simplex is `0` when its size is negative. -/
theorem volume_cornerSimplex_of_neg {n : ℕ} {c : ℝ} (hc : c < 0) :
    volume (cornerSimplex n c) = 0 := by
  rw [cornerSimplex_eq_empty_of_neg hc, measure_empty]

/-- Volume of the `0`-dimensional corner simplex: a single point, volume `1`, for `c ≥ 0`. -/
theorem volume_cornerSimplex_zero {c : ℝ} (hc : 0 ≤ c) :
    volume (cornerSimplex 0 c) = ENNReal.ofReal (c ^ 0 / (Nat.factorial 0)) := by
  have huniv : cornerSimplex 0 c = (Set.univ : Set (Fin 0 → ℝ)) := by
    ext x
    simp only [cornerSimplex, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨fun i => i.elim0, by simp [hc]⟩
  rw [huniv]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one]
  -- volume of univ in `Fin 0 → ℝ` is 1
  rw [show (volume : Measure (Fin 0 → ℝ)) = Measure.pi (fun _ => volume) from rfl]
  rw [Measure.pi_univ]
  simp

/-- The key splitting identity: under the volume-preserving equivalence
`f : (Fin (n+1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ)`, `f x = (x 0, fun j => x j.succ)`, the corner simplex
`cornerSimplex (n+1) c` is the preimage of the product-shaped set
`{p | 0 ≤ p.1 ∧ (∀ j, 0 ≤ p.2 j) ∧ p.1 + ∑ j, p.2 j ≤ c}`. -/
theorem cornerSimplex_succ_eq_preimage (n : ℕ) (c : ℝ) :
    cornerSimplex (n + 1) c =
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0) ⁻¹'
        {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ (∀ j, 0 ≤ p.2 j) ∧ p.1 + ∑ j, p.2 j ≤ c} := by
  ext x
  simp only [cornerSimplex, Set.mem_setOf_eq, Set.mem_preimage,
    MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply]
  constructor
  · rintro ⟨hpos, hsum⟩
    refine ⟨hpos 0, fun j => ?_, ?_⟩
    · simpa [Fin.succAbove_zero] using hpos j.succ
    · rw [Fin.sum_univ_succ] at hsum
      simpa [Fin.succAbove_zero] using hsum
  · rintro ⟨h0, hj, hsum⟩
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using h0
      · intro j; simpa [Fin.succAbove_zero] using hj j
    · rw [Fin.sum_univ_succ]
      simpa [Fin.succAbove_zero] using hsum

/-- The first-coordinate slice of the product-shaped set: for fixed `t`, the set of `y : Fin n → ℝ`
with `(∀ j, 0 ≤ y j) ∧ t + ∑ j, y j ≤ c`.  If `0 ≤ t` this is exactly `cornerSimplex n (c - t)`. -/
theorem slice_eq_cornerSimplex {n : ℕ} {c t : ℝ} :
    {y : Fin n → ℝ | (0 ≤ t ∧ (∀ j, 0 ≤ y j) ∧ t + ∑ j, y j ≤ c)} =
      (if 0 ≤ t then cornerSimplex n (c - t) else ∅) := by
  by_cases ht : 0 ≤ t
  · simp only [ht, true_and, if_true]
    ext y
    simp only [cornerSimplex, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp, hs⟩; exact ⟨hp, by linarith⟩
    · rintro ⟨hp, hs⟩; exact ⟨hp, by linarith⟩
  · simp only [ht, false_and, if_false]
    ext y
    simp

/-- **Volume of the corner simplex**: `volume (cornerSimplex n c) = ENNReal.ofReal (cⁿ / n!)`
for `c ≥ 0`. -/
theorem volume_cornerSimplex (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    volume (cornerSimplex n c) = ENNReal.ofReal (c ^ n / (Nat.factorial n)) := by
  induction n generalizing c with
  | zero => exact volume_cornerSimplex_zero hc
  | succ n ih =>
    -- Move to the product `ℝ × (Fin n → ℝ)` via the volume-preserving equivalence.
    set f := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with hf
    set P : Set (ℝ × (Fin n → ℝ)) :=
      {p | 0 ≤ p.1 ∧ (∀ j, 0 ≤ p.2 j) ∧ p.1 + ∑ j, p.2 j ≤ c} with hP
    have hmp : MeasurePreserving f
        (volume : Measure (Fin (n + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
      have := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
      simpa using this
    have hPmeas : MeasurableSet P := by
      have hp1 : MeasurableSet {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1} :=
        measurableSet_le measurable_const measurable_fst
      have hp2 : MeasurableSet {p : ℝ × (Fin n → ℝ) | ∀ j, 0 ≤ p.2 j} := by
        have : {p : ℝ × (Fin n → ℝ) | ∀ j, 0 ≤ p.2 j}
            = ⋂ j, {p : ℝ × (Fin n → ℝ) | 0 ≤ p.2 j} := by
          ext p; simp [Set.mem_iInter]
        rw [this]
        refine MeasurableSet.iInter (fun j => ?_)
        exact measurableSet_le measurable_const ((measurable_pi_apply j).comp measurable_snd)
      have hp3 : MeasurableSet {p : ℝ × (Fin n → ℝ) | p.1 + ∑ j, p.2 j ≤ c} := by
        refine measurableSet_le ?_ measurable_const
        refine measurable_fst.add ?_
        exact Finset.univ.measurable_sum
          (fun j _ => (measurable_pi_apply j).comp measurable_snd)
      have heq : P = {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1} ∩ {p | ∀ j, 0 ≤ p.2 j}
          ∩ {p | p.1 + ∑ j, p.2 j ≤ c} := by
        rw [hP]; ext p; simp only [Set.mem_inter_iff, Set.mem_setOf_eq]; tauto
      rw [heq]
      exact (hp1.inter hp2).inter hp3
    rw [cornerSimplex_succ_eq_preimage n c, ← hf, ← hP]
    rw [hmp.measure_preimage hPmeas.nullMeasurableSet]
    -- Tonelli for sets: prod measure = ∫⁻ t, volume (slice at t)
    rw [Measure.prod_apply hPmeas]
    -- Identify the slice.
    have hslice : ∀ t : ℝ, (Prod.mk t ⁻¹' P)
        = (if 0 ≤ t then cornerSimplex n (c - t) else ∅) := by
      intro t
      rw [← slice_eq_cornerSimplex (n := n) (c := c) (t := t)]
      ext y
      simp only [hP, Set.mem_preimage, Set.mem_setOf_eq]
    -- The integrand equals the indicator of `[0,c]` of `(c-t)^n / n!`.
    have hint : (fun t => volume (Prod.mk t ⁻¹' P))
        = (Set.Icc (0:ℝ) c).indicator
            (fun t => ENNReal.ofReal ((c - t) ^ n / (Nat.factorial n))) := by
      funext t
      rw [hslice t]
      by_cases ht : 0 ≤ t
      · simp only [ht, if_true]
        by_cases htc : t ≤ c
        · rw [ih (by linarith), Set.indicator_of_mem (Set.mem_Icc.mpr ⟨ht, htc⟩)]
        · -- t > c : `c - t < 0`, simplex empty, volume 0; indicator also 0.
          rw [volume_cornerSimplex_of_neg (by linarith : c - t < 0),
            Set.indicator_of_notMem (by simp [Set.mem_Icc, htc])]
      · simp only [ht, if_false, measure_empty]
        rw [Set.indicator_of_notMem (by simp [Set.mem_Icc, ht])]
    rw [hint]
    -- ∫⁻ t, indicator [0,c] (ofReal ((c-t)^n/n!)) = c^(n+1)/(n+1)!.
    rw [lintegral_indicator measurableSet_Icc]
    -- Nonnegativity of the integrand on [0,c].
    have hnn : ∀ t ∈ Set.Icc (0:ℝ) c, 0 ≤ (c - t) ^ n / (Nat.factorial n) := by
      intro t ht
      apply div_nonneg
      · exact pow_nonneg (by linarith [ht.2]) n
      · positivity
    have hcont : ContinuousOn (fun t => (c - t) ^ n / (Nat.factorial n)) (Set.Icc 0 c) := by
      fun_prop
    have hintegrable : IntegrableOn
        (fun t => (c - t) ^ n / (Nat.factorial n)) (Set.Icc 0 c) volume :=
      hcont.integrableOn_compact isCompact_Icc
    -- Convert the lintegral of `ofReal` into `ofReal` of a Bochner set integral.
    rw [← ofReal_integral_eq_lintegral_ofReal hintegrable
        ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hnn))]
    -- Compute the real set integral over Icc 0 c.
    have hval : ∫ t in Set.Icc (0:ℝ) c, (c - t) ^ n / (Nat.factorial n)
        = c ^ (n + 1) / (Nat.factorial (n + 1)) := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hc]
      have hpull : ∫ t in (0:ℝ)..c, (c - t) ^ n / (Nat.factorial n)
          = (∫ t in (0:ℝ)..c, (c - t) ^ n) / (Nat.factorial n) := by
        rw [intervalIntegral.integral_div]
      rw [hpull]
      have hsub : ∫ t in (0:ℝ)..c, (c - t) ^ n = ∫ u in (0:ℝ)..c, u ^ n := by
        have := intervalIntegral.integral_comp_sub_left (a := 0) (b := c)
          (fun u => u ^ n) c
        simpa using this
      rw [hsub, integral_pow]
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    rw [hval]

/-! ## Transport to `EuclideanSpace ℝ (Fin 3)` -/

open ProofsInTheBook.TetPearls

/-- The corner simplex `{x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}` in Euclidean 3-space. -/
def cornerSimplexE : Set Pt3 := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

/-- The Euclidean corner simplex is the preimage of `cornerSimplex 3 1` under `WithLp.ofLp`
(which is the symm of the volume-preserving `MeasurableEquiv.toLp`). -/
theorem cornerSimplexE_eq_preimage :
    cornerSimplexE = (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm ⁻¹' cornerSimplex 3 1 := by
  ext x
  simp only [cornerSimplexE, cornerSimplex, Set.mem_setOf_eq, Set.mem_preimage,
    MeasurableEquiv.coe_toLp_symm]

/-- Volume of the Euclidean corner simplex is `1/6`. -/
theorem volume_cornerSimplexE : volume cornerSimplexE = ENNReal.ofReal (1 / 6) := by
  rw [cornerSimplexE_eq_preimage]
  have hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm
      (volume : Measure Pt3) (volume : Measure (Fin 3 → ℝ)) :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))
  rw [hmp.measure_preimage_equiv, volume_cornerSimplex 3 (by norm_num)]
  norm_num [Nat.factorial]

/-! ## The standard simplex as a convex hull of `{0, e₀, e₁, e₂}` -/

/-- The four "standard vertices" of the corner simplex: `0` and the three unit basis vectors. -/
def stdVerts : Fin 4 → Pt3 :=
  Fin.cases (0 : Pt3) (fun j => EuclideanSpace.single j 1)

theorem stdVerts_zero : stdVerts 0 = 0 := rfl

theorem stdVerts_succ (j : Fin 3) : stdVerts j.succ = EuclideanSpace.single j 1 := rfl

theorem cornerSimplexE_convex : Convex ℝ cornerSimplexE := by
  have hlin : ∀ i : Fin 3, IsLinearMap ℝ (fun x : Pt3 => x i) :=
    fun i => ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  have h1 : Convex ℝ {x : Pt3 | ∀ i, 0 ≤ x i} := by
    have heq : {x : Pt3 | ∀ i, 0 ≤ x i} = ⋂ i, {x : Pt3 | (0:ℝ) ≤ (fun x : Pt3 => x i) x} := by
      ext x; simp [Set.mem_iInter]
    rw [heq]
    exact convex_iInter (fun i => convex_halfSpace_ge (hlin i) 0)
  have h2 : Convex ℝ {x : Pt3 | ∑ i, x i ≤ 1} := by
    have hlin2 : IsLinearMap ℝ (fun x : Pt3 => ∑ i, x i) := by
      refine ⟨fun a b => ?_, fun c a => ?_⟩
      · simp only [PiLp.add_apply]; rw [Finset.sum_add_distrib]
      · simp only [PiLp.smul_apply, smul_eq_mul]; rw [Finset.mul_sum]
    exact convex_halfSpace_le hlin2 1
  exact h1.inter h2

/-- The standard corner simplex in `EuclideanSpace ℝ (Fin 3)` is the convex hull of
`{0, e₀, e₁, e₂}`. -/
theorem convexHull_stdVerts_eq_cornerSimplexE :
    convexHull ℝ (Set.range stdVerts) = cornerSimplexE := by
  apply Set.Subset.antisymm
  · -- the hull is contained in the (convex) corner simplex
    refine convexHull_min ?_ cornerSimplexE_convex
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ ?_ i
    · -- stdVerts 0 = 0
      simp only [stdVerts_zero, cornerSimplexE, Set.mem_setOf_eq]
      refine ⟨fun k => le_refl 0, ?_⟩
      simp
    · -- stdVerts (j.succ) = single j 1
      intro j
      simp only [stdVerts_succ, cornerSimplexE, Set.mem_setOf_eq]
      constructor
      · intro k
        simp only [PiLp.single_apply]
        split <;> norm_num
      · rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk; simp [hk]
        · intro h; exact absurd (Finset.mem_univ j) h
  · -- every corner-simplex point is a convex combination of the four vertices
    intro x hx
    obtain ⟨hpos, hsum⟩ := hx
    -- weights: w 0 = 1 - ∑ x, w (j.succ) = x j
    set w : Fin 4 → ℝ := Fin.cases (1 - ∑ i, x i) (fun j => x j) with hw
    have hw0 : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intro i _
      refine Fin.cases ?_ ?_ i
      · show 0 ≤ 1 - ∑ i, x i; linarith
      · intro j; exact hpos j
    have hwsum : ∑ i, w i = 1 := by
      rw [Fin.sum_univ_succ]
      show (1 - ∑ i, x i) + ∑ j : Fin 3, w j.succ = 1
      have : ∀ j : Fin 3, w j.succ = x j := fun j => rfl
      simp only [this]
      ring
    have hcm := Finset.univ.centerMass_mem_convexHull (z := stdVerts) hw0
      (by rw [hwsum]; norm_num) (fun i _ => Set.mem_range_self i)
    rw [Finset.centerMass, hwsum] at hcm
    simp only [inv_one, one_smul] at hcm
    -- show the center of mass equals x
    have hval : ∑ i, w i • stdVerts i = x := by
      rw [Fin.sum_univ_succ]
      show w 0 • stdVerts 0 + ∑ j : Fin 3, w j.succ • stdVerts j.succ = x
      simp only [stdVerts_zero, smul_zero, zero_add]
      have hsucc : ∀ j : Fin 3, w j.succ • stdVerts j.succ = x j • EuclideanSpace.single j 1 := by
        intro j; rw [stdVerts_succ]; rfl
      simp only [hsucc]
      refine PiLp.ext (fun k => ?_)
      have hcoord : (∑ j : Fin 3, x j • (EuclideanSpace.single j 1 : Pt3)) k
          = ∑ j : Fin 3, (x j • (EuclideanSpace.single j 1 : Pt3)) k := by
        have := WithLp.ofLp_sum (p := 2) (V := Fin 3 → ℝ) Finset.univ
          (fun j => x j • (EuclideanSpace.single j 1 : Pt3))
        exact congrFun this k
      rw [hcoord]
      simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro h; exact absurd (Finset.mem_univ k) h
    rwa [hval] at hcm

/-! ## The affine map carrying the standard simplex onto a tetrahedron -/

/-- The linear part of the affine parametrization: the Euclidean linear map of the transpose of the
edge matrix.  Its columns are the edge vectors `v (j.succ) − v 0`. -/
def edgeLin (T : Tet) : Pt3 →ₗ[ℝ] Pt3 :=
  Matrix.toEuclideanLin (Matrix.transpose T.edgeMatrix)

/-- `edgeLin` sends the `j`-th unit vector to the `j`-th edge vector `v (j.succ) − v 0`. -/
theorem edgeLin_single (T : Tet) (j : Fin 3) :
    edgeLin T (EuclideanSpace.single j 1) = T.v j.succ - T.v 0 := by
  refine PiLp.ext (fun i => ?_)
  rw [edgeLin]
  show (Matrix.mulVec (Matrix.transpose T.edgeMatrix) (Pi.single j (1:ℝ))) i
      = (T.v j.succ - T.v 0) i
  rw [Matrix.mulVec_single_one]
  show (Matrix.transpose T.edgeMatrix) i j = (T.v j.succ - T.v 0) i
  rw [Matrix.transpose_apply, Tet.edgeMatrix]

/-- The determinant of `edgeLin` is the edge-matrix determinant. -/
theorem det_edgeLin (T : Tet) : LinearMap.det (edgeLin T) = T.edgeMatrix.det := by
  rw [edgeLin, Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin,
    Matrix.det_transpose]

/-- The affine parametrization `A x = v 0 + edgeLin x`, which maps the standard vertices onto the
tetrahedron's vertices. -/
def edgeAffine (T : Tet) : Pt3 → Pt3 := fun x => T.v 0 + edgeLin T x

theorem edgeAffine_stdVerts (T : Tet) : edgeAffine T ∘ stdVerts = T.v := by
  funext i
  refine Fin.cases ?_ ?_ i
  · show T.v 0 + edgeLin T (stdVerts 0) = T.v 0
    rw [stdVerts_zero, map_zero, add_zero]
  · intro j
    show T.v 0 + edgeLin T (stdVerts j.succ) = T.v j.succ
    rw [stdVerts_succ, edgeLin_single]
    abel

theorem edgeAffine_image_stdVerts (T : Tet) :
    edgeAffine T '' (Set.range stdVerts) = Set.range T.v := by
  rw [← Set.range_comp, edgeAffine_stdVerts]

/-- The carrier of the tetrahedron is the `edgeAffine`-image of the standard corner simplex. -/
theorem carrier_eq_image (T : Tet) :
    T.carrier = edgeAffine T '' cornerSimplexE := by
  rw [Tet.carrier, ← convexHull_stdVerts_eq_cornerSimplexE]
  -- edgeAffine is affine; use AffineMap.image_convexHull
  set A : Pt3 →ᵃ[ℝ] Pt3 := (edgeLin T).toAffineMap + AffineMap.const ℝ Pt3 (T.v 0) with hA
  have hAcoe : ⇑A = edgeAffine T := by
    funext x
    rw [hA, AffineMap.coe_add, Pi.add_apply, LinearMap.coe_toAffineMap,
      AffineMap.coe_const, Function.const_apply, edgeAffine, add_comm]
  rw [← hAcoe, A.image_convexHull, hAcoe, edgeAffine_image_stdVerts]

/-- Volume is multiplied by `|det|` under `edgeAffine` (linear scaling + translation invariance). -/
theorem volume_edgeAffine_image (T : Tet) (s : Set Pt3) :
    volume (edgeAffine T '' s)
      = ENNReal.ofReal |LinearMap.det (edgeLin T)| * volume s := by
  have hsplit : edgeAffine T '' s
      = (MeasurableEquiv.addLeft (T.v 0)) '' (edgeLin T '' s) := by
    rw [Set.image_image]
    rfl
  rw [hsplit]
  -- translation invariance: image under addLeft = preimage under addLeft (-v0)
  have hinv : (MeasurableEquiv.addLeft (T.v 0)) '' (edgeLin T '' s)
      = (fun y => (-T.v 0) + y) ⁻¹' (edgeLin T '' s) := by
    rw [Set.image_eq_preimage_of_inverse]
    · intro x; simp
    · intro x; simp
  rw [hinv]
  have hmp : MeasurePreserving (⇑(MeasurableEquiv.addLeft (-T.v 0)))
      (volume : Measure Pt3) (volume : Measure Pt3) := by
    rw [MeasurableEquiv.coe_addLeft]
    exact measurePreserving_add_left (volume : Measure Pt3) (-T.v 0)
  rw [show (fun y => (-T.v 0) + y) = ⇑(MeasurableEquiv.addLeft (-T.v 0)) from
    (MeasurableEquiv.coe_addLeft _).symm]
  rw [hmp.measure_preimage_equiv]
  -- linear scaling
  rw [Measure.addHaar_image_linearMap (volume : Measure Pt3) (edgeLin T)]

/-! ## The volume formula -/

/-- **Volume of a tetrahedron.** `volume T.carrier = |det edgeMatrix| / 6`. -/
theorem volumeTetFormula : VolumeTetFormula := by
  intro T
  rw [carrier_eq_image, volume_edgeAffine_image, volume_cornerSimplexE, det_edgeLin]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

end ProofsInTheBook.TetVolume
