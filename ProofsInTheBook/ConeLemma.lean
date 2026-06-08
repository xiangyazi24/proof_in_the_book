import Mathlib
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Cone lemma

This file proves the rational cone lemma used in Chapter 9: a strictly positive
real point in the kernel of a rational matrix yields a strictly positive
integer point in the same kernel.
-/

namespace ProofsInTheBook

open scoped BigOperators
open TensorProduct

noncomputable section

namespace ConeLemma

variable {M N : ℕ}

private lemma cast_mulVec_eq_zero_of_rat
    (A : Matrix (Fin M) (Fin N) ℚ) (q : Fin N → ℚ)
    (hq : A.mulVec q = 0) :
    (A.map ((↑) : ℚ → ℝ)).mulVec (fun j => (q j : ℝ)) = 0 := by
  ext i
  calc
    ((A.map ((↑) : ℚ → ℝ)).mulVec (fun j => (q j : ℝ))) i
        = ((A.mulVec q i : ℚ) : ℝ) := by
          exact (RingHom.map_mulVec (Rat.castHom ℝ) A q i).symm
    _ = 0 := by simp [hq]

private lemma rat_kernel_vector_mem_real_kernel
    (A : Matrix (Fin M) (Fin N) ℚ)
    (q : LinearMap.ker A.mulVecLin) :
    (fun j : Fin N => ((q : Fin N → ℚ) j : ℝ)) ∈
      LinearMap.ker (A.map ((↑) : ℚ → ℝ)).mulVecLin := by
  change (A.map ((↑) : ℚ → ℝ)).mulVec (fun j => ((q : Fin N → ℚ) j : ℝ)) = 0
  exact cast_mulVec_eq_zero_of_rat A q q.property

private lemma lTensor_mulVecLin_piScalarRight
    (A : Matrix (Fin M) (Fin N) ℚ) :
    (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin M)).toLinearMap.comp
        (AlgebraTensorModule.lTensor ℝ ℝ A.mulVecLin) =
      (A.map ((↑) : ℚ → ℝ)).mulVecLin.comp
        (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N)).toLinearMap := by
  classical
  ext r v
  simp [Matrix.mulVec, dotProduct]
  change ((A v r : ℚ) : ℝ) =
    (fun x : Fin N => ((A v x : ℚ) : ℝ)) ⬝ᵥ
      (fun x : Fin N => (((Pi.single r (1 : ℚ) : Fin N → ℚ) x : ℚ) : ℝ))
  have hsingle :
      (fun x : Fin N => (((Pi.single r (1 : ℚ) : Fin N → ℚ) x : ℚ) : ℝ)) =
        Pi.single r (1 : ℝ) := by
    ext x
    by_cases hx : x = r
    · subst x
      simp [Pi.single]
    · simp [Pi.single, hx]
  rw [hsingle]
  exact (dotProduct_single_one (fun x : Fin N => ((A v x : ℚ) : ℝ)) r).symm

private lemma real_kernel_eq_tensor_span
    (A : Matrix (Fin M) (Fin N) ℚ)
    (x : LinearMap.ker (A.map ((↑) : ℚ → ℝ)).mulVecLin) :
    ∃ t : ℝ ⊗[ℚ] LinearMap.ker A.mulVecLin,
      (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N))
        ((LinearMap.ker A.mulVecLin).subtype.lTensor ℝ t) = (x : Fin N → ℝ) := by
  let eN := TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N)
  let eM := TensorProduct.piScalarRight ℚ ℝ ℝ (Fin M)
  have hcomm := lTensor_mulVecLin_piScalarRight A
  let xt : ℝ ⊗[ℚ] (Fin N → ℚ) := eN.symm (x : Fin N → ℝ)
  have hxt : xt ∈ LinearMap.ker (AlgebraTensorModule.lTensor ℝ ℝ A.mulVecLin) := by
    change AlgebraTensorModule.lTensor ℝ ℝ A.mulVecLin xt = 0
    apply eM.injective
    calc
      eM (AlgebraTensorModule.lTensor ℝ ℝ A.mulVecLin xt)
          = (A.map ((↑) : ℚ → ℝ)).mulVecLin (eN xt) := by
            simpa [LinearMap.comp_apply, eN, eM, xt] using congrFun (congrArg DFunLike.coe hcomm) xt
      _ = (A.map ((↑) : ℚ → ℝ)).mulVecLin (x : Fin N → ℝ) := by simp [xt, eN]
      _ = 0 := x.property
  refine ⟨(LinearMap.tensorKerEquiv ℝ ℝ A.mulVecLin).symm ⟨xt, hxt⟩, ?_⟩
  have hsub :
      (LinearMap.ker A.mulVecLin).subtype.lTensor ℝ
          ((LinearMap.tensorKerEquiv ℝ ℝ A.mulVecLin).symm ⟨xt, hxt⟩) = xt := by
    exact
      LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm (S := ℝ) (M := ℝ)
        (f := A.mulVecLin) ⟨xt, hxt⟩
  calc
    eN ((LinearMap.ker A.mulVecLin).subtype.lTensor ℝ
          ((LinearMap.tensorKerEquiv ℝ ℝ A.mulVecLin).symm ⟨xt, hxt⟩))
        = eN xt := by rw [hsub]
    _ = (x : Fin N → ℝ) := by simp [xt, eN]

private lemma piScalarRight_lTensor_smul_baseChange_apply
    (A : Matrix (Fin M) (Fin N) ℚ)
    (r : ℝ) (q : LinearMap.ker A.mulVecLin) (j : Fin N) :
    (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N))
        ((LinearMap.ker A.mulVecLin).subtype.lTensor ℝ
          (r • ((1 : ℝ) ⊗ₜ[ℚ] q))) j =
      r * ((q : Fin N → ℚ) j : ℝ) := by
  change ((TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N)).toLinearMap
        ((LinearMap.ker A.mulVecLin).subtype.lTensor ℝ
          (r • ((1 : ℝ) ⊗ₜ[ℚ] q)))) j =
      r * ((q : Fin N → ℚ) j : ℝ)
  rw [TensorProduct.smul_tmul']
  simp [TensorProduct.piScalarRight, LinearMap.lTensor_tmul, Algebra.smul_def, smul_eq_mul,
    mul_comm]

private lemma exists_real_kernel_basis_expansion
    (A : Matrix (Fin M) (Fin N) ℚ)
    (x : LinearMap.ker (A.map ((↑) : ℚ → ℝ)).mulVecLin) :
    ∃ c : Fin (Module.finrank ℚ (LinearMap.ker A.mulVecLin)) → ℝ,
      (x : Fin N → ℝ) =
        fun j =>
          ∑ i : Fin (Module.finrank ℚ (LinearMap.ker A.mulVecLin)),
            c i * ((Module.finBasis ℚ (LinearMap.ker A.mulVecLin) i : Fin N → ℚ) j : ℝ) := by
  let b := Module.finBasis ℚ (LinearMap.ker A.mulVecLin)
  obtain ⟨t, ht⟩ := real_kernel_eq_tensor_span A x
  let bR := b.baseChange ℝ
  refine ⟨fun i => bR.repr t i, ?_⟩
  ext j
  calc
    (x : Fin N → ℝ) j =
        (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N)
          ((LinearMap.ker A.mulVecLin).subtype.lTensor ℝ t)) j := by
          rw [ht]
    _ =
        (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N)
          ((LinearMap.ker A.mulVecLin).subtype.lTensor ℝ
            (∑ i, bR.repr t i • bR i))) j := by
          exact congrArg (fun y =>
            (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N)
              ((LinearMap.ker A.mulVecLin).subtype.lTensor ℝ y)) j)
            (bR.sum_repr t).symm
    _ = ∑ i,
          (TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N)
            ((LinearMap.ker A.mulVecLin).subtype.lTensor ℝ
              (bR.repr t i • bR i))) j := by
          change ((TensorProduct.piScalarRight ℚ ℝ ℝ (Fin N)).toLinearMap
            ((LinearMap.ker A.mulVecLin).subtype.lTensor ℝ
              (∑ i, bR.repr t i • bR i))) j = _
          rw [map_sum]
          rw [map_sum]
          simp
    _ = ∑ i, (bR.repr t i) *
          ((Module.finBasis ℚ (LinearMap.ker A.mulVecLin) i : Fin N → ℚ) j : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _hi
          simpa [b, bR, Module.Basis.baseChange_apply] using
            piScalarRight_lTensor_smul_baseChange_apply A (bR.repr t i) (b i) j

private lemma exists_rat_near_real (x ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℚ, |(q : ℝ) - x| < ε := by
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (sub_lt_self x hε)
  refine ⟨q, ?_⟩
  rw [abs_lt]
  constructor <;> linarith

private lemma abs_sum_mul_le
    {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    |∑ i, a i * b i| ≤ ∑ i, |a i| * |b i| := by
  calc
    |∑ i, a i * b i| ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |a i| * |b i| := by simp [abs_mul]

private lemma exists_positive_rat_kernel_vector
    (A : Matrix (Fin M) (Fin N) ℚ)
    (x : Fin N → ℝ)
    (hsol : (A.map ((↑) : ℚ → ℝ)).mulVec x = 0)
    (hpos : ∀ j, 0 < x j) :
    ∃ q : Fin N → ℚ, (∀ j, 0 < q j) ∧ A.mulVec q = 0 := by
  classical
  by_cases hN : IsEmpty (Fin N)
  · let q : Fin N → ℚ := fun j => False.elim (hN.false j)
    refine ⟨q, ?_, ?_⟩
    · intro j
      exact False.elim (hN.false j)
    · ext i
      simp [Matrix.mulVec, dotProduct, q]
  haveI : Nonempty (Fin N) := not_isEmpty_iff.mp hN
  let xr : LinearMap.ker (A.map ((↑) : ℚ → ℝ)).mulVecLin := ⟨x, hsol⟩
  obtain ⟨c, hc⟩ := exists_real_kernel_basis_expansion A xr
  let k := Module.finrank ℚ (LinearMap.ker A.mulVecLin)
  let b := Module.finBasis ℚ (LinearMap.ker A.mulVecLin)
  let v : Fin k → Fin N → ℝ := fun i j => ((b i : Fin N → ℚ) j : ℝ)
  have hx : x = fun j => ∑ i : Fin k, c i * v i j := by
    simpa [k, b, v] using hc
  let S : Fin N → ℝ := fun j => ∑ i : Fin k, |v i j|
  have hS_nonneg : ∀ j, 0 ≤ S j := by
    intro j
    exact Finset.sum_nonneg fun i _ => abs_nonneg _
  let δ : Fin N → ℝ := fun j => if S j = 0 then 1 else x j / (2 * S j)
  have hδ_pos : ∀ j, 0 < δ j := by
    intro j
    by_cases hS : S j = 0
    · simp [δ, hS]
    · have hSpos : 0 < S j := lt_of_le_of_ne (hS_nonneg j) (Ne.symm hS)
      rw [show δ j = x j / (2 * S j) by simp [δ, hS]]
      exact div_pos (hpos j) (mul_pos (by norm_num) hSpos)
  let ε : ℝ := (Finset.univ.image δ).min' (by
    classical
    exact Finset.image_nonempty.mpr Finset.univ_nonempty)
  have hε_pos : 0 < ε := by
    classical
    dsimp [ε]
    have hmem := Finset.min'_mem (Finset.univ.image δ)
      (by exact Finset.image_nonempty.mpr Finset.univ_nonempty)
    rcases Finset.mem_image.mp hmem with ⟨j, -, hj⟩
    simpa [hj] using hδ_pos j
  have hε_le : ∀ j, ε ≤ δ j := by
    intro j
    classical
    dsimp [ε]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  obtain ⟨d, hd⟩ : ∃ d : Fin k → ℚ, ∀ i, |(d i : ℝ) - c i| < ε / (Fintype.card (Fin k) + 1) := by
    choose d hd using fun i : Fin k =>
      exists_rat_near_real (c i) (ε / (Fintype.card (Fin k) + 1 : ℝ))
        (div_pos hε_pos (by positivity))
    exact ⟨d, hd⟩
  let q : Fin N → ℚ := fun j => ∑ i : Fin k, d i * (b i : Fin N → ℚ) j
  have hq_cast : ∀ j, (q j : ℝ) = ∑ i : Fin k, (d i : ℝ) * v i j := by
    intro j
    simp [q, v]
  have hq_pos : ∀ j, 0 < q j := by
    intro j
    have hdiff :
        |(q j : ℝ) - x j| < x j := by
      have hxj : x j = ∑ i : Fin k, c i * v i j := by
        simpa using congrFun hx j
      calc
        |(q j : ℝ) - x j|
            = |(∑ i : Fin k, (d i : ℝ) * v i j) - ∑ i : Fin k, c i * v i j| := by
              rw [hq_cast j, hxj]
        _ = |∑ i : Fin k, (((d i : ℝ) - c i) * v i j)| := by
              congr 1
              simp_rw [sub_mul]
              rw [Finset.sum_sub_distrib]
        _ ≤ ∑ i : Fin k, |(d i : ℝ) - c i| * |v i j| := abs_sum_mul_le _ _
        _ < x j := by
          have hterm : ∀ i : Fin k,
              |(d i : ℝ) - c i| * |v i j| ≤
                (ε / (Fintype.card (Fin k) + 1 : ℝ)) * |v i j| := by
            intro i
            exact mul_le_mul_of_nonneg_right (le_of_lt (hd i)) (abs_nonneg _)
          have hsum_le :
              (∑ i : Fin k, |(d i : ℝ) - c i| * |v i j|) ≤
                (ε / (Fintype.card (Fin k) + 1 : ℝ)) * S j := by
            calc
              (∑ i : Fin k, |(d i : ℝ) - c i| * |v i j|)
                  ≤ ∑ i : Fin k,
                      (ε / (Fintype.card (Fin k) + 1 : ℝ)) * |v i j| :=
                    Finset.sum_le_sum fun i _ => hterm i
              _ = (ε / (Fintype.card (Fin k) + 1 : ℝ)) * S j := by
                    simp [S, Finset.mul_sum]
          have hsmall : (ε / (Fintype.card (Fin k) + 1 : ℝ)) * S j < x j := by
            by_cases hS : S j = 0
            · simp [hS, hpos j]
            · have hSpos : 0 < S j := lt_of_le_of_ne (hS_nonneg j) (Ne.symm hS)
              have hεδ := hε_le j
              have hcard : (1 : ℝ) ≤ (Fintype.card (Fin k) + 1 : ℝ) := by
                norm_num
              have hdiv_le : ε / (Fintype.card (Fin k) + 1 : ℝ) ≤ ε := by
                exact div_le_self hε_pos.le hcard
              have hmain :
                  (ε / (Fintype.card (Fin k) + 1 : ℝ)) * S j ≤
                    δ j * S j := by
                exact mul_le_mul_of_nonneg_right (hdiv_le.trans hεδ) (hS_nonneg j)
              have hδS : δ j * S j = x j / 2 := by
                rw [show δ j = x j / (2 * S j) by simp [δ, hS]]
                field_simp [hS]
              exact lt_of_le_of_lt hmain (by rw [hδS]; linarith [hpos j])
          exact lt_of_le_of_lt hsum_le hsmall
    have : 0 < (q j : ℝ) := by
      rw [abs_sub_lt_iff] at hdiff
      linarith [hpos j]
    exact Rat.cast_pos.mp this
  have hq_mem : A.mulVec q = 0 := by
    have hq_eq : q = ∑ i : Fin k, d i • (b i : Fin N → ℚ) := by
      ext j
      simp [q, Pi.smul_apply, smul_eq_mul]
    change A.mulVecLin q = 0
    rw [hq_eq]
    simp
  exact ⟨q, hq_pos, hq_mem⟩

private lemma exists_positive_int_kernel_vector_of_rat
    (A : Matrix (Fin M) (Fin N) ℚ)
    (q : Fin N → ℚ)
    (hqpos : ∀ j, 0 < q j)
    (hqker : A.mulVec q = 0) :
    ∃ z : Fin N → ℤ, (∀ j, 0 < z j) ∧
      A.mulVec (fun j => (z j : ℚ)) = 0 := by
  classical
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  have hb_ne : (b : ℤ) ≠ 0 := nonZeroDivisors.ne_zero b.property
  let sgn : ℤ := if 0 < (b : ℤ) then 1 else -1
  have hsgn_ne : (sgn : ℤ) ≠ 0 := by
    by_cases hbpos : 0 < (b : ℤ) <;> simp [sgn, hbpos]
  have hcpos : 0 < (sgn : ℤ) * (b : ℤ) := by
    by_cases hbpos : 0 < (b : ℤ)
    · simp [sgn, hbpos]
    · have hbneg : (b : ℤ) < 0 := lt_of_le_of_ne (le_of_not_gt hbpos) hb_ne
      simp [sgn, hbpos, hbneg]
  choose a ha using hb
  let z : Fin N → ℤ := fun j => sgn * a j
  refine ⟨z, ?_, ?_⟩
  · intro j
    have ha_cast : ((a j : ℤ) : ℚ) = ((b : ℤ) : ℚ) * q j := by
      simpa [Algebra.smul_def] using ha j
    have hz_cast : ((z j : ℤ) : ℚ) = (((sgn : ℤ) * (b : ℤ) : ℤ) : ℚ) * q j := by
      simp [z, ha_cast, mul_assoc]
    have hz_pos_rat : 0 < ((z j : ℤ) : ℚ) := by
      rw [hz_cast]
      exact mul_pos (by exact_mod_cast hcpos) (hqpos j)
    exact_mod_cast hz_pos_rat
  · have hz_cast : ∀ j, ((z j : ℤ) : ℚ) = (((sgn : ℤ) * (b : ℤ) : ℤ) : ℚ) * q j := by
      intro j
      have ha_cast : ((a j : ℤ) : ℚ) = ((b : ℤ) : ℚ) * q j := by
        simpa [Algebra.smul_def] using ha j
      simp [z, ha_cast, mul_assoc]
    let c : ℚ := (((sgn : ℤ) * (b : ℤ) : ℤ) : ℚ)
    have hz_eq : (fun j => (z j : ℚ)) = c • q := by
      ext j
      simp [c, hz_cast, Pi.smul_apply, smul_eq_mul]
    change A.mulVecLin (fun j => (z j : ℚ)) = 0
    rw [hz_eq]
    simp [hqker]

end ConeLemma

theorem cone_lemma {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℚ)
    (x : Fin N → ℝ)
    (hsol : (A.map ((↑) : ℚ → ℝ)).mulVec x = 0)
    (hpos : ∀ j, 0 < x j) :
    ∃ z : Fin N → ℤ, (∀ j, 0 < z j) ∧ A.mulVec (fun j => (z j : ℚ)) = 0 := by
  obtain ⟨q, hqpos, hqker⟩ := ConeLemma.exists_positive_rat_kernel_vector A x hsol hpos
  exact ConeLemma.exists_positive_int_kernel_vector_of_rat A q hqpos hqker

end

end ProofsInTheBook
