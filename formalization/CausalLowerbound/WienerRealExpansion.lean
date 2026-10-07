import CausalLowerbound.PartB.PositiveWienerPolarization

/-!
# A canonical real trigonometric expansion

The coefficients below are computed directly from the complex Fourier
coefficients. No choice of a pre-existing real expansion is an input.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal
open UnitAddTorus

namespace CausalLowerbound.Wiener

variable {ν : Type*}

def rotatedRealSeries (z : ℂ) (a : Series ν ℂ) : Series ν ℝ :=
  ⟨fun k => (z * a k).re, memℓp_gen (by
    simpa using (Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
      (fun k => (Complex.abs_re_le_norm (z * a k)).trans_eq (norm_mul z (a k)))
      ((summable_norm a).mul_left ‖z‖)))⟩

theorem rotatedRealSeries_bound (z : ℂ) (a : Series ν ℂ) :
    ‖rotatedRealSeries z a‖ ≤ ‖z‖ * ‖a‖ := by
  rw [norm_eq_tsum, norm_eq_tsum a, ← tsum_mul_left]
  apply Summable.tsum_le_tsum
    (fun k => (Complex.abs_re_le_norm (z * a k)).trans_eq (norm_mul z (a k)))
    (summable_norm (rotatedRealSeries z a)) ((summable_norm a).mul_left ‖z‖)

def rotatedReal (z : ℂ) : Series ν ℂ →L[ℝ] Series ν ℝ :=
  LinearMap.mkContinuous
    { toFun := rotatedRealSeries z
      map_add' := by
        intro a b; apply lp.ext; funext k
        change (z * (a k + b k)).re = (z * a k).re + (z * b k).re
        rw [mul_add, Complex.add_re]
      map_smul' := by
        intro r a; apply lp.ext; funext k
        change (z * ((r : ℂ) * a k)).re = r * (z * a k).re
        rw [mul_left_comm z, Complex.re_ofReal_mul] }
    ‖z‖ (rotatedRealSeries_bound z)

@[simp]
theorem rotatedReal_apply (z : ℂ) (a : Series ν ℂ) (k : ν) :
    rotatedReal z a k = (z * a k).re := rfl

theorem rotatedReal_single [DecidableEq ν] (z : ℂ) (k : ν) (c : ℂ) :
    rotatedReal z (lp.single 1 k c) = lp.single 1 k ((z * c).re) := by
  apply lp.ext; funext j
  by_cases h : j = k
  · subst j; simp
  · simp [h, lp.single_apply_ne]

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d]

def trigPhase (b : ι → Bool) : ℂ := ∏ i, if b i then Complex.I else 1

theorem trigPhase_norm (b : ι → Bool) : ‖trigPhase b‖ = 1 := by
  simp only [trigPhase, norm_prod]
  have h (i : ι) : ‖(if b i then Complex.I else 1 : ℂ)‖ = 1 := by
    cases b i <;> simp
  simp only [h, Finset.prod_const_one]

def trigIndex (b : ι → Bool) (k : (ι × d) → ℤ) :
    PartB.PositiveWiener.BasisIndex d ι := fun i => (fun j => k (i, j), b i)

/-- Fixed real linear coefficients, with one finite mask for each Fourier mode. -/
def realExpansion : Fourier (ι × d) →L[ℝ]
    Series (PartB.PositiveWiener.BasisIndex d ι) ℝ :=
  ∑ b : ι → Bool, (regroup (trigIndex b)).comp (rotatedReal (trigPhase b))

theorem realExpansion_bound (a : Fourier (ι × d)) :
    ‖realExpansion a‖ ≤ (2 : ℝ) ^ Fintype.card ι * ‖a‖ := by
  change ‖(∑ b : ι → Bool, (regroup (trigIndex b)).comp
    (rotatedReal (trigPhase b))) a‖ ≤ _
  rw [ContinuousLinearMap.sum_apply]
  calc
    _ ≤ ∑ b : ι → Bool, ‖regroup (trigIndex b) (rotatedReal (trigPhase b) a)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _b : ι → Bool, ‖a‖ := by
      apply Finset.sum_le_sum; intro b _
      exact (regroup_bound _ _).trans (by
        simpa only [trigPhase_norm, one_mul] using rotatedRealSeries_bound (trigPhase b) a)
    _ = _ := by simp [Fintype.card_fun]

theorem realExpansion_single (k : (ι × d) → ℤ) (c : ℂ) :
    realExpansion (lp.single 1 k c) =
      ∑ b : ι → Bool, lp.single 1 (trigIndex b k) ((trigPhase b * c).re) := by
  simp only [realExpansion, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    rotatedReal_single, regroup_single]

theorem complex_product_trig (z : ι → ℂ) :
    ∏ i, z i = ∑ b : ι → Bool, trigPhase b *
      ((∏ i, if b i then (z i).im else (z i).re : ℝ) : ℂ) := by
  simp only [trigPhase, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : ι) (b : Bool) =>
    (if b then Complex.I else (1 : ℂ)) *
      ((if b then (z i).im else (z i).re : ℝ) : ℂ))]
  apply Finset.prod_congr rfl; intro i _
  simpa only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, one_mul, mul_one,
    mul_comm, add_comm] using
    (Complex.re_add_im (z i)).symm

theorem complex_product_real (z : ι → ℂ) (c : ℂ) :
    (c * ∏ i, z i).re = ∑ b : ι → Bool,
      (trigPhase b * c).re * ∏ i, if b i then (z i).im else (z i).re := by
  rw [complex_product_trig, Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [← mul_assoc, mul_comm c, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

def permuteSlots (σ : Equiv.Perm ι) (x : Torus (ι × d)) : Torus (ι × d) :=
  fun p => x (σ p.1, p.2)

theorem character_slots (k : (ι × d) → ℤ) (x : Torus (ι × d)) :
    mFourier k x = ∏ i, mFourier (fun j => k (i, j)) (fun j => x (i, j)) := by
  simp only [mFourier, ContinuousMap.coe_mk, Fintype.prod_prod_type]

def trigValue (k : d → ℤ) (b : Bool) (x : Torus d) : ℝ :=
  if b then (mFourier k x).im else (mFourier k x).re

theorem trigSeries_value (k : d → ℤ) (b : Bool) (x : Torus d) :
    toContinuous (trigSeries k b) x = (trigValue k b x : ℂ) := by
  cases b <;> simp [trigSeries, trigValue, cosineSeries_value, sineSeries_value]

theorem basisTensor_value (b : ι → Bool) (k : (ι × d) → ℤ) (x : Torus (ι × d)) :
    toContinuous (PartB.PositiveWiener.basisTensor (trigIndex b k)) x =
      (((Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ *
        ∑ σ : Equiv.Perm ι, ∏ i,
          trigValue (fun j => k (i, j)) (b i) (fun j => x (σ.symm i, j)) : ℝ) : ℂ) := by
  simp only [PartB.PositiveWiener.basisTensor, symTensor_value, trigIndex, trigSeries_value,
    Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_prod, Complex.real_smul]
  congr 1
  apply Finset.sum_congr rfl; intro σ _
  simpa only [Equiv.symm_apply_apply] using (Equiv.prod_comp σ
    (fun i => (trigValue (fun j => k (i, j)) (b i) (fun j => x (σ.symm i, j)) : ℂ)))

def evaluation (x : Torus d) : Fourier d →L[ℝ] ℂ :=
  ((ContinuousMap.evalCLM ℂ x).comp toContinuous).restrictScalars ℝ

@[simp]
theorem evaluation_apply (x : Torus d) (a : Fourier d) :
    evaluation x a = toContinuous a x := rfl

def symmetricRealEvaluation (x : Torus (ι × d)) : Fourier (ι × d) →L[ℝ] ℂ :=
  (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ • ∑ σ : Equiv.Perm ι,
    Complex.ofRealCLM.comp (Complex.reCLM.comp (evaluation (permuteSlots σ.symm x)))

theorem expansion_single_value (k : (ι × d) → ℤ) (c : ℂ) (x : Torus (ι × d)) :
    toContinuous (PartB.PositiveWiener.realTensorSynthesis
      (realExpansion (lp.single 1 k c))) x =
      symmetricRealEvaluation x (lp.single 1 k c) := by
  rw [realExpansion_single]
  simp only [map_sum, PartB.PositiveWiener.realTensorSynthesis, synthesis_single,
    toContinuous_real_smul, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    basisTensor_value, Complex.real_smul]
  have he : toContinuous (lp.single 1 k c) = c • mFourier k :=
    synthesis_single mFourier 1 (fun _ => mFourier_norm.le) k c
  simp only [symmetricRealEvaluation, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    Complex.reCLM_apply, evaluation_apply, he, ContinuousMap.smul_apply, smul_eq_mul,
    Complex.real_smul]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  simp_rw [← mul_assoc, mul_comm _ (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹, mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro σ _
  rw [character_slots, complex_product_real]
  rfl

/-- Canonical synthesis equals the real part of the permutation average. -/
theorem realExpansion_value (a : Fourier (ι × d)) (x : Torus (ι × d)) :
    toContinuous (PartB.PositiveWiener.realTensorSynthesis (realExpansion a)) x =
      symmetricRealEvaluation x a := by
  let left := (evaluation x).comp (PartB.PositiveWiener.realTensorSynthesis.comp realExpansion)
  have he : left = symmetricRealEvaluation x := by
    apply lp.ext_continuousLinearMap (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    intro k; apply ContinuousLinearMap.ext; intro c
    exact expansion_single_value k c x
  exact congrArg (fun f : Fourier (ι × d) →L[ℝ] ℂ => f a) he

/-- On every symmetric real Wiener function, the canonical expansion reconstructs
the function itself. Both properties are pointwise properties of its realization. -/
theorem realExpansion_reconstruction (a : Fourier (ι × d))
    (hreal : ∀ x, (toContinuous a x).im = 0)
    (hsym : ∀ σ : Equiv.Perm ι, ∀ x, toContinuous a (permuteSlots σ x) = toContinuous a x) :
    PartB.PositiveWiener.realTensorSynthesis (realExpansion a) = a := by
  apply toContinuous_injective; ext x
  rw [realExpansion_value]
  simp only [symmetricRealEvaluation, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, Complex.reCLM_apply, evaluation_apply, hsym]
  have hr : ((toContinuous a x).re : ℂ) = toContinuous a x := by
    apply Complex.ext <;> simp [hreal]
  rw [hr]
  simp [Fintype.card_ne_zero, ← mul_smul]

end CausalLowerbound.Wiener
