import CausalLowerbound.PartC.PositiveRepresentativeFactors

/-! Masked averages of actual representative factors. Their estimates also
hold after applying any continuous linear projection, including symbol parts. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartC.Representative

open PartB.Polarization

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def averageFactor (f : ι → Factor d J D) (b : ι → Bool) : Factor d J D :=
  if maskMass b = 0 then factorUnit else (maskMass b)⁻¹ • ∑ i, select b i • f i

theorem averageFactor_map {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Factor d J D →L[ℝ] F) (f : ι → Factor d J D) (b : ι → Bool) :
    L (averageFactor f b) = if maskMass b = 0 then L factorUnit
      else (maskMass b)⁻¹ • ∑ i, select b i • L (f i) := by
  unfold averageFactor
  split_ifs <;> simp only [map_smul, map_sum]

theorem averageFactor_map_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Factor d J D →L[ℝ] F) (f : ι → Factor d J D) (b : ι → Bool) (M : ℝ)
    (hM : ‖L factorUnit‖ ≤ M) (hf : ∀ i, ‖L (f i)‖ ≤ M) : ‖L (averageFactor f b)‖ ≤ M := by
  by_cases h : maskMass b = 0
  · simpa only [averageFactor_map, if_pos h] using hM
  · have hs : ‖∑ i, select b i • L (f i)‖ ≤ maskMass b * M := by
      calc
        _ ≤ ∑ i, ‖select b i • L (f i)‖ := norm_sum_le _ _
        _ ≤ ∑ i, select b i * M := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (select_nonneg b i)]
          exact mul_le_mul_of_nonneg_left (hf i) (select_nonneg b i)
        _ = _ := by rw [← Finset.sum_mul]; rfl
    rw [averageFactor_map, if_neg h, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (maskMass_nonneg b))]
    calc
      _ ≤ (maskMass b)⁻¹ * (maskMass b * M) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (maskMass_nonneg b))
      _ = M := by rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]

theorem averageFactor_norm (f : ι → Factor d J D) (b : ι → Bool) (M : ℝ)
    (hM : 1 ≤ M) (hf : ∀ i, ‖f i‖ ≤ M) : ‖averageFactor f b‖ ≤ M := by
  simpa only [ContinuousLinearMap.id_apply] using averageFactor_map_bound
    (ContinuousLinearMap.id ℝ (Factor d J D)) f b M (by simpa using hM) hf

theorem averageFactor_symbol_bound (j : J) (f : ι → Factor d J D) (b : ι → Bool) (σ : ℝ)
    (hσ : 0 ≤ σ) (hf : ∀ i, ‖factorSymbol j (f i)‖ ≤ σ) :
    ‖factorSymbol j (averageFactor f b)‖ ≤ σ :=
  averageFactor_map_bound (factorSymbol j) f b σ (by simpa using hσ) hf

theorem averageFactor_linearMean (L : Factor d J D →ₗ[ℝ] ℝ) (hL : L factorUnit = 1)
    (f : ι → Factor d J D) (hf : ∀ i, L (f i) = 1) (b : ι → Bool) : L (averageFactor f b) = 1 := by
  by_cases h : maskMass b = 0
  · simp [averageFactor, h, hL]
  · simp only [averageFactor, if_neg h, map_smul, map_sum, hf, smul_eq_mul, mul_one]
    change (maskMass b)⁻¹ * maskMass b = 1
    exact inv_mul_cancel₀ h

theorem averageFactor_value (f : ι → Factor d J D) (b : ι → Bool) (x : Wiener.Torus d)
    (z : ℝ) (ζ : J → Bool) : factorValue x z ζ (averageFactor f b) =
      if maskMass b = 0 then 1 else (maskMass b)⁻¹ • ∑ i, select b i • factorValue x z ζ (f i) := by
  rw [← factorEvaluation_apply, averageFactor_map]
  simp only [factorEvaluation_apply, factorUnit_value]

theorem averageFactor_re (f : ι → Factor d J D) (b : ι → Bool) (x : Wiener.Torus d)
    (z : ℝ) (ζ : J → Bool) : (factorValue x z ζ (averageFactor f b)).re =
      if maskMass b = 0 then 1 else (maskMass b)⁻¹ * ∑ i, select b i * (factorValue x z ζ (f i)).re := by
  rw [averageFactor_value]
  split_ifs <;> simp only [Complex.one_re, Complex.real_smul, Complex.mul_re,
    Complex.re_sum, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem averageFactor_real (f : ι → Factor d J D) (b : ι → Bool) (x : Wiener.Torus d)
    (z : ℝ) (ζ : J → Bool) (hf : ∀ i, (factorValue x z ζ (f i)).im = 0) :
    (factorValue x z ζ (averageFactor f b)).im = 0 := by
  rw [averageFactor_value]
  split_ifs <;> simp only [Complex.one_im, Complex.real_smul, Complex.mul_im, Complex.im_sum,
    Complex.ofReal_re, Complex.ofReal_im, hf, mul_zero, zero_mul, zero_add, Finset.sum_const_zero]

theorem averageFactor_range (f : ι → Factor d J D) (b : ι → Bool) (x : Wiener.Torus d)
    (z η : ℝ) (hη : 0 ≤ η) (ζ : J → Bool)
    (hf : ∀ i, 1 - η ≤ (factorValue x z ζ (f i)).re ∧ (factorValue x z ζ (f i)).re ≤ 1 + η) :
    1 - η ≤ (factorValue x z ζ (averageFactor f b)).re ∧
      (factorValue x z ζ (averageFactor f b)).re ≤ 1 + η := by
  simpa only [averageAtom, averageFactor_re] using
    averageAtom_bounds (fun i (_ : Unit) => (factorValue x z ζ (f i)).re) b η hη (fun i _ => hf i) ()

end CausalLowerbound.PartC.Representative
