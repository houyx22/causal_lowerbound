import CausalLowerbound.PartC.RepresentativeRealExpansion

/-! Canonical reconstruction symmetrizes the degree and Fourier slots
together. It does not infer equality of arrays from equality after evaluation. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal Classical
open UnitAddTorus

namespace CausalLowerbound.PartC.Representative

open PartB.Polarization

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

theorem polynomial_mode_basis_value (e : Degree ι D) (b : ι → Bool) (k : (ι × d) → ℤ)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (ζ : J → Bool) :
    pointValue x z ζ (polynomialBasisTensor (basisWithDegree e (Wiener.trigIndex b k)) : Array d ι J D) =
      (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ * ∑ σ : Equiv.Perm ι,
        monomial e (fun i => z (σ.symm i)) *
          ∏ i, Wiener.trigValue (fun j => k (i, j)) (b i) (fun j => x (σ.symm i, j)) := by
  have hreal (i : ι) (y : Wiener.Torus d) (t : ℝ) :
      (factorValue y t ζ (basisFactor (e i) (fun j => k (i, j)) (b i) : Factor d J D)).im = 0 := by
    rw [basisFactor_value, Wiener.trigSeries_value]
    simp only [Complex.real_smul, Complex.mul_im, Complex.ofReal_im, mul_zero, zero_mul, add_zero]
  simp only [polynomialBasisTensor, basisWithDegree, Wiener.trigIndex]
  rw [symTensor_value _ x z ζ hreal]
  simp only [symProduct, basisWithDegree, Wiener.trigIndex, basisFactor_value, Wiener.trigSeries_value,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [monomial, ← Finset.prod_mul_distrib]
  simpa only [Equiv.symm_apply_apply] using (Equiv.prod_comp σ
    (fun i => z (σ.symm i) ^ (e i).val *
      Wiener.trigValue (fun j => k (i, j)) (b i) (fun j => x (σ.symm i, j))))

theorem canonicalRealExpansion_mode_value (r : Row ι J D) (k : (ι × d) → ℤ) (c : ℂ)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool) :
    expansionPointEvaluation x z hz ζ
      (canonicalRealExpansion (lp.single 1 r (lp.single 1 k c) : Array d ι J D)) =
        symmetricPointEvaluation x z hz ζ (lp.single 1 r (lp.single 1 k c)) := by
  have he : Wiener.toContinuous (lp.single 1 k c) = c • mFourier k :=
    Wiener.synthesis_single mFourier 1 (fun _ => mFourier_norm.le) k c
  have hσ (σ : Equiv.Perm ι) : (c * mFourier k (Wiener.permuteSlots σ.symm x)).re =
      ∑ b : ι → Bool, (Wiener.trigPhase b * c).re *
        ∏ i, Wiener.trigValue (fun j => k (i, j)) (b i) (fun j => x (σ.symm i, j)) := by
    rw [Wiener.character_slots, Wiener.complex_product_real]
    rfl
  rw [canonicalRealExpansion_mode, map_sum]
  simp only [expansionPointEvaluation_single, polynomial_mode_basis_value,
    symmetricPointEvaluation_apply, pointValue_single, rowWeight, he,
    ContinuousMap.smul_apply, smul_eq_mul, hσ]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem canonicalRealExpansion_value (a : Array d ι J D)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool) :
    expansionPointEvaluation x z hz ζ (canonicalRealExpansion a) =
      symmetricPointEvaluation x z hz ζ a := by
  have he : (expansionPointEvaluation x z hz ζ).comp canonicalRealExpansion =
      symmetricPointEvaluation (D := D) x z hz ζ := by
    apply lp.ext_continuousLinearMap (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    intro r
    apply lp.ext_continuousLinearMap (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)
    intro k
    apply ContinuousLinearMap.ext
    intro c
    exact canonicalRealExpansion_mode_value r k c x z hz ζ
  exact congrArg (fun f : Array d ι J D →L[ℝ] ℝ => f a) he

theorem canonicalRealExpansion_reconstruction (a : Array d ι J D)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool)
    (hsym : ∀ σ : Equiv.Perm ι,
      pointValue (Wiener.permuteSlots σ.symm x) (fun i => z (σ.symm i)) ζ a = pointValue x z ζ a) :
    expansionPointEvaluation x z hz ζ (canonicalRealExpansion a) = pointValue x z ζ a := by
  rw [canonicalRealExpansion_value, symmetricPointEvaluation_apply]
  simp only [hsym, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

end CausalLowerbound.PartC.Representative
