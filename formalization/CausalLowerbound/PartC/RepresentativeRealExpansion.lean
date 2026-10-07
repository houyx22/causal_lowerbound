import CausalLowerbound.PartC.PolynomialPolarization
import CausalLowerbound.WienerRealExpansion

/-! A canonical real expansion from the retained Fourier rows. Degree and
Walsh labels are carried along without a choice of an expansion or a loss
depending on the number of rough signs. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal Classical

namespace CausalLowerbound.PartC.Representative

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

abbrev RealExpansion (d ι J : Type*) (D : ℕ) := Wiener.Series (PolynomialBasis d ι D × Finset J) ℝ

def basisWithDegree (e : Degree ι D) (v : PartB.PositiveWiener.BasisIndex d ι) : PolynomialBasis d ι D :=
  fun i => (e i, v i)

def canonicalRealExpansion : Array d ι J D →L[ℝ] RealExpansion d ι J D :=
  ∑ r : Row ι J D, (Wiener.regroup (fun v => (basisWithDegree r.1 v, r.2))).comp
    (Wiener.realExpansion.comp (FiniteL1.entry r))

theorem canonicalRealExpansion_bound (a : Array d ι J D) :
    ‖canonicalRealExpansion a‖ ≤ (2 : ℝ) ^ Fintype.card ι * ‖a‖ := by
  simp only [canonicalRealExpansion, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    FiniteL1.entry_apply]
  calc
    _ ≤ ∑ r : Row ι J D, ‖Wiener.regroup (fun v => (basisWithDegree r.1 v, r.2))
        (Wiener.realExpansion (a r))‖ := norm_sum_le _ _
    _ ≤ ∑ r : Row ι J D, (2 : ℝ) ^ Fintype.card ι * ‖a r‖ := Finset.sum_le_sum (fun r _ =>
      (Wiener.regroup_bound _ _).trans (Wiener.realExpansion_bound (a r)))
    _ = (2 : ℝ) ^ Fintype.card ι * ‖a‖ := by rw [← Finset.mul_sum, norm_eq_sum]

theorem canonicalRealExpansion_single (r : Row ι J D) (a : Wiener.Fourier (ι × d)) :
    canonicalRealExpansion (lp.single 1 r a : Array d ι J D) =
      Wiener.regroup (fun v => (basisWithDegree r.1 v, r.2)) (Wiener.realExpansion a) := by
  simp only [canonicalRealExpansion, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    FiniteL1.entry_apply]
  rw [Finset.sum_eq_single r]
  · rw [lp.single_apply_self]
  · intro s _ hsr
    rw [lp.single_apply_ne _ _ _ hsr, map_zero, map_zero]
  · simp

theorem canonicalRealExpansion_mode (r : Row ι J D) (k : (ι × d) → ℤ) (c : ℂ) :
    canonicalRealExpansion (lp.single 1 r (lp.single 1 k c) : Array d ι J D) =
      ∑ b : ι → Bool, lp.single 1 (basisWithDegree r.1 (Wiener.trigIndex b k), r.2)
        ((Wiener.trigPhase b * c).re) := by
  rw [canonicalRealExpansion_single, Wiener.realExpansion_single, map_sum]
  simp only [Wiener.regroup_single]

def symmetricPointEvaluation (x : Wiener.Torus (ι × d)) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool) : Array d ι J D →L[ℝ] ℝ :=
  (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ • ∑ σ : Equiv.Perm ι,
    pointEvaluation (Wiener.permuteSlots σ.symm x) (fun i => z (σ.symm i)) (fun i => hz (σ.symm i)) ζ

theorem symmetricPointEvaluation_apply (x : Wiener.Torus (ι × d)) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool) (a : Array d ι J D) :
    symmetricPointEvaluation x z hz ζ a = (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm ι, pointValue (Wiener.permuteSlots σ.symm x) (fun i => z (σ.symm i)) ζ a := by
  simp only [symmetricPointEvaluation, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    pointEvaluation_apply, smul_eq_mul]

theorem polynomialBasis_value_bound (v : PolynomialBasis d ι D) (S : Finset J)
    (x : Wiener.Torus (ι × d)) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool) :
    |Walsh.character S ζ * pointValue x z ζ (polynomialBasisTensor v : Array d ι J D)| ≤ 1 := by
  rw [abs_mul, Walsh.abs_character, one_mul]
  exact (pointValue_bound x z hz ζ _).trans (polynomialBasisTensor_norm v)

def expansionPointEvaluation (x : Wiener.Torus (ι × d)) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool) : RealExpansion d ι J D →L[ℝ] ℝ :=
  Wiener.synthesis (fun v => Walsh.character v.2 ζ *
    pointValue x z ζ (polynomialBasisTensor v.1 : Array d ι J D)) 1
    (fun v => polynomialBasis_value_bound v.1 v.2 x z hz ζ)

theorem expansionPointEvaluation_single (x : Wiener.Torus (ι × d)) (z : ι → ℝ)
    (hz : ∀ i, |z i| ≤ 1) (ζ : J → Bool) (v : PolynomialBasis d ι D) (S : Finset J) (c : ℝ) :
    expansionPointEvaluation x z hz ζ (lp.single 1 (v, S) c) =
      c * (Walsh.character S ζ * pointValue x z ζ (polynomialBasisTensor v : Array d ι J D)) :=
  Wiener.synthesis_single _ _ _ _ c

end CausalLowerbound.PartC.Representative
