import CausalLowerbound.PartC.RetainedPropensityCompletion
import CausalLowerbound.PartC.CarrierPermutationSymmetry

/-! Permutation averaging of retained-site matching. Every summand uses
the same retained physical sites, with the completion reindexed by the
inverse permutation. The removed carrier is symmetric for arbitrary
formal slot variables, so the averaged identity has the original value. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative RoughPropensity
variable {I G V d J Ω : Type*} [Fintype I] [Fintype G] [Fintype V] [LinearOrder V]
  [Fintype d] [DecidableEq d] [Fintype J] [DecidableEq J] [Fintype Ω]

def symmetricPropensityCoefficientFunctional (Q : ℕ) (μ : FiniteLaw Ω)
    (U : Ω → CoefficientExponent d Q → ℝ) (amp τ : ℝ) (κ : V → ℝ)
    (W : Representative.Array d V J 1) (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) :
    MvPolynomial (CoefficientExponent d Q) ℝ →ₗ[ℝ] ℝ :=
  (Fintype.card (Equiv.Perm V) : ℝ)⁻¹ • ∑ σ : Equiv.Perm V,
    propensityCoefficientFunctional edgeLeft edgeRight μ U polynomialBasisDegree amp τ
      (κ ∘ σ) W (permuteConfiguration σ u) (z ∘ σ) ζ

theorem symmetricPropensityCoefficientFunctional_zero (Q : ℕ) (μ : FiniteLaw Ω)
    (U : Ω → CoefficientExponent d Q → ℝ) (amp τ : ℝ) (κ : V → ℝ)
    (W : Representative.Array d V J 1) (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool)
    (hχ : graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) = 0)
    (p : MvPolynomial (CoefficientExponent d Q) ℝ) :
    symmetricPropensityCoefficientFunctional Q μ U amp τ κ W u z ζ p = 0 := by
  simp only [symmetricPropensityCoefficientFunctional, propensityCoefficientFunctional,
    complete_graphTaper_permute, hχ, zero_smul, Finset.sum_const_zero, smul_zero, LinearMap.zero_apply]

omit [LinearOrder V] in
theorem physicalLocalSigns_union_permute (x₀ : d → ℝ) (ℓ h : ℝ) (x : V → d → ℝ)
    (σ : Equiv.Perm V) :
    Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x (σ i))) =
      Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i)) := by
  ext j
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨σ.symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩

set_option maxHeartbeats 400000 in
theorem removed_physical_propensity_symmetric_retained_matching
    (Q : ℕ) (hQ : 0 < Q) (hcard : Fintype.card V ≤ Q)
    (μ : FiniteLaw Ω) (U : Ω → CoefficientExponent d Q → ℝ)
    (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h) (x : V → d → ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * ℓ < ‖x i - x j‖)
    (e : I ⊕ G ≃ V) (R T : I → ℝ) (ja scale offset ψ : V → ℝ)
    (W : Representative.Array d V (activeBlocks (d := d) ℓ h) 1)
    (hsym : ∀ (a : Torus (V × d)) (z : V → ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool)
      (σ : Equiv.Perm V), pointValue (permuteSlots σ a) (z ∘ σ) ζ W = pointValue a z ζ W)
    (u : V × d → ℝ) (τ amp : ℝ) :
    let keep : I → V := fun i => e (Sum.inl i)
    let B := remove (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) W
    independentSigns.expect (fun ζ =>
      symmetricPropensityCoefficientFunctional Q μ U amp τ
        (fun i => scale i ^ 2 * ja i ^ 2 * (coarseBump x₀ h (x i) ^ 2) ^ 2) B u
        (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ
        (retainedPropensityPolynomial Q R T (ja ∘ keep)
          (fun i => physicalRoughField x₀ ℓ h ζ (x (keep i))) (offset ∘ keep) (ψ ∘ keep)
          (configurationSite u ∘ keep))) =
      graphTaper edgeLeft edgeRight taperCutoff τ (graphDistance edgeLeft edgeRight u) *
        μ.expect (fun ξ => independentSigns.expect (fun ζ =>
          pointValue (torusProjection u) (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ B *
            ((∏ i, (likelihood (R i) (T i) (ja (keep i))
              (offset (keep i) + ψ (keep i) * coefficientEvaluation (U ξ) (configurationSite u (keep i)))
                (physicalRoughField x₀ ℓ h ζ (x (keep i))) +
              realField (R i) (T i) (ja (keep i))
                (ja (keep i) * (ψ (keep i) * amp) * scale (keep i) * coarseBump x₀ h (x (keep i)) ^ 2)
                (physicalRoughField x₀ ℓ h ζ (x (keep i))))) -
              ∏ i, likelihood (R i) (T i) (ja (keep i))
                (offset (keep i) + ψ (keep i) * coefficientEvaluation (U ξ) (configurationSite u (keep i)))
                (physicalRoughField x₀ ℓ h ζ (x (keep i)))))) := by
  dsimp only
  have hperm (σ : Equiv.Perm V) :=
    removed_physical_propensity_retained_matching Q hQ hcard μ U x₀ ℓ h hℓ hh (x ∘ σ)
      (fun i j hij => hsep (σ i) (σ j) (σ.injective.ne hij)) (e.trans σ.symm) R T
      (ja ∘ σ) (scale ∘ σ) (offset ∘ σ) (ψ ∘ σ) W (permuteConfiguration σ u) τ amp
  have hsite (σ : Equiv.Perm V) (i : I) :
      configurationSite (permuteConfiguration σ u) (σ.symm (e (Sum.inl i))) =
        configurationSite u (e (Sum.inl i)) := by
    funext a
    change u (σ (σ.symm (e (Sum.inl i))), a) = u (e (Sum.inl i), a)
    rw [Equiv.apply_symm_apply]
  have hvalue (σ : Equiv.Perm V) (ζ : activeBlocks (d := d) ℓ h → Bool) :
      pointValue (torusProjection (permuteConfiguration σ u))
        (fun i => scale (σ i) * physicalRoughField x₀ ℓ h ζ (x (σ i))) ζ
        (remove (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) W) =
      pointValue (torusProjection u) (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ
        (remove (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) W) :=
    pointValue_remove_symmetric
      (Finset.univ.biUnion (fun i => physicalLocalSigns x₀ ℓ h (x i))) W hsym
      (torusProjection u) (fun i => scale i * physicalRoughField x₀ ℓ h ζ (x i)) ζ σ
  simp only [Function.comp_def, Equiv.trans_apply, Equiv.apply_symm_apply,
    physicalLocalSigns_union_permute, complete_graphTaper_permute, hsite, hvalue] at hperm
  simp only [symmetricPropensityCoefficientFunctional, LinearMap.smul_apply,
    LinearMap.sum_apply, smul_eq_mul, Function.comp_def]
  rw [FiniteLaw.expect_mul]
  have hsum (f : Equiv.Perm V → (activeBlocks (d := d) ℓ h → Bool) → ℝ) :
      independentSigns.expect (fun ζ => ∑ a, f a ζ) =
        ∑ a, independentSigns.expect (f a) := by
    simp only [FiniteLaw.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hsum]
  simp only [hperm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm V) ≠ 0)

attribute [local instance] finOrderedDecEq finOrderedDecLt

theorem paperPhysicalPropensityPolynomial_eq_symmetric (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ)
    (r h : ℝ) (k : d → ℤ) (c w N ja t τ : ℝ) (W : Representative.Array d (Fin Q) J 1)
    (u : Fin Q × d → ℝ) (z : Fin Q → ℝ) (ζ : J → Bool) :
    paperPhysicalPropensityPolynomial Q ρ x₀ r h k c w N ja t τ W u z ζ =
      symmetricPropensityCoefficientFunctional Q (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ)
        (t * N) τ (physicalPropensitySlotCorrection x₀ r h k c w N ja u) W u z ζ := rfl

end CausalLowerbound.PartC
