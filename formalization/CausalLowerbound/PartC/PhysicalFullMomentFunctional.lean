import CausalLowerbound.PartC.PhysicalPatternFunctional
import CausalLowerbound.PartC.BlockFunctionalAverages
import CausalLowerbound.PartB.TorusTaper

/-! The full physical moment is one linear functional, including its
baseline. Its permutation representation is a genuine finite probability
average and can therefore be tensorized across all carrier blocks. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative MvPolynomial
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d A Ω : Type*} [Fintype d] [DecidableEq d] [Fintype A] [DecidableEq A] [Fintype Ω]

def coefficientExpectation (μ : FiniteLaw Ω) (U : Ω → A → ℝ) : MvPolynomial A ℝ →ₗ[ℝ] ℝ :=
  ∑ ω, μ.weight ω • (aeval (U ω)).toLinearMap

theorem coefficientExpectation_apply (μ : FiniteLaw Ω) (U : Ω → A → ℝ) (p : MvPolynomial A ℝ) :
    coefficientExpectation μ U p = μ.expect (fun ω => eval (U ω) p) := by
  simp only [coefficientExpectation, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

def permutationLaw (V : Type*) [Fintype V] [DecidableEq V] : FiniteLaw (Equiv.Perm V) where
  weight _ := (Fintype.card (Equiv.Perm V) : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    have hn : (Fintype.card (Equiv.Perm V) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn]

theorem permutationLaw_expect (V : Type*) [Fintype V] [DecidableEq V] (f : Equiv.Perm V → ℝ) :
    (permutationLaw V).expect f = (Fintype.card (Equiv.Perm V) : ℝ)⁻¹ * ∑ σ, f σ := by
  simp only [FiniteLaw.expect, permutationLaw, Finset.mul_sum]

def physicalPropensityFullFunctional (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N ja t τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : Fin Q × d → ℝ) :
    MvPolynomial (CoefficientExponent d Q) ℝ →ₗ[ℝ] ℝ :=
  physicalCarrierValue x₀ ℓ r h k c w N B ζ u •
    coefficientExpectation (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ) +
      paperPhysicalPropensityPolynomial Q ρ x₀ r h k c w N ja t τ B u
        (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (configurationSite u i)) ζ

theorem physicalPropensityFullFunctional_apply (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ)
    (k : d → ℤ) (c w N ja t τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : Fin Q × d → ℝ)
    (p : MvPolynomial (CoefficientExponent d Q) ℝ) :
    physicalPropensityFullFunctional Q ρ x₀ ℓ r h k c w N ja t τ B ζ u p =
      (paperCoefficientLaw Q).expect (fun ω => eval (paperCoefficientAtoms Q ρ ω) p) *
        physicalCarrierValue x₀ ℓ r h k c w N B ζ u +
          physicalPropensityIncrementValue Q ρ x₀ ℓ r h k c w N ja t τ B ζ p u := by
  simp only [physicalPropensityFullFunctional, LinearMap.add_apply, LinearMap.smul_apply,
    coefficientExpectation_apply, smul_eq_mul, physicalPropensityIncrementValue, configurationSite]
  rw [mul_comm]
  rfl

def physicalPropensityPatternFunctional (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ)
    (k : d → ℤ) (c w N ja t τ : ℝ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : Fin Q × d → ℝ) :
    MvPolynomial (CoefficientExponent d Q) ℝ →ₗ[ℝ] ℝ :=
  (sitePatternFunctional (taperedPatternWeight (completeTaper Q τ u)
    (propensityPatternWeight (physicalPropensitySlotCorrection x₀ r h k c w N ja u) B u
      (fun i => normalizedRoughChart x₀ ℓ r h k c w N ζ (configurationSite u i)) ζ))).comp
      (coefficientShiftAverage (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ)
        (fun a v => lagrangeCoefficient edgeLeft edgeRight v (polynomialBasisDegree (d := d) (Q := Q) a) u)
        (t * N))

theorem physicalPropensityFullFunctional_permutations
    (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (c w N θ ja t τ : ℝ)
    (H : DiscreteLaw ℕ) (B : Array d (Fin Q) (activeBlocks (d := d) ℓ h) 1)
    (hseries : HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom unit
      (pairedAtom reflection (naturalPhysicalAtom (ι := Fin Q) (D := 1) x₀ ℓ r h k c w N θ)) n) B)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : Fin Q × d → ℝ) :
    physicalPropensityFullFunctional Q ρ x₀ ℓ r h k c w N ja t τ B ζ u =
      ∑ σ : Equiv.Perm (Fin Q), (permutationLaw (Fin Q)).weight σ •
        physicalPropensityPatternFunctional Q ρ x₀ ℓ r h k c w N ja t τ B ζ
          (fun p => u (σ p.1, p.2)) := by
  apply LinearMap.ext
  intro p
  rw [physicalPropensityFullFunctional_apply]
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, permutationLaw,
    ← Finset.mul_sum, physicalPropensityPatternFunctional, LinearMap.comp_apply, completeTaper,
    configurationSite] using
      physical_propensity_full_pattern_functional Q ρ x₀ ℓ r h k c w N θ ja t τ H B hseries ζ u p

end CausalLowerbound.PartC
