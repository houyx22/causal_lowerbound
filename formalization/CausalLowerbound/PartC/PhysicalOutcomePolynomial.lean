import CausalLowerbound.PartC.OutcomePolynomialTarget
import CausalLowerbound.PartC.WeightedPolynomialMoments
import CausalLowerbound.PartC.PaperOutcomeCarrier

/-! A coefficient-polynomial functional for the actual physical target.
Its value on each moment word is exactly the previously constructed
target, including symmetrization, taper, and the actual normalized variance. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {A Ω V E d J : Type*} [Fintype A] [DecidableEq A] [Fintype Ω]
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype d] [DecidableEq d] [Fintype J] [DecidableEq J]

def outcomeCoefficientFunctional (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (ν : A → d × Bool →₀ ℕ) (amp τ : ℝ) (κ : V → ℝ) (v : Representative.Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) : MvPolynomial A ℝ →ₗ[ℝ] ℝ :=
  graphTaper a b taperCutoff τ (graphDistance a b u) •
    (outcomePolynomialFunctional κ v u z ζ).comp
      (coefficientShiftPolynomial μ U (fun e i => lagrangeCoefficient a b i (ν e) u) amp)

theorem outcomeCoefficientFunctional_C (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (ν : A → d × Bool →₀ ℕ) (amp τ : ℝ) (κ : V → ℝ) (v : Representative.Array d V J 3)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (c : ℝ) :
    outcomeCoefficientFunctional a b μ U ν amp τ κ v u z ζ (MvPolynomial.C c) = 0 := by
  simp only [outcomeCoefficientFunctional, LinearMap.smul_apply, LinearMap.comp_apply,
    coefficientShiftPolynomial_C, map_zero, smul_zero]

theorem outcomeCoefficientFunctional_moment (a b : E → V) (μ : FiniteLaw Ω)
    (U : Ω → A → ℝ) (ν : A → d × Bool →₀ ℕ) (amp τ : ℝ) (κ : V → ℝ)
    (v : Representative.Array d V J 3) (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool)
    {D : ℕ} (η : MomentExponent A D) :
    outcomeCoefficientFunctional a b μ U ν amp τ κ v u z ζ (momentPolynomial η) =
      outcomeChoiceValue a b μ (fun ω (j : MomentPositions η) => U ω j.1)
        (fun j : MomentPositions η => ν j.1) amp τ κ v u z ζ := by
  rw [outcomeCoefficientFunctional, LinearMap.smul_apply, LinearMap.comp_apply,
    momentPolynomial, coefficientShiftPolynomial_word, smul_eq_mul]
  exact (outcomeChoiceValue_eq_polynomial a b μ _ _ amp τ κ v u z ζ).symm

def paperPhysicalOutcomePolynomial (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (r h : ℝ) (k : d → ℤ)
    (c w N t τ : ℝ) (v : Representative.Array d (Fin Q) J 3)
    (u : Fin Q × d → ℝ) (z : Fin Q → ℝ) (ζ : J → Bool) :
    MvPolynomial (CoefficientExponent d Q) ℝ →ₗ[ℝ] ℝ :=
  (Fintype.card (Equiv.Perm (Fin Q)) : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin Q),
    outcomeCoefficientFunctional edgeLeft edgeRight (paperCoefficientLaw Q) (paperCoefficientAtoms Q ρ)
      polynomialBasisDegree (t * N) τ
      (fun i => normalizedRoughVariance x₀ r h k c w N (fun j => u (σ i, j)))
      v (fun p => u (σ p.1, p.2)) (fun i => z (σ i)) ζ

theorem paperPhysicalOutcomePolynomial_C (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (r h : ℝ)
    (k : d → ℤ) (c w N t τ : ℝ) (v : Representative.Array d (Fin Q) J 3)
    (u : Fin Q × d → ℝ) (z : Fin Q → ℝ) (ζ : J → Bool) (b : ℝ) :
    paperPhysicalOutcomePolynomial Q ρ x₀ r h k c w N t τ v u z ζ (MvPolynomial.C b) = 0 := by
  simp only [paperPhysicalOutcomePolynomial, LinearMap.smul_apply, LinearMap.sum_apply,
    outcomeCoefficientFunctional_C, Finset.sum_const_zero, smul_zero]

theorem paperPhysicalOutcomePolynomial_moment (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (r h : ℝ)
    (k : d → ℤ) (c w N t τ : ℝ) (v : Representative.Array d (Fin Q) J 3)
    (u : Fin Q × d → ℝ) (z : Fin Q → ℝ) (ζ : J → Bool)
    (η : MomentExponent (CoefficientExponent d Q) (4 * Q)) :
    paperPhysicalOutcomePolynomial Q ρ x₀ r h k c w N t τ v u z ζ (momentPolynomial η) =
      paperPhysicalOutcomeValue Q ρ x₀ r h k c w N t τ v η u z ζ := by
  simp only [paperPhysicalOutcomePolynomial, LinearMap.smul_apply, LinearMap.sum_apply,
    outcomeCoefficientFunctional_moment, smul_eq_mul, paperPhysicalOutcomeValue]

theorem physical_outcome_polynomial_hasSum (Q : ℕ) (ρ : ℝ) (x₀ : d → ℝ) (ℓ r h : ℝ)
    (k : d → ℤ) (c w N θ t τ : ℝ)
    (B : Representative.Array d (Fin Q) (activeBlocks (d := d) ℓ h) 3) (H : DiscreteLaw ℕ)
    (kernel : (activeBlocks (d := d) ℓ h → Bool) → ℕ →
      FiniteLaw (MomentGrid (CoefficientExponent d Q) (4 * Q)))
    (ζ : activeBlocks (d := d) ℓ h → Bool) (u : UnitChart (Fin Q × d))
    (hm : ∀ η : MomentExponent (CoefficientExponent d Q) (4 * Q),
      HasSum (fun n => (H.weight n *
        ((kernel ζ n).expect (monomialFeature (paperCoefficientAtoms Q ρ) η) -
          (paperCoefficientLaw Q).expect (monomialFeature (paperCoefficientAtoms Q ρ) η))) *
        ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ (fun a => u.val (j, a)))
        (paperPhysicalOutcomeValue Q ρ x₀ r h k c w N t τ B η u.val
          (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u.val (j, a))) ζ))
    (p : MvPolynomial (CoefficientExponent d Q) ℝ) (hp : p.totalDegree ≤ 4 * Q) :
    HasSum (fun n => (H.weight n *
      ((kernel ζ n).expect (fun ω => MvPolynomial.eval (paperCoefficientAtoms Q ρ ω) p) -
        (paperCoefficientLaw Q).expect (fun ω => MvPolynomial.eval (paperCoefficientAtoms Q ρ ω) p))) *
      ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ (fun a => u.val (j, a)))
      (paperPhysicalOutcomePolynomial Q ρ x₀ r h k c w N t τ B u.val
        (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u.val (j, a))) ζ p) := by
  apply weighted_polynomial_moment_hasSum (4 * Q) (paperCoefficientLaw Q) (kernel ζ)
    (paperCoefficientAtoms Q ρ) H.weight
    (fun n => ∏ j, carrierPhysicalDensity (ι := Fin Q) (D := 3) x₀ ℓ r h k c w N θ n ζ (fun a => u.val (j, a)))
    (paperPhysicalOutcomePolynomial Q ρ x₀ r h k c w N t τ B u.val
      (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u.val (j, a))) ζ)
    (paperPhysicalOutcomePolynomial_C Q ρ x₀ r h k c w N t τ B u.val
      (fun j => normalizedRoughChart x₀ ℓ r h k c w N ζ (fun a => u.val (j, a))) ζ) _ p hp
  intro η
  rw [paperPhysicalOutcomePolynomial_moment]
  exact hm η

end CausalLowerbound.PartC
