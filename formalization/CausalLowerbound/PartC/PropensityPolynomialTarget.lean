import CausalLowerbound.PartC.SitePolynomialFunctional
import CausalLowerbound.PartC.PropensityChoiceTarget

/-! Identification of the existing degree-one target with a linear
functional on the unaveraged virtual-shift polynomial. Thus the occurrence
filter in the actual target is exactly square-free polynomial truncation. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative
variable {Ω K V E d J : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype d] [DecidableEq d] [Fintype J] [DecidableEq J]

def propensityPatternWeight (κ : V → ℝ) (v : Representative.Array d V J 1)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (S : Finset V) : ℝ :=
  ∑ r : Row V J 1, Walsh.character r.2 ζ * (toContinuous (v r) (torusProjection u)).re *
    ∏ i, propensitySlotFactor S κ z r.1 i

def propensityPolynomialFunctional (κ : V → ℝ) (v : Representative.Array d V J 1)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) : MvPolynomial V ℝ →ₗ[ℝ] ℝ :=
  sitePatternFunctional (propensityPatternWeight κ v u z ζ)

theorem propensityPatternWeight_empty (κ : V → ℝ) (v : Representative.Array d V J 1)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) :
    propensityPatternWeight κ v u z ζ ∅ = pointValue (torusProjection u) z ζ v := by
  unfold propensityPatternWeight pointValue rowWeight monomial
  simp only [propensitySlotFactor, Finset.not_mem_empty, if_false]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem propensityPolynomialFunctional_C (κ : V → ℝ) (v : Representative.Array d V J 1)
    (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) (c : ℝ) :
    propensityPolynomialFunctional κ v u z ζ (MvPolynomial.C c) =
      c * pointValue (torusProjection u) z ζ v := by
  rw [propensityPolynomialFunctional, sitePatternFunctional_C, propensityPatternWeight_empty]

theorem propensityChoiceValue_eq_polynomial (a b : E → V) (μ : FiniteLaw Ω)
    (U : Ω → K → ℝ) (ν : K → d × Bool →₀ ℕ) (amp τ : ℝ) (κ : V → ℝ)
    (v : Representative.Array d V J 1) (u : V × d → ℝ) (z : V → ℝ) (ζ : J → Bool) :
    propensityChoiceValue a b μ U ν amp τ κ v u z ζ =
      graphTaper a b taperCutoff τ (graphDistance a b u) *
        propensityPolynomialFunctional κ v u z ζ
          (wordShiftPolynomial μ U (fun k i => lagrangeCoefficient a b i (ν k) u) amp) := by
  rw [propensityPolynomialFunctional, sitePatternFunctional_shift, Finset.mul_sum]
  unfold propensityChoiceValue
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Function.Injective (choiceSite s)
  · simp only [if_pos hs, shiftChoiceCoefficient, taperedLagrangeProduct, propensityPatternWeight]
    ring
  · simp only [if_neg hs, mul_zero]

end CausalLowerbound.PartC
