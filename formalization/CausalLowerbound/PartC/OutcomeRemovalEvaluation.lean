import CausalLowerbound.PartC.PhysicalOutcomePolynomial
import CausalLowerbound.PartC.PropensityRemovalEvaluation

/-! Deleting local Walsh symbols makes the cubic target independent of
those explicit signs, before averaging the physical rough variables. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Representative
variable {d V J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

theorem outcomePolynomialFunctional_remove_congr (S : Finset J)
    (κ : V → ℝ) (W : Representative.Array d V J 3) (u : V × d → ℝ) (z : V → ℝ)
    (ζ ζ' : J → Bool) (h : ∀ j ∉ S, ζ j = ζ' j) (p : MvPolynomial V ℝ) :
    outcomePolynomialFunctional κ (remove S W) u z ζ p =
      outcomePolynomialFunctional κ (remove S W) u z ζ' p := by
  have he : outcomePatternWeight κ (remove S W) u z ζ =
      outcomePatternWeight κ (remove S W) u z ζ' := by
    funext a
    unfold outcomePatternWeight
    apply Finset.sum_congr rfl
    intro r _
    rw [removed_row_coefficient_congr S W (Wiener.torusProjection u) r ζ ζ' h]
  simp only [outcomePolynomialFunctional, he]

theorem outcomeCoefficientFunctional_remove_congr {A E Ω : Type*}
    [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E] [Fintype Ω] [DecidableEq d]
    (S : Finset J) (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (ν : A → d × Bool →₀ ℕ) (amp τ : ℝ) (κ : V → ℝ)
    (W : Representative.Array d V J 3) (u : V × d → ℝ) (z : V → ℝ)
    (ζ ζ' : J → Bool) (h : ∀ j ∉ S, ζ j = ζ' j) (p : MvPolynomial A ℝ) :
    outcomeCoefficientFunctional a b μ U ν amp τ κ (remove S W) u z ζ p =
      outcomeCoefficientFunctional a b μ U ν amp τ κ (remove S W) u z ζ' p := by
  simp only [outcomeCoefficientFunctional, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
  rw [outcomePolynomialFunctional_remove_congr S κ W u z ζ ζ' h]

end CausalLowerbound.PartC
