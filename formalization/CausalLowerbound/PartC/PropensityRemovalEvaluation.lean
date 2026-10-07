import CausalLowerbound.PartC.PhysicalPropensityPolynomial

/-! Removed representatives depend only on the retained Walsh signs.
This applies before rough-field averaging, to every site polynomial and
every coefficient target, with no bound on the supplied real variables. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open Representative
variable {d V J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

theorem removed_row_coefficient_congr {D : ℕ} (S : Finset J)
    (W : Representative.Array d V J D) (x : Wiener.Torus (V × d)) (r : Row V J D)
    (ζ ζ' : J → Bool) (h : ∀ j ∉ S, ζ j = ζ' j) :
    Walsh.character r.2 ζ * (Wiener.toContinuous (remove S W r) x).re =
      Walsh.character r.2 ζ' * (Wiener.toContinuous (remove S W r) x).re := by
  simp only [remove_apply]
  by_cases hd : Disjoint r.2 S
  · simp only [if_pos hd]
    rw [Walsh.character_congr r.2 ζ ζ' (fun j hj => h j (Finset.disjoint_left.mp hd hj))]
  · simp only [if_neg hd, map_zero, ContinuousMap.zero_apply, Complex.zero_re, mul_zero]

theorem pointValue_remove_congr {D : ℕ} (S : Finset J)
    (W : Representative.Array d V J D) (x : Wiener.Torus (V × d)) (z : V → ℝ)
    (ζ ζ' : J → Bool) (h : ∀ j ∉ S, ζ j = ζ' j) :
    pointValue x z ζ (remove S W) = pointValue x z ζ' (remove S W) := by
  simp only [pointValue, rowWeight, mul_assoc]
  apply Finset.sum_congr rfl
  intro r _
  rw [removed_row_coefficient_congr S W x r ζ ζ' h]

theorem propensityPolynomialFunctional_remove_congr (S : Finset J)
    (κ : V → ℝ) (W : Representative.Array d V J 1) (u : V × d → ℝ) (z : V → ℝ)
    (ζ ζ' : J → Bool) (h : ∀ j ∉ S, ζ j = ζ' j) (p : MvPolynomial V ℝ) :
    propensityPolynomialFunctional κ (remove S W) u z ζ p =
      propensityPolynomialFunctional κ (remove S W) u z ζ' p := by
  have he : propensityPatternWeight κ (remove S W) u z ζ =
      propensityPatternWeight κ (remove S W) u z ζ' := by
    funext A
    unfold propensityPatternWeight
    apply Finset.sum_congr rfl
    intro r _
    rw [removed_row_coefficient_congr S W (Wiener.torusProjection u) r ζ ζ' h]
  simp only [propensityPolynomialFunctional, he]

theorem propensityCoefficientFunctional_remove_congr {A E Ω : Type*}
    [Fintype A] [DecidableEq A] [Fintype E] [DecidableEq E] [Fintype Ω] [DecidableEq d]
    (S : Finset J) (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → A → ℝ)
    (ν : A → d × Bool →₀ ℕ) (amp τ : ℝ) (κ : V → ℝ)
    (W : Representative.Array d V J 1) (u : V × d → ℝ) (z : V → ℝ)
    (ζ ζ' : J → Bool) (h : ∀ j ∉ S, ζ j = ζ' j) (p : MvPolynomial A ℝ) :
    propensityCoefficientFunctional a b μ U ν amp τ κ (remove S W) u z ζ p =
      propensityCoefficientFunctional a b μ U ν amp τ κ (remove S W) u z ζ' p := by
  simp only [propensityCoefficientFunctional, LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul]
  rw [propensityPolynomialFunctional_remove_congr S κ W u z ζ ζ' h]

end CausalLowerbound.PartC
