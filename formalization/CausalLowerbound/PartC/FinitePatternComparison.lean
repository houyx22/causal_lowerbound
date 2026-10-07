import CausalLowerbound.PartC.ObservationComparisonBounds

/-! Finite-pattern comparison with an arbitrary finite set of nonconstant
choices. This includes cubic choices with repeated observation slots. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB
variable {A J : Type*} [Fintype J] [DecidableEq J]

theorem finite_pattern_comparison_bound
    (choices : Finset A) (T : Finset J) (a : (J → Bool) → A → ℝ)
    (F W : A → (J → Bool) → (J → Bool) → ℝ)
    (g : A → ℝ) (E₁ E₂ C : ℝ) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hg : (∑ s ∈ choices, g s) ≤ C)
    (hfirst : ∀ s ∈ choices,
      |independentSigns.expect (fun ζ => a ζ s *
        (F s ζ ζ - Walsh.resampleAverage T (F s ζ) ζ))| ≤ g s * E₁)
    (hsecond : ∀ s ∈ choices,
      |independentSigns.expect (fun ζ => a ζ s *
        Walsh.resampleAverage T (fun η => F s ζ η - W s ζ η) ζ)| ≤ g s * E₂) :
    |independentSigns.expect (fun ζ => ∑ s ∈ choices, a ζ s * F s ζ ζ) -
      independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => ∑ s ∈ choices, a ζ s * W s ζ η) ζ)| ≤ C * (E₁ + E₂) := by
  have ht (s : A) (hs : s ∈ choices) :
      |independentSigns.expect (fun ζ => a ζ s * F s ζ ζ) -
        independentSigns.expect (fun ζ => Walsh.resampleAverage T
          (fun η => a ζ s * W s ζ η) ζ)| ≤ g s * (E₁ + E₂) := by
    have he ζ : a ζ s * F s ζ ζ - Walsh.resampleAverage T (fun η => a ζ s * W s ζ η) ζ =
        a ζ s * (F s ζ ζ - Walsh.resampleAverage T (F s ζ) ζ) +
          a ζ s * Walsh.resampleAverage T (fun η => F s ζ η - W s ζ η) ζ := by
      simp only [Walsh.resampleAverage, FiniteLaw.expect_mul, FiniteLaw.expect_sub]
      ring
    rw [← FiniteLaw.expect_sub, FiniteLaw.expect_congr _ he, FiniteLaw.expect_add]
    exact (abs_add _ _).trans ((add_le_add (hfirst s hs) (hsecond s hs)).trans (by rw [mul_add]))
  have hr ζ : Walsh.resampleAverage T (fun η => ∑ s ∈ choices, a ζ s * W s ζ η) ζ =
      ∑ s ∈ choices, Walsh.resampleAverage T (fun η => a ζ s * W s ζ η) ζ :=
    FiniteLaw.expect_finset_sum independentSigns choices
      (fun s fresh => a ζ s * W s ζ (Walsh.resample T ζ fresh))
  rw [FiniteLaw.expect_congr _ hr, FiniteLaw.expect_finset_sum,
    FiniteLaw.expect_finset_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ s ∈ choices, |independentSigns.expect (fun ζ => a ζ s * F s ζ ζ) -
        independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => a ζ s * W s ζ η) ζ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ choices, g s * (E₁ + E₂) := Finset.sum_le_sum ht
    _ = (∑ s ∈ choices, g s) * (E₁ + E₂) := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right hg (add_nonneg hE₁ hE₂)

theorem finite_observation_comparison_bound
    (choices : Finset A) (T : Finset J) (a : (J → Bool) → A → ℝ)
    (F W : A → (J → Bool) → (J → Bool) → ℝ)
    (value : (J → Bool) → ℝ) (base : (J → Bool) → (J → Bool) → ℝ)
    (cells : Bool → (J → Bool) → ℝ)
    (g : A → ℝ) (E₁ E₂ C R : ℝ) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hg : (∑ s ∈ choices, g s) ≤ C)
    (hfirst : ∀ s ∈ choices,
      |independentSigns.expect (fun ζ => a ζ s *
        (F s ζ ζ - Walsh.resampleAverage T (F s ζ) ζ))| ≤ g s * E₁)
    (hsecond : ∀ s ∈ choices,
      |independentSigns.expect (fun ζ => a ζ s *
        Walsh.resampleAverage T (fun η => F s ζ η - W s ζ η) ζ)| ≤ g s * E₂)
    (hzero : ∀ ζ, value ζ = (∑ s ∈ choices, a ζ s * F s ζ ζ) + base ζ ζ * cells false ζ)
    (hmatch : independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => ∑ s ∈ choices, a ζ s * W s ζ η) ζ) =
      independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => base ζ η * (cells true ζ - cells false ζ)) ζ))
    (hrestore : |independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => base ζ η * (cells true ζ - cells false ζ)) ζ) -
      independentSigns.expect (fun ζ => base ζ ζ * (cells true ζ - cells false ζ))| ≤ R) :
    |independentSigns.expect value - independentSigns.expect
      (fun ζ => base ζ ζ * cells true ζ)| ≤ C * (E₁ + E₂) + R := by
  have he : independentSigns.expect value - independentSigns.expect
      (fun ζ => base ζ ζ * cells true ζ) =
      independentSigns.expect (fun ζ => ∑ s ∈ choices, a ζ s * F s ζ ζ) -
        independentSigns.expect (fun ζ => base ζ ζ * (cells true ζ - cells false ζ)) := by
    rw [FiniteLaw.expect_congr _ hzero, FiniteLaw.expect_add]
    simp only [mul_sub, FiniteLaw.expect_sub]
    ring
  rw [he]
  apply (abs_sub_le _ (independentSigns.expect (fun ζ => Walsh.resampleAverage T
    (fun η => ∑ s ∈ choices, a ζ s * W s ζ η) ζ)) _).trans
  apply add_le_add
  · exact finite_pattern_comparison_bound choices T a F W g E₁ E₂ C hE₁ hE₂ hg hfirst hsecond
  · rw [hmatch]
    exact hrestore

end CausalLowerbound.PartC
