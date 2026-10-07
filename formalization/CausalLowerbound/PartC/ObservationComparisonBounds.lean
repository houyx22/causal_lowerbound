import CausalLowerbound.PartC.UntaperedIncrementMatching
import CausalLowerbound.PartC.ResamplingParity

/-! Sum the two pattern errors, cancel the empty pattern, and restore the
original signs after matching. All averages use the same finite sign law. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB
variable {Ω I K J : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
  [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]

theorem nonempty_choice_expect_sum (μ : FiniteLaw Ω) (f : Ω → (I → Option K) → ℝ) :
    μ.expect (fun ω => ∑ s : I → Option K, if 0 < choiceDegree s then f ω s else 0) =
      ∑ s : I → Option K, if 0 < choiceDegree s then μ.expect (fun ω => f ω s) else 0 := by
  rw [FiniteLaw.expect_fintype_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : 0 < choiceDegree s <;> simp only [hs, if_true, if_false, FiniteLaw.expect_const]

theorem nonempty_pattern_comparison_bound
    (T : Finset J) (a : (J → Bool) → (I → Option K) → ℝ)
    (F W : (I → Option K) → (J → Bool) → (J → Bool) → ℝ)
    (g : (I → Option K) → ℝ) (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg : (∑ s : I → Option K, if 0 < choiceDegree s then g s else 0) ≤ C)
    (hfirst : ∀ s, 0 < choiceDegree s →
      |independentSigns.expect (fun ζ => a ζ s * (F s ζ ζ - Walsh.resampleAverage T (F s ζ) ζ))| ≤ g s * A)
    (hsecond : ∀ s, 0 < choiceDegree s →
      |independentSigns.expect (fun ζ => a ζ s * Walsh.resampleAverage T (fun η => F s ζ η - W s ζ η) ζ)| ≤ g s * B) :
    |independentSigns.expect (fun ζ => ∑ s : I → Option K,
        if 0 < choiceDegree s then a ζ s * F s ζ ζ else 0) -
      independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => ∑ s : I → Option K,
        if 0 < choiceDegree s then a ζ s * W s ζ η else 0) ζ)| ≤ C * (A + B) := by
  have ht (s : I → Option K) (hs : 0 < choiceDegree s) :
      |independentSigns.expect (fun ζ => a ζ s * F s ζ ζ) -
        independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => a ζ s * W s ζ η) ζ)| ≤
        g s * (A + B) := by
    have he ζ : a ζ s * F s ζ ζ - Walsh.resampleAverage T (fun η => a ζ s * W s ζ η) ζ =
        a ζ s * (F s ζ ζ - Walsh.resampleAverage T (F s ζ) ζ) +
          a ζ s * Walsh.resampleAverage T (fun η => F s ζ η - W s ζ η) ζ := by
      simp only [Walsh.resampleAverage, FiniteLaw.expect_mul, FiniteLaw.expect_sub]
      ring
    rw [← FiniteLaw.expect_sub, FiniteLaw.expect_congr _ he, FiniteLaw.expect_add]
    exact (abs_add _ _).trans ((add_le_add (hfirst s hs) (hsecond s hs)).trans (by rw [mul_add]))
  have hr ζ : Walsh.resampleAverage T (fun η => ∑ s : I → Option K,
      if 0 < choiceDegree s then a ζ s * W s ζ η else 0) ζ =
      ∑ s : I → Option K, if 0 < choiceDegree s then
        Walsh.resampleAverage T (fun η => a ζ s * W s ζ η) ζ else 0 :=
    nonempty_choice_expect_sum independentSigns (fun fresh s => a ζ s * W s ζ (Walsh.resample T ζ fresh))
  rw [FiniteLaw.expect_congr _ hr, nonempty_choice_expect_sum, nonempty_choice_expect_sum,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ s : I → Option K, |(if 0 < choiceDegree s then
          independentSigns.expect (fun ζ => a ζ s * F s ζ ζ) else 0) -
        (if 0 < choiceDegree s then independentSigns.expect
          (fun ζ => Walsh.resampleAverage T (fun η => a ζ s * W s ζ η) ζ) else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : I → Option K, if 0 < choiceDegree s then g s * (A + B) else 0 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : 0 < choiceDegree s
      · simp only [if_pos hs]
        exact ht s hs
      · simp only [if_neg hs, sub_self, abs_zero, le_refl]
    _ = (∑ s : I → Option K, if 0 < choiceDegree s then g s else 0) * (A + B) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : 0 < choiceDegree s <;> simp only [hs, if_true, if_false, zero_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hg (add_nonneg hA hB)

theorem observation_pattern_comparison_bound
    (T : Finset J) (a : (J → Bool) → (I → Option K) → ℝ)
    (F W : (I → Option K) → (J → Bool) → (J → Bool) → ℝ)
    (base : (J → Bool) → (J → Bool) → ℝ) (cells : Bool → (J → Bool) → ℝ)
    (g : (I → Option K) → ℝ) (A B C R : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg : (∑ s : I → Option K, if 0 < choiceDegree s then g s else 0) ≤ C)
    (hfirst : ∀ s, 0 < choiceDegree s →
      |independentSigns.expect (fun ζ => a ζ s * (F s ζ ζ - Walsh.resampleAverage T (F s ζ) ζ))| ≤ g s * A)
    (hsecond : ∀ s, 0 < choiceDegree s →
      |independentSigns.expect (fun ζ => a ζ s * Walsh.resampleAverage T (fun η => F s ζ η - W s ζ η) ζ)| ≤ g s * B)
    (hzero : ∀ ζ, a ζ (fun _ => none) * F (fun _ => none) ζ ζ = base ζ ζ * cells false ζ)
    (hmatch : independentSigns.expect (fun ζ => Walsh.resampleAverage T (fun η => ∑ s : I → Option K,
        if 0 < choiceDegree s then a ζ s * W s ζ η else 0) ζ) =
      independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => base ζ η * (cells true ζ - cells false ζ)) ζ))
    (hrestore : |independentSigns.expect (fun ζ => Walsh.resampleAverage T
        (fun η => base ζ η * (cells true ζ - cells false ζ)) ζ) -
      independentSigns.expect (fun ζ => base ζ ζ * (cells true ζ - cells false ζ))| ≤ R) :
    |independentSigns.expect (fun ζ => ∑ s : I → Option K, a ζ s * F s ζ ζ) -
      independentSigns.expect (fun ζ => base ζ ζ * cells true ζ)| ≤ C * (A + B) + R := by
  have hz ζ : (∑ s : I → Option K, a ζ s * F s ζ ζ) =
      (∑ s : I → Option K, if 0 < choiceDegree s then a ζ s * F s ζ ζ else 0) + base ζ ζ * cells false ζ := by
    have he := nonempty_observation_choice_sum (fun s : I → Option K => a ζ s * F s ζ ζ)
    rw [hzero ζ] at he
    linarith
  have he : independentSigns.expect (fun ζ => ∑ s : I → Option K, a ζ s * F s ζ ζ) -
      independentSigns.expect (fun ζ => base ζ ζ * cells true ζ) =
      independentSigns.expect (fun ζ => ∑ s : I → Option K,
        if 0 < choiceDegree s then a ζ s * F s ζ ζ else 0) -
      independentSigns.expect (fun ζ => base ζ ζ * (cells true ζ - cells false ζ)) := by
    rw [FiniteLaw.expect_congr _ hz, FiniteLaw.expect_add]
    simp only [mul_sub, FiniteLaw.expect_sub]
    ring
  rw [he]
  apply (abs_sub_le _ (independentSigns.expect (fun ζ => Walsh.resampleAverage T
    (fun η => ∑ s : I → Option K, if 0 < choiceDegree s then a ζ s * W s ζ η else 0) ζ)) _).trans
  apply add_le_add
  · exact nonempty_pattern_comparison_bound T a F W g A B C hA hB hg hfirst hsecond
  · rw [hmatch]
    exact hrestore

end CausalLowerbound.PartC
