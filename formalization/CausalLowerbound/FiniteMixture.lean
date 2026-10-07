import CausalLowerbound.FiniteBounds

/-! Finite mixtures and the error saved by an exactly matched component. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.FiniteLaw

open scoped BigOperators

variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ]

def mixture (μ : FiniteLaw Λ) (laws : Λ → FiniteLaw Ω) : FiniteLaw Ω where
  weight ω := μ.expect (fun a => (laws a).weight ω)
  nonneg ω := μ.expect_nonneg _ (fun a => (laws a).nonneg ω)
  total := by
    simp only [expect]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, FiniteLaw.total, mul_one]

theorem expect_mixture (μ : FiniteLaw Λ) (laws : Λ → FiniteLaw Ω) (f : Ω → ℝ) :
    (mixture μ laws).expect f = μ.expect (fun a => (laws a).expect f) := by
  simp only [expect, mixture, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem weight_le_one (μ : FiniteLaw Ω) (ω : Ω) : μ.weight ω ≤ 1 := by
  classical
  calc
    _ ≤ ∑ z, μ.weight z := Finset.single_le_sum (fun z _ => μ.nonneg z) (Finset.mem_univ ω)
    _ = 1 := μ.total

/-- If one mixture component is exact, only its complement contributes error. -/
theorem matched_component_error (μ : FiniteLaw Ω) (good : Ω) (f : Ω → ℝ)
    (target ε : ℝ) (hgood : f good = target) (herr : ∀ ω, |f ω - target| ≤ ε) :
    |μ.expect f - target| ≤ ε * (1 - μ.weight good) := by
  classical
  calc
    _ = |μ.expect (fun ω => f ω - target)| := by rw [μ.expect_sub, μ.expect_const]
    _ ≤ μ.expect (fun ω => |f ω - target|) := μ.abs_expect_le _
    _ ≤ μ.expect (fun ω => ε - if ω = good then ε else 0) := by
      apply μ.expect_mono
      intro ω
      by_cases h : ω = good
      · subst ω
        simp [hgood]
      · simpa only [h, if_false, sub_zero] using herr ω
    _ = ε * (1 - μ.weight good) := by
      rw [μ.expect_sub, μ.expect_const]
      simp only [expect, mul_ite, mul_zero]
      simp
      ring

/-- Squaring the error still costs only one power of the unmatched mass. -/
theorem matched_component_sq_error (μ : FiniteLaw Ω) (good : Ω) (f : Ω → ℝ)
    (target ε : ℝ) (hgood : f good = target)
    (herr : ∀ ω, |f ω - target| ≤ ε) :
    (μ.expect f - target) ^ 2 ≤ ε ^ 2 * (1 - μ.weight good) := by
  have he := μ.matched_component_error good f target ε hgood herr
  have hb0 : 0 ≤ 1 - μ.weight good := sub_nonneg.mpr (μ.weight_le_one good)
  have hb1 : 1 - μ.weight good ≤ 1 := by linarith [μ.nonneg good]
  have he0 := abs_nonneg (μ.expect f - target)
  have he2 := mul_self_le_mul_self he0 he
  have hb2 : (1 - μ.weight good) ^ 2 ≤ 1 - μ.weight good := by nlinarith
  have hs := mul_le_mul_of_nonneg_left hb2 (sq_nonneg ε)
  rw [← sq, ← sq, sq_abs] at he2
  nlinarith

end CausalLowerbound.FiniteLaw
