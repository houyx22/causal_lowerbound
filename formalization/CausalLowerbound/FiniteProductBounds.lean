import CausalLowerbound.FiniteBounds

/-! A product perturbation bound that does not assume positivity of the
intermediate factors. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical
namespace CausalLowerbound

theorem abs_prod_sub_prod_le_bounded {I : Type*} (s : Finset I) (f g : I → ℝ)
    (M : ℝ) (hM : 1 ≤ M) (hf : ∀ i ∈ s, |f i| ≤ M) (hg : ∀ i ∈ s, |g i| ≤ M) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ M ^ s.card * ∑ i ∈ s, |f i - g i| := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hnorm (v : ℝ) (hv : |v| ≤ M) : |v / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hM0]
    exact (div_le_one hM0).mpr hv
  have he := abs_prod_sub_prod_le s (fun i => f i / M) (fun i => g i / M)
    (fun i hi => hnorm _ (hf i hi)) (fun i hi => hnorm _ (hg i hi))
  have hs : (∑ i ∈ s, |f i / M - g i / M|) ≤ ∑ i ∈ s, |f i - g i| := by
    apply Finset.sum_le_sum
    intro i _
    rw [← sub_div, abs_div, abs_of_pos hM0]
    exact div_le_self (abs_nonneg _) hM
  have he' := he.trans hs
  simp only [Finset.prod_div_distrib, Finset.prod_const, ← sub_div, abs_div,
    abs_of_pos (pow_pos hM0 s.card)] at he'
  simpa only [mul_comm] using (div_le_iff₀ (pow_pos hM0 s.card)).mp he'

end CausalLowerbound
