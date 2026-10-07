import CausalLowerbound.PartC.SharedSignFactorization

/-! Integrate the countable labels and conditionally independent block
coefficients while retaining the common rough signs. Finite polynomial
expansions then reduce to products of actual one-block weighted moments. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB
variable {K J Ω I : Type*} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]
  [Fintype Ω] [Fintype I]

theorem signBlockPrior_expect_separable (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (f : K → (J → Bool) → ℕ → Ω → ℝ) (B : K → ℝ)
    (hf : ∀ k ζ n u, |f k ζ n u| ≤ B k) :
    (signBlockPrior H kernel).expect (fun z => ∏ k, f k z.1.2 (z.1.1 k) (z.2 k)) =
      independentSigns.expect (fun ζ => ∏ k,
        (H k).expect (fun n => (kernel k ζ n).expect (f k ζ n))) := by
  have hprod (z : ((K → ℕ) × (J → Bool)) × (K → Ω)) :
      |∏ k, f k z.1.2 (z.1.1 k) (z.2 k)| ≤ ∏ k, B k := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun k _ => hf k z.1.2 (z.1.1 k) (z.2 k))
  have he (k : K) (ζ : J → Bool) (n : ℕ) : |(kernel k ζ n).expect (f k ζ n)| ≤ B k :=
    (kernel k ζ n).abs_expect_le_bound _ _ (hf k ζ n)
  have hep (labels : K → ℕ) (ζ : J → Bool) :
      |∏ k, (kernel k ζ (labels k)).expect (f k ζ (labels k))| ≤ ∏ k, B k := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun k _ => he k ζ (labels k))
  rw [signBlockPrior_expect H kernel _ (∏ k, B k) hprod]
  simp only [signBlockKernel, FiniteLaw.expect_independent_prod]
  rw [sharedSignPrior_expect H _ (∏ k, B k) (fun z => hep z.1 z.2),
    DiscreteLaw.expect_finite_comm _ independentSigns _ (∏ k, B k) hep]
  apply FiniteLaw.expect_congr
  intro ζ
  exact DiscreteLaw.expect_independent_prod H (fun k n => (kernel k ζ n).expect (f k ζ n)) B
    (fun k n => he k ζ n)

theorem signBlockPrior_expect_sum_products (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (coeff : I → ℝ)
    (f : I → K → (J → Bool) → ℕ → Ω → ℝ) (B : I → K → ℝ)
    (hf : ∀ i k ζ n u, |f i k ζ n u| ≤ B i k) :
    (signBlockPrior H kernel).expect (fun z => ∑ i, coeff i * ∏ k, f i k z.1.2 (z.1.1 k) (z.2 k)) =
      independentSigns.expect (fun ζ => ∑ i, coeff i * ∏ k,
        (H k).expect (fun n => (kernel k ζ n).expect (f i k ζ n))) := by
  have hb (i : I) (z : ((K → ℕ) × (J → Bool)) × (K → Ω)) :
      |coeff i * ∏ k, f i k z.1.2 (z.1.1 k) (z.2 k)| ≤ |coeff i| * ∏ k, B i k := by
    rw [abs_mul, Finset.abs_prod]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun k _ => hf i k z.1.2 (z.1.1 k) (z.2 k)))
      (abs_nonneg _)
  rw [DiscreteLaw.expect_fintype_sum _ _ (fun i => |coeff i| * ∏ k, B i k) hb,
    FiniteLaw.expect_fintype_sum]
  simp only [DiscreteLaw.expect_const_mul, FiniteLaw.expect_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [signBlockPrior_expect_separable H kernel (f i) (B i) (hf i)]

end CausalLowerbound.PartC
