import CausalLowerbound.PartC.BlockPolynomialExpansion
import CausalLowerbound.PartC.SharedBlockMoments

/-! The actual design-weighted polynomial expectation under a shared-sign
prior. The polynomial may itself depend on the shared signs; their average
stays outside the products of one-block moments. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB MvPolynomial
variable {K J A Ω : Type*} [Fintype K] [DecidableEq K] [Fintype J] [DecidableEq J]
  [Fintype A] [DecidableEq A] [Fintype Ω]

theorem signBlockPrior_expect_by_sign (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω)
    (f : (J → Bool) → (K → ℕ) → (K → Ω) → ℝ)
    (B : ℝ) (hf : ∀ ζ labels U, |f ζ labels U| ≤ B) :
    (signBlockPrior H kernel).expect (fun z => f z.1.2 z.1.1 z.2) =
      independentSigns.expect (fun ζ => (DiscreteLaw.independent H).expect (fun labels =>
        (FiniteLaw.independent (fun k => kernel k ζ (labels k))).expect (f ζ labels))) := by
  rw [signBlockPrior_expect H kernel _ B (fun z => hf z.1.2 z.1.1 z.2)]
  have he (labels : K → ℕ) (ζ : J → Bool) :
      |(signBlockKernel kernel (labels, ζ)).expect (f ζ labels)| ≤ B :=
    (signBlockKernel kernel (labels, ζ)).abs_expect_le_bound _ _ (hf ζ labels)
  rw [sharedSignPrior_expect H _ B (fun z => he z.1 z.2),
    DiscreteLaw.expect_finite_comm _ independentSigns _ B he]
  rfl

theorem independent_weighted_polynomial_expect (H : K → DiscreteLaw ℕ)
    (kernel : K → ℕ → FiniteLaw Ω) (atoms : Ω → A → ℝ)
    (density : K → ℕ → ℝ) (D : K → ℝ) (hD : ∀ k, 0 ≤ D k)
    (hd : ∀ k n, |density k n| ≤ D k) (p : MvPolynomial (K × A) ℝ) :
    (DiscreteLaw.independent H).expect (fun labels =>
      (FiniteLaw.independent (fun k => kernel k (labels k))).expect (fun U =>
        (∏ k, density k (labels k)) * eval (fun ka => atoms (U ka.1) ka.2) p)) =
      ∑ m ∈ p.support, p.coeff m * ∏ k,
        (H k).expect (fun n => density k n * (kernel k n).expect
          (fun u => eval (atoms u) (blockMonomial m k))) := by
  let F (m : (K × A) →₀ ℕ) (k : K) (n : ℕ) :=
    density k n * (kernel k n).expect (fun u => eval (atoms u) (blockMonomial m k))
  let C (m : (K × A) →₀ ℕ) (k : K) :=
    D k * ∑ u, |eval (atoms u) (blockMonomial m k)|
  have hF (m : (K × A) →₀ ℕ) (k : K) (n : ℕ) : |F m k n| ≤ C m k := by
    dsimp only [F, C]
    rw [abs_mul]
    exact mul_le_mul (hd k n) ((kernel k n).abs_expect_le_bound _ _ (fun u =>
      Finset.single_le_sum (fun v _ => abs_nonneg (eval (atoms v) (blockMonomial m k)))
        (Finset.mem_univ u))) (abs_nonneg _) (hD k)
  have he (labels : K → ℕ) :
      (FiniteLaw.independent (fun k => kernel k (labels k))).expect (fun U =>
        (∏ k, density k (labels k)) * eval (fun ka => atoms (U ka.1) ka.2) p) =
        ∑ m : p.support, p.coeff m.val * ∏ k, F m.val k (labels k) := by
    calc
      _ = (FiniteLaw.independent (fun k => kernel k (labels k))).expect (fun U =>
          ∑ m ∈ p.support, p.coeff m * ∏ k,
            density k (labels k) * eval (atoms (U k)) (blockMonomial m k)) :=
        FiniteLaw.expect_congr _ (fun U => weighted_eval_block_expansion p
          (fun k => atoms (U k)) (fun k => density k (labels k)))
      _ = _ := by
        rw [FiniteLaw.expect_finset_sum]
        simp only [FiniteLaw.expect_mul]
        rw [← Finset.sum_coe_sort p.support]
        apply Finset.sum_congr rfl
        intro m _
        rw [FiniteLaw.expect_independent_prod (fun k => kernel k (labels k))
          (fun k u => density k (labels k) * eval (atoms u) (blockMonomial m.val k))]
        simp only [FiniteLaw.expect_mul, F]
  have hb (m : p.support) (labels : K → ℕ) :
      |p.coeff m.val * ∏ k, F m.val k (labels k)| ≤ |p.coeff m.val| * ∏ k, C m.val k := by
    rw [abs_mul, Finset.abs_prod]
    exact mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun k _ => hF m.val k (labels k)))
      (abs_nonneg _)
  simp_rw [he]
  rw [DiscreteLaw.expect_fintype_sum _ _ (fun m : p.support => |p.coeff m.val| * ∏ k, C m.val k) hb]
  simp only [DiscreteLaw.expect_const_mul]
  simp_rw [DiscreteLaw.expect_independent_prod H (F _) (C _) (hF _)]
  simpa only [F] using Finset.sum_coe_sort p.support
    (fun m => p.coeff m * ∏ k, (H k).expect (F m k))

theorem signBlockPrior_weighted_polynomial_expect (H : K → DiscreteLaw ℕ)
    (kernel : K → (J → Bool) → ℕ → FiniteLaw Ω) (atoms : Ω → A → ℝ)
    (density : K → (J → Bool) → ℕ → ℝ) (D : K → ℝ) (hD : ∀ k, 0 ≤ D k)
    (hd : ∀ k ζ n, |density k ζ n| ≤ D k)
    (p : (J → Bool) → MvPolynomial (K × A) ℝ) :
    (signBlockPrior H kernel).expect (fun z =>
      (∏ k, density k z.1.2 (z.1.1 k)) * eval (fun ka => atoms (z.2 ka.1) ka.2) (p z.1.2)) =
      independentSigns.expect (fun ζ => ∑ m ∈ (p ζ).support, (p ζ).coeff m * ∏ k,
        (H k).expect (fun n => density k ζ n * (kernel k ζ n).expect
          (fun u => eval (atoms u) (blockMonomial m k)))) := by
  let M := ∑ ζ : J → Bool, ∑ U : K → Ω, |eval (fun ka => atoms (U ka.1) ka.2) (p ζ)|
  have hm (ζ : J → Bool) (U : K → Ω) :
      |eval (fun ka => atoms (U ka.1) ka.2) (p ζ)| ≤ M :=
    (Finset.single_le_sum (fun (V : K → Ω) _ => abs_nonneg (eval (fun ka => atoms (V ka.1) ka.2) (p ζ)))
      (Finset.mem_univ U)).trans
      (Finset.single_le_sum (fun (η : J → Bool) _ => Finset.sum_nonneg (fun (V : K → Ω) _ =>
        abs_nonneg (eval (fun ka => atoms (V ka.1) ka.2) (p η)))) (Finset.mem_univ ζ))
  have hb (ζ : J → Bool) (labels : K → ℕ) (U : K → Ω) :
      |(∏ k, density k ζ (labels k)) * eval (fun ka => atoms (U ka.1) ka.2) (p ζ)| ≤
        (∏ k, D k) * M := by
    rw [abs_mul, Finset.abs_prod]
    exact mul_le_mul (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun k _ => hd k ζ (labels k)))
      (hm ζ U) (abs_nonneg _) (Finset.prod_nonneg (fun k _ => hD k))
  rw [signBlockPrior_expect_by_sign H kernel _ ((∏ k, D k) * M) hb]
  apply FiniteLaw.expect_congr
  intro ζ
  exact independent_weighted_polynomial_expect H (fun k => kernel k ζ) atoms
    (fun k => density k ζ) D hD (fun k => hd k ζ) (p ζ)

end CausalLowerbound.PartC
