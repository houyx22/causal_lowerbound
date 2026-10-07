import CausalLowerbound.DiscreteIntegration
import CausalLowerbound.PartB.IdealIncrementExpansion

/-! Finite coefficient/output laws mixed over every countable carrier
label, including their exact posterior moment differences. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace CausalLowerbound.DiscreteLaw
variable {Ω Γ I : Type*} [Fintype Γ] [Fintype I]

theorem expect_fintype_sum (μ : DiscreteLaw Ω) (f : I → Ω → ℝ) (B : I → ℝ)
    (hb : ∀ i x, |f i x| ≤ B i) :
    μ.expect (fun x => ∑ i, f i x) = ∑ i, μ.expect (f i) := by
  unfold expect
  simp only [Finset.mul_sum]
  exact Summable.tsum_finsetSum (fun i _ => μ.summable_expect_of_bounded (f i) (B i) (hb i))

theorem expect_sub_bounded (μ : DiscreteLaw Ω) (f g : Ω → ℝ) (B C : ℝ)
    (hf : ∀ x, |f x| ≤ B) (hg : ∀ x, |g x| ≤ C) :
    μ.expect (fun x => f x - g x) = μ.expect f - μ.expect g := by
  unfold expect
  simp only [mul_sub]
  exact (μ.summable_expect_of_bounded f B hf).tsum_sub (μ.summable_expect_of_bounded g C hg)

theorem expect_const_mul (μ : DiscreteLaw Ω) (c : ℝ) (f : Ω → ℝ) :
    μ.expect (fun x => c * f x) = c * μ.expect f := by
  simp only [expect, mul_left_comm (μ.weight _) c, tsum_mul_left]

def mixFinite (μ : DiscreteLaw Ω) (kernel : Ω → FiniteLaw Γ) : FiniteLaw Γ where
  weight y := μ.expect (fun label => (kernel label).weight y)
  nonneg y := tsum_nonneg (fun label => mul_nonneg (μ.nonneg label) ((kernel label).nonneg y))
  total := by
    rw [← μ.expect_fintype_sum _ (fun _ : Γ => 1) (fun y label => by
      rw [abs_of_nonneg ((kernel label).nonneg y)]; exact (kernel label).weight_le_one y)]
    simp only [FiniteLaw.total, expect, mul_one, μ.tsum_weight]

theorem mixFinite_expect (μ : DiscreteLaw Ω) (kernel : Ω → FiniteLaw Γ) (f : Γ → ℝ) :
    (μ.mixFinite kernel).expect f = μ.expect (fun label => (kernel label).expect f) := by
  have hb (y : Γ) (label : Ω) : |(kernel label).weight y * f y| ≤ |f y| := by
    rw [abs_mul, abs_of_nonneg ((kernel label).nonneg y)]
    exact mul_le_of_le_one_left (abs_nonneg _) ((kernel label).weight_le_one y)
  simp only [FiniteLaw.expect, mixFinite, expect, ← tsum_mul_right, mul_assoc]
  simp only [Finset.mul_sum]
  exact (Summable.tsum_finsetSum (s := Finset.univ)
    (fun y _ => μ.summable_expect_of_bounded _ (|f y|) (hb y))).symm

theorem posterior_moment_difference (μ : DiscreteLaw Ω) (P Q : Ω → FiniteLaw Γ)
    (g : Ω → ℝ) (lo hi : ℝ) (hlo : 0 < lo) (hg : ∀ x, lo ≤ g x ∧ g x ≤ hi)
    (f : Γ → ℝ) :
    ((μ.tilt g lo hi hlo hg).mixFinite Q).expect f -
      ((μ.tilt g lo hi hlo hg).mixFinite P).expect f =
        (μ.expect g)⁻¹ * μ.expect (fun label => g label * ((Q label).expect f - (P label).expect f)) := by
  have hb (y : Γ) : |f y| ≤ ∑ z, |f z| :=
    Finset.single_le_sum (fun z _ => abs_nonneg (f z)) (Finset.mem_univ y)
  rw [mixFinite_expect, mixFinite_expect,
    ← expect_sub_bounded _ _ _ (∑ z, |f z|) (∑ z, |f z|)
      (fun label => (Q label).abs_expect_le_bound f _ hb)
      (fun label => (P label).abs_expect_le_bound f _ hb), tilt_expect]

end CausalLowerbound.DiscreteLaw
