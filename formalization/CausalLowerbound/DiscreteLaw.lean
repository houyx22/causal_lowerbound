import CausalLowerbound.FiniteMixture
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Discrete probability laws, including countably many carrier labels. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound

open scoped BigOperators

/-- Nonnegative real weights with an actual convergent sum of one. -/
structure DiscreteLaw (Ω : Type*) where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : HasSum weight 1

namespace DiscreteLaw

variable {Ω : Type*} (μ : DiscreteLaw Ω)

def expect (f : Ω → ℝ) : ℝ := ∑' ω, μ.weight ω * f ω

theorem summable_weight : Summable μ.weight := μ.total.summable

theorem tsum_weight : (∑' ω, μ.weight ω) = 1 := μ.total.tsum_eq

theorem weight_le_one (ω : Ω) : μ.weight ω ≤ 1 := by
  rw [← μ.tsum_weight]
  exact μ.summable_weight.le_tsum ω (fun z _ => μ.nonneg z)

theorem summable_expect_of_bounded (f : Ω → ℝ) (B : ℝ) (hf : ∀ ω, |f ω| ≤ B) :
    Summable (fun ω => μ.weight ω * f ω) := by
  apply Summable.of_norm_bounded (fun ω => μ.weight ω * B) (μ.summable_weight.mul_right B)
  intro ω
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (μ.nonneg ω)]
  exact mul_le_mul_of_nonneg_left (hf ω) (μ.nonneg ω)

/-- Label zero carries the residual mass; label m+1 carries w_m. -/
def withRemainder (w : ℕ → ℝ) (hw : Summable w) (h0 : ∀ m, 0 ≤ w m)
    (h1 : (∑' m, w m) ≤ 1) : DiscreteLaw ℕ where
  weight n := match n with
    | 0 => 1 - ∑' m, w m
    | m + 1 => w m
  nonneg n := by
    cases n with
    | zero => exact sub_nonneg.mpr h1
    | succ m => exact h0 m
  total := by
    have h := (hasSum_nat_add_iff (f := fun n => match n with
      | 0 => 1 - ∑' m, w m
      | m + 1 => w m) 1).mp hw.hasSum
    simpa only [Finset.sum_range_one, ← add_sub_assoc, add_sub_cancel_left] using h

@[simp] theorem withRemainder_zero (w : ℕ → ℝ) (hw : Summable w)
    (h0 : ∀ m, 0 ≤ w m) (h1 : (∑' m, w m) ≤ 1) :
    (withRemainder w hw h0 h1).weight 0 = 1 - ∑' m, w m := rfl

@[simp] theorem withRemainder_succ (w : ℕ → ℝ) (hw : Summable w)
    (h0 : ∀ m, 0 ≤ w m) (h1 : (∑' m, w m) ≤ 1) (m : ℕ) :
    (withRemainder w hw h0 h1).weight (m + 1) = w m := rfl

variable {Γ : Type*} [Fintype Γ]

theorem joint_weights_summable (kernel : Ω → FiniteLaw Γ) :
    Summable (fun z : Ω × Γ => μ.weight z.1 * (kernel z.1).weight z.2) := by
  apply (summable_prod_of_nonneg (fun z => mul_nonneg (μ.nonneg z.1)
    ((kernel z.1).nonneg z.2))).mpr
  refine ⟨fun x => (hasSum_fintype _).summable, ?_⟩
  simpa only [tsum_fintype, ← Finset.mul_sum, FiniteLaw.total, mul_one] using μ.summable_weight

/-- A countable label and a conditionally drawn finite coefficient vector. -/
def joint (kernel : Ω → FiniteLaw Γ) : DiscreteLaw (Ω × Γ) where
  weight z := μ.weight z.1 * (kernel z.1).weight z.2
  nonneg z := mul_nonneg (μ.nonneg z.1) ((kernel z.1).nonneg z.2)
  total := by
    have hs := μ.joint_weights_summable kernel
    have ht : (∑' z : Ω × Γ, μ.weight z.1 * (kernel z.1).weight z.2) = 1 := by
      rw [hs.tsum_prod]
      simp only [tsum_fintype, ← Finset.mul_sum, FiniteLaw.total, mul_one, μ.tsum_weight]
    simpa only [ht] using hs.hasSum

/-- Every conditional kernel gives exactly the same label marginal. -/
theorem joint_label_marginal (kernel : Ω → FiniteLaw Γ) (x : Ω) :
    (∑ y, (μ.joint kernel).weight (x, y)) = μ.weight x := by
  simp only [joint, ← Finset.mul_sum, FiniteLaw.total, mul_one]

theorem expect_joint (kernel : Ω → FiniteLaw Γ) (f : Ω × Γ → ℝ)
    (B : ℝ) (hf : ∀ z, |f z| ≤ B) :
    (μ.joint kernel).expect f = μ.expect (fun x => (kernel x).expect (fun y => f (x, y))) := by
  have hs := (μ.joint kernel).summable_expect_of_bounded f B hf
  unfold expect
  rw [hs.tsum_prod]
  simp only [tsum_fintype, joint, FiniteLaw.expect, Finset.mul_sum, mul_assoc]

/-- Conditional expectation and subtraction for a bounded density-weighted moment. -/
theorem weighted_moment_difference (P Q : Ω → FiniteLaw Γ) (g : Ω → ℝ)
    (feature : Γ → ℝ) (C B : ℝ) (hC : 0 ≤ C)
    (hg : ∀ x, |g x| ≤ C) (hfeature : ∀ y, |feature y| ≤ B) :
    (μ.joint Q).expect (fun z => g z.1 * feature z.2) -
      (μ.joint P).expect (fun z => g z.1 * feature z.2) =
    μ.expect (fun x => g x * ((Q x).expect feature - (P x).expect feature)) := by
  have hpair : ∀ z : Ω × Γ, |g z.1 * feature z.2| ≤ C * B := by
    intro z
    rw [abs_mul]
    exact mul_le_mul (hg z.1) (hfeature z.2) (abs_nonneg _) hC
  have hbound : ∀ kernel : Ω → FiniteLaw Γ,
      ∀ x, |g x * (kernel x).expect feature| ≤ C * B := by
    intro kernel x
    rw [abs_mul]
    exact mul_le_mul (hg x) ((kernel x).abs_expect_le_bound feature B hfeature)
      (abs_nonneg _) hC
  rw [μ.expect_joint Q _ (C * B) hpair, μ.expect_joint P _ (C * B) hpair]
  simp only [FiniteLaw.expect_mul]
  have hsQ := μ.summable_expect_of_bounded _ (C * B) (hbound Q)
  have hsP := μ.summable_expect_of_bounded _ (C * B) (hbound P)
  unfold expect
  rw [← hsQ.tsum_sub hsP]
  apply tsum_congr
  intro x
  ring

end DiscreteLaw
end CausalLowerbound
