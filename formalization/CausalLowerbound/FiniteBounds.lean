import CausalLowerbound.FiniteExpectation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Elementary expectation inequalities and a finite product telescoping bound. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound

open scoped BigOperators

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem expect_nonneg (f : Ω → ℝ) (h : ∀ ω, 0 ≤ f ω) : 0 ≤ μ.expect f :=
  Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (h ω))

theorem expect_mono {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

theorem abs_expect_le (f : Ω → ℝ) :
    |μ.expect f| ≤ μ.expect (fun ω => |f ω|) := by
  unfold expect
  calc
    _ ≤ ∑ ω, |μ.weight ω * f ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (μ.nonneg _)]

theorem abs_expect_le_bound (f : Ω → ℝ) (B : ℝ) (h : ∀ ω, |f ω| ≤ B) :
    |μ.expect f| ≤ B := by
  calc
    _ ≤ μ.expect (fun ω => |f ω|) := μ.abs_expect_le f
    _ ≤ μ.expect (fun _ => B) := μ.expect_mono h
    _ = B := μ.expect_const B

end FiniteLaw

/-- Tensorization for bounded Walsh coefficients. -/
theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1) (hb : ∀ i ∈ s, |b i| ≤ 1) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have has : ∀ j ∈ s, |a j| ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hbs : ∀ j ∈ s, |b j| ≤ 1 := fun j hj => hb j (Finset.mem_insert_of_mem hj)
    have hap : |∏ j ∈ s, a j| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun j _ => abs_nonneg _) has
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      _ = |(a i - b i) * (∏ j ∈ s, a j) +
          b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j)| := by congr 1; ring
      _ ≤ |(a i - b i) * (∏ j ∈ s, a j)| +
          |b i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j)| := abs_add _ _
      _ = |a i - b i| * |∏ j ∈ s, a j| +
          |b i| * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| := by rw [abs_mul, abs_mul]
      _ ≤ |a i - b i| * 1 + 1 * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| :=
        add_le_add (mul_le_mul_of_nonneg_left hap (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (hb i (Finset.mem_insert_self _ _)) (abs_nonneg _))
      _ ≤ |a i - b i| + ∑ j ∈ s, |a j - b j| := by
        simpa only [mul_one, one_mul] using add_le_add_left (ih has hbs) |a i - b i|

end CausalLowerbound
