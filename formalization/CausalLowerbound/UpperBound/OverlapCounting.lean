import CausalLowerbound.UpperBound.Covariance
import Mathlib.Data.Fintype.BigOperators

/-! Exact overlap counts for the average over one index from each role group.
The role group sizes may differ. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace CausalLowerbound.UpperBound

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {J : I → Type*} [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]

def overlap (a b : ∀ i, J i) : Finset I := Finset.univ.filter fun i => a i = b i

omit [DecidableEq I] [∀ i, Fintype (J i)] in
@[simp] theorem mem_overlap (a b : ∀ i, J i) (i : I) :
    i ∈ overlap a b ↔ a i = b i := by simp [overlap]

omit [DecidableEq I] [∀ i, Fintype (J i)] in
theorem overlap_eq_iff (a b : ∀ i, J i) (S : Finset I) :
    overlap a b = S ↔ ∀ i, (a i = b i ↔ i ∈ S) := by
  simp only [Finset.ext_iff, mem_overlap]

def overlapMultiplicity (J : I → Type*) [∀ i, Fintype (J i)] (S : Finset I) : ℕ :=
  ∏ i, if i ∈ S then 1 else Fintype.card (J i) - 1

theorem overlap_fiber_eq_piFinset (a : ∀ i, J i) (S : Finset I) :
    Finset.univ.filter (fun b : ∀ i, J i => overlap a b = S) =
      Fintype.piFinset (fun i => if i ∈ S then {a i} else Finset.univ.erase (a i)) := by
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
    overlap_eq_iff]
  apply forall_congr'
  intro i
  by_cases hi : i ∈ S <;> simp [hi, eq_comm]

theorem overlap_fiber_card (a : ∀ i, J i) (S : Finset I) :
    (Finset.univ.filter (fun b : ∀ i, J i => overlap a b = S)).card =
      overlapMultiplicity J S := by
  rw [overlap_fiber_eq_piFinset, Fintype.card_piFinset]
  unfold overlapMultiplicity
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [hi]

theorem sum_overlap_function (a : ∀ i, J i) (v : Finset I → ℝ) :
    (∑ b : ∀ i, J i, v (overlap a b)) =
      ∑ S : Finset I, (overlapMultiplicity J S : ℝ) * v S := by
  rw [← Finset.sum_fiberwise' Finset.univ (overlap a) v]
  simp only [Finset.sum_const, nsmul_eq_mul, overlap_fiber_card]

/-- The exact probability of an overlap pattern for two uniform tuple indices. -/
def overlapWeight (J : I → Type*) [∀ i, Fintype (J i)] (S : Finset I) : ℝ :=
  (overlapMultiplicity J S : ℝ) / Fintype.card (∀ i, J i)

omit [∀ i, DecidableEq (J i)] in
theorem overlapWeight_nonneg (S : Finset I) : 0 ≤ overlapWeight J S := by
  unfold overlapWeight
  positivity

omit [∀ i, DecidableEq (J i)] in
theorem overlapWeight_eq_product [∀ i, Nonempty (J i)] (S : Finset I) :
    overlapWeight J S =
      ∏ i, if i ∈ S then (Fintype.card (J i) : ℝ)⁻¹
        else 1 - (Fintype.card (J i) : ℝ)⁻¹ := by
  unfold overlapWeight overlapMultiplicity
  rw [Fintype.card_pi, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hc : 0 < Fintype.card (J i) := Fintype.card_pos
  have hc' : (Fintype.card (J i) : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hc
  by_cases hi : i ∈ S
  · simp [hi, one_div]
  · simp only [hi, if_false, Nat.cast_sub (Nat.succ_le_of_lt hc), Nat.cast_one]
    field_simp

/-- The split tuple average as a real-valued statistic. -/
def tupleAverage {Ω : Type*} (f : (∀ i, J i) → Ω → ℝ) (x : Ω) : ℝ :=
  (Fintype.card (∀ i, J i) : ℝ)⁻¹ * ∑ a, f a x

/-- After the probabilistic covariance identity has been proved, all tuple
coincidences are counted exactly, including the zero-overlap term. -/
theorem variance_tupleAverage_of_overlap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] [∀ i, Nonempty (J i)]
    (f : (∀ i, J i) → Ω → ℝ) (hf : ∀ a, MemLp (f a) 2 μ)
    (v : Finset I → ℝ) (hv : ∀ a b, covariance μ (f a) (f b) = v (overlap a b)) :
    variance μ (tupleAverage f) = ∑ S : Finset I, overlapWeight J S * v S := by
  unfold tupleAverage
  rw [variance_const_mul, variance_sum μ f hf]
  simp_rw [hv, sum_overlap_function]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  have hc : (Fintype.card (∀ i, J i) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos (α := ∀ i, J i)))
  unfold overlapWeight
  field_simp
  ring

end CausalLowerbound.UpperBound
