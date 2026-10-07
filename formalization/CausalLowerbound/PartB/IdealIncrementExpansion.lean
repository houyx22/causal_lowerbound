import CausalLowerbound.PartB.ShiftedMonomials

/-! Exact averaging of the ideal shifted monomial. Its increment has a
finite expansion in coefficient products, and every nonzero coefficient
contains at least two shift factors. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound

theorem FiniteLaw.expect_fintype_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (μ : FiniteLaw Ω) (f : I → Ω → ℝ) :
    μ.expect (fun ω => ∑ i, f i ω) = ∑ i, μ.expect (f i) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_comm

namespace PartB

variable {Ω K V : Type*} [Fintype Ω] [Fintype K] [DecidableEq K] [Fintype V] [DecidableEq V]

def choiceMean (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (s : K → Option V) : ℝ :=
  μ.expect (fun ω => choiceBase (U ω) s) *
    independentSigns.expect (fun ζ => ∏ k : ShiftPositions s, sign (ζ (choiceSite s k)))

def incrementWeight (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (s : K → Option V) : ℝ :=
  if s = (fun _ => none) then 0 else choiceMean μ U s

def idealMonomialMoment (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (c : K → V → ℝ) (t : ℝ) : ℝ :=
  (μ.prod (independentSigns (ι := V))).expect
    (fun p => ∏ k, (U p.1 k + t * ∑ i, c k i * sign (p.2 i)))

theorem choice_mean_term (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (c : K → V → ℝ) (t : ℝ)
    (s : K → Option V) :
    (μ.prod (independentSigns (ι := V))).expect
      (fun p => choiceValue (U p.1) (fun k i => t * c k i * sign (p.2 i)) s) =
      choiceMean μ U s * t ^ choiceDegree s * ∏ k : ShiftPositions s, c k.val (choiceSite s k) := by
  simp_rw [choiceValue_scaled]
  rw [FiniteLaw.expect_prod]
  simp only [FiniteLaw.expect_mul, FiniteLaw.expect_mul_const]
  unfold choiceMean
  ring

theorem idealMonomialMoment_expansion (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (c : K → V → ℝ) (t : ℝ) :
    idealMonomialMoment μ U c t = ∑ s : K → Option V,
      choiceMean μ U s * t ^ choiceDegree s * ∏ k : ShiftPositions s, c k.val (choiceSite s k) := by
  have he (p : Ω × (V → Bool)) : (∏ k, (U p.1 k + t * ∑ i, c k i * sign (p.2 i))) =
      ∑ s : K → Option V, choiceValue (U p.1) (fun k i => t * c k i * sign (p.2 i)) s := by
    simp only [Finset.mul_sum, ← mul_assoc]
    exact shifted_product_expansion _ _
  rw [idealMonomialMoment, (μ.prod (independentSigns (ι := V))).expect_congr he,
    FiniteLaw.expect_fintype_sum]
  simp only [choice_mean_term]

theorem choice_mean_degree_one (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (s : K → Option V)
    (hs : choiceDegree s = 1) : choiceMean μ U s = 0 := by
  rw [choiceMean, sign_product_one_mean (choiceSite s) hs, mul_zero]

theorem incrementWeight_nonzero_degree (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (s : K → Option V)
    (h : incrementWeight μ U s ≠ 0) : 2 ≤ choiceDegree s := by
  have hne : s ≠ (fun _ => none) := by
    intro he
    exact h (by simp only [incrementWeight, if_pos he])
  have h0 : choiceDegree s ≠ 0 := fun hz => hne ((choiceDegree_zero_iff s).mp hz)
  have h1 : choiceDegree s ≠ 1 := by
    intro ho
    exact h (by rw [incrementWeight, if_neg hne, choice_mean_degree_one μ U s ho])
  omega

theorem finite_sum_sub_single {I : Type*} [Fintype I] [DecidableEq I] (f : I → ℝ) (z : I) :
    (∑ i, f i) - f z = ∑ i, if i = z then 0 else f i := by
  classical
  have he : (∑ i, f i) = f z + ∑ i, if i = z then 0 else f i := by
    calc
      (∑ i, f i) = ∑ i, ((if i = z then f z else 0) + (if i = z then 0 else f i)) := by
        apply Finset.sum_congr rfl
        intro i _
        split_ifs with h
        · rw [h, add_zero]
        · rw [zero_add]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [he]
  ring

theorem idealMonomialIncrement_expansion (μ : FiniteLaw Ω) (U : Ω → K → ℝ) (c : K → V → ℝ) (t : ℝ) :
    idealMonomialMoment μ U c t - μ.expect (fun ω => ∏ k, U ω k) =
      ∑ s : K → Option V,
        incrementWeight μ U s * t ^ choiceDegree s * ∏ k : ShiftPositions s, c k.val (choiceSite s k) := by
  let f (s : K → Option V) := choiceMean μ U s * t ^ choiceDegree s *
    ∏ k : ShiftPositions s, c k.val (choiceSite s k)
  have hz : f (fun _ => none) = μ.expect (fun ω => ∏ k, U ω k) := by
    dsimp only [f]
    rw [← choice_mean_term μ U c t (fun _ => none)]
    rw [FiniteLaw.expect_prod]
    simp only [choiceValue, Option.elim_none, FiniteLaw.expect_const]
  rw [idealMonomialMoment_expansion, ← hz, finite_sum_sub_single f (fun _ => none)]
  apply Finset.sum_congr rfl
  intro s _
  simp only [incrementWeight, ite_mul, zero_mul]
  rfl

end PartB
end CausalLowerbound
