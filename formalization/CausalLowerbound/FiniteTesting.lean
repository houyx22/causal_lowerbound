import CausalLowerbound.PartB.ComponentMixture

/-! Finite Hellinger tensorization, total variation, and absolute-loss
two-point testing. Constants use H² = sum (sqrt p - sqrt q)². -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace CausalLowerbound.FiniteLaw
variable {Ω : Type*} [Fintype Ω]

def affinity (P Q : FiniteLaw Ω) : ℝ := ∑ w, Real.sqrt (P.weight w) * Real.sqrt (Q.weight w)
def totalVariation (P Q : FiniteLaw Ω) : ℝ := (∑ w, |P.weight w - Q.weight w|) / 2

theorem affinity_nonneg (P Q : FiniteLaw Ω) : 0 ≤ P.affinity Q :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem affinity_le_one (P Q : FiniteLaw Ω) : P.affinity Q ≤ 1 := by
  have h := Real.sum_sqrt_mul_sqrt_le Finset.univ P.nonneg Q.nonneg
  simpa only [P.total, Q.total, Real.sqrt_one, mul_one] using h

theorem hellingerSq_eq_affinity (P Q : FiniteLaw Ω) : P.hellingerSq Q = 2 - 2 * P.affinity Q := by
  have he (w : Ω) : (Real.sqrt (P.weight w) - Real.sqrt (Q.weight w)) ^ 2 =
      P.weight w + Q.weight w - 2 * (Real.sqrt (P.weight w) * Real.sqrt (Q.weight w)) := by
    nlinarith [Real.sq_sqrt (P.nonneg w), Real.sq_sqrt (Q.nonneg w)]
  simp only [hellingerSq, he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, P.total, Q.total, affinity]
  ring

theorem hellingerSq_nonneg (P Q : FiniteLaw Ω) : 0 ≤ P.hellingerSq Q :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem hellingerSq_le_two (P Q : FiniteLaw Ω) : P.hellingerSq Q ≤ 2 := by
  rw [hellingerSq_eq_affinity]
  linarith [affinity_nonneg P Q]

theorem sqrt_prod_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) : Real.sqrt (∏ i ∈ s, f i) = ∏ i ∈ s, Real.sqrt (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Real.sqrt_mul (hf i (Finset.mem_insert_self _ _)),
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)), Finset.prod_insert hi]

theorem affinity_independent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ξ : ι → Type*} [∀ i, Fintype (Ξ i)] (P Q : ∀ i, FiniteLaw (Ξ i)) :
    (independent P).affinity (independent Q) = ∏ i, (P i).affinity (Q i) := by
  unfold affinity
  simp only [independent]
  simp_rw [sqrt_prod_nonneg _ _ (fun i _ => (P i).nonneg _),
    sqrt_prod_nonneg _ _ (fun i _ => (Q i).nonneg _), ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i (w : Ξ i) => Real.sqrt ((P i).weight w) * Real.sqrt ((Q i).weight w))).symm

theorem hellingerSq_independent_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ξ : ι → Type*} [∀ i, Fintype (Ξ i)] (P Q : ∀ i, FiniteLaw (Ξ i)) :
    (independent P).hellingerSq (independent Q) ≤ ∑ i, (P i).hellingerSq (Q i) := by
  rw [hellingerSq_eq_affinity, affinity_independent]
  simp_rw [hellingerSq_eq_affinity]
  have h := PartB.one_sub_prod_le_sum (fun i => (P i).affinity (Q i))
    (fun i => affinity_nonneg _ _) (fun i => affinity_le_one _ _)
  have he : (∑ i, (2 - 2 * (P i).affinity (Q i))) = 2 * ∑ i, (1 - (P i).affinity (Q i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  linarith

theorem totalVariation_nonneg (P Q : FiniteLaw Ω) : 0 ≤ P.totalVariation Q := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

theorem totalVariation_le_one (P Q : FiniteLaw Ω) : P.totalVariation Q ≤ 1 := by
  have h : (∑ w, |P.weight w - Q.weight w|) ≤ 2 := by
    calc
      _ ≤ ∑ w, (P.weight w + Q.weight w) := Finset.sum_le_sum (fun w _ =>
        (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (P.nonneg w), abs_of_nonneg (Q.nonneg w)]))
      _ = _ := by rw [Finset.sum_add_distrib, P.total, Q.total]; norm_num
  unfold totalVariation
  linarith

theorem totalVariation_sq_le_hellingerSq (P Q : FiniteLaw Ω) :
    (P.totalVariation Q) ^ 2 ≤ P.hellingerSq Q := by
  let a := fun w => |Real.sqrt (P.weight w) - Real.sqrt (Q.weight w)|
  let b := fun w => Real.sqrt (P.weight w) + Real.sqrt (Q.weight w)
  have hab (w : Ω) : a w * b w = |P.weight w - Q.weight w| := by
    dsimp [a, b]
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg (P.weight w)) (Real.sqrt_nonneg (Q.weight w)))]
    rw [← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (P.nonneg w), Real.sq_sqrt (Q.nonneg w)]
  have ha : (∑ w, a w ^ 2) = P.hellingerSq Q := by simp only [a, sq_abs, hellingerSq]
  have hb : (∑ w, b w ^ 2) ≤ 4 := by
    have he (w : Ω) : b w ^ 2 = P.weight w + Q.weight w +
        2 * (Real.sqrt (P.weight w) * Real.sqrt (Q.weight w)) := by
      dsimp [b]
      nlinarith [Real.sq_sqrt (P.nonneg w), Real.sq_sqrt (Q.nonneg w)]
    simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum, P.total, Q.total]
    have h := affinity_le_one P Q
    unfold affinity at h
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  simp only [hab, ha] at hcs
  have hmul := mul_le_mul_of_nonneg_left hb (hellingerSq_nonneg P Q)
  dsimp [totalVariation]
  nlinarith

theorem totalVariation_le_sqrt_hellingerSq (P Q : FiniteLaw Ω) :
    P.totalVariation Q ≤ Real.sqrt (P.hellingerSq Q) :=
  Real.le_sqrt_of_sq_le (totalVariation_sq_le_hellingerSq P Q)

theorem overlap_eq_one_sub_totalVariation (P Q : FiniteLaw Ω) :
    (∑ w, min (P.weight w) (Q.weight w)) = 1 - P.totalVariation Q := by
  have he (w : Ω) : 2 * min (P.weight w) (Q.weight w) =
      P.weight w + Q.weight w - |P.weight w - Q.weight w| := by
    rcases le_total (P.weight w) (Q.weight w) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  have hsum := congrArg (fun f : Ω → ℝ => ∑ w, f w) (funext he)
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib, P.total, Q.total] at hsum
  unfold totalVariation
  linarith

/-- Absolute loss, with the sharper separation/2 constant. -/
theorem two_point_absolute_loss (P Q : FiniteLaw Ω) (est : Ω → ℝ) (θ₀ θ₁ : ℝ) (hθ : θ₀ ≤ θ₁) :
    (θ₁ - θ₀) / 2 * (1 - P.totalVariation Q) ≤
      max (P.expect (fun w => |est w - θ₁|)) (Q.expect (fun w => |est w - θ₀|)) := by
  have htri (w : Ω) : θ₁ - θ₀ ≤ |est w - θ₁| + |est w - θ₀| := by
    have h := abs_sub_le θ₁ (est w) θ₀
    rw [abs_of_nonneg (sub_nonneg.mpr hθ), abs_sub_comm θ₁ (est w)] at h
    exact h
  have hpoint (w : Ω) : min (P.weight w) (Q.weight w) * (θ₁ - θ₀) ≤
      P.weight w * |est w - θ₁| + Q.weight w * |est w - θ₀| := by
    calc
      _ ≤ min (P.weight w) (Q.weight w) * (|est w - θ₁| + |est w - θ₀|) :=
        mul_le_mul_of_nonneg_left (htri w) (le_min (P.nonneg w) (Q.nonneg w))
      _ ≤ _ := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (min_le_right _ _) (abs_nonneg _))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hpoint w)
  simp only [← Finset.sum_mul, Finset.sum_add_distrib, overlap_eq_one_sub_totalVariation] at hs
  change (1 - P.totalVariation Q) * (θ₁ - θ₀) ≤
    P.expect (fun w => |est w - θ₁|) + Q.expect (fun w => |est w - θ₀|) at hs
  have hmax₁ := le_max_left (P.expect (fun w => |est w - θ₁|)) (Q.expect (fun w => |est w - θ₀|))
  have hmax₀ := le_max_right (P.expect (fun w => |est w - θ₁|)) (Q.expect (fun w => |est w - θ₀|))
  nlinarith

end CausalLowerbound.FiniteLaw
