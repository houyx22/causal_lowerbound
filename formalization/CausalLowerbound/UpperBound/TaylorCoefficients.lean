import CausalLowerbound.UpperBound.TaylorCancellation
import CausalLowerbound.UpperBound.ObservedFeatures
import CausalLowerbound.UpperBound.AcceptanceProbability

/-! The Taylor coefficient vector for the actual reflected tensor features.
Coordinate words are grouped by their exponent vector. This gives an exact
representation, the target as its constant coordinate, and a coefficient
bound independent of the target and the bandwidth. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def taylorWordCoefficient (q : ℕ) (f : (d → ℝ) → ℝ) (x : d → ℝ)
    (L : (d → ℝ) →L[ℝ] (d → ℝ)) (k : Fin (q + 1)) (s : Fin k.val → d) : ℝ :=
  (k.val.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k.val f x (fun a => L (Pi.single (s a) 1))

def taylorTensorCoefficients (p q : ℕ) (hqp : q ≤ p) (f : (d → ℝ) → ℝ) (x : d → ℝ)
    (L : (d → ℝ) →L[ℝ] (d → ℝ)) (ν : TensorIndex d p) : ℝ :=
  ∑ k : Fin (q + 1), ∑ s : Fin k.val → d,
    if wordIndex p s ((Nat.lt_succ_iff.mp k.isLt).trans hqp) = ν then
      taylorWordCoefficient q f x L k s else 0

theorem taylorTensorCoefficients_eval (p q : ℕ) (hqp : q ≤ p)
    (f : (d → ℝ) → ℝ) (x u : d → ℝ) (L : (d → ℝ) →L[ℝ] (d → ℝ)) :
    tensorPolynomial p (taylorTensorCoefficients p q hqp f x L) u =
      frechetTaylor f q x (x + L u) := by
  unfold tensorPolynomial taylorTensorCoefficients
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hk (k : Fin (q + 1)) :
      (∑ ν : TensorIndex d p, ∑ s : Fin k.val → d,
        (if wordIndex p s ((Nat.lt_succ_iff.mp k.isLt).trans hqp) = ν then
          taylorWordCoefficient q f x L k s else 0) * tensorMonomial p ν u) =
        (k.val.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k.val f x (fun _ => L u) := by
    rw [Finset.sum_comm]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      tensorMonomial_wordIndex]
    have he := multilinear_coordinate_expansion
      ((iteratedFDeriv ℝ k.val f x).compContinuousLinearMap (fun _ => L)) u
    change iteratedFDeriv ℝ k.val f x (fun _ => L u) =
      ∑ s : Fin k.val → d, (∏ a, u (s a)) *
        iteratedFDeriv ℝ k.val f x (fun a => L (Pi.single (s a) 1)) at he
    rw [he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    unfold taylorWordCoefficient
    ring
  simp_rw [hk]
  simp only [frechetTaylor, add_sub_cancel_left]
  exact Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k f x (fun _ => L u)) (q + 1)

theorem tensorMonomial_zero (p : ℕ) (ν : TensorIndex d p) :
    tensorMonomial p ν 0 = if ν = 0 then 1 else 0 := by
  by_cases hν : ν = 0
  · simp [hν, tensorMonomial]
  · rw [if_neg hν]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hν
    have hi₀ : (ν i : ℕ) ≠ 0 := fun he => hi (Fin.ext he)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (zero_pow hi₀)

theorem tensorPolynomial_zero (p : ℕ) (θ : TensorIndex d p → ℝ) :
    tensorPolynomial p θ 0 = θ 0 := by
  simp [tensorPolynomial, tensorMonomial_zero]

theorem taylorTensorCoefficients_constant (p q : ℕ) (hqp : q ≤ p)
    (f : (d → ℝ) → ℝ) (x : d → ℝ) (L : (d → ℝ) →L[ℝ] (d → ℝ)) :
    taylorTensorCoefficients p q hqp f x L 0 = f x := by
  rw [← tensorPolynomial_zero p (taylorTensorCoefficients p q hqp f x L),
    taylorTensorCoefficients_eval, map_zero, add_zero, frechetTaylor_self]

theorem taylorWordCoefficient_bound (q : ℕ) (f : (d → ℝ) → ℝ) (x : d → ℝ)
    (L : (d → ℝ) →L[ℝ] (d → ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ k ≤ q, ‖iteratedFDeriv ℝ k f x‖ ≤ C)
    (hL : ∀ i, ‖L (Pi.single i 1)‖ ≤ 1) (k : Fin (q + 1)) (s : Fin k.val → d) :
    |taylorWordCoefficient q f x L k s| ≤ C := by
  have hA : |iteratedFDeriv ℝ k.val f x (fun a => L (Pi.single (s a) 1))| ≤ C := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ k.val f x‖ * ∏ a, ‖L (Pi.single (s a) 1)‖ := by
        simpa only [Real.norm_eq_abs] using
          (iteratedFDeriv ℝ k.val f x).le_opNorm (fun a => L (Pi.single (s a) 1))
      _ ≤ C * 1 := mul_le_mul (hf k (Nat.lt_succ_iff.mp k.isLt))
        (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun a _ => hL (s a)))
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hC
      _ = C := mul_one _
  have hfac : (1 : ℝ) ≤ k.val.factorial := by exact_mod_cast Nat.factorial_pos k.val
  have hinv : (k.val.factorial : ℝ)⁻¹ ≤ 1 := by simpa using inv_anti₀ zero_lt_one hfac
  rw [taylorWordCoefficient, abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg _)]
  exact (mul_le_mul hinv hA (abs_nonneg _) zero_le_one).trans_eq (one_mul C)

theorem taylorTensorCoefficients_bound (p q : ℕ) (hqp : q ≤ p)
    (f : (d → ℝ) → ℝ) (x : d → ℝ) (L : (d → ℝ) →L[ℝ] (d → ℝ))
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ k ≤ q, ‖iteratedFDeriv ℝ k f x‖ ≤ C)
    (hL : ∀ i, ‖L (Pi.single i 1)‖ ≤ 1) :
    ‖taylorTensorCoefficients p q hqp f x L‖ ≤
      C * ∑ k : Fin (q + 1), (Fintype.card d : ℝ) ^ k.val := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro ν
  rw [Real.norm_eq_abs, taylorTensorCoefficients]
  calc
    _ ≤ ∑ k : Fin (q + 1), ∑ s : Fin k.val → d,
        |if wordIndex p s ((Nat.lt_succ_iff.mp k.isLt).trans hqp) = ν then
          taylorWordCoefficient q f x L k s else 0| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ k : Fin (q + 1), ∑ _s : Fin k.val → d, C := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro s _
      split
      · exact taylorWordCoefficient_bound q f x L hC hf hL k s
      · simpa using hC
    _ = _ := by simp [Fintype.card_fun, Finset.mul_sum, mul_comm]

def stencilTaylorCoefficients (p q : ℕ) (hqp : q ≤ p) (f : (d → ℝ) → ℝ)
    (x₀ : d → ℝ) (h : ℝ) : TensorIndex d p → ℝ :=
  taylorTensorCoefficients p q hqp f x₀ (h • inwardReflectionL x₀)

theorem stencilTaylorCoefficients_constant (p q : ℕ) (hqp : q ≤ p) (f : (d → ℝ) → ℝ)
    (x₀ : d → ℝ) (h : ℝ) : stencilTaylorCoefficients p q hqp f x₀ h 0 = f x₀ :=
  taylorTensorCoefficients_constant p q hqp f x₀ _

theorem stencilTaylorCoefficients_bound (p q : ℕ) (hqp : q ≤ p) (f : (d → ℝ) → ℝ)
    (x₀ : d → ℝ) {h C : ℝ} (hh : 0 ≤ h) (hh1 : h ≤ 1) (hC : 0 ≤ C)
    (hf : ∀ k ≤ q, ‖iteratedFDeriv ℝ k f x₀‖ ≤ C) :
    ‖stencilTaylorCoefficients p q hqp f x₀ h‖ ≤
      C * ∑ k : Fin (q + 1), (Fintype.card d : ℝ) ^ k.val := by
  apply taylorTensorCoefficients_bound p q hqp f x₀ _ hC hf
  intro i
  rw [scaled_reflection_norm, abs_of_nonneg hh]
  apply mul_le_one₀ hh1 (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  by_cases hj : j = i <;> simp [Pi.single_apply, hj]

theorem stencilTaylorCoefficients_eval (p q : ℕ) (hqp : q ≤ p) (f : (d → ℝ) → ℝ)
    (x₀ : d → ℝ) {h : ℝ} (hh : h ≠ 0) (X : StencilRole d p → d → ℝ) (i : StencilRole d p) :
    (∑ ν, stencilTaylorCoefficients p q hqp f x₀ h ν * stencilFeature p x₀ h X i ν) =
      frechetTaylor f q x₀ (X i) := by
  change tensorPolynomial p (taylorTensorCoefficients p q hqp f x₀ (h • inwardReflectionL x₀))
    (normalizedDisplacement x₀ x₀ (X i) h) = _
  rw [taylorTensorCoefficients_eval]
  simp only [ContinuousLinearMap.smul_apply, inwardReflectionL_apply]
  rw [normalizedDisplacement_reconstruct x₀ x₀ (X i) h hh]

end CausalLowerbound.UpperBound
