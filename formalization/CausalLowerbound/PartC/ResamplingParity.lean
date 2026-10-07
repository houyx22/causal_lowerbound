import CausalLowerbound.PartC.GhostSignResampling
import CausalLowerbound.PartC.SharedSignParity

/-! Conditional sign averaging preserves simultaneous parity of retained
variables and resampled coefficients. Products use one shared fresh sign
field, so this does not introduce independence between carrier blocks. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB
variable {J K I : Type*} [Fintype J] [DecidableEq J] [Fintype K] [Fintype I]

namespace Walsh

def resampleAverage (T : Finset J) (f : (J → Bool) → ℝ) (ζ : J → Bool) : ℝ :=
  independentSigns.expect (fun fresh => f (resample T ζ fresh))

theorem resample_flip (T : Finset J) (ζ fresh : J → Bool) :
    resample T (flip ζ) (flip fresh) = flip (resample T ζ fresh) := by
  funext j
  by_cases hj : j ∈ T <;> simp [resample, flip, hj]

theorem resampleAverage_congr_outside (T : Finset J) (f : (J → Bool) → ℝ)
    (ζ ζ' : J → Bool) (he : ∀ j ∉ T, ζ j = ζ' j) :
    resampleAverage T f ζ = resampleAverage T f ζ' := by
  apply FiniteLaw.expect_congr
  intro fresh
  congr 1
  funext j
  by_cases hj : j ∈ T <;> simp [resample, hj, he]

theorem resampleAverage_bound (T : Finset J) (f : (J → Bool) → ℝ)
    (M : ℝ) (hf : ∀ ζ, |f ζ| ≤ M) (ζ : J → Bool) :
    |resampleAverage T f ζ| ≤ M := FiniteLaw.abs_expect_le_bound _ _ _ (fun fresh => hf _)

theorem resampleAverage_simultaneous_parity (T : Finset J)
    (F : (J → Bool) → (J → Bool) → ℝ) (s : ℝ)
    (hF : ∀ ζ η, F (flip ζ) (flip η) = s * F ζ η) (ζ : J → Bool) :
    resampleAverage T (F (flip ζ)) (flip ζ) = s * resampleAverage T (F ζ) ζ := by
  unfold resampleAverage
  rw [← independentSigns_expect_flip (fun fresh => F (flip ζ) (resample T (flip ζ) fresh))]
  simp only [resample_flip, hF, FiniteLaw.expect_mul]

theorem resampleAverage_product_sub_bound (T : Finset J) (f : K → (J → Bool) → ℝ)
    (M : ℝ) (hM : 1 ≤ M) (hf : ∀ k ζ, |f k ζ| ≤ M)
    (C : K → J → ℝ)
    (hC : ∀ k j ζ ζ', (∀ i, i ≠ j → ζ i = ζ' i) → |f k ζ - f k ζ'| ≤ C k j)
    (ζ : J → Bool) :
    |(∏ k, f k ζ) - resampleAverage T (fun η => ∏ k, f k η) ζ| ≤
      M ^ Fintype.card K * ∑ k, ∑ j ∈ T, C k j := by
  have he := independentSigns.expect_sub (fun _ : J → Bool => ∏ k, f k ζ)
    (fun fresh => ∏ k, f k (resample T ζ fresh))
  rw [FiniteLaw.expect_const] at he
  change |(∏ k, f k ζ) - independentSigns.expect (fun fresh => ∏ k, f k (resample T ζ fresh))| ≤ _
  rw [← he]
  apply FiniteLaw.abs_expect_le_bound
  intro fresh
  exact (abs_prod_sub_prod_le_bounded Finset.univ _ _ M hM (fun k _ => hf k ζ)
    (fun k _ => hf k _)).trans
      (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun k _ => resample_function_bound (f k) (C k) (hC k) T ζ fresh))
        (pow_nonneg (by linarith) _))

end Walsh

theorem resampled_product_shift_bound (T : Finset J) (e : K → ℕ) (he : 0 < ∑ k, e k)
    (F : K → (J → Bool) → (J → Bool) → ℝ)
    (hparity : ∀ k ζ η, F k (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ e k * F k ζ η)
    (M : ℝ) (hM : 1 ≤ M) (hF : ∀ k ζ η, |F k ζ η| ≤ M)
    (C : K → J → ℝ) (hC0 : ∀ k j, 0 ≤ C k j)
    (hC : ∀ k ζ j η η', (∀ i, i ≠ j → η i = η' i) → |F k ζ η - F k ζ η'| ≤ C k j)
    (f : I → (J → Bool) → ℝ) (shift rough : ℝ)
    (hshift : 0 ≤ shift) (hrough : 0 ≤ rough) (hr1 : rough ≤ 1) (hsr : shift ≤ rough)
    (hf : ∀ i ζ, |f i ζ| ≤ rough) :
    |independentSigns.expect (fun ζ => shift ^ (∑ k, e k) *
      ((∏ k, F k ζ ζ) - Walsh.resampleAverage T (fun η => ∏ k, F k ζ η) ζ) *
        ∏ i, (1 + f i ζ))| ≤
      (M ^ Fintype.card K * ∑ k, ∑ j ∈ T, C k j) * (2 : ℝ) ^ Fintype.card I *
        ((Fintype.card I : ℝ) + 1) * (shift * rough) := by
  let P := fun ζ η => ∏ k, F k ζ η
  have hp ζ η : P (Walsh.flip ζ) (Walsh.flip η) = (-1) ^ (∑ k, e k) * P ζ η := by
    simp only [P, hparity, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have herror ζ : P (Walsh.flip ζ) (Walsh.flip ζ) -
      Walsh.resampleAverage T (P (Walsh.flip ζ)) (Walsh.flip ζ) =
        (-1) ^ (∑ k, e k) * (P ζ ζ - Walsh.resampleAverage T (P ζ) ζ) := by
    rw [hp, Walsh.resampleAverage_simultaneous_parity T P _ hp, mul_sub]
  exact parity_weighted_shift_bound (∑ k, e k) he
    (fun ζ => P ζ ζ - Walsh.resampleAverage T (P ζ) ζ) herror f
    (M ^ Fintype.card K * ∑ k, ∑ j ∈ T, C k j) shift rough
    (mul_nonneg (pow_nonneg (by linarith) _)
      (Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun j _ => hC0 k j))))
    hshift hrough hr1 hsr
    (fun ζ => Walsh.resampleAverage_product_sub_bound T (fun k => F k ζ) M hM
      (fun k η => hF k ζ η) C (fun k j η η' h => hC k ζ j η η' h) ζ) hf

end CausalLowerbound.PartC
