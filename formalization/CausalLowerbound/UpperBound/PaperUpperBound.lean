import CausalLowerbound.UpperBound.UniformPolynomialRisk
import CausalLowerbound.UpperBound.RateChoice
import CausalLowerbound.UpperBound.PaperSmoothness

/-! The paper's uniform upper bound for arbitrary positive smoothness,
bounded measurable design density and real outcomes with a conditional
second moment.  The estimator, risk constant and sample-size threshold are
chosen before the model and target.  No bandwidth, bias, matrix, moment or
measurability assertion remains as a premise. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d] [Nonempty d]

theorem paper_upper_bound
    {α β γ ε lower upper M₂ Lπ L₀ Lτ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (hε : 0 < ε) (hε1 : ε < 1) (hlower : 0 < lower) (hupper : 0 ≤ upper) (hM : 0 ≤ M₂)
    {U : Set (d → ℝ)} (hU : IsOpen U) (hcube : Icc (0 : d → ℝ) 1 ⊆ U)
    (hLπ : 0 ≤ Lπ) (hL₀ : 0 ≤ L₀) (hLτ : 0 ≤ Lτ) :
    ∃ est : (d → ℝ) → (n : ℕ) → (Fin n → (d → ℝ) × (Bool × ℝ)) → ℝ,
      (∀ x₀ n, Measurable (est x₀ n)) ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ,
        ∀ n, N ≤ n → ∀ M : RealOutcomeModel d ε lower upper M₂,
          M.PaperRegularity U α β γ Lπ L₀ Lτ →
          ∀ x₀ : d → ℝ, (∀ i, 0 ≤ x₀ i ∧ x₀ i ≤ 1) →
            (∫ z, |est x₀ n z - M.effect x₀| ∂M.sampleLaw (Fin n)) ≤
              C * (n : ℝ) ^ (-upperRateExponent α β (Fintype.card d) γ) := by
  let p := max (smoothnessOrder α) (max (smoothnessOrder β) (smoothnessOrder γ))
  have hαp : smoothnessOrder α ≤ p := le_max_left _ _
  have hβp : smoothnessOrder β ≤ p := (le_max_left _ _).trans (le_max_right _ _)
  have hγp : smoothnessOrder γ ≤ p := (le_max_right _ _).trans (le_max_right _ _)
  let T := standardStencilTemplate d p
  have hD : (0 : ℝ) < Fintype.card d := by exact_mod_cast (Fintype.card_pos (α := d))
  obtain ⟨a, b, ha, hac, hcb, htarget, hnuisance, hordinary, hpair⟩ :=
    exists_upper_bandwidth_exponents hα hβ hD hγ
  have he := exists_uniform_polynomial_upper_bound p (smoothnessOrder α) (smoothnessOrder β) (smoothnessOrder γ)
    hαp hβp hγp T hε hε1 hlower hupper hM hU hcube hLπ hL₀ hLτ
    (smoothnessFraction_pos hα).le (smoothnessFraction_pos hβ).le (smoothnessFraction_pos hγ).le
    (by simpa only [smoothness_reconstruct] using hα) a b (upperRateExponent α β (Fintype.card d) γ)
    ha hac hcb (by simpa only [smoothness_reconstruct] using htarget)
    (by simpa only [smoothness_reconstruct] using hnuisance) hordinary hpair
  obtain ⟨est, hest, C, hC, N, hN⟩ := he
  refine ⟨est, hest, C, hC, max N 1, ?_⟩
  intro n hn M hreg x₀ hx
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_one.trans_le hn1)
  have hρ := upperRateExponent_pos hα hβ hD hγ
  have hpow := Real.rpow_le_rpow_of_nonpos hnpos (le_add_of_nonneg_right zero_le_one) (neg_nonpos.mpr hρ.le)
  exact (hN n hnN M hreg x₀ hx).trans (mul_le_mul_of_nonneg_left hpow hC.le)

end CausalLowerbound.UpperBound
