import CausalLowerbound.PartB.IdealIncrementWiener

/-! Replace the exact finite-shell ceiling by the logarithmic factor in the
paper's inverse-square Wiener estimate. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace CausalLowerbound.PartB.ShellGeometry

open Wiener ConfigurationShells

def logShellConstant : ℝ := 3 + (Real.log 2)⁻¹

theorem logShellConstant_pos : 0 < logShellConstant := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold logShellConstant
  positivity

theorem levelBudget_log_bound (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ((levelBudget 2 t + 1 : ℕ) : ℝ) ≤ logShellConstant * (1 + Real.log (1 / t)) := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2t : 1 ≤ 2 / t := (le_div_iff₀ ht).mpr (by linarith)
  have h1t : 1 ≤ 1 / t := (le_div_iff₀ ht).mpr (by linarith)
  have hn := Real.log_nonneg h1t
  have hc := (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg h2t) hp.le)).le
  have he : Real.log (2 / t) / Real.log 2 = 1 + Real.log (1 / t) / Real.log 2 := by
    rw [Real.log_div (by norm_num) ht.ne', Real.log_div one_ne_zero ht.ne', Real.log_one]
    field_simp
    ring
  rw [he] at hc
  have hi : 0 ≤ (Real.log 2)⁻¹ := (inv_pos.mpr hp).le
  rw [Nat.cast_add, Nat.cast_one]
  unfold levelBudget
  rw [he]
  unfold logShellConstant
  rw [div_eq_mul_inv] at hc ⊢
  nlinarith

variable {Ω K V E d : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype d] [DecidableEq d]

/-- The paper's strong inverse-square estimate for an actual coordinate
monomial of the ideal increment. The number of graph edges is the logarithmic
exponent; for the complete graph this is Q choose 2. -/
theorem ideal_increment_log_wiener_bound (a b : E → V) (μ : FiniteLaw Ω) (U : Ω → K → ℝ)
    (ν : K → d × Bool →₀ ℕ) :
    ∃ C ≥ 0, ∀ amp ≥ 0, ∀ t ∈ Set.Ioc 0 1, ∃ A : Fourier (V × d),
      (∀ u, toContinuous A (torusProjection u) = (idealIncrement a b μ U ν amp t u : ℝ)) ∧
      ‖A‖ ≤ C * (1 + Real.log (1 / t)) ^ Fintype.card E *
        ∑ j ∈ Finset.Icc 2 (Fintype.card K), (amp / t) ^ j := by
  obtain ⟨C0, hC0, hb⟩ := ideal_increment_wiener_bound a b μ U ν
  refine ⟨C0 * logShellConstant ^ Fintype.card E, mul_nonneg hC0 (pow_nonneg logShellConstant_pos.le _), ?_⟩
  intro amp hamp t ht
  obtain ⟨A, hA, hn⟩ := hb amp hamp t ht.1
  refine ⟨A, hA, hn.trans ?_⟩
  have hs : 0 ≤ ∑ j ∈ Finset.Icc 2 (Fintype.card K), (amp / t) ^ j :=
    Finset.sum_nonneg (fun _ _ => pow_nonneg (div_nonneg hamp ht.1.le) _)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ ((levelBudget 2 t + 1 : ℕ) : ℝ))
    (levelBudget_log_bound t ht.1 ht.2) (Fintype.card E)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC0) hs
  simpa only [mul_pow, mul_assoc] using hh

end CausalLowerbound.PartB.ShellGeometry
