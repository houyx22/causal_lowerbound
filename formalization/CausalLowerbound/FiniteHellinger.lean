import CausalLowerbound.FiniteMixture
import Mathlib.Data.Real.Sqrt

/-! Finite squared Hellinger distance (without the optional factor 1/2). -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound

open scoped BigOperators

/-- A one-sided positive lower bound is enough; the other cell may have zero mass. -/
theorem sqrt_sub_sq_le (p q lower : ℝ) (hlower : 0 < lower) (hp : lower ≤ p) (hq : 0 ≤ q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ (p - q) ^ 2 / lower := by
  have hp0 : 0 ≤ p := hlower.le.trans hp
  have hp_sq := Real.sq_sqrt hp0
  have hq_sq := Real.sq_sqrt hq
  have hprod := mul_nonneg (Real.sqrt_nonneg p) (Real.sqrt_nonneg q)
  have hsum : lower ≤ (Real.sqrt p + Real.sqrt q) ^ 2 := by nlinarith
  have hid : (Real.sqrt p - Real.sqrt q) ^ 2 *
      (Real.sqrt p + Real.sqrt q) ^ 2 = (p - q) ^ 2 := by
    calc
      _ = (Real.sqrt p ^ 2 - Real.sqrt q ^ 2) ^ 2 := by ring
      _ = _ := by rw [hp_sq, hq_sq]
  apply (le_div_iff₀ hlower).mpr
  calc
    _ ≤ (Real.sqrt p - Real.sqrt q) ^ 2 * (Real.sqrt p + Real.sqrt q) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := hid

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

def hellingerSq (μ ν : FiniteLaw Ω) : ℝ :=
  ∑ ω, (Real.sqrt (μ.weight ω) - Real.sqrt (ν.weight ω)) ^ 2

theorem hellingerSq_le_of_sq_error (μ ν : FiniteLaw Ω) (lower B : ℝ)
    (hlower : 0 < lower) (hμ : ∀ ω, lower ≤ μ.weight ω)
    (herr : ∀ ω, (μ.weight ω - ν.weight ω) ^ 2 ≤ B) :
    μ.hellingerSq ν ≤ (Fintype.card Ω : ℝ) * B / lower := by
  calc
    _ ≤ ∑ ω : Ω, B / lower := Finset.sum_le_sum (fun ω _ =>
      (sqrt_sub_sq_le _ _ lower hlower (hμ ω) (ν.nonneg ω)).trans
        (div_le_div_of_nonneg_right (herr ω) hlower.le))
    _ = _ := by simp [mul_div_assoc]

end FiniteLaw
end CausalLowerbound
