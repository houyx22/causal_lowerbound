import CausalLowerbound.PartC.SignCarrierMoments
import CausalLowerbound.PartC.WalshCoefficients

/-! Concrete Walsh-valued moment coefficients give positive conditional laws
on the fixed moment-grid support, with one normalization for all sign vectors. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC

open PartB

variable {J I Γ : Type*} [DecidableEq J] [Fintype I] [DecidableEq I] [Fintype Γ]

theorem exists_walsh_carrier_kernel (feature : I → Γ → ℝ) (μ : FiniteLaw Γ)
    (hμ : ∀ x, 0 < μ.weight x) (R : MomentRightInverse feature) :
    ∃ K : ℝ, 0 < K ∧ ∀ a : ℕ → I → Walsh.Coefficients J,
      ∃ kernel : (J → Bool) → ℕ → FiniteLaw Γ,
        (∀ ζ, kernel ζ 0 = μ) ∧
        (∀ ζ n x, 0 < (kernel ζ n).weight x) ∧
        ∀ ζ m i, (kernel ζ (m + 1)).expect (feature i) = μ.expect (feature i) +
          Walsh.evaluateCoordinate ζ i (normalizedCoefficient K (a m)) := by
  classical
  obtain ⟨radius, hpos, realize⟩ := exists_positive_moment_radius feature R μ hμ
  refine ⟨radius⁻¹, inv_pos.mpr hpos, ?_⟩
  intro a
  obtain ⟨kernel, hzero, hpositive, hmoment⟩ :=
    exists_sign_carrier_kernel feature μ radius realize Walsh.evaluateCoordinate
      Walsh.evaluateCoordinate_bound a radius⁻¹ (inv_pos.mpr hpos) (by simp)
  refine ⟨kernel, hzero, ?_, hmoment⟩
  intro ζ n x
  cases n with
  | zero => simpa only [hzero ζ] using hμ x
  | succ m => exact hpositive ζ m x

end CausalLowerbound.PartC
