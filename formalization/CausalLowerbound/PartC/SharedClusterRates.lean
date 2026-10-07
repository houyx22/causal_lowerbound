import CausalLowerbound.PartC.SharedClusterProbability
import CausalLowerbound.PartC.RateLedgers

/-! The actual large-component exception vanishes at the mixed-case
scales. Label and sign index sets may vary with the sample size. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology

namespace CausalLowerbound.PartC
open PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Nonempty d] [Fintype Ω]
  {K J : ℕ → Type*} [∀ n, Fintype (K n)] [∀ n, DecidableEq (K n)]
  [∀ n, Fintype (J n)] [∀ n, DecidableEq (J n)]

theorem paper_sharedLargeCluster_probability_tendsto (A γ s ε θ : ℝ)
    (hA : 0 < A) (hγ : 0 < γ) (hs : 0 < s) (hε : 0 < ε) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (F : ∀ n, ((K n → ℕ) × (J n → Bool)) → CarrierProfile d θ)
    (H : ∀ n, K n → DiscreteLaw ℕ)
    (kernel : ∀ n, K n → (J n → Bool) → ℕ → FiniteLaw Ω)
    (S : ℕ → Finset (d → ℤ)) (x₀ : d → ℝ) :
    let D := (Fintype.card d : ℝ)
    let Q := matchingOrder A D γ s ε
    let r : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-carrierExponent A D ε)
    let h : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-((rateExponent A D γ s + ε) / γ))
    Tendsto (fun n => (mixedCarrierDesign (F n) hθ hθ1 (S n) x₀ (r n) (H n) (kernel n) (n + 1)).real
      (sharedLargeClusterEvent (n + 1) Q x₀ (r n) (h n))) atTop (𝓝 0) := by
  let D := (Fintype.card d : ℝ)
  let Q := matchingOrder A D γ s ε
  let r : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-carrierExponent A D ε)
  let h : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-((rateExponent A D γ s + ε) / γ))
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (Fintype.card_pos (α := d))
  have ht := (global_rate_ledgers A D γ s ε 0 hA hD hγ hs hε).2.2
  simp only [Real.rpow_zero, mul_one] at ht
  have htC := ht.const_mul (sharedClusterProbabilityConstant d Q θ)
  rw [mul_zero] at htC
  have he (n : ℕ) :
      ((n : ℝ) + 1) ^ (Q + 1) * (h n) ^ Fintype.card d * (r n) ^ (Q * Fintype.card d) =
        highComponentMass A D γ s ε ((n : ℝ) + 1) := by
    dsimp only [highComponentMass, h, r]
    change _ = ((n : ℝ) + 1) ^ (Q + 1) *
      (((n : ℝ) + 1) ^ (-((rateExponent A D γ s + ε) / γ))) ^ D *
      (((n : ℝ) + 1) ^ (-carrierExponent A D ε)) ^ (D * Q)
    rw [show D * (Q : ℝ) = ((Q * Fintype.card d : ℕ) : ℝ) by dsimp [D]; push_cast; ring]
    simp only [D, Real.rpow_natCast]
  apply squeeze_zero (fun n => measureReal_nonneg) _ htC
  intro n
  have hb := sharedLargeClusterEvent_real_probability_le (F n) hθ hθ1 (S n) x₀ (r n) (h n)
    (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _) (H n) (kernel n) (n + 1) Q
  simp only [Nat.cast_add, Nat.cast_one] at hb
  rwa [he] at hb

end CausalLowerbound.PartC
