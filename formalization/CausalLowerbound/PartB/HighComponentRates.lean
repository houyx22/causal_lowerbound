import CausalLowerbound.PartB.HighComponentProbability
import CausalLowerbound.PartB.RateLedgers

/-! The large-component probability vanishes for the paper's actual
polynomial scales, uniformly over the constructed priors and kernels. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
namespace CausalLowerbound.PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Nonempty d]

theorem paper_largeCluster_probability_tendsto (A γ ε θ : ℝ)
    (hA : 0 < A) (hγ : 0 < γ) (hε : 0 < ε) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (H : ℕ → DiscreteLaw ℕ) (kernel : ℕ → ℕ → FiniteLaw Ω) (x₀ : d → ℝ) :
    let D := (Fintype.card d : ℝ)
    let Q := matchingOrder D γ (rateExponent A D γ + ε) (D * ε / (2 * A))
    let r : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-carrierExponent A D ε)
    let h : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-((rateExponent A D γ + ε) / γ))
    Tendsto (fun n =>
      (mixedDesignExperiment Q (activeBlocks (r n) (h n)) θ hθ hθ1 (H n) (kernel n) x₀ (r n) (n + 1)).real
        (largeClusterEvent (n + 1) Q x₀ (r n) (h n))) atTop (𝓝 0) := by
  let D := (Fintype.card d : ℝ)
  let Q := matchingOrder D γ (rateExponent A D γ + ε) (D * ε / (2 * A))
  let r : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-carrierExponent A D ε)
  let h : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-((rateExponent A D γ + ε) / γ))
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (Fintype.card_pos (α := d))
  have ht := (global_rate_ledgers A D γ ε 0 hA hD hγ hε).2.2
  simp only [Real.rpow_zero, mul_one] at ht
  have htC := ht.const_mul (clusterProbabilityConstant d Q θ)
  rw [mul_zero] at htC
  have he (n : ℕ) :
      ((n : ℝ) + 1) ^ (Q + 1) * (h n) ^ Fintype.card d * (r n) ^ (Q * Fintype.card d) =
        highComponentMass A D γ ε ((n : ℝ) + 1) := by
    dsimp only [highComponentMass, h, r]
    change _ = ((n : ℝ) + 1) ^ (Q + 1) *
      (((n : ℝ) + 1) ^ (-((rateExponent A D γ + ε) / γ))) ^ D *
      (((n : ℝ) + 1) ^ (-carrierExponent A D ε)) ^ (D * Q)
    rw [show D * (Q : ℝ) = ((Q * Fintype.card d : ℕ) : ℝ) by dsimp [D]; push_cast; ring]
    simp only [D, Real.rpow_natCast]
  apply squeeze_zero (fun n => measureReal_nonneg) _ htC
  intro n
  have hb := largeClusterEvent_real_probability_le (n + 1) Q (activeBlocks (r n) (h n))
    θ hθ hθ1 (H n) (kernel n) x₀ (r n) (h n)
    (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  simp only [Nat.cast_add, Nat.cast_one] at hb
  rwa [he] at hb

end CausalLowerbound.PartB.ShellGeometry
