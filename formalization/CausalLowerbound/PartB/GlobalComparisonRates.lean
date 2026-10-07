import CausalLowerbound.PartB.GlobalGhostRates
import CausalLowerbound.PartB.HighComponentRates

/-! The complete numerical upper bound for the actual joint total variation
tends to zero, uniformly over the sequence of constructed priors. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Nonempty d]

theorem paper_globalComparison_bound_tendsto (A γ ε θ C : ℝ)
    (hA : 0 < A) (hγ : 0 < γ) (hε : 0 < ε) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hreg : A * (2 + (Fintype.card d : ℝ) / γ) < Fintype.card d)
    (hεsmall : ε < γ / Fintype.card d - rateExponent A (Fintype.card d) γ)
    (B : ℝ) (H : ℕ → DiscreteLaw ℕ) (kernel : ℕ → ℕ → FiniteLaw Ω) (x₀ : d → ℝ) :
    let D := (Fintype.card d : ℝ)
    let Q := matchingOrder D γ (rateExponent A D γ + ε) (D * ε / (2 * A))
    let r : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-carrierExponent A D ε)
    let h : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-((rateExponent A D γ + ε) / γ))
    let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-(rateExponent A D γ + ε))
    let t : ℕ → ℝ := fun n => logarithmicThreshold (jitterExponent A D γ ε) B ((n : ℝ) + 1)
    let μ := fun n => mixedDesignExperiment Q (activeBlocks (r n) (h n)) θ hθ hθ1 (H n) (kernel n) x₀ (r n) (n + 1)
    Tendsto (fun n => (μ n).real (largeClusterEvent (n + 1) Q x₀ (r n) (h n)) +
      Real.sqrt (C * (δ n) ^ 2 * ∫ x : Fin (n + 1) → d → ℝ,
        globalGhostCost (H n) Q θ (t n) x₀ (r n) (h n) x ∂μ n)) atTop (𝓝 0) := by
  let D := (Fintype.card d : ℝ)
  let Q := matchingOrder D γ (rateExponent A D γ + ε) (D * ε / (2 * A))
  obtain ⟨s, hs, hsd, hcost⟩ := paper_globalGhostCost_scaled_tendsto (d := d) (Ω := Ω)
    A γ ε θ hA hγ hε hθ hθ1 hreg hεsmall
  have hQ : Q - 1 + 1 = Q := Nat.sub_add_cancel (by
    have hh := matchingOrder_ge_two D γ (rateExponent A D γ + ε) (D * ε / (2 * A))
    change 1 ≤ Q
    omega)
  have hc := hcost (Q - 1) B H kernel x₀
  dsimp only at hc
  rw [hQ] at hc
  have hC := hc.const_mul C
  rw [mul_zero] at hC
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hC
  simp only [mul_zero, Real.sqrt_zero] at hsqrt
  have hb := paper_largeCluster_probability_tendsto A γ ε θ hA hγ hε hθ hθ1 H kernel x₀
  have ht := hb.add hsqrt
  simpa only [add_zero, mul_assoc] using ht

end CausalLowerbound.PartB.ShellGeometry
