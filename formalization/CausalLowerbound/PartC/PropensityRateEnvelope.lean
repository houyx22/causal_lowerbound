import CausalLowerbound.PartC.PropensityCostAlgebra

/-! A deterministic vanishing upper bound for the total variation of
every actual propensity carrier chosen at the mixed-case scales. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology
namespace CausalLowerbound.PartC

def propensityRateEnvelope (D : ℕ) (CF CC B CG CP A γ s ε a v gap : ℝ) (n : ℕ) : ℝ :=
  CP * highComponentMass A D γ s ε ((n : ℝ) + 1) +
  Real.sqrt (a ^ 2 * ((CF * (5 ^ D * B * 10 ^ D) +
    CC * (B * (2 * D * (2 : ℝ) ^ (D - 1) * 7 ^ D))) * singletonMass A D γ s ε ((n : ℝ) + 1) +
    (CF * CG) * relaxedGhostMass A D γ s ε v gap ((n : ℝ) + 1) +
    (CC * (B ^ 2 * 10 ^ D * 4 ^ D)) * collisionMass A D γ s ε ((n : ℝ) + 1)))

theorem propensityRateEnvelope_tendsto (D : ℕ) (CF CC B CG CP A γ s ε a : ℝ)
    (hA : 0 < A) (hD : 0 < (D : ℝ)) (hγ : 0 < γ) (hs : 0 < s) (hε : 0 < ε)
    (budget : PowerBudget D (jitterExponent A D γ s ε) (rateMargin D γ s ε)) :
    Tendsto (propensityRateEnvelope D CF CC B CG CP A γ s ε a budget.volumeExponent budget.taperGap)
      atTop (𝓝 0) := by
  have hl := global_rate_ledgers A D γ s ε 0 hA hD hγ hs hε
  simp only [Real.rpow_zero, mul_one] at hl
  have hg := relaxedGhostMass_tendsto_of_budget A D γ s ε hA hD hγ hs hε budget
  have he := (hl.2.2.const_mul CP).add
    (((((hl.1.const_mul (CF * (5 ^ D * B * 10 ^ D) +
      CC * (B * (2 * D * (2 : ℝ) ^ (D - 1) * 7 ^ D)))).add (hg.const_mul (CF * CG))).add
      (hl.2.1.const_mul (CC * (B ^ 2 * 10 ^ D * 4 ^ D)))).const_mul (a ^ 2)).sqrt)
  simpa only [mul_zero, add_zero, Real.sqrt_zero, propensityRateEnvelope] using he

theorem highComponentMass_at_scales (D : ℕ) (A γ s ε : ℝ) (n : ℕ) :
    let Q := matchingOrder A D γ s ε
    ((n : ℝ) + 1) ^ (Q + 1) * coarseScale A D γ s ε n ^ D *
      carrierScale A D ε n ^ (Q * D) = highComponentMass A D γ s ε ((n : ℝ) + 1) := by
  dsimp only [highComponentMass, coarseScale, carrierScale]
  rw [show (D : ℝ) * (matchingOrder A D γ s ε : ℝ) = ((matchingOrder A D γ s ε * D : ℕ) : ℝ) by
    push_cast; ring]
  simp only [Real.rpow_natCast]

theorem propensity_numeric_bound_le_envelope (D : ℕ) (CF CC B CG CP A γ s ε a v gap : ℝ)
    (hA : 0 < A) (hD : 0 < (D : ℝ)) (hγ : 0 < γ) (hs : 0 < s)
    (hreg : A * (2 + (D : ℝ) / γ) < D) (hε : 0 < ε)
    (hεsmall : ε < γ / D - rateExponent A D γ s)
    (hCF : 0 ≤ CF) (hCC : 0 ≤ CC) (hB : 0 ≤ B)
    (n : ℕ) (w : ℝ) (hw : w ≤ jitterScale A D γ s ε n ^ D) :
    let Q := matchingOrder A D γ s ε
    CP * (((n : ℝ) + 1) ^ (Q + 1) * coarseScale A D γ s ε n ^ D *
      carrierScale A D ε n ^ (Q * D)) +
    Real.sqrt (propensityScalarCost D CF CC B CG (roughScale A D γ s ε n)
      (carrierScale A D ε n) (coarseScale A D γ s ε n) ((n : ℝ) + 1)
      (a * signalScale A D γ s ε n) ((jitterScale A D γ s ε n ^ (1 - gap)) ^ v) w) ≤
      propensityRateEnvelope D CF CC B CG CP A γ s ε a v gap n := by
  dsimp only
  rw [highComponentMass_at_scales]
  exact add_le_add_left (Real.sqrt_le_sqrt (propensityScalarCost_le_rates D A γ s ε a CF CC B CG v gap
    hA hD hγ hs hreg hε hεsmall hCF hCC hB n w hw)) _

end CausalLowerbound.PartC
