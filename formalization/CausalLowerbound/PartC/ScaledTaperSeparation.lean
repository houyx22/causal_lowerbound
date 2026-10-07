import CausalLowerbound.PartC.PhysicalTaperSeparation
import CausalLowerbound.PartC.NormalizedCarrierScales

/-! The relaxed taper is eventually wider than the rough-packet scale
by every fixed geometric constant. This discharges the separation
condition uniformly over carrier locations and carrier radii. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry ConfigurationShells
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [LinearOrder V]

theorem eventually_carrierTaper_dominates (C p gap : ℝ) (hp : 0 < p) (hgap : 0 < gap) :
    ∀ᶠ n : ℕ in atTop, C * ((n : ℝ) + 1) ^ (-p) < carrierTaper gap (((n : ℝ) + 1) ^ (-p)) := by
  have hlim := normalizedCarrierRatio_tendsto C p gap 0 hp hgap
  have he := hlim (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [he] with n hn
  have ht : 0 < ((n : ℝ) + 1) ^ (-p) := by positivity
  simp only [carrierDegreeWeight, neg_zero, Real.rpow_zero, mul_one] at hn
  have hh := (div_lt_one (carrierTaper_pos gap _ ht)).mp hn
  simpa only [mul_comm] using hh

theorem eventually_physical_taper_separation (p gap : ℝ) (hp : 0 < p) (hgap : 0 < gap) :
    ∀ᶠ n : ℕ in atTop, ∀ (x₀ : d → ℝ) (r : ℝ), 0 < r → ∀ (k : d → ℤ) (u : V × d → ℝ),
      graphTaper edgeLeft edgeRight taperCutoff (carrierTaper gap (((n : ℝ) + 1) ^ (-p)))
        (graphDistance edgeLeft edgeRight u) ≠ 0 →
      ∀ i j, i ≠ j → 2 * (((n : ℝ) + 1) ^ (-p) * r) <
        ‖roughChartPoint x₀ r k (configurationSite u i) - roughChartPoint x₀ r k (configurationSite u j)‖ := by
  filter_upwards [eventually_carrierTaper_dominates (physicalChartDistanceConstant d) p gap hp hgap] with n hn
  intro x₀ r hr k u hχ
  have ht : 0 < ((n : ℝ) + 1) ^ (-p) := by positivity
  apply taper_nonzero_physical_separation x₀ _ r hr k u _ (carrierTaper_pos gap _ ht) _ hχ
  have hm := mul_lt_mul_of_pos_left hn hr
  have hτ := carrierTaper_pos gap _ ht
  nlinarith [mul_pos hr hτ]

end CausalLowerbound.PartC
