import CausalLowerbound.PartB.GlobalGhostCost
import CausalLowerbound.PartB.SubcriticalRates

/-! The actual integrated leakage majorant, multiplied by the square of
the target separation, tends to zero at the paper's scales. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped Topology BigOperators
namespace CausalLowerbound.PartB.ShellGeometry
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω] [Nonempty d]

theorem carrier_occupancy_le_one (A D ε x : ℝ) (hA : 0 < A) (hD : 0 < D)
    (hε : 0 ≤ ε) (hx : 1 ≤ x) : x * (x ^ (-carrierExponent A D ε)) ^ D ≤ 1 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  rw [← Real.rpow_mul hx0.le]
  conv_lhs => arg 1; rw [← Real.rpow_one x]
  rw [← Real.rpow_add hx0]
  apply Real.rpow_le_one_of_one_le_of_nonpos hx
  have he : 1 + -carrierExponent A D ε * D = -D * ε / (2 * A) := by
    unfold carrierExponent
    field_simp
    ring
  rw [he]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hD.le) hε) (by positivity)

theorem scaled_ghost_mass_eq (A D γ ε B s x : ℝ) (hx : 1 ≤ x) :
    (x ^ (-(rateExponent A D γ + ε))) ^ (2 : ℕ) *
        (x * (x ^ (-((rateExponent A D γ + ε) / γ))) ^ D *
          logarithmicThreshold (jitterExponent A D γ ε) B x ^ s) =
      singletonMass A D γ ε x * x ^ ((D - s) * jitterExponent A D γ ε) * logScale x ^ (B * s) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  unfold logarithmicThreshold polynomialAmplitude
  rw [Real.mul_rpow (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg (logScale_pos hx).le _),
    ← Real.rpow_mul (logScale_pos hx).le,
    jitter_power_loss x (jitterExponent A D γ ε) D s hx0]
  unfold singletonMass
  ring

theorem paper_globalGhostCost_scaled_tendsto (A γ ε θ : ℝ)
    (hA : 0 < A) (hγ : 0 < γ) (hε : 0 < ε) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hreg : A * (2 + (Fintype.card d : ℝ) / γ) < Fintype.card d)
    (hεsmall : ε < γ / Fintype.card d - rateExponent A (Fintype.card d) γ) :
    ∃ s : ℝ, 0 < s ∧ s < (Fintype.card d : ℝ) ∧
      ∀ (q : ℕ) (B : ℝ) (H : ℕ → DiscreteLaw ℕ) (kernel : ℕ → ℕ → FiniteLaw Ω) (x₀ : d → ℝ),
        let D := (Fintype.card d : ℝ)
        let r : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-carrierExponent A D ε)
        let h : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-((rateExponent A D γ + ε) / γ))
        let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-(rateExponent A D γ + ε))
        let t : ℕ → ℝ := fun n => logarithmicThreshold (jitterExponent A D γ ε) B ((n : ℝ) + 1)
        Tendsto (fun n => (δ n) ^ 2 *
          ∫ x : Fin (n + 1) → d → ℝ, globalGhostCost (H n) (q + 1) θ (t n) x₀ (r n) (h n) x
            ∂mixedDesignExperiment (q + 1) (activeBlocks (r n) (h n)) θ hθ hθ1 (H n) (kernel n) x₀ (r n) (n + 1))
          atTop (𝓝 0) := by
  let D := (Fintype.card d : ℝ)
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (Fintype.card_pos (α := d))
  obtain ⟨s, hs, hsd, hrate⟩ := exists_subcritical_rate_control A D γ ε hA hD hγ hreg hε hεsmall
  refine ⟨s, hs, hsd, ?_⟩
  intro q B H kernel x₀
  let r : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-carrierExponent A D ε)
  let h : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-((rateExponent A D γ + ε) / γ))
  let δ : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-(rateExponent A D γ + ε))
  let t : ℕ → ℝ := fun n => logarithmicThreshold (jitterExponent A D γ ε) B ((n : ℝ) + 1)
  have hx (n : ℕ) : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hr (n : ℕ) : 0 < r n := Real.rpow_pos_of_pos (by positivity) _
  have ht (n : ℕ) : 0 < t n := logarithmicThreshold_pos _ _ (hx n)
  have hrh (n : ℕ) : r n ≤ h n := Real.rpow_le_rpow_of_exponent_le (hx n)
    (neg_le_neg ((concrete_scale_exponents A D γ ε hA hD hγ hreg hε hεsmall).2.1.le))
  have hnr (n : ℕ) : ((n : ℝ) + 1) * (r n) ^ Fintype.card d ≤ 1 := by
    simpa only [D, Real.rpow_natCast] using carrier_occupancy_le_one A D ε ((n : ℝ) + 1) hA hD hε.le (hx n)
  have hmass : Tendsto (fun n : ℕ => (δ n) ^ 2 *
      (((n : ℝ) + 1) * (h n) ^ Fintype.card d * (t n) ^ s)) atTop (𝓝 0) := by
    apply (hrate (B * s)).1.congr'
    filter_upwards [] with n
    have he := scaled_ghost_mass_eq A D γ ε B s ((n : ℝ) + 1) (hx n)
    simpa only [D, Real.rpow_natCast] using he.symm
  have hupper := hmass.const_mul (globalGhostConstant d q θ s)
  rw [mul_zero] at hupper
  apply squeeze_zero _ _ hupper
  · intro n
    exact mul_nonneg (sq_nonneg _) (integral_nonneg
      (fun x => globalGhostCost_nonneg (H n) (q + 1) θ (t n) hθ hθ1 x₀ (r n) (h n) (hr n) x))
  · intro n
    have hb := globalGhostCost_integral_le (H n) q θ hθ hθ1 s hs hsd (t n) (ht n)
      (kernel n) x₀ (r n) (h n) (hr n) (hrh n) (n + 1) (by simpa using hnr n)
    have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg (δ n))
    simp only [Nat.cast_add, Nat.cast_one] at hh
    convert hh using 1 <;> ring

end CausalLowerbound.PartB.ShellGeometry
