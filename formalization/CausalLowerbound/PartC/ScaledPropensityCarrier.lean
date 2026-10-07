import CausalLowerbound.PartC.PaperPropensityCarrier
import CausalLowerbound.PartC.NormalizedAssignment

/-! A physical carrier along the actual polynomial jitter scales. All
norm, positivity, moment realization, and fixed point smallness conditions
are discharged, uniformly over the physical block and the coarse scales. -/

noncomputable section
set_option autoImplicit false
open Filter
open scoped BigOperators Topology Classical

namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry Wiener ConfigurationShells Representative
attribute [local instance] finOrderedDecEq finOrderedDecLt
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem jitterPower_tendsto (p α : ℝ) (hp : 0 < p) (hα : 0 < α) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ (-p)) ^ α) atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-(p * α))) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one, Real.rpow_zero, mul_one] using
      polynomial_log_tendsto (p * α) 0 (mul_pos hp hα)
  apply hh.congr'
  filter_upwards [] with n
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  congr 1
  ring

set_option maxHeartbeats 800000 in
theorem exists_scaled_paperPropensityCarrier (Q : ℕ) [NeZero Q] (ρ θ η : ℝ)
    (hρ : 0 < ρ) (hθ : 0 < θ) (hθ1 : θ < 1) (hη : 0 < η) :
    ∃ c > 0, c ≤ 1 ∧ ∃ N₀ > 0, ∃ R > 0, ∃ C ≥ 0, ∃ K > 0,
      (∀ (x₀ : d → ℝ) (ℓ h : ℝ), 0 < ℓ → ℓ ≤ h →
        ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀) ∧
      ∀ (p gap α a₀ : ℝ), 0 < p → gap < 1 → (Fintype.card d : ℝ) * η < gap → 0 < α →
        Tendsto (normalizedCarrierBound (Q.choose 2) (4 * Q) C R p gap ((Fintype.card d : ℝ) * η))
          atTop (𝓝 0) ∧
        ∀ᶠ n : ℕ in atTop,
          let t := ((n : ℝ) + 1) ^ (-p)
          let N := carrierDegreeWeight R ((Fintype.card d : ℝ) * η) t
          let τ := carrierTaper gap t
          let δ := normalizedCarrierBound (Q.choose 2) (4 * Q) C R p gap ((Fintype.card d : ℝ) * η) n
          ∃ w : ℝ, 0 < w ∧ w ≤ 1 / 2 ∧
            t ^ Fintype.card d / 4 ≤ w ∧ w ≤ t ^ Fintype.card d / 2 ∧
            N₀ / c ≤ N ∧
            (∀ y : d → ℝ, assignmentMultiplier c w y * linearPartition y = assignmentPartition w y ∧
              0 ≤ assignmentMultiplier c w y ∧ assignmentMultiplier c w y ≤ 1 / c) ∧
            ∀ (x₀ : d → ℝ) (r h : ℝ), 0 < r → r ≤ h → h ≤ 1 →
              ∀ k : activeBlocks (d := d) r h,
              HasPaperPropensityCarrier Q ρ x₀ (t * r) r h k.val
                c w N N₀ θ (a₀ * (t * r) ^ α) t τ K δ := by
  obtain ⟨c, hc, hc1, N₀, hN₀, R, hR, hrough, hassignment⟩ :=
    exists_normalized_assignment (d := d) η hη
  obtain ⟨C, hC, Cκ, hCκ, K, hK, hcarrier⟩ :=
    exists_paperPropensityCarrier (d := d) Q ρ θ hρ hθ hθ1
  refine ⟨c, hc, hc1, N₀, hN₀, R, hR, C, hC, K, hK, hrough, fun p gap α a₀ hp hgap hlg hα => ?_⟩
  let δ := normalizedCarrierBound (Q.choose 2) (4 * Q) C R p gap ((Fintype.card d : ℝ) * η)
  have hδ : Tendsto δ atTop (𝓝 0) :=
    normalizedCarrierBound_tendsto _ _ C R p gap _ hC hR.le hp hgap hlg
  refine ⟨hδ, ?_⟩
  let P := (Fintype.card (MomentExponent (CoefficientExponent d Q) (4 * Q)) : ℝ) *
    polarizationBound (Fin Q) θ
  let Mθ := (1 + |θ|) ^ Q + 1
  have hsmalllim : Tendsto (fun n => K * Mθ * (2 * (P * δ n))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((hδ.const_mul P).const_mul 2).const_mul (K * Mθ)
  have hmasslim : Tendsto (fun n => 2 * K * (2 * (P * δ n))) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((hδ.const_mul P).const_mul 2).const_mul (2 * K)
  have hcorrlim : Tendsto (fun n : ℕ => Cκ * (a₀ ^ 2 * ((((n : ℝ) + 1) ^ (-p)) ^ α) ^ 2))
      atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using
      (((jitterPower_tendsto p α hp hα).pow 2).const_mul (a₀ ^ 2)).const_mul Cκ
  filter_upwards [hsmalllim (eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)),
    hmasslim (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)),
    hcorrlim (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))] with n hsmall hmass hcorr
  dsimp only
  let t := ((n : ℝ) + 1) ^ (-p)
  have ht : 0 < t := Real.rpow_pos_of_pos (by positivity) _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
  obtain ⟨w, hw, hw1, hwlo, hwhi, hN, M, hM, hMv, hm⟩ := hassignment t ht ht1
  refine ⟨w, hw, hw1, hwlo, hwhi, hN, hm, fun x₀ r h hr hrh hh1 k => ?_⟩
  have hℓ : 0 < t * r := mul_pos ht hr
  have hℓh : t * r ≤ h := (mul_le_of_le_one_left hr.le ht1).trans hrh
  have hpow : (t * r) ^ α ≤ t ^ α :=
    Real.rpow_le_rpow hℓ.le (mul_le_of_le_one_right ht.le (hrh.trans hh1)) hα.le
  have hκ : Cκ * (a₀ * (t * r) ^ α) ^ 2 ≤ 1 := by
    have hsquare := pow_le_pow_left₀ (Real.rpow_nonneg hℓ.le α) hpow 2
    have hb := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsquare (sq_nonneg a₀)) hCκ
    rw [← mul_pow] at hb
    exact hb.trans hcorr.le
  exact hcarrier x₀ (t * r) r h hℓ hr hrh k c w
    (carrierDegreeWeight R ((Fintype.card d : ℝ) * η) t) N₀ (a₀ * (t * r) ^ α) t
    (carrierTaper gap t) hc hw hw1 hN₀ hN ht (carrierTaper_pos gap t ht)
    (fun y => (hm y).2) (hrough x₀ (t * r) h hℓ hℓh) M hM hMv hκ hsmall.le hmass

end CausalLowerbound.PartC
