import CausalLowerbound.PartC.RoughWalshPowers
import CausalLowerbound.PartC.RoughPacketChartVolume
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual centering of rough-field powers as finite Walsh coefficient arrays.
Evaluation commutes with the Bochner integral. Every explicit symbol in the
centering polynomial has mass O((ℓ/r)^d), with constants independent of the
number of fine packets. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry

variable {d : Type*} [Fintype d] [DecidableEq d]

def roughChartPoint (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) (u : d → ℝ) : d → ℝ :=
  fun i => x₀ i + r * (k i + 4 * u i - 2)

theorem roughChartPoint_continuous (x₀ : d → ℝ) (r : ℝ) (k : d → ℤ) :
    Continuous (roughChartPoint x₀ r k) := by
  unfold roughChartPoint
  fun_prop

def roughCentering (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (n : ℕ)
    (w : (d → ℝ) → ℝ) : Walsh.Coefficients (activeBlocks (d := d) ℓ h) :=
  ∫ u in Set.Icc (0 : d → ℝ) 1,
    w u • Walsh.power (physicalRoughWalsh x₀ ℓ h (roughChartPoint x₀ r k u)) n

theorem roughCentering_integrable (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (n : ℕ)
    (w : (d → ℝ) → ℝ) (hw : Continuous w) :
    IntegrableOn (fun u => w u •
      Walsh.power (physicalRoughWalsh x₀ ℓ h (roughChartPoint x₀ r k u)) n)
      (Set.Icc (0 : d → ℝ) 1) := by
  have hc := hw.smul (Walsh.continuous_power _
    ((physicalRoughWalsh_continuous x₀ ℓ h).comp (roughChartPoint_continuous x₀ r k)) n)
  exact hc.continuousOn.integrableOn_compact isCompact_Icc

theorem roughCentering_evaluate (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (n : ℕ)
    (w : (d → ℝ) → ℝ) (hw : Continuous w) (ζ : activeBlocks (d := d) ℓ h → Bool) :
    Walsh.evaluate ζ (roughCentering x₀ ℓ r h k n w) =
      ∫ u in Set.Icc (0 : d → ℝ) 1,
        w u * physicalRoughField x₀ ℓ h ζ (roughChartPoint x₀ r k u) ^ n := by
  rw [roughCentering, ← (Walsh.evaluate ζ).integral_comp_comm
    (roughCentering_integrable x₀ ℓ r h k n w hw)]
  simp only [map_smul, smul_eq_mul, physicalRoughWalsh_power_evaluate]

theorem roughCentering_norm (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (n : ℕ)
    (N₀ : ℝ) (hN : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (w : (d → ℝ) → ℝ) (B : ℝ) (hB : 0 ≤ B) (hw : ∀ u, |w u| ≤ B) :
    ‖roughCentering x₀ ℓ r h k n w‖ ≤ B * N₀ ^ n := by
  have hvol : volume (Set.Icc (0 : d → ℝ) 1) = 1 := by
    simp [Real.volume_Icc_pi]
  have hp (u : d → ℝ) :
      ‖w u • Walsh.power (physicalRoughWalsh x₀ ℓ h (roughChartPoint x₀ r k u)) n‖ ≤
        B * N₀ ^ n := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hw u) ((Walsh.power_norm _ n).trans
      (pow_le_pow_left₀ (norm_nonneg _) (hN _) n)) (norm_nonneg _) hB
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0 : d → ℝ) 1)
    (by rw [hvol]; exact ENNReal.one_lt_top) (fun u _ => hp u)
  simpa only [roughCentering, measureReal_def, hvol, ENNReal.toReal_one, mul_one] using hb

theorem roughCentering_symbol_bound (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (n : ℕ)
    (hℓ : 0 < ℓ) (hr : 0 < r) (N₀ : ℝ) (hN₀ : 0 ≤ N₀)
    (hN : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (w : (d → ℝ) → ℝ) (hw : Continuous w) (B : ℝ) (hB : 0 ≤ B)
    (hwB : ∀ u, |w u| ≤ B) (j : activeBlocks (d := d) ℓ h) :
    ‖Walsh.symbolPart j (roughCentering x₀ ℓ r h k n w)‖ ≤
      (B * n * N₀ ^ (n - 1)) * (ℓ / (2 * r)) ^ Fintype.card d := by
  let f := fun u => w u •
    Walsh.power (physicalRoughWalsh x₀ ℓ h (roughChartPoint x₀ r k u)) n
  let C := B * n * N₀ ^ (n - 1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hpoint (u : d → ℝ) : ‖Walsh.symbolPart j (f u)‖ ≤
      C * |roughPacketChart x₀ ℓ r h k j.val u| := by
    dsimp only [f]
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ B * ((n : ℝ) * N₀ ^ (n - 1) *
          |packet (coarseBump x₀ h) x₀ ℓ j.val (roughChartPoint x₀ r k u)|) :=
        mul_le_mul (hwB u) (physicalRoughWalsh_power_symbol x₀ ℓ h _ j n N₀ (hN _))
          (norm_nonneg _) hB
      _ = _ := by
        change B * ((n : ℝ) * N₀ ^ (n - 1) *
          |packet (coarseBump x₀ h) x₀ ℓ j.val (roughChartPoint x₀ r k u)|) =
          (B * n * N₀ ^ (n - 1)) *
            |packet (coarseBump x₀ h) x₀ ℓ j.val (roughChartPoint x₀ r k u)|
        ring
  have hlin : (∫⁻ u in Set.Icc (0 : d → ℝ) 1, ENNReal.ofReal ‖Walsh.symbolPart j (f u)‖) ≤
      ENNReal.ofReal (C * (ℓ / (2 * r)) ^ Fintype.card d) := by
    calc
      _ ≤ ∫⁻ u in Set.Icc (0 : d → ℝ) 1,
          ENNReal.ofReal (C * |roughPacketChart x₀ ℓ r h k j.val u|) :=
        lintegral_mono (fun u => ENNReal.ofReal_le_ofReal (hpoint u))
      _ = ENNReal.ofReal C * ∫⁻ u in Set.Icc (0 : d → ℝ) 1,
          ENNReal.ofReal |roughPacketChart x₀ ℓ r h k j.val u| := by
        simp only [ENNReal.ofReal_mul hC]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal C * ∫⁻ u, ENNReal.ofReal |roughPacketChart x₀ ℓ r h k j.val u| :=
        mul_le_mul_left' (setLIntegral_le_lintegral _ _) _
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (ℓ / (2 * r)) ^ Fintype.card d :=
        mul_le_mul_left' (roughPacketChart_lintegral x₀ ℓ r h k j.val hℓ hr) _
      _ = _ := by
        rw [← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ ℓ / (2 * r)),
          ← ENNReal.ofReal_mul hC]
  rw [roughCentering, ← (Walsh.symbolPart j).integral_comp_comm
    (roughCentering_integrable x₀ ℓ r h k n w hw)]
  apply (norm_integral_le_lintegral_norm (μ := volume.restrict (Set.Icc (0 : d → ℝ) 1))
    (fun u => Walsh.symbolPart j (f u))).trans
  apply (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin).trans_eq
  exact ENNReal.toReal_ofReal (mul_nonneg hC (pow_nonneg (by positivity) _))

/-- A single constant controls the actual centering polynomials for every
physical scale, packet count, carrier block, degree, and bounded continuous weight. -/
theorem physical_roughCentering_bounds : ∃ N₀ > 0,
    ∀ (x₀ : d → ℝ) (ℓ r h : ℝ), 0 < ℓ → 0 < r → ℓ ≤ h →
    ∀ (k : d → ℤ) (n : ℕ) (w : (d → ℝ) → ℝ), Continuous w →
    ∀ B : ℝ, 0 ≤ B → (∀ u, |w u| ≤ B) →
      ‖roughCentering x₀ ℓ r h k n w‖ ≤ B * N₀ ^ n ∧
      ∀ j : activeBlocks (d := d) ℓ h,
        ‖Walsh.symbolPart j (roughCentering x₀ ℓ r h k n w)‖ ≤
          (B * n * N₀ ^ (n - 1)) * (ℓ / (2 * r)) ^ Fintype.card d := by
  obtain ⟨N₀, hN₀, hb⟩ := physicalRoughWalsh_bound (d := d)
  refine ⟨N₀, hN₀, fun x₀ ℓ r h hℓ hr hℓh k n w hw B hB hwB => ?_⟩
  have hN := hb x₀ ℓ h hℓ hℓh
  exact ⟨roughCentering_norm x₀ ℓ r h k n N₀ hN w B hB hwB,
    fun j => roughCentering_symbol_bound x₀ ℓ r h k n hℓ hr N₀ hN₀.le hN w hw B hB hwB j⟩

end CausalLowerbound.PartC
