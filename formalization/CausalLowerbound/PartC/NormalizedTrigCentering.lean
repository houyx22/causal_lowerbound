import CausalLowerbound.PartC.PhysicalRepresentativeEvaluation
import CausalLowerbound.WienerTrigonometric

/-! Actual normalized trigonometric centering coefficients. Their total norm
is at most one; each explicit rough symbol costs one packet volume. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry

variable {d : Type*} [Fintype d] [DecidableEq d]

def normalizedTrigWeight (c w N : ℝ) (n : ℕ) (q : d → ℤ) (b : Bool) (u : d → ℝ) : ℝ :=
  (assignmentMultiplier c w (fun j => 4 * u j - 2) / N) ^ n *
    (Wiener.toContinuous (Wiener.trigSeries q b) (Wiener.torusProjection u)).re

theorem normalizedTrigWeight_continuous (c w N : ℝ) (hc : 0 < c) (n : ℕ) (q : d → ℤ) (b : Bool) :
    Continuous (normalizedTrigWeight c w N n q b) := by
  have hm := (assignmentMultiplier_smooth (d := d) c w hc).continuous.comp
    (by fun_prop : Continuous (fun u : d → ℝ => fun j => 4 * u j - 2))
  have ht := Complex.continuous_re.comp ((Wiener.toContinuous (Wiener.trigSeries q b)).continuous.comp
    Wiener.torusProjection_quotient.continuous)
  simpa only [normalizedTrigWeight, div_eq_mul_inv] using
    ((hm.mul (continuous_const (y := N⁻¹))).pow n).mul ht

theorem normalizedTrigWeight_bound (c w N : ℝ) (hc : 0 < c) (hN : 0 < N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (n : ℕ) (q : d → ℤ) (b : Bool) (u : d → ℝ) :
    |normalizedTrigWeight c w N n q b u| ≤ ((1 / c) / N) ^ n := by
  have ht : |(Wiener.toContinuous (Wiener.trigSeries q b) (Wiener.torusProjection u)).re| ≤ 1 :=
    (Complex.abs_re_le_norm _).trans ((Wiener.evaluate_bound _ _).trans (Wiener.trigSeries_norm _ _))
  rw [normalizedTrigWeight, abs_mul, abs_pow, abs_div, abs_of_pos hN, abs_of_nonneg (hm _).1]
  calc
    _ ≤ ((1 / c) / N) ^ n * 1 := mul_le_mul
      (pow_le_pow_left₀ (div_nonneg (hm _).1 hN.le)
        (div_le_div_of_nonneg_right (hm _).2 hN.le) n)
      ht (abs_nonneg _) (by positivity)
    _ = _ := mul_one _

def normalizedTrigCenter (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (n : ℕ) (q : d → ℤ) (b : Bool) : Walsh.Coefficients (activeBlocks (d := d) ℓ h) :=
  roughCentering x₀ ℓ r h k n (normalizedTrigWeight c w N n q b)

theorem normalizedTrigCenter_evaluate (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N : ℝ) (hc : 0 < c) (n : ℕ) (q : d → ℤ) (b : Bool)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    Walsh.evaluate ζ (normalizedTrigCenter x₀ ℓ r h k c w N n q b) =
      ∫ u in Set.Icc (0 : d → ℝ) 1, normalizedRoughChart x₀ ℓ r h k c w N ζ u ^ n *
        (Wiener.toContinuous (Wiener.trigSeries q b) (Wiener.torusProjection u)).re := by
  rw [normalizedTrigCenter, roughCentering_evaluate _ _ _ _ _ _ _
    (normalizedTrigWeight_continuous c w N hc n q b)]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [normalizedTrigWeight, normalizedRoughChart, mul_pow, div_pow]
  ring

theorem normalizedTrigCenter_bounds (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N N₀ : ℝ) (hℓ : 0 < ℓ) (hr : 0 < r) (hc : 0 < c) (hN₀ : 0 < N₀) (hN : N₀ / c ≤ N)
    (hm : ∀ v : d → ℝ, 0 ≤ assignmentMultiplier c w v ∧ assignmentMultiplier c w v ≤ 1 / c)
    (hrough : ∀ x, ‖physicalRoughWalsh x₀ ℓ h x‖ ≤ N₀)
    (n : ℕ) (q : d → ℤ) (b : Bool) :
    ‖normalizedTrigCenter x₀ ℓ r h k c w N n q b‖ ≤ 1 ∧
      ∀ j : activeBlocks (d := d) ℓ h,
        ‖Walsh.symbolPart j (normalizedTrigCenter x₀ ℓ r h k c w N n q b)‖ ≤
          (n / N₀) * (ℓ / (2 * r)) ^ Fintype.card d := by
  have hNp : 0 < N := (div_pos hN₀ hc).trans_le hN
  let B := ((1 / c) / N) ^ n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBn : B * N₀ ^ n ≤ 1 := by
    rw [show B = ((1 / c) / N) ^ n from rfl, ← mul_pow]
    apply pow_le_one₀ (by positivity)
    rw [show (1 / c / N) * N₀ = (N₀ / c) / N by ring]
    exact (div_le_one hNp).mpr hN
  have hw := normalizedTrigWeight_continuous c w N hc n q b
  have hwB := normalizedTrigWeight_bound c w N hc hNp hm n q b
  refine ⟨(roughCentering_norm x₀ ℓ r h k n N₀ hrough _ B hB hwB).trans hBn, fun j => ?_⟩
  have hcoef : B * n * N₀ ^ (n - 1) ≤ n / N₀ := by
    cases n with
    | zero => simp
    | succ m =>
      have hp : B * N₀ ^ m ≤ 1 / N₀ := by
        apply (le_div_iff₀ hN₀).mpr
        simpa only [pow_succ, mul_assoc] using hBn
      simp only [Nat.succ_sub_one]
      calc
        _ = (m + 1 : ℝ) * (B * N₀ ^ m) := by push_cast; ring
        _ ≤ (m + 1 : ℝ) * (1 / N₀) := mul_le_mul_of_nonneg_left hp (by positivity)
        _ = _ := by push_cast; ring
  exact (roughCentering_symbol_bound x₀ ℓ r h k n hℓ hr N₀ hN₀.le hrough _ hw B hB hwB j).trans
    (mul_le_mul_of_nonneg_right hcoef (by positivity))

/-- The two constants work simultaneously for every positive physical scale,
carrier block, basis index, and polynomial degree. -/
theorem exists_normalizedTrigCenter_bounds :
    ∃ c > 0, ∃ N₀ > 0, ∀ (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ) (w N : ℝ),
      0 < ℓ → 0 < r → ℓ ≤ h → 0 < w → w ≤ 1 / 2 → N₀ / c ≤ N →
      ∀ (n : ℕ) (q : d → ℤ) (b : Bool),
        ‖normalizedTrigCenter x₀ ℓ r h k c w N n q b‖ ≤ 1 ∧
          ∀ j : activeBlocks (d := d) ℓ h,
            ‖Walsh.symbolPart j (normalizedTrigCenter x₀ ℓ r h k c w N n q b)‖ ≤
              (n / N₀) * (ℓ / (2 * r)) ^ Fintype.card d := by
  obtain ⟨c, hc, _, hm⟩ := exists_assignmentMultiplier (d := d)
  obtain ⟨N₀, hN₀, hrough⟩ := physicalRoughWalsh_bound (d := d)
  refine ⟨c, hc, N₀, hN₀, fun x₀ ℓ r h k w N hℓ hr hℓh hw hw1 hN n q b => ?_⟩
  exact normalizedTrigCenter_bounds x₀ ℓ r h k c w N N₀ hℓ hr hc hN₀ hN
    (fun v => ((hm w hw hw1).2.2 v).2) (hrough x₀ ℓ h hℓ hℓh) n q b

end CausalLowerbound.PartC
