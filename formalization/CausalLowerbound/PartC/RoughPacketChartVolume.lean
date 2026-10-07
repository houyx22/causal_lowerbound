import CausalLowerbound.PartC.PhysicalRoughRegularity
import CausalLowerbound.PartB.ClusterVolume

/-! The fine rough packet in a carrier chart has support volume O((ℓ/r)^d).
This gives its actual L¹ bound independently of the number and locations of
rough packets, including packets cut by the boundary of the unit chart. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal ContDiff

namespace CausalLowerbound.PartC

open PartB PartB.ShellGeometry

variable {d : Type*} [Fintype d] [DecidableEq d]

def roughPacketChart (x₀ : d → ℝ) (ℓ r h : ℝ) (k a : d → ℤ) (u : d → ℝ) : ℝ :=
  packet (coarseBump x₀ h) x₀ ℓ a (fun i => x₀ i + r * (k i + 4 * u i - 2))

def roughPacketChartCenter (ℓ r : ℝ) (k a : d → ℤ) : d → ℝ :=
  fun i => (ℓ / r * a i - k i + 2) / 4

theorem roughPacketChart_smooth (x₀ : d → ℝ) (ℓ r h : ℝ) (k a : d → ℤ) :
    ContDiff ℝ ∞ (roughPacketChart x₀ ℓ r h k a) := by
  apply (packet_smooth _ (rescaled_smooth _ quadraticPartition_smooth _ _) _ _ _).comp
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.add (contDiff_const.mul
    ((contDiff_const.add (contDiff_const.mul (contDiff_apply ℝ ℝ i))).sub contDiff_const))

theorem roughPacketChart_abs_le (x₀ : d → ℝ) (ℓ r h : ℝ) (k a : d → ℤ)
    (u : d → ℝ) : |roughPacketChart x₀ ℓ r h k a u| ≤ 1 := by
  rw [roughPacketChart, packet, abs_mul,
    abs_of_nonneg (coarseBump_range _ _ _).1]
  exact (mul_le_mul (coarseBump_range _ _ _).2 (quadraticPartition_abs_le _)
    (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem roughPacketChart_support (x₀ : d → ℝ) (ℓ r h : ℝ) (k a : d → ℤ)
    (hℓ : 0 < ℓ) (hr : 0 < r) :
    Function.support (roughPacketChart x₀ ℓ r h k a) ⊆
      coordinateBox (roughPacketChartCenter ℓ r k a) (ℓ / (4 * r)) := by
  intro u hu
  have hpacket : quadraticPartition (fun i =>
      ((x₀ i + r * (k i + 4 * u i - 2) - x₀ i) / ℓ - a i)) ≠ 0 :=
    (mul_ne_zero_iff.mp hu).2
  have hs := quadraticPartition_support (subset_tsupport _ hpacket)
  apply (mem_coordinateBox _ _ _).mpr
  intro i
  have he : (x₀ i + r * (k i + 4 * u i - 2) - x₀ i) / ℓ - a i =
      (u i - roughPacketChartCenter ℓ r k a i) / (ℓ / (4 * r)) := by
    dsimp only [roughPacketChartCenter]
    field_simp [hℓ.ne', hr.ne']
    <;> ring
  have hb : |(u i - roughPacketChartCenter ℓ r k a i) / (ℓ / (4 * r))| ≤ 1 := by
    rw [← he]
    exact abs_le.mpr ⟨hs.1 i, hs.2 i⟩
  have hscale : 0 < ℓ / (4 * r) := by positivity
  rw [abs_div, abs_of_pos hscale, div_le_one hscale] at hb
  exact hb

/-- A global Euclidean integral bound also bounds the integral over the unit
chart. No disjointness from the chart boundary is required. -/
theorem roughPacketChart_lintegral (x₀ : d → ℝ) (ℓ r h : ℝ) (k a : d → ℤ)
    (hℓ : 0 < ℓ) (hr : 0 < r) :
    (∫⁻ u, ENNReal.ofReal |roughPacketChart x₀ ℓ r h k a u|) ≤
      ENNReal.ofReal (ℓ / (2 * r)) ^ Fintype.card d := by
  let B := coordinateBox (roughPacketChartCenter ℓ r k a) (ℓ / (4 * r))
  have hpoint (u : d → ℝ) : ENNReal.ofReal |roughPacketChart x₀ ℓ r h k a u| ≤
      B.indicator (fun _ => (1 : ℝ≥0∞)) u := by
    by_cases hu : u ∈ B
    · rw [Set.indicator_of_mem hu]
      exact (ENNReal.ofReal_le_ofReal (roughPacketChart_abs_le x₀ ℓ r h k a u)).trans_eq
        ENNReal.ofReal_one
    · have hz : roughPacketChart x₀ ℓ r h k a u = 0 := by
        by_contra hn
        exact hu (roughPacketChart_support x₀ ℓ r h k a hℓ hr hn)
      simp [hz, Set.indicator_of_not_mem hu]
  apply (lintegral_mono hpoint).trans
  rw [lintegral_indicator_const (show MeasurableSet B from measurableSet_Icc), one_mul,
    coordinateBox_volume]
  have he : 2 * (ℓ / (4 * r)) = ℓ / (2 * r) := by ring
  rw [he]

theorem roughPacketChart_fine_lintegral (x₀ : d → ℝ) (r h t : ℝ) (k a : d → ℤ)
    (hr : 0 < r) (ht : 0 < t) :
    (∫⁻ u, ENNReal.ofReal |roughPacketChart x₀ (t * r) r h k a u|) ≤
      ENNReal.ofReal (t ^ Fintype.card d) := by
  apply (roughPacketChart_lintegral x₀ (t * r) r h k a (mul_pos ht hr) hr).trans
  have he : t * r / (2 * r) = t / 2 := by field_simp [hr.ne']; ring
  rw [he, ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ t / 2)]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) (by linarith) _)

end CausalLowerbound.PartC
