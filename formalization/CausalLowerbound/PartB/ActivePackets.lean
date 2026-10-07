import CausalLowerbound.PartB.PacketProfiles

/-! A concrete finite set containing every active physical packet. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff

namespace CausalLowerbound.PartB.ShellGeometry

variable {d : Type*} [Fintype d] [DecidableEq d]

def coarseBump (x₀ : d → ℝ) (h : ℝ) : (d → ℝ) → ℝ :=
  rescaled quadraticPartition x₀ h

def activeBlocks (r h : ℝ) : Finset (d → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-⌈h / r + 1⌉) ⌈h / r + 1⌉)

theorem coarseBump_center (x₀ : d → ℝ) (h : ℝ) : coarseBump x₀ h x₀ = 1 := by
  simp [coarseBump, rescaled]

theorem coarseBump_range (x₀ : d → ℝ) (h : ℝ) (x : d → ℝ) :
    0 ≤ coarseBump x₀ h x ∧ coarseBump x₀ h x ≤ 1 :=
  ⟨quadraticPartition_nonneg _, (le_abs_self _).trans (quadraticPartition_abs_le _)⟩

theorem packet_zero_outside_active (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hh : 0 < h)
    (k : d → ℤ) (hk : k ∉ activeBlocks (d := d) r h) (x : d → ℝ) :
    packet (coarseBump x₀ h) x₀ r k x = 0 := by
  by_contra hn
  have hg := (mul_ne_zero_iff.mp hn).1
  have hp := (mul_ne_zero_iff.mp hn).2
  apply hk
  apply Fintype.mem_piFinset.mpr
  intro i
  have hgi : quadraticWindow (h⁻¹ * (x i - x₀ i)) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hg) i (Finset.mem_univ i)
  have hpi : quadraticWindow ((x i - x₀ i) / r - k i) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i)
  have hgi' : |(x i - x₀ i) / h| < 1 := by
    simpa only [div_eq_mul_inv, mul_comm] using abs_lt.mpr (quadraticWindow_support hgi)
  rw [abs_div, abs_of_pos hh, div_lt_one hh] at hgi'
  have hy : |(x i - x₀ i) / r| ≤ h / r := by
    rw [abs_div, abs_of_pos hr]
    exact div_le_div_of_nonneg_right hgi'.le hr.le
  have hlocal := abs_lt.mpr (quadraticWindow_support hpi)
  have htri := abs_sub ((x i - x₀ i) / r) ((x i - x₀ i) / r - k i)
  have he : (x i - x₀ i) / r - ((x i - x₀ i) / r - k i) = (k i : ℝ) := by ring
  rw [he] at htri
  have hki : |(k i : ℝ)| ≤ h / r + 1 := by linarith
  have hkM := hki.trans (Int.le_ceil (h / r + 1))
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (abs_le.mp hkM).1
  · exact_mod_cast (abs_le.mp hkM).2

/-- The finite model retains the exact quadratic partition, everywhere. -/
theorem active_packet_square_sum (x₀ : d → ℝ) (r h : ℝ) (hr : 0 < r) (hh : 0 < h) (x : d → ℝ) :
    (∑ k ∈ activeBlocks (d := d) r h, packet (coarseBump x₀ h) x₀ r k x ^ 2) =
      coarseBump x₀ h x ^ 2 := by
  rw [← packet_sum_sq (coarseBump x₀ h) x₀ r x]
  symm
  apply tsum_eq_sum
  intro k hk
  rw [packet_zero_outside_active x₀ r h hr hh k hk x]
  norm_num

theorem packetField_eq_physical {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h : ℝ)
    (hr : 0 < r) (x : d → ℝ) :
    packetField S U x₀ r h x = ∑ k ∈ S, packet (coarseBump x₀ h) x₀ r k x *
      coefficientEvaluation (U k) (carrierCoordinate (fun i => (x i - x₀ i) / r - k i)) := by
  rw [packetField, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [rescaled, packetProfile, packet_local_coordinate x₀ r hr.ne',
    packet, coarseBump]
  ring

def targetField (x₀ : d → ℝ) (h Δ : ℝ) (x : d → ℝ) : ℝ := Δ * coarseBump x₀ h x ^ 2

theorem targetField_center (x₀ : d → ℝ) (h Δ : ℝ) : targetField x₀ h Δ x₀ = Δ := by
  simp [targetField, coarseBump_center]

theorem targetField_abs_le (x₀ : d → ℝ) (h Δ : ℝ) (x : d → ℝ) : |targetField x₀ h Δ x| ≤ |Δ| := by
  rw [targetField, abs_mul, abs_of_nonneg (sq_nonneg (coarseBump x₀ h x))]
  exact mul_le_of_le_one_right (abs_nonneg _) (by
    have hG := coarseBump_range x₀ h x
    nlinarith)

end CausalLowerbound.PartB.ShellGeometry
