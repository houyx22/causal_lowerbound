import CausalLowerbound.PartB.ActivePackets

/-! Amplitude cancellation for the actual propensity packets and the target
bump. This proves the Hölder bounds at their separate fine and coarse scales. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff

namespace CausalLowerbound.PartB.ShellGeometry

variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def propensityPerturbation {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r h a : ℝ) (x : d → ℝ) : ℝ :=
  a * packetField S U x₀ r h x

/-- a=c_a r^α exactly cancels the fine-scale Hölder loss. -/
theorem propensityPerturbation_holder {Q : ℕ} (U : Ω → CoefficientExponent d Q → ℝ)
    (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω) (x₀ : d → ℝ)
      (r h ca : ℝ), 0 < r → r ≤ h → r ≤ 1 → 0 ≤ ca →
      HolderControl m θ (ca * C)
        (propensityPerturbation S (fun k => U (sample k)) x₀ r h (ca * r ^ ((m : ℝ) + θ))) := by
  obtain ⟨C, hC, hb⟩ := packetField_holder_bound U m θ hθ hθ1
  refine ⟨C, hC, ?_⟩
  intro S sample x₀ r h ca hr hrh hr1 hca
  have hh := (hb S sample x₀ r h hr hrh hr1).const_smul
    (packetField_smooth S (fun k => U (sample k)) x₀ r h) (ca * r ^ ((m : ℝ) + θ))
  have he : |ca * r ^ ((m : ℝ) + θ)| * (C * r ^ (-((m : ℝ) + θ))) = ca * C := by
    rw [abs_of_nonneg (mul_nonneg hca (Real.rpow_nonneg hr.le _)), Real.rpow_neg hr.le]
    have hpow : r ^ ((m : ℝ) + θ) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
    field_simp
    ring
  simpa only [he, smul_eq_mul, propensityPerturbation] using hh

def targetProfile (x : d → ℝ) : ℝ := quadraticPartition x ^ 2

theorem targetProfile_smooth : ContDiff ℝ ∞ (targetProfile (d := d)) :=
  quadraticPartition_smooth.pow 2

theorem targetProfile_compact : HasCompactSupport (targetProfile (d := d)) :=
  (quadraticPartition_compact (d := d)).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)

theorem targetField_holder (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C > 0, ∀ (x₀ : d → ℝ) (h Δ : ℝ), 0 < h → h ≤ 1 →
      HolderControl m θ (C * |Δ| * h ^ (-((m : ℝ) + θ))) (targetField x₀ h Δ) := by
  obtain ⟨C, hC, hb⟩ := compact_smooth_holder_scaling (targetProfile (d := d))
    targetProfile_smooth targetProfile_compact m θ hθ hθ1
  refine ⟨C, hC, ?_⟩
  intro x₀ h Δ hh hh1
  have ht := (hb x₀ h hh hh1).const_smul
    (rescaled_smooth _ targetProfile_smooth x₀ h) Δ
  simpa only [targetField, targetProfile, coarseBump, rescaled, smul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm] using ht

/-- The target amplitude Δ=h^γ cancels the coarse-scale Hölder loss. -/
theorem balanced_target_holder (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C > 0, ∀ (x₀ : d → ℝ) (h c : ℝ), 0 < h → h ≤ 1 → 0 ≤ c →
      HolderControl m θ (C * c) (targetField x₀ h (c * h ^ ((m : ℝ) + θ))) := by
  obtain ⟨C, hC, hb⟩ := targetField_holder (d := d) m θ hθ hθ1
  refine ⟨C, hC, ?_⟩
  intro x₀ h c hh hh1 hc
  have he : C * |c * h ^ ((m : ℝ) + θ)| * h ^ (-((m : ℝ) + θ)) = C * c := by
    rw [abs_of_nonneg (mul_nonneg hc (Real.rpow_nonneg hh.le _)), Real.rpow_neg hh.le]
    have hpow : h ^ ((m : ℝ) + θ) ≠ 0 := (Real.rpow_pos_of_pos hh _).ne'
    field_simp
    ring
  simpa only [he] using hb x₀ h (c * h ^ ((m : ℝ) + θ)) hh hh1

end CausalLowerbound.PartB.ShellGeometry
