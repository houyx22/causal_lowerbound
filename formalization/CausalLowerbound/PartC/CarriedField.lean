import CausalLowerbound.PartC.LatticeFields
import CausalLowerbound.PartC.LinearPartition

/-! The smooth carried field uses the linear partition, without a coarse
envelope factor. The fixed finite coefficient support gives uniform
regularity for every sample and every finite set of active blocks. -/
noncomputable section
set_option autoImplicit false
open scoped ContDiff BigOperators
namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [Fintype Ω]

def carriedProfile {Q : ℕ} (U : CoefficientExponent d Q → ℝ) (u : d → ℝ) : ℝ :=
  linearPartition u * coefficientEvaluation U (carrierCoordinate u)

theorem carriedProfile_smooth {Q : ℕ} (U : CoefficientExponent d Q → ℝ) :
    ContDiff ℝ ∞ (carriedProfile U) :=
  linearPartition_smooth.mul ((coefficientEvaluation_smooth U).comp carrierCoordinate_smooth)

theorem carriedProfile_support {Q : ℕ} (U : CoefficientExponent d Q → ℝ) :
    tsupport (carriedProfile U) ⊆ Set.Icc (fun _ => -1) (fun _ => 1) :=
  tsupport_mul_subset_left.trans linearPartition_support

def carriedField {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r : ℝ) (x : d → ℝ) : ℝ :=
  ∑ k ∈ S, rescaled (carriedProfile (U k)) (packetCenter x₀ r k) r x

theorem carriedField_smooth {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r : ℝ) :
    ContDiff ℝ ∞ (carriedField S U x₀ r) :=
  ContDiff.sum (fun k hk => rescaled_smooth _ (carriedProfile_smooth _) _ _)

theorem carriedField_eq_physical {Q : ℕ} (S : Finset (d → ℤ))
    (U : (d → ℤ) → CoefficientExponent d Q → ℝ) (x₀ : d → ℝ) (r : ℝ) (hr : 0 < r) (x : d → ℝ) :
    carriedField S U x₀ r x = ∑ k ∈ S,
      linearPartition (fun i => (x i - x₀ i) / r - k i) *
        coefficientEvaluation (U k) (carrierCoordinate (fun i => (x i - x₀ i) / r - k i)) := by
  simp only [carriedField, rescaled, carriedProfile, packet_local_coordinate x₀ r hr.ne']

theorem carriedField_scale_control {Q : ℕ} (U : Ω → CoefficientExponent d Q → ℝ) (M : ℕ) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω) (x₀ : d → ℝ) (r : ℝ),
      0 < r → ScaleControl M r C (carriedField S (fun k => U (sample k)) x₀ r) :=
  latticeField_scale_control (fun sampleIndex => carriedProfile (U sampleIndex))
    (fun sampleIndex => carriedProfile_smooth _) (fun sampleIndex => carriedProfile_support _) M

theorem carriedField_amplitude_holder {Q : ℕ} (U : Ω → CoefficientExponent d Q → ℝ)
    (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C > 0, ∀ (S : Finset (d → ℤ)) (sample : (d → ℤ) → Ω) (x₀ : d → ℝ) (r c : ℝ),
      0 < r → r ≤ 1 → 0 ≤ c → HolderControl m θ (C * c)
        (fun x => (c * r ^ ((m : ℝ) + θ)) * carriedField S (fun k => U (sample k)) x₀ r x) :=
  latticeField_amplitude_holder (fun sampleIndex => carriedProfile (U sampleIndex))
    (fun sampleIndex => carriedProfile_smooth _) (fun sampleIndex => carriedProfile_support _) m θ hθ hθ1

end CausalLowerbound.PartC
