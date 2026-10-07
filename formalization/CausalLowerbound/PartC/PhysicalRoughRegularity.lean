import CausalLowerbound.PartC.PhysicalRoughMoments
import CausalLowerbound.PartC.LatticeFields

/-! Uniform regularity of the actual finite rough field, together with a
uniform sum of packet magnitudes. The latter is the Walsh evaluation bound
and does not grow with the number of fine-scale signs. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff
namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def signPacketProfile (b : Bool) (x : d → ℝ) : ℝ := sign b * quadraticPartition x

theorem signPacketProfile_smooth (b : Bool) : ContDiff ℝ ∞ (signPacketProfile (d := d) b) :=
  contDiff_const.mul quadraticPartition_smooth

theorem signPacketProfile_support (b : Bool) :
    tsupport (signPacketProfile (d := d) b) ⊆ Set.Icc (fun _ => -1) (fun _ => 1) :=
  tsupport_mul_subset_right.trans quadraticPartition_support

def extendRoughSigns (S : Finset (d → ℤ)) (ζ : S → Bool) (k : d → ℤ) : Bool :=
  if hk : k ∈ S then ζ ⟨k, hk⟩ else false

@[simp] theorem extendRoughSigns_coe (S : Finset (d → ℤ)) (ζ : S → Bool) (k : S) :
    extendRoughSigns S ζ k.val = ζ k := by simp [extendRoughSigns, k.property]

theorem physicalRoughField_eq_localized (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) :
    physicalRoughField x₀ ℓ h ζ = localizedLatticeField (activeBlocks ℓ h) signPacketProfile
      (extendRoughSigns (activeBlocks ℓ h) ζ) x₀ ℓ h := by
  funext x
  rw [physicalRoughField_eq_sum, localizedLatticeField, latticeField, Finset.mul_sum,
    ← Finset.sum_coe_sort (activeBlocks ℓ h) (fun k => coarseBump x₀ h x *
      rescaled (signPacketProfile (extendRoughSigns (activeBlocks ℓ h) ζ k)) (packetCenter x₀ ℓ k) ℓ x)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [rescaled, signPacketProfile, extendRoughSigns_coe,
    packet_local_coordinate x₀ ℓ hℓ.ne', packet]
  ring

theorem physicalRoughField_scale_control (M : ℕ) :
    ∃ C > 0, ∀ (x₀ : d → ℝ) (ℓ h : ℝ), 0 < ℓ → ℓ ≤ h →
      ∀ ζ : activeBlocks (d := d) ℓ h → Bool, ScaleControl M ℓ C (physicalRoughField x₀ ℓ h ζ) := by
  obtain ⟨C, hC, hb⟩ := localizedLatticeField_scale_control (signPacketProfile (d := d))
    signPacketProfile_smooth signPacketProfile_support M
  refine ⟨C, hC, fun x₀ ℓ h hℓ hℓh ζ => ?_⟩
  rw [physicalRoughField_eq_localized x₀ ℓ h hℓ ζ]
  exact hb _ _ _ _ _ hℓ hℓh

theorem physicalRoughField_amplitude_holder (m : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∃ C > 0, ∀ (x₀ : d → ℝ) (ℓ h c : ℝ), 0 < ℓ → ℓ ≤ h → ℓ ≤ 1 → 0 ≤ c →
      ∀ ζ : activeBlocks (d := d) ℓ h → Bool,
      HolderControl m θ (C * c) (fun x => (c * ℓ ^ ((m : ℝ) + θ)) * physicalRoughField x₀ ℓ h ζ x) := by
  obtain ⟨C, hC, hb⟩ := physicalRoughField_scale_control (d := d) (m + 1)
  exact ⟨2 * C, by positivity, fun x₀ ℓ h c hℓ hℓh hℓ1 hc ζ =>
    (hb x₀ ℓ h hℓ hℓh ζ).amplitude_holder hθ hθ1 hℓ hℓ1 c hc⟩

theorem physicalRough_packet_mass_bound : ∃ N₀ > 0, ∀ (x₀ : d → ℝ) (ℓ h : ℝ),
    0 < ℓ → ℓ ≤ h → ∀ x : d → ℝ,
      (∑ k : activeBlocks (d := d) ℓ h, |physicalJitterWeights x₀ ℓ h 1 1 x k|) ≤ N₀ := by
  obtain ⟨C, hC, hb⟩ := physicalRoughField_scale_control (d := d) 0
  refine ⟨C, hC, fun x₀ ℓ h hℓ hℓh x => ?_⟩
  have hs := hb x₀ ℓ h hℓ hℓh (fun _ => true)
  have hn : |physicalRoughField x₀ ℓ h (fun _ => true) x| ≤ C := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, mul_one] using hs.bound 0 (by omega) x
  have hp (k : activeBlocks (d := d) ℓ h) : 0 ≤ physicalJitterWeights x₀ ℓ h 1 1 x k := by
    simp only [physicalJitterWeights, one_mul, packet]
    exact mul_nonneg (coarseBump_range x₀ h x).1 (quadraticPartition_nonneg _)
  simp only [abs_of_nonneg (hp _)]
  have he : (∑ k : activeBlocks (d := d) ℓ h, physicalJitterWeights x₀ ℓ h 1 1 x k) =
      physicalRoughField x₀ ℓ h (fun _ => true) x := by
    simp only [physicalRoughField, independentSignSum, sign, mul_one]
  rw [he]
  exact (le_abs_self _).trans hn

theorem physicalRoughField_sign_locality (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ)
    (ζ ξ : activeBlocks (d := d) ℓ h → Bool)
    (heq : ∀ k, packet (coarseBump x₀ h) x₀ ℓ k.val x ≠ 0 → ζ k = ξ k) :
    physicalRoughField x₀ ℓ h ζ x = physicalRoughField x₀ ℓ h ξ x := by
  simp only [physicalRoughField_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hp : packet (coarseBump x₀ h) x₀ ℓ k.val x = 0
  · simp only [hp, zero_mul]
  · rw [heq k hp]

end CausalLowerbound.PartC
