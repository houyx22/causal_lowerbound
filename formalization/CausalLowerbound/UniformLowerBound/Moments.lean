import CausalLowerbound.UniformLowerBound.Models
import CausalLowerbound.PartB.FiniteRademacher

/-! The finite sign prior and exact first two moments of the signed field. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace CausalLowerbound.UniformLowerBound
open PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def signPrior (S : Finset (d → ℤ)) : FiniteLaw (S → Bool) := independentSigns

theorem signedField_extend_eq_sum (S : Finset (d → ℤ)) (ζ : S → Bool)
    (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ) :
    signedField S (extendBlockSample S ζ) x₀ ℓ h x =
      ∑ k : S, packet (coarseBump x₀ h) x₀ ℓ k x * sign (ζ k) := by
  rw [signedField, ← Finset.sum_attach S]
  apply Finset.sum_congr rfl
  intro k _
  simp [extendBlockSample, k.property, mul_comm]

theorem signPrior_mean (S : Finset (d → ℤ)) (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ) :
    (signPrior S).expect (fun ζ => signedField S (extendBlockSample S ζ) x₀ ℓ h x) = 0 := by
  simp_rw [signedField_extend_eq_sum]
  exact (independentSignSum_moments (fun k : S => packet (coarseBump x₀ h) x₀ ℓ k x)).1

theorem signPrior_secondMoment_sum (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ h : ℝ) (x : d → ℝ) :
    (signPrior S).expect (fun ζ => signedField S (extendBlockSample S ζ) x₀ ℓ h x ^ 2) =
      ∑ k ∈ S, packet (coarseBump x₀ h) x₀ ℓ k x ^ 2 := by
  simp_rw [signedField_extend_eq_sum]
  have hh := (independentSignSum_moments (fun k : S => packet (coarseBump x₀ h) x₀ ℓ k x)).2.1
  rw [← Finset.sum_attach S]
  exact hh

theorem signPrior_secondMoment (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h)
    (x : d → ℝ) :
    (signPrior (activeBlocks ℓ h)).expect (fun ζ =>
      signedField (activeBlocks ℓ h) (extendBlockSample (activeBlocks ℓ h) ζ) x₀ ℓ h x ^ 2) =
      coarseBump x₀ h x ^ 2 := by
  rw [signPrior_secondMoment_sum, active_packet_square_sum x₀ ℓ h hℓ hh]

theorem packet_abs_le_one (x₀ : d → ℝ) (ℓ h : ℝ) (k : d → ℤ) (x : d → ℝ) :
    |packet (coarseBump x₀ h) x₀ ℓ k x| ≤ 1 := by
  rw [packet, abs_mul]
  exact mul_le_one₀ (by simpa [abs_of_nonneg (coarseBump_range x₀ h x).1] using
    (coarseBump_range x₀ h x).2) (abs_nonneg _) (quadraticPartition_abs_le _)

theorem signedField_abs_le (S : Finset (d → ℤ)) (ζ : (d → ℤ) → Bool)
    (x₀ : d → ℝ) (ℓ h : ℝ) (x : d → ℝ) :
    |signedField S ζ x₀ ℓ h x| ≤ (2 : ℝ) ^ Fintype.card d := by
  classical
  let N := latticeNeighbors (fun i => (x i - x₀ i) / ℓ)
  let T := S ∩ N
  have hTS : T ⊆ S := Finset.inter_subset_left
  have hz : ∀ k ∈ S, k ∉ T → sign (ζ k) * packet (coarseBump x₀ h) x₀ ℓ k x = 0 := by
    intro k hk hkT
    have hkN : k ∉ N := fun hh => hkT (Finset.mem_inter.mpr ⟨hk, hh⟩)
    simp only [packet, quadraticPartition_zero_outside_neighbors _ _ hkN, mul_zero]
  rw [signedField, ← Finset.sum_subset hTS hz]
  calc
    _ ≤ ∑ k ∈ T, |sign (ζ k) * packet (coarseBump x₀ h) x₀ ℓ k x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ T, (1 : ℝ) := Finset.sum_le_sum (fun k _ => by
      simpa only [abs_mul, abs_sign, one_mul] using packet_abs_le_one x₀ ℓ h k x)
    _ = (T.card : ℝ) := by simp
    _ ≤ (N.card : ℝ) := by exact_mod_cast (Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := N)))
    _ = _ := by rw [latticeNeighbors_card]; norm_cast

theorem signedField_incident_local (S : Finset (d → ℤ)) (x₀ : d → ℝ)
    (ℓ h : ℝ) (x : d → ℝ) (ζ ζ' : S → Bool)
    (he : ∀ k : S, x ∈ carrierBox x₀ ℓ k.val → ζ k = ζ' k) :
    signedField S (extendBlockSample S ζ) x₀ ℓ h x =
      signedField S (extendBlockSample S ζ') x₀ ℓ h x := by
  rw [signedField_extend_eq_sum, signedField_extend_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hx : x ∈ carrierBox x₀ ℓ k.val
  · rw [he k hx]
  · rw [packet_zero_outside_carrier _ _ _ _ _ hx]
    simp

end CausalLowerbound.UniformLowerBound
