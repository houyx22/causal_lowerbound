import CausalLowerbound.PartC.RoughFieldMoments
import CausalLowerbound.PartB.PhysicalJitterMoments

/-! The actual finite rough-sign field at the fine spatial scale. All
moment identities hold on the whole space, including where the coarse
envelope vanishes; no normalization of unspecified packet weights is assumed. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators ContDiff
namespace CausalLowerbound.PartC
open PartB PartB.ShellGeometry
variable {d : Type*} [Fintype d] [DecidableEq d]

def physicalRoughField (x₀ : d → ℝ) (ℓ h : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) : ℝ :=
  independentSignSum (physicalJitterWeights x₀ ℓ h 1 1 x) ζ

def physicalRoughCorrection (x₀ : d → ℝ) (ℓ h ja : ℝ) (x : d → ℝ) : ℝ :=
  ja ^ 2 * coarseBump x₀ h x ^ 2 * (3 - 2 * quarticField (activeBlocks ℓ h) x₀ ℓ x)

theorem physicalRoughField_eq_sum (x₀ : d → ℝ) (ℓ h : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) :
    physicalRoughField x₀ ℓ h ζ x =
      ∑ k : activeBlocks ℓ h, packet (coarseBump x₀ h) x₀ ℓ k.val x * sign (ζ k) := by
  simp only [physicalRoughField, independentSignSum, physicalJitterWeights, one_mul]

theorem physicalRoughField_smooth (x₀ : d → ℝ) (ℓ h : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) : ContDiff ℝ ∞ (physicalRoughField x₀ ℓ h ζ) := by
  simp_rw [show physicalRoughField x₀ ℓ h ζ = (fun x =>
      ∑ k : activeBlocks ℓ h, packet (coarseBump x₀ h) x₀ ℓ k.val x * sign (ζ k)) from
    funext (physicalRoughField_eq_sum x₀ ℓ h ζ)]
  apply ContDiff.sum
  intro k hk
  exact (packet_smooth _ (rescaled_smooth _ quadraticPartition_smooth _ _) _ _ _).mul contDiff_const

theorem physicalRoughField_zero (x₀ : d → ℝ) (ℓ h : ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (x : d → ℝ) (hG : coarseBump x₀ h x = 0) :
    physicalRoughField x₀ ℓ h ζ x = 0 := by
  simp only [physicalRoughField_eq_sum, packet, hG, zero_mul, Finset.sum_const_zero]

theorem physicalRoughField_moments (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h)
    (x : d → ℝ) :
    independentSigns.expect (fun ζ => physicalRoughField x₀ ℓ h ζ x) = 0 ∧
    independentSigns.expect (fun ζ => physicalRoughField x₀ ℓ h ζ x ^ 2) = coarseBump x₀ h x ^ 2 ∧
    independentSigns.expect (fun ζ => physicalRoughField x₀ ℓ h ζ x ^ 3) = 0 ∧
    independentSigns.expect (fun ζ => physicalRoughField x₀ ℓ h ζ x ^ 4) =
      coarseBump x₀ h x ^ 4 * (3 - 2 * quarticField (activeBlocks ℓ h) x₀ ℓ x) := by
  have hm := independentSignSum_moments (physicalJitterWeights x₀ ℓ h 1 1 x)
  have hv := physicalJitter_variance x₀ ℓ h 1 1 hℓ hh x
  have hf := physicalJitter_fourth_sum x₀ ℓ h 1 1 hℓ x
  simp only [one_pow, one_mul] at hv hf
  refine ⟨hm.1, hm.2.1.trans hv, hm.2.2.1, ?_⟩
  change independentSigns.expect (fun ζ => independentSignSum (physicalJitterWeights x₀ ℓ h 1 1 x) ζ ^ 4) = _
  rw [hm.2.2.2, hv, hf]
  ring

theorem physicalRoughCorrection_identity (x₀ : d → ℝ) (ℓ h ja jb : ℝ)
    (hℓ : 0 < ℓ) (hh : 0 < h) (x : d → ℝ) :
    (ja * jb * coarseBump x₀ h x ^ 2) * physicalRoughCorrection x₀ ℓ h ja x =
      ja ^ 3 * jb * independentSigns.expect (fun ζ => physicalRoughField x₀ ℓ h ζ x ^ 4) := by
  rw [(physicalRoughField_moments x₀ ℓ h hℓ hh x).2.2.2]
  unfold physicalRoughCorrection
  ring

theorem physicalRoughCorrection_bounds (x₀ : d → ℝ) (ℓ h ja : ℝ) (hℓ : 0 < ℓ) (x : d → ℝ) :
    0 ≤ physicalRoughCorrection x₀ ℓ h ja x ∧ physicalRoughCorrection x₀ ℓ h ja x ≤ 3 * ja ^ 2 := by
  have hq := quarticField_bounds (activeBlocks (d := d) ℓ h) x₀ ℓ hℓ x
  have hG := coarseBump_range x₀ h x
  have hG2 : coarseBump x₀ h x ^ 2 ≤ 1 := by nlinarith
  refine ⟨mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by linarith), ?_⟩
  change ja ^ 2 * coarseBump x₀ h x ^ 2 * (3 - 2 * quarticField (activeBlocks ℓ h) x₀ ℓ x) ≤ _
  calc
    _ ≤ ja ^ 2 * coarseBump x₀ h x ^ 2 * 3 :=
      mul_le_mul_of_nonneg_left (by linarith [hq.1]) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ ja ^ 2 * 1 * 3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG2 (sq_nonneg _)) (by norm_num)
    _ = _ := by ring

theorem physicalRoughPropensity_bridge (x₀ : d → ℝ) (ℓ h R T ja jb : ℝ)
    (hℓ : 0 < ℓ) (hh : 0 < h) (x : d → ℝ) (f : ℕ) (hf : f ≤ 1) :
    independentSigns.expect (fun ζ =>
      RoughPropensity.substitution f ja (coarseBump x₀ h x ^ 2) (physicalRoughField x₀ ℓ h ζ x) *
      RoughPropensity.increment R T ja jb (physicalRoughField x₀ ℓ h ζ x)) =
    independentSigns.expect (fun ζ => physicalRoughField x₀ ℓ h ζ x ^ f *
      RoughPropensity.realField R T ja (ja * jb * coarseBump x₀ h x ^ 2) (physicalRoughField x₀ ℓ h ζ x)) := by
  have hm := physicalRoughField_moments x₀ ℓ h hℓ hh x
  exact RoughPropensity.design_weighted_bridge _ _ _ _ _ _ _ hm.1 hm.2.1 f hf

theorem physicalRoughOutcome_bridge (x₀ : d → ℝ) (ℓ h R T ja jb p : ℝ)
    (hℓ : 0 < ℓ) (hh : 0 < h) (x : d → ℝ) (f : ℕ) :
    let X := fun ζ => physicalRoughField x₀ ℓ h ζ x
    let η := physicalRoughCorrection x₀ ℓ h ja x
    independentSigns.expect (fun ζ =>
      RoughOutcome.substitution 1 f independentSigns X (X ζ) * RoughOutcome.incrementOne R T ja jb η p (X ζ) +
      RoughOutcome.substitution 2 f independentSigns X (X ζ) * RoughOutcome.incrementTwo R T ja jb p (X ζ) +
      RoughOutcome.substitution 3 f independentSigns X (X ζ) * RoughOutcome.incrementThree R T ja jb (X ζ)) =
    independentSigns.expect (fun ζ => X ζ ^ f * RoughOutcome.realField R T p (ja * jb * coarseBump x₀ h x ^ 2)) := by
  have hm := physicalRoughField_moments x₀ ℓ h hℓ hh x
  exact RoughOutcome.design_weighted_bridge _ _ _ _ _ _ _ _ _ hm.1 hm.2.1 hm.2.2.1
    (physicalRoughCorrection_identity x₀ ℓ h ja jb hℓ hh x) f

end CausalLowerbound.PartC
