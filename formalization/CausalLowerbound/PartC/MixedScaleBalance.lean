import CausalLowerbound.PartC.Scales

/-! Exact amplitude identities for the actual fine-scale rough fields. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound.PartC

def roughScale (A d γ s ε : ℝ) (n : ℕ) : ℝ :=
  jitterScale A d γ s ε n * carrierScale A d ε n

theorem roughScale_bounds (A d γ s ε : ℝ) (hA : 0 < A) (hd : 0 < d)
    (hγ : 0 < γ) (hs : 0 < s) (hreg : A * (2 + d / γ) < d) (hε : 0 < ε)
    (hεsmall : ε < γ / d - rateExponent A d γ s) (n : ℕ) :
    0 < roughScale A d γ s ε n ∧ roughScale A d γ s ε n ≤ carrierScale A d ε n := by
  have hb := scales_balanced A d γ s ε hA hd hγ hs hreg hε hεsmall n
  exact ⟨mul_pos hb.2.2.2.1 hb.1,
    mul_le_of_le_one_left hb.1.le hb.2.2.2.2.1⟩

theorem mixed_amplitude_factorization (u v r t : ℝ) (hr : 0 < r) (ht : 0 < t) :
    (t * r) ^ u * r ^ v * t = r ^ (u + v) * t ^ (u + 1) := by
  rw [Real.mul_rpow ht.le hr.le, Real.rpow_add hr, Real.rpow_add ht, Real.rpow_one]
  ring

theorem roughPropensity_scale_balance (α β d γ ε : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : α ≤ β) (hd : 0 < d) (hγ : 0 < γ)
    (hreg : (α + β) * (2 + d / γ) < d) (hε : 0 < ε)
    (hεsmall : ε < γ / d - rateExponent (α + β) d γ (effectiveSmoothness α β)) (n : ℕ) :
    let s := effectiveSmoothness α β
    roughScale (α + β) d γ s ε n ^ α * carrierScale (α + β) d ε n ^ β *
      jitterScale (α + β) d γ s ε n = coarseScale (α + β) d γ s ε n ^ γ := by
  have hb := scales_balanced (α + β) d γ (effectiveSmoothness α β) ε
    (add_pos hα hβ) hd hγ (effectiveSmoothness_pos α β hα hβ) hreg hε hεsmall n
  have hs : 2 * effectiveSmoothness α β = α + 1 := by
    rw [effectiveSmoothness, min_eq_left hαβ]
    ring
  dsimp only
  rw [roughScale, mixed_amplitude_factorization _ _ _ _ hb.1 hb.2.2.2.1, ← hs]
  exact hb.2.2.2.2.2.symm

theorem roughOutcome_scale_balance (α β d γ ε : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hβα : β ≤ α) (hd : 0 < d) (hγ : 0 < γ)
    (hreg : (α + β) * (2 + d / γ) < d) (hε : 0 < ε)
    (hεsmall : ε < γ / d - rateExponent (α + β) d γ (effectiveSmoothness α β)) (n : ℕ) :
    let s := effectiveSmoothness α β
    carrierScale (α + β) d ε n ^ α * jitterScale (α + β) d γ s ε n *
      roughScale (α + β) d γ s ε n ^ β = coarseScale (α + β) d γ s ε n ^ γ := by
  have hb := scales_balanced (α + β) d γ (effectiveSmoothness α β) ε
    (add_pos hα hβ) hd hγ (effectiveSmoothness_pos α β hα hβ) hreg hε hεsmall n
  have hs : 2 * effectiveSmoothness α β = β + 1 := by
    rw [effectiveSmoothness, min_eq_right hβα]
    ring
  have hf := mixed_amplitude_factorization β α (carrierScale (α + β) d ε n)
    (jitterScale (α + β) d γ (effectiveSmoothness α β) ε n) hb.1 hb.2.2.2.1
  rw [add_comm β α, ← hs, ← hb.2.2.2.2.2] at hf
  dsimp only
  unfold roughScale
  calc
    _ = (jitterScale (α + β) d γ (effectiveSmoothness α β) ε n * carrierScale (α + β) d ε n) ^ β *
        carrierScale (α + β) d ε n ^ α * jitterScale (α + β) d γ (effectiveSmoothness α β) ε n := by ring
    _ = _ := hf

end CausalLowerbound.PartC
