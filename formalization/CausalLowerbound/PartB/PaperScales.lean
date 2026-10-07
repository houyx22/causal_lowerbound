import CausalLowerbound.PartB.RateRegime

/-! Fixed polynomial scales and the exact target separation, with the
small-amplitude inequalities needed by the physical information bound. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound.PartB

def paperFineScale (A D ε : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-carrierExponent A D ε)
def paperCoarseScale (A D γ ε : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-((rateExponent A D γ + ε) / γ))
def paperSignalScale (A D γ ε : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-(rateExponent A D γ + ε))
def paperJitterScale (A D γ ε : ℝ) (n : ℕ) : ℝ := polynomialAmplitude (jitterExponent A D γ ε) ((n : ℝ) + 1)

theorem paper_scales_balanced (α β D γ ε : ℝ)
    (hA : 0 < α + β) (hD : 0 < D) (hγ : 0 < γ)
    (hreg : (α + β) * (2 + D / γ) < D) (hε : 0 < ε)
    (hεsmall : ε < γ / D - rateExponent (α + β) D γ) (n : ℕ) :
    let r := paperFineScale (α + β) D ε n
    let h := paperCoarseScale (α + β) D γ ε n
    let t := paperJitterScale (α + β) D γ ε n
    0 < r ∧ r ≤ h ∧ h ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ h ^ γ = r ^ (α + β) * t ^ 2 := by
  have he := concrete_scale_exponents (α + β) D γ ε hA hD hγ hreg hε hεsmall
  exact ShellGeometry.polynomial_scales_balanced α β γ
    (rateExponent (α + β) D γ + ε) (carrierExponent (α + β) D ε) ((n : ℝ) + 1)
    (le_add_of_nonneg_left (Nat.cast_nonneg n)) hγ he.1.le he.2.1.le he.2.2.le

theorem paper_coarse_signal (A D γ ε : ℝ) (hγ : γ ≠ 0) (n : ℕ) :
    paperCoarseScale A D γ ε n ^ γ = paperSignalScale A D γ ε n := by
  unfold paperCoarseScale paperSignalScale
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
  congr 1
  field_simp

theorem paper_target_balance (α β D γ ε ca cb : ℝ)
    (hA : 0 < α + β) (hD : 0 < D) (hγ : 0 < γ)
    (hreg : (α + β) * (2 + D / γ) < D) (hε : 0 < ε)
    (hεsmall : ε < γ / D - rateExponent (α + β) D γ) (n : ℕ) :
    (ca * paperFineScale (α + β) D ε n ^ α) * (cb * paperFineScale (α + β) D ε n ^ β) *
        paperJitterScale (α + β) D γ ε n ^ 2 = ca * cb * paperSignalScale (α + β) D γ ε n := by
  have hs := paper_scales_balanced α β D γ ε hA hD hγ hreg hε hεsmall n
  rw [← paper_coarse_signal (α + β) D γ ε hγ.ne', hs.2.2.2.2.2,
    Real.rpow_add hs.1 α β]
  ring

theorem paper_amplitude_bounds (α β D γ ε ca cb : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hA : 0 < α + β) (hD : 0 < D) (hγ : 0 < γ)
    (hreg : (α + β) * (2 + D / γ) < D) (hε : 0 < ε)
    (hεsmall : ε < γ / D - rateExponent (α + β) D γ)
    (hca : 0 < ca) (hca1 : ca ≤ 1 / 2) (hcb : 0 < cb) (hcb1 : cb ≤ 1 / 2) (n : ℕ) :
    let r := paperFineScale (α + β) D ε n
    let t := paperJitterScale (α + β) D γ ε n
    let a := ca * r ^ α
    let b := cb * r ^ β
    0 < a ∧ 0 ≤ b ∧ a ^ 2 * t ^ 2 ≤ 1 ∧ a * b * t ^ 2 ≤ 1 / 2 := by
  have hs := paper_scales_balanced α β D γ ε hA hD hγ hreg hε hεsmall n
  dsimp only
  let r := paperFineScale (α + β) D ε n
  let t := paperJitterScale (α + β) D γ ε n
  have hr1 : r ≤ 1 := hs.2.1.trans hs.2.2.1
  have ha : 0 < ca * r ^ α := mul_pos hca (Real.rpow_pos_of_pos hs.1 _)
  have hb : 0 < cb * r ^ β := mul_pos hcb (Real.rpow_pos_of_pos hs.1 _)
  have ha1 : ca * r ^ α ≤ 1 / 2 :=
    (mul_le_of_le_one_right hca.le (Real.rpow_le_one hs.1.le hr1 hα)).trans hca1
  have hb1 : cb * r ^ β ≤ 1 / 2 :=
    (mul_le_of_le_one_right hcb.le (Real.rpow_le_one hs.1.le hr1 hβ)).trans hcb1
  have ht0 : 0 ≤ t := hs.2.2.2.1
  have ht1 : t ≤ 1 := hs.2.2.2.2.1
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have ha2 : (ca * r ^ α) ^ 2 ≤ 1 := by nlinarith
  have hab : (ca * r ^ α) * (cb * r ^ β) ≤ 1 / 2 := by
    have he := mul_le_mul ha1 hb1 hb.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    linarith
  exact ⟨ha, hb.le, (mul_le_of_le_one_right (sq_nonneg _) ht2).trans ha2,
    (mul_le_of_le_one_right (mul_nonneg ha.le hb.le) ht2).trans hab⟩

end CausalLowerbound.PartB
