import CausalLowerbound.PartB.NuisanceLegality

/-! Explicit polynomial fine/coarse scales satisfy the exact balance used
in the uniform legality theorem. Rate optimization is a separate step. -/
noncomputable section
set_option autoImplicit false
namespace CausalLowerbound.PartB.ShellGeometry

theorem polynomial_scales_balanced (α β γ z ξ x : ℝ) (hx : 1 ≤ x)
    (hγ : 0 < γ) (hz : 0 ≤ z) (hξ : z / γ ≤ ξ) (hp : 0 ≤ (z - ξ * (α + β)) / 2) :
    let r := x ^ (-ξ)
    let h := x ^ (-(z / γ))
    let t := x ^ (-((z - ξ * (α + β)) / 2))
    0 < r ∧ r ≤ h ∧ h ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧ h ^ γ = r ^ (α + β) * t ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  dsimp
  refine ⟨Real.rpow_pos_of_pos hx0 _, Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hξ),
    Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr (div_nonneg hz hγ.le)),
    Real.rpow_nonneg hx0.le _, Real.rpow_le_one_of_one_le_of_nonpos hx (neg_nonpos.mpr hp), ?_⟩
  rw [← Real.rpow_natCast (n := 2)]
  simp only [← Real.rpow_mul hx0.le]
  rw [← Real.rpow_add hx0]
  congr 1
  field_simp
  ring

end CausalLowerbound.PartB.ShellGeometry
