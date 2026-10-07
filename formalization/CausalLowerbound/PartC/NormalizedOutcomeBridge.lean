import CausalLowerbound.PartC.NormalizedRoughMoments

/-! The cubic design-weighted bridge in the actual carrier normalization.
The fourth-moment correction uses the effective shift `shift * scale`.
There is no division by `scale`, so the identities include zero assignment. -/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartC.RoughOutcome
variable {Ω : Type*} [Fintype Ω]

def normalizedSubstitution (e : ℕ) (f : Fin 4) (scale v X : ℝ) : ℝ :=
  Representative.outcomeMoment (scale ^ 2 * v) f * (scale * X) ^ e

theorem normalizedMoment_eq_expect (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (v scale : ℝ) (hmean : μ.expect X = 0) (hvar : μ.expect (fun ω => X ω ^ 2) = v)
    (hthird : μ.expect (fun ω => X ω ^ 3) = 0) (f : Fin 4) :
    Representative.outcomeMoment (scale ^ 2 * v) f =
      μ.expect (fun ω => (scale * X ω) ^ f.val) := by
  apply Representative.outcomeMoment_eq_expect μ _ _ _ _ _ f
  · rw [μ.expect_mul, hmean, mul_zero]
  · simp only [mul_pow, μ.expect_mul, hvar]
  · simp only [mul_pow, μ.expect_mul, hthird, mul_zero]

theorem normalized_design_weighted_bridge (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (R T shift jb η ζ v scale : ℝ) (hmean : μ.expect X = 0)
    (hvar : μ.expect (fun ω => X ω ^ 2) = v) (hthird : μ.expect (fun ω => X ω ^ 3) = 0)
    (hcorrection : ((shift * scale) * jb * v) * η =
      (shift * scale) ^ 3 * jb * μ.expect (fun ω => X ω ^ 4)) (f : Fin 4) :
    μ.expect (fun ω =>
      normalizedSubstitution 1 f scale v (X ω) * incrementOne R T shift jb η ζ (X ω) +
      normalizedSubstitution 2 f scale v (X ω) * incrementTwo R T shift jb ζ (X ω) +
      normalizedSubstitution 3 f scale v (X ω) * incrementThree R T shift jb (X ω)) =
    μ.expect (fun ω => (scale * X ω) ^ f.val * realField R T ζ ((shift * scale) * jb * v)) := by
  calc
    _ = μ.expect (fun ω => μ.expect (fun ξ => (scale * X ξ) ^ f.val) *
        totalIncrement R T (shift * scale) jb η ζ (X ω)) := by
      apply μ.expect_congr
      intro ω
      simp only [normalizedSubstitution, normalizedMoment_eq_expect μ X v scale hmean hvar hthird f]
      unfold totalIncrement incrementOne incrementTwo incrementThree
      ring
    _ = μ.expect (fun ω => (scale * X ω) ^ f.val) * realField R T ζ ((shift * scale) * jb * v) := by
      rw [μ.expect_mul, mean_increment μ X R T (shift * scale) jb η ζ v hmean hvar hthird hcorrection]
    _ = _ := (μ.expect_mul_const _ _).symm

theorem normalized_cell_bridge (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (R T shift jb η ζ v scale : ℝ) (hmean : μ.expect X = 0)
    (hvar : μ.expect (fun ω => X ω ^ 2) = v) (hthird : μ.expect (fun ω => X ω ^ 3) = 0)
    (hcorrection : ((shift * scale) * jb * v) * η =
      (shift * scale) ^ 3 * jb * μ.expect (fun ω => X ω ^ 4)) (f : Fin 4) :
    μ.expect (fun ω => (scale * X ω) ^ f.val * likelihood R T jb η ζ (X ω) +
      (normalizedSubstitution 1 f scale v (X ω) * incrementOne R T shift jb η ζ (X ω) +
        normalizedSubstitution 2 f scale v (X ω) * incrementTwo R T shift jb ζ (X ω) +
        normalizedSubstitution 3 f scale v (X ω) * incrementThree R T shift jb (X ω))) =
      μ.expect (fun ω => (scale * X ω) ^ f.val *
        (likelihood R T jb η ζ (X ω) + realField R T ζ ((shift * scale) * jb * v))) := by
  rw [μ.expect_add, normalized_design_weighted_bridge μ X R T shift jb η ζ v scale
    hmean hvar hthird hcorrection f]
  simp only [mul_add, μ.expect_add]

theorem normalized_physical_bridge {d : Type*} [Fintype d] [DecidableEq d]
    (x₀ : d → ℝ) (ℓ h R T shift jb ζ scale : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h)
    (x : d → ℝ) (f : Fin 4) :
    let X := fun ξ => physicalRoughField x₀ ℓ h ξ x
    let v := PartB.ShellGeometry.coarseBump x₀ h x ^ 2
    let η := physicalRoughCorrection x₀ ℓ h (shift * scale) x
    PartB.independentSigns.expect (fun ξ =>
      normalizedSubstitution 1 f scale v (X ξ) * incrementOne R T shift jb η ζ (X ξ) +
      normalizedSubstitution 2 f scale v (X ξ) * incrementTwo R T shift jb ζ (X ξ) +
      normalizedSubstitution 3 f scale v (X ξ) * incrementThree R T shift jb (X ξ)) =
    PartB.independentSigns.expect (fun ξ => (scale * X ξ) ^ f.val *
      realField R T ζ ((shift * scale) * jb * v)) := by
  have hm := physicalRoughField_moments x₀ ℓ h hℓ hh x
  exact normalized_design_weighted_bridge PartB.independentSigns _ R T shift jb _ ζ _ scale
    hm.1 hm.2.1 hm.2.2.1 (physicalRoughCorrection_identity x₀ ℓ h (shift * scale) jb hℓ hh x) f

end CausalLowerbound.PartC.RoughOutcome
