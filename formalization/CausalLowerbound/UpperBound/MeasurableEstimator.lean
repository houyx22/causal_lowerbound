import CausalLowerbound.UpperBound.MatrixOperators
import CausalLowerbound.UpperBound.EmpiricalStatistics
import CausalLowerbound.UpperBound.RiskReduction

/-! Borel measurability of the actual clipped estimating-equation solution.
The good-matrix set is closed, and the finite-dimensional truncated inverse
agrees there with mathlib's measurable matrix inverse. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

variable {I : Type*} [Fintype I]

theorem matrixLowerBound_isClosed (κ : ℝ) :
    IsClosed {A : Matrix I I ℝ | ∀ x : I → ℝ, κ * ‖x‖ ≤ ‖A *ᵥ x‖} := by
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro x
  have hm : Continuous (fun A : Matrix I I ℝ => A *ᵥ x) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  exact isClosed_le continuous_const hm.norm

theorem truncatedSolve_matrix_eq {κ : ℝ} (hκ : 0 < κ) (A : Matrix I I ℝ) (b : I → ℝ) :
    truncatedSolve κ hκ (matrixOperator A) b =
      if (∀ x : I → ℝ, κ * ‖x‖ ≤ ‖A *ᵥ x‖) then A⁻¹ *ᵥ b else 0 := by
  by_cases hA : ∀ x : I → ℝ, κ * ‖x‖ ≤ ‖A *ᵥ x‖
  · rw [if_pos hA]
    have hinj := lower_bound_injective (matrixOperator A) hκ hA
    have hdet := (Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
    apply hinj
    rw [apply_truncatedSolve_of_lower_bound hκ _ _ hA, matrixOperator_apply,
      Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  · have hA' : ¬ ∀ x : I → ℝ, κ * ‖x‖ ≤ ‖matrixOperator A x‖ := hA
    rw [if_neg hA, truncatedSolve, dif_neg hA']

theorem truncatedSolve_matrix_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    {κ : ℝ} (hκ : 0 < κ) (A : Ω → Matrix I I ℝ) (b : Ω → I → ℝ)
    (hA : Measurable A) (hb : Measurable b) :
    Measurable (fun z => truncatedSolve κ hκ (matrixOperator (A z)) (b z)) := by
  have he : (fun z => truncatedSolve κ hκ (matrixOperator (A z)) (b z)) =
      (fun z => if (∀ x : I → ℝ, κ * ‖x‖ ≤ ‖A z *ᵥ x‖) then
        interpolationCoefficients (A z) (b z) else 0) :=
    funext (fun z => truncatedSolve_matrix_eq hκ (A z) (b z))
  rw [he]
  exact Measurable.ite ((matrixLowerBound_isClosed (I := I) κ).measurableSet.preimage hA)
    (measurable_interpolationCoefficients A b hA hb) measurable_const

theorem clip_continuous (L : ℝ) : Continuous (clip L) :=
  continuous_const.max (continuous_const.min continuous_id)

variable {d : Type*} [Fintype d]

def empiricalStencilEstimate (p : ℕ) (T : StencilTemplate d p) (x₀ : d → ℝ) (h ℓ r : ℝ)
    (J : StencilRole d p → Type*) [∀ i, Fintype (J i)]
    (κ : ℝ) (hκ : 0 < κ) (L : ℝ)
    (z : (Σ i, J i) → (d → ℝ) × (Bool × ℝ)) : ℝ :=
  clip L ((truncatedSolve κ hκ
    (matrixOperator (empiricalStencilMatrix p T x₀ h ℓ r J z))
    (empiricalStencilResponse p T x₀ h ℓ r J z)) 0)

theorem empiricalStencilEstimate_measurable (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (J : StencilRole d p → Type*) [∀ i, Fintype (J i)]
    {κ : ℝ} (hκ : 0 < κ) (L : ℝ) :
    Measurable (empiricalStencilEstimate p T x₀ h ℓ r J κ hκ L) := by
  have hm := truncatedSolve_matrix_measurable_comp hκ
    (empiricalStencilMatrix p T x₀ h ℓ r J) (empiricalStencilResponse p T x₀ h ℓ r J)
    (empiricalStencilMatrix_measurable p T x₀ h ℓ r J) (empiricalStencilResponse_measurable p T x₀ h ℓ r J)
  exact (clip_continuous L).measurable.comp ((measurable_pi_apply 0).comp hm)

theorem empiricalStencilEstimate_eq_clippedEstimate (p : ℕ) (T : StencilTemplate d p)
    (x₀ : d → ℝ) (h ℓ r : ℝ) (J : StencilRole d p → Type*) [∀ i, Fintype (J i)]
    {κ : ℝ} (hκ : 0 < κ) (L : ℝ) (z : (Σ i, J i) → (d → ℝ) × (Bool × ℝ)) :
    empiricalStencilEstimate p T x₀ h ℓ r J κ hκ L z =
      clippedEstimate κ hκ L (ContinuousLinearMap.proj (0 : TensorIndex d p))
        (matrixOperator (empiricalStencilMatrix p T x₀ h ℓ r J z))
        (empiricalStencilResponse p T x₀ h ℓ r J z) := rfl

end CausalLowerbound.UpperBound
