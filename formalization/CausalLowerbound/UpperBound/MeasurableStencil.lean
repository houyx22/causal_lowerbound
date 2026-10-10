import CausalLowerbound.UpperBound.CompletedStencil
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! The stencil is measurable even off the accepted event: the matrix
inverse in mathlib is defined to be zero at singular matrices. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

instance matrixMeasurableSpace (I J : Type*) : MeasurableSpace (Matrix I J ℝ) :=
  inferInstanceAs (MeasurableSpace (I → J → ℝ))

instance matrixBorelSpace (I J : Type*) [Fintype I] [Fintype J] : BorelSpace (Matrix I J ℝ) :=
  inferInstanceAs (BorelSpace (I → J → ℝ))

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem measurable_matrix_inverse : Measurable (fun A : Matrix I I ℝ => A⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact continuous_id.matrix_det.measurable.inv.smul continuous_id.matrix_adjugate.measurable

theorem measurable_matrix_inverse_entry (i j : I) :
    Measurable (fun A : Matrix I I ℝ => A⁻¹ i j) :=
  ((measurable_pi_apply j).comp (measurable_pi_apply i)).comp measurable_matrix_inverse

theorem measurable_interpolationCoefficients {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix I I ℝ) (b : Ω → I → ℝ) (hA : Measurable A) (hb : Measurable b) :
    Measurable (fun x => interpolationCoefficients (A x) (b x)) := by
  apply measurable_pi_lambda
  intro j
  unfold interpolationCoefficients Matrix.mulVec dotProduct
  apply Finset.measurable_sum
  intro ν _
  exact ((measurable_matrix_inverse_entry j ν).comp hA).mul ((measurable_pi_apply ν).comp hb)

omit [Fintype I] [DecidableEq I] in
theorem continuous_completedCoefficients : Continuous (completedCoefficients (J := I)) := by
  apply continuous_pi
  intro i
  cases i <;> simp only [completedCoefficients, Option.elim'_none, Option.elim'_some]
  · exact continuous_const
  · exact continuous_apply _

omit [DecidableEq I] in
theorem continuous_completedStencil (i : Option (Option I)) :
    Continuous (fun c : I → ℝ => completedStencil c i) :=
  (continuous_normalizedStencil i).comp continuous_completedCoefficients

variable {d : Type*} [Fintype d]

theorem measurable_tensorContrastCoefficients (p : ℕ) :
    Measurable (fun zv : (TensorIndex d p → d → ℝ) × (d → ℝ) =>
      tensorContrastCoefficients p zv.1 zv.2) := by
  have hA : Measurable (fun zv : (TensorIndex d p → d → ℝ) × (d → ℝ) =>
      tensorEvaluation p zv.1) := by
    apply measurable_pi_lambda
    intro ν
    apply measurable_pi_lambda
    intro j
    exact (continuous_tensorMonomial p ν).measurable.comp
      ((measurable_pi_apply j).comp measurable_fst)
  have hb : Measurable (fun zv : (TensorIndex d p → d → ℝ) × (d → ℝ) =>
      fun ν => tensorMonomial p ν zv.2 - tensorMonomial p ν 0) := by
    apply measurable_pi_lambda
    intro ν
    exact ((continuous_tensorMonomial p ν).measurable.comp measurable_snd).sub measurable_const
  exact measurable_interpolationCoefficients _ _ hA hb

theorem measurable_tensorContrastWeights (p : ℕ) :
    Measurable (fun zv : (TensorIndex d p → d → ℝ) × (d → ℝ) =>
      tensorContrastWeights p zv.1 zv.2) := by
  apply measurable_pi_lambda
  intro i
  exact (continuous_completedStencil i).measurable.comp (measurable_tensorContrastCoefficients p)

theorem measurable_tensorContrastWeights_comp {Ω : Type*} [MeasurableSpace Ω]
    (p : ℕ) (z : Ω → TensorIndex d p → d → ℝ) (v : Ω → d → ℝ)
    (hz : Measurable z) (hv : Measurable v) :
    Measurable (fun x => tensorContrastWeights p (z x) (v x)) := by
  have hpair := hz.prodMk hv
  have hweight := measurable_tensorContrastWeights (d := d) p
  have h := hweight.comp hpair
  exact h

end CausalLowerbound.UpperBound
