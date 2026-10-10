import CausalLowerbound.UpperBound.Covariance
import Mathlib.MeasureTheory.Integral.Prod

/-! The exact covariance identity for two tuples sharing some coordinates.

`A` is the space of shared observations and `B` is the space of the remaining
observations.  The two copies of `B` are independent conditional on `A`.
Only a second moment of the kernel is required. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory

namespace CausalLowerbound.UpperBound

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable (μ : Measure A) (ν : Measure B)
variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Integrate out the coordinates that the two tuples do not share. -/
def partialKernel (K : A × B → ℝ) (a : A) : ℝ := ∫ b, K (a, b) ∂ν

theorem completion_fst_measurePreserving :
    MeasurePreserving (fun z : A × (B × B) => (z.1, z.2.1))
      (μ.prod (ν.prod ν)) (μ.prod ν) := by
  have hf : MeasurePreserving (Prod.fst : B × B → B) (ν.prod ν) ν :=
    ⟨measurable_fst, by simp⟩
  exact (MeasurePreserving.id μ).prod hf

theorem completion_snd_measurePreserving :
    MeasurePreserving (fun z : A × (B × B) => (z.1, z.2.2))
      (μ.prod (ν.prod ν)) (μ.prod ν) := by
  have hf : MeasurePreserving (Prod.snd : B × B → B) (ν.prod ν) ν :=
    ⟨measurable_snd, by simp⟩
  exact (MeasurePreserving.id μ).prod hf

theorem completion_fst_memLp {K : A × B → ℝ} (hK : MemLp K 2 (μ.prod ν)) :
    MemLp (fun z : A × (B × B) => K (z.1, z.2.1)) 2 (μ.prod (ν.prod ν)) :=
  hK.comp_measurePreserving (completion_fst_measurePreserving μ ν)

theorem completion_snd_memLp {K : A × B → ℝ} (hK : MemLp K 2 (μ.prod ν)) :
    MemLp (fun z : A × (B × B) => K (z.1, z.2.2)) 2 (μ.prod (ν.prod ν)) :=
  hK.comp_measurePreserving (completion_snd_measurePreserving μ ν)

theorem integral_shared_completion_product {K : A × B → ℝ}
    (hK : MemLp K 2 (μ.prod ν)) :
    (∫ z : A × (B × B), K (z.1, z.2.1) * K (z.1, z.2.2)
      ∂μ.prod (ν.prod ν)) = ∫ a, partialKernel ν K a ^ 2 ∂μ := by
  have hp := (completion_fst_memLp μ ν hK).integrable_mul
    (completion_snd_memLp μ ν hK)
  rw [integral_prod (fun z : A × (B × B) => K (z.1, z.2.1) * K (z.1, z.2.2)) hp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    simpa only [partialKernel, pow_two] using
      (integral_prod_mul (μ := ν) (ν := ν) (fun b => K (a, b)) (fun b => K (a, b)))

theorem partialKernel_memLp {K : A × B → ℝ} (hK : MemLp K 2 (μ.prod ν)) :
    MemLp (partialKernel ν K) 2 μ := by
  have hi := (hK.integrable one_le_two).integral_prod_left
  refine (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).mpr ?_
  have hp := ((completion_fst_memLp μ ν hK).integrable_mul
    (completion_snd_memLp μ ν hK)).integral_prod_left
  have he (a : A) :
      (∫ b : B × B, K (a, b.1) * K (a, b.2) ∂ν.prod ν) = partialKernel ν K a ^ 2 := by
    simpa only [partialKernel, pow_two] using
      (integral_prod_mul (μ := ν) (ν := ν) (fun b => K (a, b)) (fun b => K (a, b)))
  simpa only [Pi.mul_apply, he] using hp

theorem integral_partialKernel {K : A × B → ℝ} (hK : Integrable K (μ.prod ν)) :
    (∫ a, partialKernel ν K a ∂μ) = ∫ z, K z ∂μ.prod ν :=
  (integral_prod K hK).symm

theorem integral_completion_fst {K : A × B → ℝ} (hK : MemLp K 2 (μ.prod ν)) :
    (∫ z : A × (B × B), K (z.1, z.2.1) ∂μ.prod (ν.prod ν)) =
      ∫ a, partialKernel ν K a ∂μ := by
  rw [integral_prod _ ((completion_fst_memLp μ ν hK).integrable one_le_two)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    simpa only [measureReal_univ_eq_one, one_smul, partialKernel] using
      (integral_fun_fst (μ := ν) (ν := ν) (fun b => K (a, b)))

theorem integral_completion_snd {K : A × B → ℝ} (hK : MemLp K 2 (μ.prod ν)) :
    (∫ z : A × (B × B), K (z.1, z.2.2) ∂μ.prod (ν.prod ν)) =
      ∫ a, partialKernel ν K a ∂μ := by
  rw [integral_prod _ ((completion_snd_memLp μ ν hK).integrable one_le_two)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    simpa only [measureReal_univ_eq_one, one_smul, partialKernel] using
      (integral_fun_snd (μ := ν) (ν := ν) (fun b => K (a, b)))

/-- The covariance of overlapping tuples is the variance of their shared
projection.  This supplies the probabilistic step behind the overlap ledger. -/
theorem covariance_shared_completion {K : A × B → ℝ} (hK : MemLp K 2 (μ.prod ν)) :
    covariance (μ.prod (ν.prod ν))
      (fun z : A × (B × B) => K (z.1, z.2.1))
      (fun z : A × (B × B) => K (z.1, z.2.2)) =
      variance μ (partialKernel ν K) := by
  rw [covariance, integral_shared_completion_product μ ν hK,
    integral_completion_fst μ ν hK, integral_completion_snd μ ν hK,
    variance_eq_secondMoment_sub, pow_two]

theorem covariance_shared_completion_nonneg {K : A × B → ℝ}
    (hK : MemLp K 2 (μ.prod ν)) :
    0 ≤ covariance (μ.prod (ν.prod ν))
      (fun z : A × (B × B) => K (z.1, z.2.1))
      (fun z : A × (B × B) => K (z.1, z.2.2)) := by
  rw [covariance_shared_completion μ ν hK]
  exact variance_nonneg μ (partialKernel_memLp μ ν hK)

theorem covariance_shared_completion_le_secondMoment {K : A × B → ℝ}
    (hK : MemLp K 2 (μ.prod ν)) :
    covariance (μ.prod (ν.prod ν))
      (fun z : A × (B × B) => K (z.1, z.2.1))
      (fun z : A × (B × B) => K (z.1, z.2.2)) ≤
      ∫ a, partialKernel ν K a ^ 2 ∂μ := by
  rw [covariance_shared_completion μ ν hK]
  exact variance_le_secondMoment μ _

end CausalLowerbound.UpperBound
