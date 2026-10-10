import CausalLowerbound.CommonMarginalTesting
import Mathlib.MeasureTheory.Function.L2Space

/-! Covariance and finite-sum second moments for the two-scale upper bound.

The summands in a tuple estimator overlap and are not independent.  These
identities therefore retain every cross term.  All uses of real-valued
integrals have explicit integrability hypotheses; the outcome need not be
bounded or discrete. -/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace CausalLowerbound.UpperBound

variable {Ω : Type*} [MeasurableSpace Ω]

def covariance (μ : Measure Ω) (f g : Ω → ℝ) : ℝ :=
  (∫ x, f x * g x ∂μ) - (∫ x, f x ∂μ) * (∫ x, g x ∂μ)

def variance (μ : Measure Ω) (f : Ω → ℝ) : ℝ := covariance μ f f

@[simp] theorem variance_const (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) :
    variance μ (fun _ => c) = 0 := by
  simp [variance, covariance]

theorem covariance_comm (μ : Measure Ω) (f g : Ω → ℝ) :
    covariance μ f g = covariance μ g f := by
  simp only [covariance, mul_comm]

theorem variance_eq_secondMoment_sub (μ : Measure Ω) (f : Ω → ℝ) :
    variance μ f = (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
  simp only [variance, covariance, pow_two]

theorem covariance_eq_centered {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    covariance μ f g =
      ∫ x, (f x - ∫ y, f y ∂μ) * (g x - ∫ y, g y ∂μ) ∂μ := by
  have hfg : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have hfc := (hf.integrable one_le_two).mul_const (∫ y, g y ∂μ)
  have hgc := (hg.integrable one_le_two).const_mul (∫ y, f y ∂μ)
  have he (x : Ω) :
      (f x - ∫ y, f y ∂μ) * (g x - ∫ y, g y ∂μ) =
        ((f x * g x - f x * ∫ y, g y ∂μ) - (∫ y, f y ∂μ) * g x) +
          (∫ y, f y ∂μ) * (∫ y, g y ∂μ) := by ring
  simp_rw [he]
  rw [integral_add (f := fun x => (f x * g x - f x * ∫ y, g y ∂μ) -
      (∫ y, f y ∂μ) * g x) ((hfg.sub hfc).sub hgc) (integrable_const _),
    integral_sub (f := fun x => f x * g x - f x * ∫ y, g y ∂μ)
      (hfg.sub hfc) hgc,
    integral_sub (f := fun x => f x * g x) hfg hfc,
    integral_mul_const, integral_const_mul, integral_const]
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul, covariance]
  ring

theorem variance_nonneg (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 2 μ) : 0 ≤ variance μ f := by
  rw [variance, covariance_eq_centered hf hf]
  exact integral_nonneg fun x => mul_self_nonneg _

theorem variance_le_secondMoment (μ : Measure Ω) (f : Ω → ℝ) :
    variance μ f ≤ ∫ x, f x ^ 2 ∂μ := by
  rw [variance_eq_secondMoment_sub]
  exact sub_le_self _ (sq_nonneg _)

theorem covariance_const_mul_left (μ : Measure Ω) (f g : Ω → ℝ) (a : ℝ) :
    covariance μ (fun x => a * f x) g = a * covariance μ f g := by
  simp only [covariance, mul_assoc, integral_const_mul]
  ring

theorem covariance_const_mul_right (μ : Measure Ω) (f g : Ω → ℝ) (a : ℝ) :
    covariance μ f (fun x => a * g x) = a * covariance μ f g := by
  rw [covariance_comm, covariance_const_mul_left, covariance_comm μ g f]

theorem variance_const_mul (μ : Measure Ω) (f : Ω → ℝ) (a : ℝ) :
    variance μ (fun x => a * f x) = a ^ 2 * variance μ f := by
  rw [variance, covariance_const_mul_left, covariance_const_mul_right]
  simp only [variance]
  ring

theorem integral_comp_measurePreserving {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {T : Ω → Ω'} (hT : MeasurePreserving T μ ν)
    {f : Ω' → ℝ} (hf : AEStronglyMeasurable f ν) :
    (∫ x, f (T x) ∂μ) = ∫ y, f y ∂ν := by
  have hm : AEStronglyMeasurable f (μ.map T) := hT.map_eq.symm ▸ hf
  simpa only [hT.map_eq] using (integral_map hT.measurable.aemeasurable hm).symm

theorem covariance_comp_measurePreserving {Ω' : Type*} [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} {T : Ω → Ω'} (hT : MeasurePreserving T μ ν)
    {f g : Ω' → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    covariance μ (f ∘ T) (g ∘ T) = covariance ν f g := by
  unfold covariance
  simp only [Function.comp_apply]
  rw [integral_comp_measurePreserving hT (f := fun x => f x * g x)
      (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable),
    integral_comp_measurePreserving hT hf.aestronglyMeasurable,
    integral_comp_measurePreserving hT hg.aestronglyMeasurable]

theorem covariance_sum_left {I : Type*} [Fintype I] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : I → Ω → ℝ) (g : Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : MemLp g 2 μ) :
    covariance μ (fun x => ∑ i, f i x) g = ∑ i, covariance μ (f i) g := by
  simp only [covariance, Finset.sum_mul]
  rw [integral_finset_sum _ (f := fun i x => f i x * g x)
      (fun i _ => (hf i).integrable_mul hg),
    integral_finset_sum _ (f := f) (fun i _ => (hf i).integrable one_le_two)]
  simp only [Finset.sum_mul, Finset.sum_sub_distrib]

theorem covariance_sum_right {I : Type*} [Fintype I] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (g : I → Ω → ℝ)
    (hf : MemLp f 2 μ) (hg : ∀ i, MemLp (g i) 2 μ) :
    covariance μ f (fun x => ∑ i, g i x) = ∑ i, covariance μ f (g i) := by
  rw [covariance_comm, covariance_sum_left μ g f hg hf]
  exact Finset.sum_congr rfl fun i _ => covariance_comm μ (g i) f

theorem covariance_sum_sum {I J : Type*} [Fintype I] [Fintype J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : I → Ω → ℝ) (g : J → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : ∀ j, MemLp (g j) 2 μ) :
    covariance μ (fun x => ∑ i, f i x) (fun x => ∑ j, g j x) =
      ∑ i, ∑ j, covariance μ (f i) (g j) := by
  rw [covariance_sum_left μ f _ hf (memLp_finset_sum _ (fun j _ => hg j))]
  exact Finset.sum_congr rfl fun i _ => covariance_sum_right μ (f i) g (hf i) hg

theorem variance_sum {I : Type*} [Fintype I] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : I → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) :
    variance μ (fun x => ∑ i, f i x) = ∑ i, ∑ j, covariance μ (f i) (f j) :=
  covariance_sum_sum μ f f hf hf

theorem mean_absolute_le_sqrt_secondMoment (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have hs := square_integral_le_integral_square μ (fun x => |f x|)
    (hf.integrable one_le_two).abs (by simpa only [sq_abs] using hf.integrable_sq)
  simp only [sq_abs] at hs
  have hnonneg : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (∫ x, f x ^ 2 ∂μ)]

end CausalLowerbound.UpperBound
