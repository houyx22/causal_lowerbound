import CausalLowerbound.WienerTrigonometric

/-!
# The Wiener product

Convolution is constructed by an absolutely convergent series of translated
coefficient sequences. Its norm inequality and its realization as pointwise
multiplication are proved for arbitrary Wiener elements.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open UnitAddTorus

namespace CausalLowerbound.Wiener

variable {d : Type*} [Fintype d]

def translate (k : d → ℤ) : Fourier d →L[ℂ] Fourier d := regroup (fun n => k + n)

theorem translate_bound (k : d → ℤ) (a : Fourier d) : ‖translate k a‖ ≤ ‖a‖ :=
  regroup_bound _ a

theorem toContinuous_translate (k : d → ℤ) (a : Fourier d) :
    toContinuous (translate k a) = mFourier k * toContinuous a := by
  change synthesis mFourier 1 _ (regroup (fun n => k + n) a) = _
  rw [synthesis_regroup]
  ext x
  have h := (ContinuousMap.evalCLM ℂ x).map_tsum
    (summable_synthesis (fun n => mFourier (k + n)) 1 (fun _ => mFourier_norm.le) a)
  have h' := (ContinuousMap.evalCLM ℂ x).map_tsum
    (summable_synthesis mFourier 1 (fun _ => mFourier_norm.le) a)
  simp only [ContinuousMap.evalCLM_apply] at h h'
  change (∑' n, a n • mFourier (k + n)) x = mFourier k x * (∑' n, a n • mFourier n) x
  rw [h, h']
  simp only [ContinuousMap.smul_apply, smul_eq_mul, mFourier_add]
  simp_rw [mul_left_comm (a _) (mFourier k x)]
  exact tsum_mul_left

/-- Multiplication by a fixed Wiener series, linear in the left input. -/
def convolutionRight (b : Fourier d) : Fourier d →L[ℂ] Fourier d :=
  synthesis (fun k => translate k b) ‖b‖ (fun k => translate_bound k b)

def convolution (a b : Fourier d) : Fourier d := convolutionRight b a

theorem convolution_bound (a b : Fourier d) :
    ‖convolution a b‖ ≤ ‖a‖ * ‖b‖ := by
  simpa only [mul_comm] using
    norm_synthesis (fun k => translate k b) ‖b‖ (fun k => translate_bound k b) a

theorem toContinuous_convolution (a b : Fourier d) :
    toContinuous (convolution a b) = toContinuous a * toContinuous b := by
  change toContinuous (∑' k, a k • translate k b) = _
  rw [toContinuous.map_tsum (summable_synthesis (fun k => translate k b) ‖b‖
    (fun k => translate_bound k b) a)]
  simp_rw [map_smul, toContinuous_translate]
  ext x
  have hs : Summable (fun k => a k • (mFourier k * toContinuous b)) := by
    apply summable_synthesis _ ‖toContinuous b‖ _ a
    intro k
    calc
      _ ≤ ‖mFourier k‖ * ‖toContinuous b‖ := norm_mul_le _ _
      _ = _ := by rw [mFourier_norm, one_mul]
  have h := (ContinuousMap.evalCLM ℂ x).map_tsum hs
  have h' := (ContinuousMap.evalCLM ℂ x).map_tsum
    (summable_synthesis mFourier 1 (fun _ => mFourier_norm.le) a)
  simp only [ContinuousMap.evalCLM_apply] at h h'
  change (∑' k, a k • (mFourier k * toContinuous b)) x =
    (∑' k, a k • mFourier k) x * toContinuous b x
  rw [h, h']
  simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul]
  simp_rw [← mul_assoc]
  exact tsum_mul_right

theorem convolution_comm (a b : Fourier d) : convolution a b = convolution b a := by
  apply toContinuous_injective
  rw [toContinuous_convolution, toContinuous_convolution, mul_comm]

theorem convolution_assoc (a b c : Fourier d) :
    convolution (convolution a b) c = convolution a (convolution b c) := by
  apply toContinuous_injective
  simp only [toContinuous_convolution, mul_assoc]

instance fourierCommMonoid : CommMonoid (Fourier d) where
  mul := convolution
  one := characterSeries 0
  mul_assoc := convolution_assoc
  mul_comm := convolution_comm
  one_mul a := by
    apply toContinuous_injective
    change toContinuous (convolution (characterSeries 0) a) = toContinuous a
    rw [toContinuous_convolution, characterSeries_toContinuous, mFourier_zero, one_mul]
  mul_one a := by
    apply toContinuous_injective
    change toContinuous (convolution a (characterSeries 0)) = toContinuous a
    rw [toContinuous_convolution, characterSeries_toContinuous, mFourier_zero, mul_one]

@[simp]
theorem toContinuous_one : toContinuous (1 : Fourier d) = 1 := by
  exact (characterSeries_toContinuous 0).trans mFourier_zero

@[simp]
theorem toContinuous_mul (a b : Fourier d) : toContinuous (a * b) = toContinuous a * toContinuous b :=
  toContinuous_convolution a b

instance fourierCommRing : CommRing (Fourier d) where
  __ := fourierCommMonoid
  __ := inferInstanceAs (AddCommGroup (Fourier d))
  left_distrib a b c := by
    apply toContinuous_injective
    simp only [map_add, toContinuous_mul, mul_add]
  right_distrib a b c := by
    apply toContinuous_injective
    simp only [map_add, toContinuous_mul, add_mul]
  zero_mul a := by
    apply toContinuous_injective
    simp only [map_zero, toContinuous_mul, zero_mul]
  mul_zero a := by
    apply toContinuous_injective
    simp only [map_zero, toContinuous_mul, mul_zero]

instance fourierNormedCommRing : NormedCommRing (Fourier d) where
  __ := fourierCommRing
  __ := inferInstanceAs (NormedAddCommGroup (Fourier d))
  norm_mul_le := convolution_bound

instance fourierNormOne : NormOneClass (Fourier d) where
  norm_one := characterSeries_norm 0

instance fourierAlgebra : Algebra ℝ (Fourier d) :=
  Algebra.ofModule
    (fun r a b => by
      apply toContinuous_injective
      change toContinuous (convolution (r • a) b) = toContinuous (r • convolution a b)
      exact congrArg toContinuous ((convolutionRight b).restrictScalars ℝ |>.map_smul r a))
    (fun r a b => by
      rw [mul_comm a (r • b), mul_comm a b]
      apply toContinuous_injective
      change toContinuous (convolution (r • b) a) = toContinuous (r • convolution b a)
      exact congrArg toContinuous ((convolutionRight a).restrictScalars ℝ |>.map_smul r b))

instance fourierNormedAlgebra : NormedAlgebra ℝ (Fourier d) where
  norm_smul_le := norm_smul_le

@[simp]
theorem toContinuous_real_smul (r : ℝ) (a : Fourier d) :
    toContinuous (r • a) = r • toContinuous a :=
  ((toContinuous (d := d)).restrictScalars ℝ).map_smul r a

end CausalLowerbound.Wiener
