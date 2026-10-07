import CausalLowerbound.PartB.PositiveWienerAtoms
import CausalLowerbound.WienerTensor
import CausalLowerbound.WienerStencil

/-!
# Concrete polarization of absolutely summable real trigonometric tensors

The coefficient operator and density dictionary are fixed and explicit.
Reconstruction takes place in the Wiener norm, including for infinite input
series. The input here is an ℓ¹ real trigonometric tensor expansion; identifying
the canonical expansion of an arbitrary symmetric real Wiener function is a
separate obligation.
-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open UnitAddTorus

namespace CausalLowerbound.PartB.PositiveWiener
open Wiener Polarization

variable {d ι : Type*} [Fintype d] [Fintype ι] [DecidableEq ι]

abbrev BasisIndex (d ι : Type*) := ι → (d → ℤ) × Bool

def basisTensor (w : BasisIndex d ι) : Fourier (ι × d) :=
  symTensor (fun i => trigSeries (w i).1 (w i).2)

def atomTensor (θ : ℝ) (m : AtomIndex d ι) : Fourier (ι × d) :=
  tensor (fun _i : ι => dictionary θ m)

theorem basisTensor_bound (w : BasisIndex d ι) : ‖basisTensor w‖ ≤ 1 :=
  symTensor_norm _ (fun _ => trigSeries_norm _ _)

theorem atomTensor_bound (θ : ℝ) (hθ : 0 ≤ θ) (m : AtomIndex d ι) :
    ‖atomTensor θ m‖ ≤ (1 + θ) ^ Fintype.card ι := by
  calc
    _ ≤ ∏ _i : ι, ‖dictionary θ m‖ := tensor_norm _
    _ ≤ ∏ _i : ι, (1 + θ) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => dictionary_norm θ hθ m)
    _ = _ := by simp

def weights (θ : ℝ) (w : BasisIndex d ι) (m : (ι → Bool) × (ι → Bool)) : ℝ :=
  stencilWeight (fun i => trigMean (w i).1 (w i).2) θ m

theorem weights_bound (θ : ℝ) (w : BasisIndex d ι) :
    (∑ m, |weights θ w m|) ≤ stencilBound (ι := ι) θ :=
  stencilWeight_bound _ (fun _ => trigMean_bound _ _) θ

theorem basis_polarization [Nonempty ι] (θ : ℝ) (hθ : θ ≠ 0) (w : BasisIndex d ι) :
    basisTensor w = ∑ m, weights θ w m • atomTensor θ (w, m) := by
  apply toContinuous_injective
  ext x
  let g : ι → Torus d → ℝ := fun i y =>
    (toContinuous (centeredTrig (w i).1 (w i).2) y).re
  let c : ι → ℝ := fun i => trigMean (w i).1 (w i).2
  have he (i : ι) (y : Torus d) : toContinuous (trigSeries (w i).1 (w i).2) y =
      ((c i + g i y : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [g, c, centeredTrig, map_sub, map_smul, characterSeries_toContinuous,
        mFourier_zero, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, smul_eq_mul, mul_one, Complex.sub_re,
        Complex.ofReal_re, Complex.ofReal_add, Complex.add_re]
      ring
    · simp only [trigSeries_real, Complex.ofReal_im]
  have hpol := positive_polarization c g θ hθ (fun i j => x (i, j))
  have heval (m : (ι → Bool) × (ι → Bool)) (y : Torus d) :
      toContinuous (dictionary θ (w, m)) y = (stencilAtom g θ m y : ℂ) :=
    atomSeries_value _ θ (fun i y => centeredTrig_real _ _ y) m y
  simp only [basisTensor, symTensor_value, map_sum, toContinuous_real_smul,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, atomTensor, tensor_value]
  simp_rw [he, heval]
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) hpol
  simpa only [symProduct, weights, c, Complex.ofReal_mul, Complex.ofReal_sum,
    Complex.ofReal_prod, Complex.ofReal_add, Complex.real_smul] using hcast

/-- Fixed, explicit bounded linear polarization coefficients. -/
def coefficientOperator (θ : ℝ) :
    Series (BasisIndex d ι) ℝ →L[ℝ] Series (AtomIndex d ι) ℝ :=
  extendStencil (weights θ) (stencilBound (ι := ι) θ) (weights_bound θ)

theorem coefficientOperator_entry (θ : ℝ) (a : Series (BasisIndex d ι) ℝ)
    (w : BasisIndex d ι) (m : (ι → Bool) × (ι → Bool)) :
    coefficientOperator θ a (w, m) = a w * weights θ w m :=
  extendStencil_entry _ _ _ a w m

theorem coefficientOperator_bound (θ : ℝ) (a : Series (BasisIndex d ι) ℝ) :
    (∑' m, |coefficientOperator θ a m|) ≤ stencilBound (ι := ι) θ * ‖a‖ := by
  simpa only [← Real.norm_eq_abs, ← norm_eq_tsum] using
    extendStencil_bound (weights θ) (stencilBound (ι := ι) θ) (weights_bound θ) a

theorem coefficientOperator_summable (θ : ℝ) (a : Series (BasisIndex d ι) ℝ) :
    Summable (fun m => |coefficientOperator θ a m|) := by
  simpa only [Real.norm_eq_abs] using summable_norm (coefficientOperator θ a)

theorem coefficientOperator_absolute_series (θ : ℝ) (hθ : 0 ≤ θ)
    (a : Series (BasisIndex d ι) ℝ) :
    Summable (fun m => ‖coefficientOperator θ a m • atomTensor θ m‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun m => ?_) ((coefficientOperator_summable θ a).mul_left ((1 + θ) ^ Fintype.card ι))
  rw [norm_smul, Real.norm_eq_abs, mul_comm ((1 + θ) ^ Fintype.card ι)]
  exact mul_le_mul_of_nonneg_left (atomTensor_bound θ hθ m) (abs_nonneg _)

theorem coefficientOperator_lipschitz (θ : ℝ) (a b : Series (BasisIndex d ι) ℝ) :
    (∑' m, |coefficientOperator θ a m - coefficientOperator θ b m|) ≤
      stencilBound (ι := ι) θ * ‖a - b‖ :=
  extendStencil_lipschitz _ _ _ a b

def realTensorSynthesis : Series (BasisIndex d ι) ℝ →L[ℝ] Fourier (ι × d) :=
  synthesis basisTensor 1 basisTensor_bound

theorem coefficientOperator_reconstruction [Nonempty ι] (θ : ℝ) (hθ : 0 < θ)
    (a : Series (BasisIndex d ι) ℝ) :
    HasSum (fun m => coefficientOperator θ a m • atomTensor θ m) (realTensorSynthesis a) := by
  have hs := synthesis_hasSum (atomTensor θ) ((1 + θ) ^ Fintype.card ι)
    (atomTensor_bound θ hθ.le) (coefficientOperator θ a)
  have he := synthesis_extendStencil (weights θ) (stencilBound (ι := ι) θ) (weights_bound θ)
    (atomTensor θ) ((1 + θ) ^ Fintype.card ι) (pow_nonneg (by linarith) _)
    (atomTensor_bound θ hθ.le) a
  simp_rw [← basis_polarization θ hθ.ne'] at he
  change synthesis (atomTensor θ) ((1 + θ) ^ Fintype.card ι)
    (atomTensor_bound θ hθ.le) (coefficientOperator θ a) = realTensorSynthesis a at he
  rw [he] at hs
  exact hs

end CausalLowerbound.PartB.PositiveWiener
