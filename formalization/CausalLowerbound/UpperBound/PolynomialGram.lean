import CausalLowerbound.UpperBound.TensorGrid
import CausalLowerbound.PartB.ClusterVolume
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Positivity of the fixed polynomial Gram matrix on the anchor box.
A scaled Vandermonde grid inside the box detects every nonzero coefficient
vector; continuity then gives a set of positive volume. -/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators Matrix Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def tensorPolynomial (p : ℕ) (θ : TensorIndex d p → ℝ) (x : d → ℝ) : ℝ :=
  ∑ ν, θ ν * tensorMonomial p ν x

theorem continuous_tensorPolynomial (p : ℕ) (θ : TensorIndex d p → ℝ) :
    Continuous (tensorPolynomial p θ) := by
  unfold tensorPolynomial tensorMonomial
  fun_prop

theorem tensorEvaluation_scaled_grid_isUnit_det (p : ℕ) {a : ℝ} (ha : a ≠ 0) :
    IsUnit (tensorEvaluation p (fun j : TensorIndex d p => a • gridNode p j)).det := by
  have he : tensorEvaluation p (fun j : TensorIndex d p => a • gridNode p j) =
      tensorMatrix (fun _ : d => (Matrix.vandermonde (fun i => a * gridCoordinate p i))ᵀ) := rfl
  rw [he]
  apply tensorMatrix_isUnit_det
  intro _
  apply Matrix.isUnit_det_transpose
  apply isUnit_iff_ne_zero.mpr
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j hij
  exact gridCoordinate_injective p (mul_left_cancel₀ ha hij)

theorem tensorPolynomial_nonzero_on_scaled_grid (p : ℕ) (θ : TensorIndex d p → ℝ)
    (hθ : θ ≠ 0) {a : ℝ} (ha : a ≠ 0) :
    ∃ j : TensorIndex d p, tensorPolynomial p θ (a • gridNode p j) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hθ
  apply Matrix.eq_zero_of_vecMul_eq_zero
    (isUnit_iff_ne_zero.mp (tensorEvaluation_scaled_grid_isUnit_det (d := d) p ha))
  ext j
  exact h j

def anchorUnitBox (d : Type*) : Set (d → ℝ) := Icc 0 (fun _ => 1 / 4)

def tensorGram (p : ℕ) : Matrix (TensorIndex d p) (TensorIndex d p) ℝ :=
  fun ν ω => ∫ x in anchorUnitBox d, tensorMonomial p ν x * tensorMonomial p ω x

def tensorGramEnergy (p : ℕ) (θ : TensorIndex d p → ℝ) : ℝ :=
  ∑ ν, ∑ ω, θ ν * θ ω * tensorGram p ν ω

theorem tensorGramEnergy_eq_integral (p : ℕ) (θ : TensorIndex d p → ℝ) :
    tensorGramEnergy p θ = ∫ x in anchorUnitBox d, tensorPolynomial p θ x ^ 2 := by
  have hi (ν ω : TensorIndex d p) :
      IntegrableOn (fun x => θ ν * θ ω * (tensorMonomial p ν x * tensorMonomial p ω x))
        (anchorUnitBox d) := by
    have hc := (continuous_tensorMonomial p ν).mul (continuous_tensorMonomial p ω)
    exact (hc.continuousOn.integrableOn_compact (show IsCompact (anchorUnitBox d)
      from isCompact_Icc)).const_mul _
  have he (x : d → ℝ) : tensorPolynomial p θ x ^ 2 =
      ∑ ν, ∑ ω, θ ν * θ ω * (tensorMonomial p ν x * tensorMonomial p ω x) := by
    simp only [tensorPolynomial, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    apply Finset.sum_congr rfl
    intro ω _
    ring
  simp_rw [he]
  rw [integral_finset_sum _ (fun ν _ => integrable_finset_sum _ (fun ω _ => hi ν ω))]
  simp_rw [integral_finset_sum _ (fun ω _ => hi _ ω), integral_const_mul]
  rfl

theorem continuous_tensorGramEnergy (p : ℕ) :
    Continuous (tensorGramEnergy (d := d) p) := by
  unfold tensorGramEnergy
  fun_prop

theorem tensorGramEnergy_nonneg (p : ℕ) (θ : TensorIndex d p → ℝ) :
    0 ≤ tensorGramEnergy p θ := by
  rw [tensorGramEnergy_eq_integral]
  exact integral_nonneg (fun _ => sq_nonneg _)

theorem tensorGramEnergy_pos (p : ℕ) (θ : TensorIndex d p → ℝ) (hθ : θ ≠ 0) :
    0 < tensorGramEnergy p θ := by
  obtain ⟨j, hj⟩ := tensorPolynomial_nonzero_on_scaled_grid p θ hθ
    (by norm_num : (1 / 4 : ℝ) ≠ 0)
  let O : Set (d → ℝ) := Set.univ.pi (fun _ => Ioo (0 : ℝ) (1 / 4))
  have hO : IsOpen O := isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hjO : (1 / 4 : ℝ) • gridNode p j ∈ O := by
    intro i _
    change 0 < (1 / 4 : ℝ) * gridCoordinate p (j i) ∧
      (1 / 4 : ℝ) * gridCoordinate p (j i) < 1 / 4
    constructor
    · exact mul_pos (by norm_num) (gridCoordinate_pos p (j i))
    · linarith [gridCoordinate_lt_one p (j i)]
  have hsub : O ⊆ anchorUnitBox d := by
    intro x hx
    exact ⟨fun i => (hx i (mem_univ i)).1.le, fun i => (hx i (mem_univ i)).2.le⟩
  have hc : Continuous (fun x => tensorPolynomial p θ x ^ 2) :=
    (continuous_tensorPolynomial p θ).pow 2
  have hpos : 0 < volume (Function.support (fun x => tensorPolynomial p θ x ^ 2) ∩ O) :=
    (hc.isOpen_support.inter hO).measure_pos volume ⟨_, pow_ne_zero 2 hj, hjO⟩
  rw [tensorGramEnergy_eq_integral]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg (tensorPolynomial p θ x)))
    (hc.continuousOn.integrableOn_compact isCompact_Icc)).mpr
  exact hpos.trans_le (measure_mono (inter_subset_inter_right _ hsub))

theorem tensorGramEnergy_smul (p : ℕ) (θ : TensorIndex d p → ℝ) (a : ℝ) :
    tensorGramEnergy p (a • θ) = a ^ 2 * tensorGramEnergy p θ := by
  simp only [tensorGramEnergy, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  apply Finset.sum_congr rfl
  intro ω _
  ring

theorem exists_tensorGram_lower_bound (p : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ : TensorIndex d p → ℝ,
      κ * ‖θ‖ ^ 2 ≤ tensorGramEnergy p θ := by
  have hne : (Metric.sphere (0 : TensorIndex d p → ℝ) 1).Nonempty := by
    refine ⟨fun _ => 1, ?_⟩
    simp [Metric.mem_sphere, dist_zero_right]
  obtain ⟨θ₀, hθ₀, hmin⟩ := (isCompact_sphere (0 : TensorIndex d p → ℝ) 1).exists_isMinOn
    hne (continuous_tensorGramEnergy p).continuousOn
  have hn₀ : ‖θ₀‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hθ₀
  have hθ₀ne : θ₀ ≠ 0 := by intro hz; simp [hz] at hn₀
  refine ⟨tensorGramEnergy p θ₀, tensorGramEnergy_pos p θ₀ hθ₀ne, ?_⟩
  intro θ
  by_cases hz : θ = 0
  · simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact tensorGramEnergy_nonneg p 0
  have hn : ‖θ‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let u : TensorIndex d p → ℝ := ‖θ‖⁻¹ • θ
  have hu : u ∈ Metric.sphere (0 : TensorIndex d p → ℝ) 1 := by
    simp only [Metric.mem_sphere, dist_zero_right, u, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_nonneg (norm_nonneg θ), inv_mul_cancel₀ hn]
  have hback : ‖θ‖ • u = θ := by simp [u, smul_smul, hn]
  calc
    tensorGramEnergy p θ₀ * ‖θ‖ ^ 2 ≤ tensorGramEnergy p u * ‖θ‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hmin hu) (sq_nonneg _)
    _ = ‖θ‖ ^ 2 * tensorGramEnergy p u := mul_comm _ _
    _ = tensorGramEnergy p (‖θ‖ • u) := (tensorGramEnergy_smul p u ‖θ‖).symm
    _ = tensorGramEnergy p θ := congrArg (tensorGramEnergy p) hback

end CausalLowerbound.UpperBound
