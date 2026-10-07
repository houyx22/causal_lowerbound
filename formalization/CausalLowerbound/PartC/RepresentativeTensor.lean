import CausalLowerbound.PartC.RepresentativeEvaluation
import CausalLowerbound.PartC.WalshParity
import CausalLowerbound.WienerTensor

/-! Cross-slot tensors of actual coefficient arrays. The degree of each slot
is retained, while repeated Walsh symbols cancel by symmetric difference. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound.PartC.Representative

abbrev FactorRow (J : Type*) (D : ℕ) := Fin (D + 1) × Finset J
abbrev Factor (d J : Type*) (D : ℕ) := FiniteL1.Family (FactorRow J D) (Wiener.Fourier d)

variable {d ι J : Type*} [Fintype d] [Fintype ι] [Fintype J]
  [DecidableEq ι] [DecidableEq J] {D : ℕ}

def tensorRow (r : ι → FactorRow J D) : Row ι J D :=
  (fun i => (r i).1, Walsh.parityUnion (fun i => (r i).2))

theorem tensorRow_weight (r : ι → FactorRow J D) (z : ι → ℝ) (ζ : J → Bool) :
    rowWeight (tensorRow r) z ζ = ∏ i, (z i ^ (r i).1.val * Walsh.character (r i).2 ζ) := by
  simp only [rowWeight, tensorRow, monomial, Walsh.character_parityUnion, Finset.prod_mul_distrib]

def tensor (f : ι → Factor d J D) : Array d ι J D :=
  ∑ r : ι → FactorRow J D, lp.single 1 (tensorRow r) (Wiener.tensor (fun i => f i (r i)))

theorem tensor_norm (f : ι → Factor d J D) : ‖tensor f‖ ≤ ∏ i, ‖f i‖ := by
  calc
    _ ≤ ∑ r : ι → FactorRow J D,
        ‖(lp.single 1 (tensorRow r) (Wiener.tensor (fun i => f i (r i))) : Array d ι J D)‖ :=
      norm_sum_le _ _
    _ = ∑ r : ι → FactorRow J D, ‖Wiener.tensor (fun i => f i (r i))‖ := by
      simp only [lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
    _ ≤ ∑ r : ι → FactorRow J D, ∏ i, ‖f i (r i)‖ :=
      Finset.sum_le_sum (fun r _ => Wiener.tensor_norm _)
    _ = ∏ i, ∑ r : FactorRow J D, ‖f i r‖ :=
      (Fintype.prod_sum (fun (i : ι) (r : FactorRow J D) => ‖f i r‖)).symm
    _ = ∏ i, ‖f i‖ := by
      apply Finset.prod_congr rfl
      intro i _
      exact (FiniteL1.norm_eq_sum (f i)).symm

def factorValue (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) (a : Factor d J D) : ℂ :=
  ∑ r : FactorRow J D, (z ^ r.1.val * Walsh.character r.2 ζ : ℝ) • Wiener.toContinuous (a r) x

theorem tensor_value (f : ι → Factor d J D) (x : Wiener.Torus (ι × d)) (z : ι → ℝ)
    (ζ : J → Bool) : pointValue x z ζ (tensor f) =
      (∏ i, factorValue (fun j => x (i, j)) (z i) ζ (f i)).re := by
  rw [tensor, pointValue_sum]
  simp only [pointValue_single, Wiener.tensor_value, tensorRow_weight, factorValue,
    Complex.real_smul, Fintype.prod_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.prod_mul_distrib (f := fun i =>
    ((z i ^ (r i).1.val * Walsh.character (r i).2 ζ : ℝ) : ℂ)), ← Complex.ofReal_prod]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem factorValue_bound (x : Wiener.Torus d) (z : ℝ) (hz : |z| ≤ 1) (ζ : J → Bool)
    (a : Factor d J D) : ‖factorValue x z ζ a‖ ≤ ‖a‖ := by
  calc
    _ ≤ ∑ r : FactorRow J D, ‖(z ^ r.1.val * Walsh.character r.2 ζ : ℝ) •
        Wiener.toContinuous (a r) x‖ := norm_sum_le _ _
    _ ≤ ∑ r : FactorRow J D, ‖a r‖ := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_pow, Walsh.abs_character, mul_one]
      calc
        _ ≤ 1 * ‖Wiener.toContinuous (a r) x‖ := mul_le_mul_of_nonneg_right
          (pow_le_one₀ (abs_nonneg _) hz) (norm_nonneg _)
        _ ≤ ‖a r‖ := by rw [one_mul]; exact Wiener.evaluate_bound _ _
    _ = ‖a‖ := (FiniteL1.norm_eq_sum a).symm

theorem tensor_value_real (f : ι → Factor d J D) (x : Wiener.Torus (ι × d)) (z : ι → ℝ)
    (ζ : J → Bool) (hreal : ∀ i, (factorValue (fun j => x (i, j)) (z i) ζ (f i)).im = 0) :
    pointValue x z ζ (tensor f) =
      ∏ i, (factorValue (fun j => x (i, j)) (z i) ζ (f i)).re := by
  rw [tensor_value]
  have h (i : ι) : factorValue (fun j => x (i, j)) (z i) ζ (f i) =
      ((factorValue (fun j => x (i, j)) (z i) ζ (f i)).re : ℂ) := by
    apply Complex.ext <;> simp [hreal i]
  calc
    _ = (∏ i, ((factorValue (fun j => x (i, j)) (z i) ζ (f i)).re : ℂ)).re :=
      congrArg Complex.re (Finset.prod_congr rfl (fun i _ => h i))
    _ = _ := by rw [← Complex.ofReal_prod, Complex.ofReal_re]

end CausalLowerbound.PartC.Representative
