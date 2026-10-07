import CausalLowerbound.PartC.RepresentativeTensor

/-! Concrete one-slot trigonometric factors and the embedding of centering
Walsh coefficients into degree-zero rows. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators ENNReal

namespace CausalLowerbound.PartC.Representative

variable {d J : Type*} [Fintype d] [Fintype J] [DecidableEq J] {D : ℕ}

def factorEvaluation (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) : Factor d J D →L[ℝ] ℂ :=
  ∑ r : FactorRow J D, (z ^ r.1.val * Walsh.character r.2 ζ) •
    ((((ContinuousMap.evalCLM ℂ x).comp Wiener.toContinuous).restrictScalars ℝ).comp (FiniteL1.entry r))

@[simp] theorem factorEvaluation_apply (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool)
    (a : Factor d J D) : factorEvaluation x z ζ a = factorValue x z ζ a := by
  simp [factorEvaluation, factorValue]

theorem factorValue_single (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool)
    (r : FactorRow J D) (a : Wiener.Fourier d) :
    factorValue x z ζ (lp.single 1 r a) =
      (z ^ r.1.val * Walsh.character r.2 ζ : ℝ) • Wiener.toContinuous a x := by
  unfold factorValue
  rw [Finset.sum_eq_single r]
  · rw [lp.single_apply_self]
  · intro s _ hsr
    rw [lp.single_apply_ne _ _ _ hsr, map_zero]
    simp
  · simp

def constantWalsh : Walsh.Coefficients J →L[ℝ] Factor d J D :=
  FiniteL1.transform (fun S => (0, S))
    (fun _ => (ContinuousLinearMap.id ℝ ℝ).smulRight (1 : Wiener.Fourier d))
    1 (fun S c => by simp [norm_smul])

theorem constantWalsh_bound (a : Walsh.Coefficients J) :
    ‖(constantWalsh a : Factor d J D)‖ ≤ ‖a‖ := by
  simpa only [one_mul] using FiniteL1.transform_bound (fun S : Finset J => ((0 : Fin (D + 1)), S))
    (fun _ => (ContinuousLinearMap.id ℝ ℝ).smulRight (1 : Wiener.Fourier d))
    1 (fun S c => by simp [norm_smul]) a

@[simp] theorem constantWalsh_apply (a : Walsh.Coefficients J) (e : Fin (D + 1)) (S : Finset J) :
    (constantWalsh a : Factor d J D) (e, S) = if e = 0 then a S • (1 : Wiener.Fourier d) else 0 := by
  simp only [constantWalsh, FiniteL1.transform_apply]
  by_cases h : e = 0
  · subst e
    simp
  · simp [h]

theorem constantWalsh_value (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) (a : Walsh.Coefficients J) :
    factorValue x z ζ (constantWalsh a : Factor d J D) = (Walsh.evaluate ζ a : ℂ) := by
  simp only [factorValue, Fintype.sum_prod_type, constantWalsh_apply]
  rw [Finset.sum_eq_single 0]
  · simp only [ite_true, Fin.val_zero, pow_zero, one_mul, Wiener.toContinuous_real_smul,
      Wiener.toContinuous_one, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_smul, smul_eq_mul, mul_one]
    simp only [Walsh.evaluate_apply, tsum_fintype, Complex.ofReal_sum, Complex.real_smul, mul_one]
    apply Finset.sum_congr rfl
    intro S _
    push_cast
    ring
  · intro e _ he
    simp [he]
  · simp

def factorSymbol (j : J) : Factor d J D →L[ℝ] Factor d J D :=
  FiniteL1.project (fun r => j ∈ r.2)

@[simp] theorem factorSymbol_apply (j : J) (a : Factor d J D) (r : FactorRow J D) :
    factorSymbol j a r = if j ∈ r.2 then a r else 0 := FiniteL1.project_apply _ _ _

theorem factorSymbol_constantWalsh (j : J) (a : Walsh.Coefficients J) :
    factorSymbol j (constantWalsh a : Factor d J D) = constantWalsh (Walsh.symbolPart j a) := by
  apply lp.ext
  funext r
  rcases r with ⟨e, S⟩
  simp only [factorSymbol_apply, constantWalsh_apply, Walsh.symbolPart_apply]
  split_ifs <;> simp

def basisFactor (e : Fin (D + 1)) (k : d → ℤ) (b : Bool) : Factor d J D :=
  lp.single 1 (e, ∅) (Wiener.trigSeries k b)

theorem basisFactor_norm (e : Fin (D + 1)) (k : d → ℤ) (b : Bool) :
    ‖(basisFactor e k b : Factor d J D)‖ ≤ 1 := by
  rw [basisFactor, lp.norm_single (by norm_num)]
  exact Wiener.trigSeries_norm k b

theorem basisFactor_value (e : Fin (D + 1)) (k : d → ℤ) (b : Bool)
    (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) :
    factorValue x z ζ (basisFactor e k b : Factor d J D) =
      z ^ e.val • Wiener.toContinuous (Wiener.trigSeries k b) x := by
  rw [basisFactor, factorValue_single]
  simp

@[simp] theorem factorSymbol_basisFactor (j : J) (e : Fin (D + 1)) (k : d → ℤ) (b : Bool) :
    factorSymbol j (basisFactor e k b : Factor d J D) = 0 := by
  apply lp.ext
  funext r
  rw [factorSymbol_apply]
  by_cases hr : r = (e, ∅)
  · subst r
    simp
  · simp [basisFactor, Pi.single_apply, hr]

def centeredFactor (e : Fin (D + 1)) (k : d → ℤ) (b : Bool) (a : Walsh.Coefficients J) : Factor d J D :=
  (1 / 2 : ℝ) • (basisFactor e k b - constantWalsh a)

theorem centeredFactor_norm (e : Fin (D + 1)) (k : d → ℤ) (b : Bool) (a : Walsh.Coefficients J)
    (ha : ‖a‖ ≤ 1) : ‖(centeredFactor e k b a : Factor d J D)‖ ≤ 1 := by
  have h := norm_sub_le (basisFactor e k b : Factor d J D) (constantWalsh a)
  have hb := basisFactor_norm (J := J) e k b
  have hc := constantWalsh_bound (d := d) (D := D) a
  rw [centeredFactor, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

theorem centeredFactor_value (e : Fin (D + 1)) (k : d → ℤ) (b : Bool) (a : Walsh.Coefficients J)
    (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) :
    factorValue x z ζ (centeredFactor e k b a : Factor d J D) =
      (1 / 2 : ℝ) • (z ^ e.val • Wiener.toContinuous (Wiener.trigSeries k b) x - (Walsh.evaluate ζ a : ℂ)) := by
  rw [← factorEvaluation_apply]
  rw [centeredFactor, map_smul, map_sub, factorEvaluation_apply, factorEvaluation_apply,
    basisFactor_value, constantWalsh_value]

theorem centeredFactor_real (e : Fin (D + 1)) (k : d → ℤ) (b : Bool) (a : Walsh.Coefficients J)
    (x : Wiener.Torus d) (z : ℝ) (ζ : J → Bool) :
    (factorValue x z ζ (centeredFactor e k b a : Factor d J D)).im = 0 := by
  rw [centeredFactor_value]
  simp only [Complex.real_smul, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Wiener.trigSeries_real, mul_zero, zero_mul, add_zero, zero_add, sub_zero]

theorem centeredFactor_symbol_bound (j : J) (e : Fin (D + 1)) (k : d → ℤ) (b : Bool)
    (a : Walsh.Coefficients J) :
    ‖factorSymbol j (centeredFactor e k b a : Factor d J D)‖ ≤ (1 / 2) * ‖Walsh.symbolPart j a‖ := by
  rw [centeredFactor, map_smul, map_sub, factorSymbol_basisFactor, factorSymbol_constantWalsh,
    zero_sub, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact mul_le_mul_of_nonneg_left (constantWalsh_bound _) (by norm_num)

end CausalLowerbound.PartC.Representative
