import CausalLowerbound.UpperBound.FiniteSampleRisk

/-! A fixed constant times the three terms of the master risk bound.
The constant is independent of bandwidths, target and sample size. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.UpperBound

variable {d : Type*} [Fintype d]

def stencilBiasConstant (p : ℕ) (T : StencilTemplate d p) (Lπ L₀ Lτ upper : ℝ) : ℝ :=
  (Lπ * (1 + Fintype.card (TensorIndex d p) * T.inverseBound) *
      (L₀ * (1 + Fintype.card (TensorIndex d p) * T.inverseBound)) +
    ((Fintype.card (StencilRole d p) : ℝ) ^ 2 + 1) * Lτ) * upper ^ Fintype.card (StencilRole d p)

def stencilMomentConstant (p qγ : ℕ) (upper M₂ Lτ B : ℝ) : ℝ :=
  stencilResponseMomentConstant (d := d) p upper M₂ B +
    9 * stencilEffectCoefficientBound (d := d) qγ Lτ ^ 2 * stencilMatrixMomentConstant (d := d) p upper B

def stencilMasterConstant (p qγ : ℕ) (T : StencilTemplate d p) (Lπ L₀ Lτ upper M₂ B c : ℝ) : ℝ :=
  Real.sqrt (3 / c ^ 2) *
    (1 + stencilBiasConstant p T Lπ L₀ Lτ upper + stencilMomentConstant (d := d) p qγ upper M₂ Lτ B)

theorem stencilBiasConstant_nonneg (p : ℕ) (T : StencilTemplate d p)
    {Lπ L₀ Lτ upper : ℝ} (hπ : 0 ≤ Lπ) (h₀ : 0 ≤ L₀) (hτ : 0 ≤ Lτ) (hu : 0 ≤ upper) :
    0 ≤ stencilBiasConstant p T Lπ L₀ Lτ upper := by
  have hw := T.inverseBound_pos
  unfold stencilBiasConstant
  positivity

theorem stencilMomentConstant_nonneg (p qγ : ℕ) {upper M₂ Lτ B : ℝ}
    (hu : 0 ≤ upper) (hM : 0 ≤ M₂) (hB : 0 ≤ B) :
    0 ≤ stencilMomentConstant (d := d) p qγ upper M₂ Lτ B := by
  unfold stencilMomentConstant stencilResponseMomentConstant stencilMatrixMomentConstant
  positivity

theorem stencilMasterConstant_pos (p qγ : ℕ) (T : StencilTemplate d p)
    {Lπ L₀ Lτ upper M₂ B c : ℝ} (hπ : 0 ≤ Lπ) (h₀ : 0 ≤ L₀) (hτ : 0 ≤ Lτ)
    (hu : 0 ≤ upper) (hM : 0 ≤ M₂) (hB : 0 ≤ B) (hc : 0 < c) :
    0 < stencilMasterConstant p qγ T Lπ L₀ Lτ upper M₂ B c := by
  have hb := stencilBiasConstant_nonneg p T hπ h₀ hτ hu
  have hm := stencilMomentConstant_nonneg (d := d) p qγ (Lτ := Lτ) hu hM hB
  unfold stencilMasterConstant
  positivity

theorem stencilBiasSize_le_master (p : ℕ) (T : StencilTemplate d p) (α β γ : ℝ)
    {Lπ L₀ Lτ upper h ℓ r : ℝ} (hπ : 0 ≤ Lπ) (h₀ : 0 ≤ L₀) (hτ : 0 ≤ Lτ)
    (hu : 0 ≤ upper) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) :
    stencilBiasSize p T α β γ Lπ L₀ Lτ upper h ℓ r ≤
      stencilBiasConstant p T Lπ L₀ Lτ upper *
        (h ^ γ + twoScaleModulus α ℓ r * twoScaleModulus β ℓ r) := by
  let a := Lπ * (1 + Fintype.card (TensorIndex d p) * T.inverseBound) *
    (L₀ * (1 + Fintype.card (TensorIndex d p) * T.inverseBound)) * upper ^ Fintype.card (StencilRole d p)
  let b := ((Fintype.card (StencilRole d p) : ℝ) ^ 2 + 1) * Lτ * upper ^ Fintype.card (StencilRole d p)
  have hw := T.inverseBound_pos
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hS := mul_nonneg (twoScaleModulus_nonneg α ℓ r hℓ hr) (twoScaleModulus_nonneg β ℓ r hℓ hr)
  have hH := Real.rpow_nonneg hh γ
  have he : stencilBiasSize p T α β γ Lπ L₀ Lτ upper h ℓ r =
      a * (twoScaleModulus α ℓ r * twoScaleModulus β ℓ r) + b * h ^ γ := by
    unfold stencilBiasSize stencilNuisanceBound a b
    ring
  have hc : stencilBiasConstant p T Lπ L₀ Lτ upper = a + b := by
    unfold stencilBiasConstant a b
    ring
  rw [he, hc]
  nlinarith [mul_nonneg ha hH, mul_nonneg hb hS]

theorem sqrt_quadratic_sum_le {a b v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hv : 0 ≤ v) :
    Real.sqrt (a ^ 2 + b * v) ≤ a + (1 + b) * Real.sqrt v := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hmul : b * v ≤ ((1 + b) * Real.sqrt v) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hv]
    exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg b]) hv
  nlinarith [mul_nonneg ha (show 0 ≤ (1 + b) * Real.sqrt v by positivity)]

theorem sqrt_stencilMseEnvelope_le_master (p qγ : ℕ) (T : StencilTemplate d p) (α β γ : ℝ)
    {Lπ L₀ Lτ upper M₂ B c h ℓ r η : ℝ}
    (hπ : 0 ≤ Lπ) (h₀ : 0 ≤ L₀) (hτ : 0 ≤ Lτ) (hu : 0 ≤ upper) (hM : 0 ≤ M₂)
    (hB : 0 ≤ B) (hh : 0 ≤ h) (hℓ : 0 ≤ ℓ) (hr : 0 ≤ r) (hη : 0 ≤ η) :
    Real.sqrt (stencilMseEnvelope p qγ T α β γ Lπ L₀ Lτ upper M₂ B c h ℓ r η) ≤
      stencilMasterConstant p qγ T Lπ L₀ Lτ upper M₂ B c *
        (h ^ γ + twoScaleModulus α ℓ r * twoScaleModulus β ℓ r +
          Real.sqrt (stencilVarianceTerm (d := d) h ℓ η)) := by
  let D := stencilBiasConstant p T Lπ L₀ Lτ upper
  let A := stencilMomentConstant (d := d) p qγ upper M₂ Lτ B
  let V := stencilVarianceTerm (d := d) h ℓ η
  let S := h ^ γ + twoScaleModulus α ℓ r * twoScaleModulus β ℓ r
  have hD : 0 ≤ D := stencilBiasConstant_nonneg p T hπ h₀ hτ hu
  have hA : 0 ≤ A := stencilMomentConstant_nonneg p qγ hu hM hB
  have hV : 0 ≤ V := by dsimp [V, stencilVarianceTerm]; positivity
  have hS : 0 ≤ S := add_nonneg (Real.rpow_nonneg hh _) (mul_nonneg
    (twoScaleModulus_nonneg α ℓ r hℓ hr) (twoScaleModulus_nonneg β ℓ r hℓ hr))
  have hδ := stencilBiasSize_nonneg p T α β γ hπ h₀ hτ hu hh hℓ hr
  have hδbound := stencilBiasSize_le_master p T α β γ hπ h₀ hτ hu hh hℓ hr
  change Real.sqrt (3 / c ^ 2 * (stencilBiasSize p T α β γ Lπ L₀ Lτ upper h ℓ r ^ 2 + A * V)) ≤
    (Real.sqrt (3 / c ^ 2) * (1 + D + A)) * (S + Real.sqrt V)
  rw [Real.sqrt_mul (by positivity), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply (sqrt_quadratic_sum_le hδ hA hV).trans
  calc
    _ ≤ D * S + (1 + A) * Real.sqrt V := add_le_add_right hδbound _
    _ ≤ (1 + D + A) * S + (1 + D + A) * Real.sqrt V :=
      add_le_add (mul_le_mul_of_nonneg_right (by linarith) hS)
        (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
    _ = _ := by ring

end CausalLowerbound.UpperBound
