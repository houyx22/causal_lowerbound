import CausalLowerbound.PartC.PairedPhysicalDensity
import CausalLowerbound.PartC.RepresentativePermutation

/-! Permutation symmetry of the actual carrier and of its removed
representatives. It is proved for arbitrary formal real site variables,
not inferred from equality only along a physical rough-field chart. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC.Representative
open Wiener
variable {d V J : Type*} [Fintype d] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] {D : ℕ}

theorem pointValue_general_bound (x : Torus (V × d)) (z : V → ℝ) (ζ : J → Bool)
    (W : Representative.Array d V J D) :
    |pointValue x z ζ W| ≤ (∑ r : Row V J D, |rowWeight r z ζ|) * ‖W‖ := by
  calc
    _ ≤ ∑ r : Row V J D, |rowWeight r z ζ * (toContinuous (W r) x).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Row V J D, |rowWeight r z ζ| * ‖W‖ := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (Complex.abs_re_le_norm _).trans ((Wiener.evaluate_bound _ _).trans
        (lp.norm_apply_le_norm (by norm_num) W r))
    _ = _ := (Finset.sum_mul _ _ _).symm

def unrestrictedPointEvaluation (x : Torus (V × d)) (z : V → ℝ) (ζ : J → Bool) :
    Representative.Array d V J D →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := pointValue x z ζ
      map_add' := pointValue_add x z ζ
      map_smul' := pointValue_smul x z ζ }
    (∑ r : Row V J D, |rowWeight r z ζ|)
    (fun W => by simpa only [Real.norm_eq_abs] using pointValue_general_bound x z ζ W)

@[simp] theorem unrestrictedPointEvaluation_apply (x : Torus (V × d)) (z : V → ℝ)
    (ζ : J → Bool) (W : Representative.Array d V J D) :
    unrestrictedPointEvaluation x z ζ W = pointValue x z ζ W := rfl

theorem tensor_constant_value_symmetric (f : Factor d J D) (x : Torus (V × d))
    (z : V → ℝ) (ζ : J → Bool) (σ : Equiv.Perm V) :
    pointValue (permuteSlots σ x) (fun i => z (σ i)) ζ (tensor (fun _ : V => f)) =
      pointValue x z ζ (tensor (fun _ : V => f)) := by
  rw [tensor_value, tensor_value]
  apply congrArg Complex.re
  exact Equiv.prod_comp σ (fun i => factorValue (fun j => x (i, j)) (z i) ζ f)

theorem naturalPolynomialAtom_value_symmetric
    (center : PolynomialBasis d V D → V → Walsh.Coefficients J) (θ : ℝ) (n : ℕ)
    (x : Torus (V × d)) (z : V → ℝ) (ζ : J → Bool) (σ : Equiv.Perm V) :
    pointValue (permuteSlots σ x) (fun i => z (σ i)) ζ (naturalPolynomialAtom center θ n) =
      pointValue x z ζ (naturalPolynomialAtom center θ n) := by
  unfold naturalPolynomialAtom
  split
  · exact tensor_constant_value_symmetric _ x z ζ σ
  · simp only [pointValue_unit]

theorem pointValue_remove_eq_expect (S : Finset J) (W : Representative.Array d V J D)
    (x : Torus (V × d)) (z : V → ℝ) (ζ : J → Bool) :
    pointValue x z ζ (remove S W) =
      PartB.independentSigns.expect (fun fresh => pointValue x z (Walsh.resample S ζ fresh) W) := by
  have hsum (f : Row V J D → (J → Bool) → ℝ) :
      PartB.independentSigns.expect (fun fresh => ∑ r, f r fresh) =
        ∑ r, PartB.independentSigns.expect (f r) := by
    simp only [FiniteLaw.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
  simp only [pointValue, rowWeight]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro r _
  rw [FiniteLaw.expect_mul_const, FiniteLaw.expect_mul, Walsh.character_resample_expect, remove_apply]
  by_cases hs : Disjoint r.2 S
  · simp only [if_pos hs]
  · simp only [if_neg hs, map_zero, ContinuousMap.zero_apply, Complex.zero_re, mul_zero, zero_mul]

theorem pointValue_remove_symmetric (S : Finset J) (W : Representative.Array d V J D)
    (hsym : ∀ (x : Torus (V × d)) (z : V → ℝ) (ζ : J → Bool) (σ : Equiv.Perm V),
      pointValue (permuteSlots σ x) (fun i => z (σ i)) ζ W = pointValue x z ζ W)
    (x : Torus (V × d)) (z : V → ℝ) (ζ : J → Bool) (σ : Equiv.Perm V) :
    pointValue (permuteSlots σ x) (fun i => z (σ i)) ζ (remove S W) = pointValue x z ζ (remove S W) := by
  rw [pointValue_remove_eq_expect, pointValue_remove_eq_expect]
  apply PartB.independentSigns.expect_congr
  intro fresh
  exact hsym x z (Walsh.resample S ζ fresh) σ

end CausalLowerbound.PartC.Representative

namespace CausalLowerbound.PartC
open Representative Wiener PartB PartB.ShellGeometry
variable {d V : Type*} [Fintype d] [DecidableEq d] [Fintype V] [DecidableEq V] {D : ℕ}

theorem carrierPhysicalAtom_value_symmetric (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N θ : ℝ) (n : ℕ) (x : Torus (V × d)) (z : V → ℝ)
    (ζ : activeBlocks (d := d) ℓ h → Bool) (σ : Equiv.Perm V) :
    let a := CarrierCoefficients.labeledAtom unit
      (pairedAtom reflection (naturalPhysicalAtom (ι := V) (D := D) x₀ ℓ r h k c w N θ)) n
    pointValue (permuteSlots σ x) (fun i => z (σ i)) ζ a = pointValue x z ζ a := by
  cases n with
  | zero => simp only [CarrierCoefficients.labeledAtom, pointValue_unit]
  | succ n =>
    simp only [CarrierCoefficients.labeledAtom, pairedAtom]
    cases PairedSeries.labels.symm n with
    | inl m => exact naturalPolynomialAtom_value_symmetric _ θ m x z ζ σ
    | inr m =>
      simp only [Sum.elim_inr, pointValue_reflection]
      exact naturalPolynomialAtom_value_symmetric _ θ m x (fun i => -z i) (Walsh.flip ζ) σ

theorem carrier_series_value_symmetric (x₀ : d → ℝ) (ℓ r h : ℝ) (k : d → ℤ)
    (c w N θ : ℝ) (H : DiscreteLaw ℕ)
    (B : Representative.Array d V (activeBlocks (d := d) ℓ h) D)
    (hs : HasSum (fun n => H.weight n • CarrierCoefficients.labeledAtom unit
      (pairedAtom reflection (naturalPhysicalAtom (ι := V) (D := D) x₀ ℓ r h k c w N θ)) n) B)
    (x : Torus (V × d)) (z : V → ℝ) (ζ : activeBlocks (d := d) ℓ h → Bool) (σ : Equiv.Perm V) :
    pointValue (permuteSlots σ x) (fun i => z (σ i)) ζ B = pointValue x z ζ B := by
  have h₁ := (unrestrictedPointEvaluation (D := D) (permuteSlots σ x) (fun i => z (σ i)) ζ).hasSum hs
  have h₂ := (unrestrictedPointEvaluation (D := D) x z ζ).hasSum hs
  simp only [map_smul, unrestrictedPointEvaluation_apply, smul_eq_mul,
    carrierPhysicalAtom_value_symmetric] at h₁ h₂
  exact h₁.unique h₂

end CausalLowerbound.PartC
