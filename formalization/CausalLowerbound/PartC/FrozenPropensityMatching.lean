import CausalLowerbound.PartC.AffineSitePolynomial
import CausalLowerbound.PartC.NormalizedPropensityBridge
import CausalLowerbound.PartC.PhysicalRoughMoments

/-! Exact matching for independent rough fields at the retained sites,
with the Fourier--Walsh coefficient array held fixed. Independence here
is an actual product law. Applying this to shared physical signs requires
the separate removal and spatial separation arguments. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open MvPolynomial Representative RoughPropensity
variable {V d J : Type*} [Fintype V] [DecidableEq V]
  [Fintype d] [Fintype J] [DecidableEq J]

theorem frozen_propensity_polynomial_matching
    {Ξ : V → Type*} [∀ i, Fintype (Ξ i)] (μ : ∀ i, FiniteLaw (Ξ i)) (F : ∀ i, Ξ i → ℝ)
    (R T ja jb v scale smooth : V → ℝ)
    (hmean : ∀ i, (μ i).expect (F i) = 0)
    (hvar : ∀ i, (μ i).expect (fun ω => F i ω ^ 2) = v i)
    (W : Representative.Array d V J 1) (u : V × d → ℝ) (ζ : J → Bool) :
    (FiniteLaw.independent μ).expect (fun ω =>
      propensityPolynomialFunctional (fun i => scale i ^ 2 * ja i ^ 2 * v i ^ 2)
        W u (fun i => scale i * F i (ω i)) ζ
        (∏ i, (C (increment (R i) (T i) (ja i) (jb i) (F i (ω i))) * X i +
          C (likelihood (R i) (T i) (ja i) (smooth i) (F i (ω i)))))) =
      (FiniteLaw.independent μ).expect (fun ω =>
        pointValue (Wiener.torusProjection u) (fun i => scale i * F i (ω i)) ζ W *
          ∏ i, (likelihood (R i) (T i) (ja i) (smooth i) (F i (ω i)) +
            realField (R i) (T i) (ja i) (ja i * jb i * scale i * v i) (F i (ω i)))) := by
  let law := FiniteLaw.independent μ
  let z (ω : ∀ i, Ξ i) (i : V) := scale i * F i (ω i)
  let a (ω : ∀ i, Ξ i) (i : V) := likelihood (R i) (T i) (ja i) (smooth i) (F i (ω i))
  let b (ω : ∀ i, Ξ i) (i : V) := increment (R i) (T i) (ja i) (jb i) (F i (ω i))
  let g (ω : ∀ i, Ξ i) (i : V) := a ω i +
    realField (R i) (T i) (ja i) (ja i * jb i * scale i * v i) (F i (ω i))
  let κ (i : V) := scale i ^ 2 * ja i ^ 2 * v i ^ 2
  let c (r : Row V J 1) := Walsh.character r.2 ζ * (Wiener.toContinuous (W r) (Wiener.torusProjection u)).re
  have hsum (f : Row V J 1 → (∀ i, Ξ i) → ℝ) :
      law.expect (fun ω => ∑ r, f r ω) = ∑ r, law.expect (f r) := by
    simp only [FiniteLaw.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hrow (e : Degree V 1) :
      law.expect (fun ω => ∏ i, (b ω i * (if e i = 0 then z ω i else κ i) +
        a ω i * z ω i ^ (e i).val)) =
      law.expect (fun ω => ∏ i, (z ω i ^ (e i).val * g ω i)) := by
    calc
      _ = law.expect (fun ω => ∏ i, (z ω i ^ (e i).val * a ω i +
          normalizedSubstitution (e i).val (scale i) (ja i) (v i) (F i (ω i)) * b ω i)) := by
        apply law.expect_congr
        intro ω
        apply Finset.prod_congr rfl
        intro i _
        simp only [normalizedSubstitution, Fin.val_eq_zero_iff]
        change b ω i * (if e i = 0 then z ω i else κ i) + a ω i * z ω i ^ (e i).val =
          z ω i ^ (e i).val * a ω i + (if e i = 0 then z ω i else κ i) * b ω i
        ring
      _ = _ := normalized_product_bridge μ F R T ja jb v scale smooth hmean hvar
        (fun i => (e i).val) (fun i => by
          change (e i).val ≤ 1
          exact Nat.le_of_lt_succ (e i).isLt)
  change law.expect (fun ω => propensityPolynomialFunctional κ W u (z ω) ζ
    (∏ i, (C (b ω i) * X i + C (a ω i)))) =
    law.expect (fun ω => pointValue (Wiener.torusProjection u) (z ω) ζ W * ∏ i, g ω i)
  simp_rw [propensityPolynomialFunctional_affine]
  rw [hsum]
  simp_rw [law.expect_mul, hrow]
  calc
    _ = law.expect (fun ω => ∑ r : Row V J 1,
        c r * ((∏ i, z ω i ^ (r.1 i).val) * ∏ i, g ω i)) := by
      rw [hsum]
      apply Finset.sum_congr rfl
      intro r _
      rw [← law.expect_mul]
      apply law.expect_congr
      intro ω
      rw [Finset.prod_mul_distrib]
    _ = _ := by
      apply law.expect_congr
      intro ω
      simp only [pointValue, rowWeight, Representative.monomial, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r _
      dsimp [c]
      ring

theorem fresh_physical_propensity_polynomial_matching [DecidableEq d]
    (x₀ : d → ℝ) (ℓ h : ℝ) (hℓ : 0 < ℓ) (hh : 0 < h) (x : V → d → ℝ)
    (R T ja jb scale smooth : V → ℝ)
    (W : Representative.Array d V J 1) (u : V × d → ℝ) (ζ : J → Bool) :
    (FiniteLaw.independent (fun _ : V => PartB.independentSigns (ι := PartB.ShellGeometry.activeBlocks (d := d) ℓ h))).expect
      (fun ω => propensityPolynomialFunctional
        (fun i => scale i ^ 2 * ja i ^ 2 * (PartB.ShellGeometry.coarseBump x₀ h (x i) ^ 2) ^ 2)
        W u (fun i => scale i * physicalRoughField x₀ ℓ h (ω i) (x i)) ζ
        (∏ i, (C (increment (R i) (T i) (ja i) (jb i) (physicalRoughField x₀ ℓ h (ω i) (x i))) * X i +
          C (likelihood (R i) (T i) (ja i) (smooth i) (physicalRoughField x₀ ℓ h (ω i) (x i)))))) =
      (FiniteLaw.independent (fun _ : V => PartB.independentSigns (ι := PartB.ShellGeometry.activeBlocks (d := d) ℓ h))).expect
        (fun ω => pointValue (Wiener.torusProjection u)
          (fun i => scale i * physicalRoughField x₀ ℓ h (ω i) (x i)) ζ W *
          ∏ i, (likelihood (R i) (T i) (ja i) (smooth i) (physicalRoughField x₀ ℓ h (ω i) (x i)) +
            realField (R i) (T i) (ja i)
              (ja i * jb i * scale i * PartB.ShellGeometry.coarseBump x₀ h (x i) ^ 2)
              (physicalRoughField x₀ ℓ h (ω i) (x i)))) := by
  exact frozen_propensity_polynomial_matching _ _ R T ja jb _ scale smooth
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).1)
    (fun i => (physicalRoughField_moments x₀ ℓ h hℓ hh (x i)).2.1) W u ζ

end CausalLowerbound.PartC
