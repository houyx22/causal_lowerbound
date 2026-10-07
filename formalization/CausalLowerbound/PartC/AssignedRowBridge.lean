import CausalLowerbound.PartC.NormalizedPropensityBridge

/-! The design-weighted bridge with overlapping carrier rows. At each
observation, only its assigned carrier has a nonzero multiplier. The other
rows remain in the product (including their zero powers), so no global
degree-one assumption is imposed on an overlapping carrier product. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC.RoughPropensity
variable {K Ω : Type*} [Fintype K] [DecidableEq K] [Fintype Ω]

theorem assigned_row_bridge (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (R T ja v smooth : ℝ) (shift scale : K → ℝ) (owner : K)
    (hscale : ∀ k, k ≠ owner → scale k = 0)
    (e : K → ℕ) (he : e owner ≤ 1)
    (hmean : μ.expect X = 0) (hvar : μ.expect (fun ω => X ω ^ 2) = v) :
    μ.expect (fun ω => (∏ k, (scale k * X ω) ^ e k) * likelihood R T ja smooth (X ω) +
      ∑ k, (normalizedSubstitution (e k) (scale k) ja v (X ω) * increment R T ja (shift k) (X ω)) *
        ∏ j ∈ Finset.univ.erase k, (scale j * X ω) ^ e j) =
    μ.expect (fun ω => (∏ k, (scale k * X ω) ^ e k) *
      (likelihood R T ja smooth (X ω) + realField R T ja (ja * shift owner * scale owner * v) (X ω))) := by
  let C := ∏ k ∈ Finset.univ.erase owner, (0 : ℝ) ^ e k
  have hoff (z : ℝ) : (∏ k ∈ Finset.univ.erase owner, (scale k * z) ^ e k) = C := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [hscale k (Finset.mem_erase.mp hk).1, zero_mul]
  have hp (z : ℝ) : (∏ k, (scale k * z) ^ e k) = C * (scale owner * z) ^ e owner := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => (scale k * z) ^ e k) (Finset.mem_univ owner), hoff]
    ring
  have hs (z : ℝ) : (∑ k, (normalizedSubstitution (e k) (scale k) ja v z * increment R T ja (shift k) z) *
      ∏ j ∈ Finset.univ.erase k, (scale j * z) ^ e j) =
      C * (normalizedSubstitution (e owner) (scale owner) ja v z * increment R T ja (shift owner) z) := by
    rw [Finset.sum_eq_single owner]
    · rw [hoff]
      ring
    · intro k _ hk
      simp only [normalizedSubstitution, hscale k hk, zero_mul, zero_pow (by decide : 2 ≠ 0), ite_self]
    · intro hk
      exact False.elim (hk (Finset.mem_univ owner))
  simp_rw [hp, hs]
  have hl (ω : Ω) : C * (scale owner * X ω) ^ e owner * likelihood R T ja smooth (X ω) +
      C * (normalizedSubstitution (e owner) (scale owner) ja v (X ω) * increment R T ja (shift owner) (X ω)) =
      C * ((scale owner * X ω) ^ e owner * likelihood R T ja smooth (X ω) +
        normalizedSubstitution (e owner) (scale owner) ja v (X ω) * increment R T ja (shift owner) (X ω)) := by ring
  simp_rw [hl, mul_assoc]
  rw [μ.expect_mul, μ.expect_mul]
  simpa only [mul_assoc] using congrArg (fun a : ℝ => C * a)
    (normalized_cell_bridge μ X R T ja (shift owner) v (scale owner) smooth hmean hvar (e owner) he)

theorem assigned_product_bridge {I : Type*} [Fintype I] [DecidableEq I]
    {Ξ : I → Type*} [∀ i, Fintype (Ξ i)] (μ : ∀ i, FiniteLaw (Ξ i)) (X : ∀ i, Ξ i → ℝ)
    (R T ja v smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0)
    (e : I → K → ℕ) (he : ∀ i, e i (owner i) ≤ 1)
    (hmean : ∀ i, (μ i).expect (X i) = 0)
    (hvar : ∀ i, (μ i).expect (fun ω => X i ω ^ 2) = v i) :
    (FiniteLaw.independent μ).expect (fun ω => ∏ i,
      ((∏ k, (scale i k * X i (ω i)) ^ e i k) * likelihood (R i) (T i) (ja i) (smooth i) (X i (ω i)) +
        ∑ k, (normalizedSubstitution (e i k) (scale i k) (ja i) (v i) (X i (ω i)) *
          increment (R i) (T i) (ja i) (shift i k) (X i (ω i))) *
          ∏ j ∈ Finset.univ.erase k, (scale i j * X i (ω i)) ^ e i j)) =
    (FiniteLaw.independent μ).expect (fun ω => ∏ i, (∏ k, (scale i k * X i (ω i)) ^ e i k) *
      (likelihood (R i) (T i) (ja i) (smooth i) (X i (ω i)) +
        realField (R i) (T i) (ja i) (ja i * shift i (owner i) * scale i (owner i) * v i) (X i (ω i)))) := by
  let L := fun i (ω : Ξ i) =>
    (∏ k, (scale i k * X i ω) ^ e i k) * likelihood (R i) (T i) (ja i) (smooth i) (X i ω) +
      ∑ k, (normalizedSubstitution (e i k) (scale i k) (ja i) (v i) (X i ω) *
        increment (R i) (T i) (ja i) (shift i k) (X i ω)) *
          ∏ j ∈ Finset.univ.erase k, (scale i j * X i ω) ^ e i j
  let P := fun i (ω : Ξ i) => (∏ k, (scale i k * X i ω) ^ e i k) *
    (likelihood (R i) (T i) (ja i) (smooth i) (X i ω) +
      realField (R i) (T i) (ja i) (ja i * shift i (owner i) * scale i (owner i) * v i) (X i ω))
  change (FiniteLaw.independent μ).expect (fun ω => ∏ i, L i (ω i)) =
    (FiniteLaw.independent μ).expect (fun ω => ∏ i, P i (ω i))
  rw [FiniteLaw.expect_independent_prod μ L, FiniteLaw.expect_independent_prod μ P]
  apply Finset.prod_congr rfl
  intro i _
  exact assigned_row_bridge (μ i) (X i) (R i) (T i) (ja i) (v i) (smooth i)
    (shift i) (scale i) (owner i) (hscale i) (e i) (he i) (hmean i) (hvar i)

end CausalLowerbound.PartC.RoughPropensity
