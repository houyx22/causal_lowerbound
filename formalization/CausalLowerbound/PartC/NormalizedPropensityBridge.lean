import CausalLowerbound.PartC.SingleSiteBridge

/-! The degree-one design bridge in the normalization used by the
physical carrier. No division by the assignment multiplier is used;
the formulas hold where that multiplier vanishes. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC.RoughPropensity
variable {Ω : Type*} [Fintype Ω]

def normalizedSubstitution (f : ℕ) (scale ja v Λ : ℝ) : ℝ :=
  if f = 0 then scale * Λ else scale ^ 2 * ja ^ 2 * v ^ 2

theorem normalizedSubstitution_eq (f : ℕ) (hf : f ≤ 1) (scale ja v Λ : ℝ) :
    normalizedSubstitution f scale ja v Λ = scale ^ (f + 1) * substitution f ja v Λ := by
  interval_cases f <;> simp [normalizedSubstitution, substitution] <;> ring

theorem normalized_design_weighted_bridge (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (R T ja jb v scale : ℝ) (hmean : μ.expect X = 0)
    (hvar : μ.expect (fun ω => X ω ^ 2) = v) (f : ℕ) (hf : f ≤ 1) :
    μ.expect (fun ω => normalizedSubstitution f scale ja v (X ω) * increment R T ja jb (X ω)) =
      μ.expect (fun ω => (scale * X ω) ^ f * realField R T ja (ja * jb * scale * v) (X ω)) := by
  calc
    _ = scale ^ (f + 1) * μ.expect (fun ω => substitution f ja v (X ω) * increment R T ja jb (X ω)) := by
      simp only [normalizedSubstitution_eq f hf, mul_assoc, FiniteLaw.expect_mul]
    _ = scale ^ (f + 1) * μ.expect (fun ω => X ω ^ f * realField R T ja (ja * jb * v) (X ω)) := by
      rw [design_weighted_bridge μ X R T ja jb v hmean hvar f hf]
    _ = _ := by
      rw [← μ.expect_mul]
      apply μ.expect_congr
      intro ω
      simp only [realField, mul_pow, pow_succ]
      ring

theorem normalized_cell_bridge (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (R T ja jb v scale ζ : ℝ) (hmean : μ.expect X = 0)
    (hvar : μ.expect (fun ω => X ω ^ 2) = v) (f : ℕ) (hf : f ≤ 1) :
    μ.expect (fun ω => (scale * X ω) ^ f * likelihood R T ja ζ (X ω) +
      normalizedSubstitution f scale ja v (X ω) * increment R T ja jb (X ω)) =
      μ.expect (fun ω => (scale * X ω) ^ f *
        (likelihood R T ja ζ (X ω) + realField R T ja (ja * jb * scale * v) (X ω))) := by
  rw [μ.expect_add, normalized_design_weighted_bridge μ X R T ja jb v scale hmean hvar f hf]
  simp only [mul_add, μ.expect_add]

theorem normalized_product_bridge {I : Type*} [Fintype I] [DecidableEq I]
    {Ξ : I → Type*} [∀ i, Fintype (Ξ i)] (μ : ∀ i, FiniteLaw (Ξ i)) (X : ∀ i, Ξ i → ℝ)
    (R T ja jb v scale ζ : I → ℝ) (hmean : ∀ i, (μ i).expect (X i) = 0)
    (hvar : ∀ i, (μ i).expect (fun ω => X i ω ^ 2) = v i) (f : I → ℕ) (hf : ∀ i, f i ≤ 1) :
    (FiniteLaw.independent μ).expect (fun ω => ∏ i,
      ((scale i * X i (ω i)) ^ f i * likelihood (R i) (T i) (ja i) (ζ i) (X i (ω i)) +
        normalizedSubstitution (f i) (scale i) (ja i) (v i) (X i (ω i)) *
          increment (R i) (T i) (ja i) (jb i) (X i (ω i)))) =
      (FiniteLaw.independent μ).expect (fun ω => ∏ i, (scale i * X i (ω i)) ^ f i *
        (likelihood (R i) (T i) (ja i) (ζ i) (X i (ω i)) +
          realField (R i) (T i) (ja i) (ja i * jb i * scale i * v i) (X i (ω i)))) := by
  rw [FiniteLaw.expect_independent_prod μ (fun i x =>
    (scale i * X i x) ^ f i * likelihood (R i) (T i) (ja i) (ζ i) (X i x) +
      normalizedSubstitution (f i) (scale i) (ja i) (v i) (X i x) *
        increment (R i) (T i) (ja i) (jb i) (X i x)),
    FiniteLaw.expect_independent_prod μ (fun i x =>
      (scale i * X i x) ^ f i *
        (likelihood (R i) (T i) (ja i) (ζ i) (X i x) +
          realField (R i) (T i) (ja i) (ja i * jb i * scale i * v i) (X i x)))]
  apply Finset.prod_congr rfl
  intro i _
  exact normalized_cell_bridge (μ i) (X i) (R i) (T i) (ja i) (jb i) (v i) (scale i) (ζ i)
    (hmean i) (hvar i) (f i) (hf i)

end CausalLowerbound.PartC.RoughPropensity
