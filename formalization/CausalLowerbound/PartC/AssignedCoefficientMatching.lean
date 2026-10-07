import CausalLowerbound.PartC.AssignedPatternExpansion

/-! Sum the assigned-row bridge over the actual finite row choices in all
blocks. Coefficients are held fixed while rough variables are averaged;
they may have arbitrary signs and may encode frozen Fourier, Walsh, and
ghost factors. No independence between carrier coefficients is required. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC
open PartB RoughPropensity
variable {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]

theorem weighted_block_pattern_expansion {A : Type*} [Fintype A]
    {Rows : K → Type*} [∀ k, Fintype (Rows k)]
    (w : A → ℝ) (b : ∀ k, Rows k → ℝ) (f : A → ∀ k, Rows k → ℝ) :
    (∑ s, w s * ∏ k, ∑ r, b k r * f s k r) =
      ∑ r : ∀ k, Rows k, (∏ k, b k (r k)) * ∑ s, w s * ∏ k, f s k (r k) := by
  simp only [Fintype.prod_sum, Finset.prod_mul_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem assigned_coefficient_pattern_matching
    {Rows : K → Type*} [∀ k, Fintype (Rows k)]
    (coeff : ∀ k, Rows k → ℝ) (degree : ∀ k, Rows k → I → ℕ)
    {Ξ : I → Type*} [∀ i, Fintype (Ξ i)] (μ : ∀ i, FiniteLaw (Ξ i)) (X : ∀ i, Ξ i → ℝ)
    (R T ja v smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0)
    (he : ∀ i r, degree (owner i) r i ≤ 1)
    (hmean : ∀ i, (μ i).expect (X i) = 0)
    (hvar : ∀ i, (μ i).expect (fun ω => X i ω ^ 2) = v i) :
    (FiniteLaw.independent μ).expect (fun ω => ∑ s : I → Option K,
      (choiceBase (fun i => likelihood (R i) (T i) (ja i) (smooth i) (X i (ω i))) s *
        ∏ i : ShiftPositions s, increment (R i.val) (T i.val) (ja i.val)
          (shift i.val (choiceSite s i)) (X i.val (ω i.val))) *
        ∏ k, ∑ r, coeff k r * ∏ i, if s i = some k then
          normalizedSubstitution (degree k r i) (scale i k) (ja i) (v i) (X i (ω i))
          else (scale i k * X i (ω i)) ^ degree k r i) =
      (FiniteLaw.independent μ).expect (fun ω =>
        (∏ k, ∑ r, coeff k r * ∏ i, (scale i k * X i (ω i)) ^ degree k r i) *
          ∏ i, (likelihood (R i) (T i) (ja i) (smooth i) (X i (ω i)) +
            realField (R i) (T i) (ja i) (ja i * shift i (owner i) * scale i (owner i) * v i) (X i (ω i)))) := by
  let law := FiniteLaw.independent μ
  let w := fun (ω : ∀ i, Ξ i) (s : I → Option K) =>
    choiceBase (fun i => likelihood (R i) (T i) (ja i) (smooth i) (X i (ω i))) s *
      ∏ i : ShiftPositions s, increment (R i.val) (T i.val) (ja i.val)
        (shift i.val (choiceSite s i)) (X i.val (ω i.val))
  let f := fun (ω : ∀ i, Ξ i) (s : I → Option K) (k : K) (r : Rows k) => ∏ i,
    if s i = some k then normalizedSubstitution (degree k r i) (scale i k) (ja i) (v i) (X i (ω i))
      else (scale i k * X i (ω i)) ^ degree k r i
  let g := fun (k : K) (r : Rows k) (ω : ∀ i, Ξ i) => ∏ i, (scale i k * X i (ω i)) ^ degree k r i
  let c := fun r : ∀ k, Rows k => ∏ k, coeff k (r k)
  let P := fun ω : ∀ i, Ξ i => ∏ i,
    (likelihood (R i) (T i) (ja i) (smooth i) (X i (ω i)) +
      realField (R i) (T i) (ja i) (ja i * shift i (owner i) * scale i (owner i) * v i) (X i (ω i)))
  have hsum (F : (∀ k, Rows k) → (∀ i, Ξ i) → ℝ) :
      law.expect (fun ω => ∑ r, F r ω) = ∑ r, law.expect (F r) := by
    simp only [FiniteLaw.expect, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hmatch (r : ∀ k, Rows k) :
      law.expect (fun ω => ∑ s, w ω s * ∏ k, f ω s k (r k)) =
        law.expect (fun ω => (∏ k, g k (r k) ω) * P ω) :=
    assigned_pattern_row_matching μ X R T ja v smooth shift scale owner hscale
      (fun i k => degree k (r k) i) (fun i => he i (r (owner i))) hmean hvar
  change law.expect (fun ω => ∑ s, w ω s * ∏ k, ∑ r, coeff k r * f ω s k r) =
    law.expect (fun ω => (∏ k, ∑ r, coeff k r * g k r ω) * P ω)
  calc
    _ = law.expect (fun ω => ∑ r : ∀ k, Rows k, c r * ∑ s, w ω s * ∏ k, f ω s k (r k)) := by
      apply law.expect_congr
      intro ω
      exact weighted_block_pattern_expansion (w ω) coeff (f ω)
    _ = ∑ r : ∀ k, Rows k, c r * law.expect (fun ω => ∑ s, w ω s * ∏ k, f ω s k (r k)) := by
      rw [hsum]
      simp only [law.expect_mul]
    _ = ∑ r : ∀ k, Rows k, c r * law.expect (fun ω => (∏ k, g k (r k) ω) * P ω) := by
      simp only [hmatch]
    _ = law.expect (fun ω => ∑ r : ∀ k, Rows k, c r * ((∏ k, g k (r k) ω) * P ω)) := by
      rw [hsum]
      simp only [law.expect_mul]
    _ = _ := by
      apply law.expect_congr
      intro ω
      simp only [Fintype.prod_sum, Finset.prod_mul_distrib, Finset.sum_mul, c]
      apply Finset.sum_congr rfl
      intro r _
      ring

end CausalLowerbound.PartC
