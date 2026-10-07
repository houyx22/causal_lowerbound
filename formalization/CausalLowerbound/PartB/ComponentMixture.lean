import CausalLowerbound.FiniteHellinger

/-!
# From partial-shift mixtures to a local Hellinger bound

This proves the finite probability argument in `B:eq:component-cell-difference`
and `B:eq:component-hellinger-local`. The input is a family of partial-shift
laws and the product activation weights. The actual carrier identity and
physical local information bound are established in ComponentActivation
and PhysicalLocalHellinger, including removal of nonincident blocks.
-/

noncomputable section
set_option autoImplicit false

namespace CausalLowerbound.PartB

open scoped BigOperators

def activationLaw (χ : ℝ) (h0 : 0 ≤ χ) (h1 : χ ≤ 1) : FiniteLaw Bool where
  weight b := if b then χ else 1 - χ
  nonneg b := by
    cases b with
    | false => exact sub_nonneg.mpr h1
    | true => exact h0
  total := by simp [Fintype.sum_bool]

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

def activationProduct (χ : ι → ℝ) (h0 : ∀ i, 0 ≤ χ i) (h1 : ∀ i, χ i ≤ 1) :
    FiniteLaw (ι → Bool) := FiniteLaw.independent (fun i => activationLaw (χ i) (h0 i) (h1 i))

theorem full_activation_weight (χ : ι → ℝ) (h0 : ∀ i, 0 ≤ χ i) (h1 : ∀ i, χ i ≤ 1) :
    (activationProduct χ h0 h1).weight (fun _ => true) = ∏ i, χ i := rfl

omit [DecidableEq ι] in
/-- The elementary union bound for failure of at least one block activation. -/
theorem one_sub_prod_le_sum (χ : ι → ℝ) (h0 : ∀ i, 0 ≤ χ i) (h1 : ∀ i, χ i ≤ 1) :
    1 - ∏ i, χ i ≤ ∑ i, (1 - χ i) := by
  have h := abs_prod_sub_prod_le Finset.univ (fun _ : ι => (1 : ℝ)) χ
    (by simp) (fun i _ => by rw [abs_of_nonneg (h0 i)]; exact h1 i)
  simp only [Finset.prod_const_one] at h
  have he : (∑ i, |1 - χ i|) = ∑ i, (1 - χ i) :=
    Finset.sum_congr rfl (fun i _ => abs_of_nonneg (sub_nonneg.mpr (h1 i)))
  rw [he] at h
  exact (le_abs_self _).trans h

/-- Exact matching when every block is active saves the fully shifted mass. -/
theorem partial_mixture_cell_bound (χ : ι → ℝ)
    (h0 : ∀ i, 0 ≤ χ i) (h1 : ∀ i, χ i ≤ 1)
    (P : FiniteLaw Ω) (laws : (ι → Bool) → FiniteLaw Ω) (ε : ℝ) (hε : 0 ≤ ε)
    (hfull : ∀ ω, (laws (fun _ => true)).weight ω = P.weight ω)
    (herr : ∀ b ω, |(laws b).weight ω - P.weight ω| ≤ ε) (ω : Ω) :
    |((activationProduct χ h0 h1).mixture laws).weight ω - P.weight ω| ≤
      ε * ∑ i, (1 - χ i) := by
  have h := (activationProduct χ h0 h1).matched_component_error (fun _ => true)
    (fun b => (laws b).weight ω) (P.weight ω) ε (hfull ω) (fun b => herr b ω)
  rw [full_activation_weight] at h
  exact h.trans (mul_le_mul_of_nonneg_left (one_sub_prod_le_sum χ h0 h1) hε)

theorem partial_mixture_sq_cell_bound (χ : ι → ℝ)
    (h0 : ∀ i, 0 ≤ χ i) (h1 : ∀ i, χ i ≤ 1)
    (P : FiniteLaw Ω) (laws : (ι → Bool) → FiniteLaw Ω) (ε : ℝ)
    (hfull : ∀ ω, (laws (fun _ => true)).weight ω = P.weight ω)
    (herr : ∀ b ω, |(laws b).weight ω - P.weight ω| ≤ ε) (ω : Ω) :
    (((activationProduct χ h0 h1).mixture laws).weight ω - P.weight ω) ^ 2 ≤
      ε ^ 2 * ∑ i, (1 - χ i) := by
  have h := (activationProduct χ h0 h1).matched_component_sq_error (fun _ => true)
    (fun b => (laws b).weight ω) (P.weight ω) ε (hfull ω) (fun b => herr b ω)
  rw [full_activation_weight] at h
  exact h.trans (mul_le_mul_of_nonneg_left (one_sub_prod_le_sum χ h0 h1) (sq_nonneg ε))

/-- The local Hellinger bound, with all finite-state constants explicit.
Taking ε = C_Q*Δ and a uniform cell lower bound lower gives the paper's form. -/
theorem partial_mixture_hellinger_bound (χ : ι → ℝ)
    (h0 : ∀ i, 0 ≤ χ i) (h1 : ∀ i, χ i ≤ 1)
    (P : FiniteLaw Ω) (laws : (ι → Bool) → FiniteLaw Ω) (ε lower : ℝ)
    (hlower : 0 < lower) (hP : ∀ ω, lower ≤ P.weight ω)
    (hfull : ∀ ω, (laws (fun _ => true)).weight ω = P.weight ω)
    (herr : ∀ b ω, |(laws b).weight ω - P.weight ω| ≤ ε) :
    P.hellingerSq ((activationProduct χ h0 h1).mixture laws) ≤
      ((Fintype.card Ω : ℝ) * ε ^ 2 / lower) * ∑ i, (1 - χ i) := by
  calc
    _ ≤ (Fintype.card Ω : ℝ) * (ε ^ 2 * ∑ i, (1 - χ i)) / lower := by
      apply FiniteLaw.hellingerSq_le_of_sq_error _ _ lower _ hlower hP
      intro ω
      have h := partial_mixture_sq_cell_bound χ h0 h1 P laws ε hfull herr ω
      nlinarith [h]
    _ = _ := by ring

end CausalLowerbound.PartB
