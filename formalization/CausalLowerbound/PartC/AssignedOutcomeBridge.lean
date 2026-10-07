import CausalLowerbound.PartC.NormalizedOutcomeBridge

/-! The cubic bridge with overlapping carrier rows. Only the assigned
row has nonzero normalization at a retained site; all other row powers
remain present. No degree-three assumption on their full product is used. -/

noncomputable section
set_option autoImplicit false
open scoped BigOperators Classical

namespace CausalLowerbound.PartC.RoughOutcome
variable {K Ω : Type*} [Fintype K] [DecidableEq K] [Fintype Ω]

def normalizedIncrement (f : Fin 4) (scale v R T shift jb η smooth X : ℝ) : ℝ :=
  normalizedSubstitution 1 f scale v X * incrementOne R T shift jb η smooth X +
    normalizedSubstitution 2 f scale v X * incrementTwo R T shift jb smooth X +
    normalizedSubstitution 3 f scale v X * incrementThree R T shift jb X

theorem normalizedIncrement_zero_scale (f : Fin 4) (v R T shift jb η smooth X : ℝ) :
    normalizedIncrement f 0 v R T shift jb η smooth X = 0 := by
  simp [normalizedIncrement, normalizedSubstitution]

theorem assigned_row_bridge (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (R T jb η v smooth : ℝ) (shift scale : K → ℝ) (owner : K)
    (hscale : ∀ k, k ≠ owner → scale k = 0) (e : K → Fin 4)
    (hmean : μ.expect X = 0) (hvar : μ.expect (fun ω => X ω ^ 2) = v)
    (hthird : μ.expect (fun ω => X ω ^ 3) = 0)
    (hcorrection : ((shift owner * scale owner) * jb * v) * η =
      (shift owner * scale owner) ^ 3 * jb * μ.expect (fun ω => X ω ^ 4)) :
    μ.expect (fun ω => (∏ k, (scale k * X ω) ^ (e k).val) * likelihood R T jb η smooth (X ω) +
      ∑ k, normalizedIncrement (e k) (scale k) v R T (shift k) jb η smooth (X ω) *
        ∏ j ∈ Finset.univ.erase k, (scale j * X ω) ^ (e j).val) =
    μ.expect (fun ω => (∏ k, (scale k * X ω) ^ (e k).val) *
      (likelihood R T jb η smooth (X ω) + realField R T smooth ((shift owner * scale owner) * jb * v))) := by
  let C := ∏ k ∈ Finset.univ.erase owner, (0 : ℝ) ^ (e k).val
  have hoff (z : ℝ) : (∏ k ∈ Finset.univ.erase owner, (scale k * z) ^ (e k).val) = C := by
    apply Finset.prod_congr rfl
    intro k hk
    rw [hscale k (Finset.mem_erase.mp hk).1, zero_mul]
  have hp (z : ℝ) : (∏ k, (scale k * z) ^ (e k).val) = C * (scale owner * z) ^ (e owner).val := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => (scale k * z) ^ (e k).val)
      (Finset.mem_univ owner), hoff]
    ring
  have hs (z : ℝ) : (∑ k, normalizedIncrement (e k) (scale k) v R T (shift k) jb η smooth z *
      ∏ j ∈ Finset.univ.erase k, (scale j * z) ^ (e j).val) =
      C * normalizedIncrement (e owner) (scale owner) v R T (shift owner) jb η smooth z := by
    rw [Finset.sum_eq_single owner]
    · rw [hoff, mul_comm]
    · intro k _ hk
      rw [hscale k hk, normalizedIncrement_zero_scale, zero_mul]
    · intro hk
      exact False.elim (hk (Finset.mem_univ owner))
  simp_rw [hp, hs]
  have hl (ω : Ω) : C * (scale owner * X ω) ^ (e owner).val * likelihood R T jb η smooth (X ω) +
      C * normalizedIncrement (e owner) (scale owner) v R T (shift owner) jb η smooth (X ω) =
      C * ((scale owner * X ω) ^ (e owner).val * likelihood R T jb η smooth (X ω) +
        normalizedIncrement (e owner) (scale owner) v R T (shift owner) jb η smooth (X ω)) := by ring
  simp_rw [hl, mul_assoc]
  rw [μ.expect_mul, μ.expect_mul]
  simpa only [normalizedIncrement, mul_assoc] using congrArg (fun a : ℝ => C * a)
    (normalized_cell_bridge μ X R T (shift owner) jb η smooth v (scale owner)
      hmean hvar hthird hcorrection (e owner))

theorem assigned_product_bridge {I : Type*} [Fintype I] [DecidableEq I]
    {Ξ : I → Type*} [∀ i, Fintype (Ξ i)] (μ : ∀ i, FiniteLaw (Ξ i)) (X : ∀ i, Ξ i → ℝ)
    (R T jb η v smooth : I → ℝ) (shift scale : I → K → ℝ) (owner : I → K)
    (hscale : ∀ i k, k ≠ owner i → scale i k = 0) (e : I → K → Fin 4)
    (hmean : ∀ i, (μ i).expect (X i) = 0)
    (hvar : ∀ i, (μ i).expect (fun ω => X i ω ^ 2) = v i)
    (hthird : ∀ i, (μ i).expect (fun ω => X i ω ^ 3) = 0)
    (hcorrection : ∀ i, ((shift i (owner i) * scale i (owner i)) * jb i * v i) * η i =
      (shift i (owner i) * scale i (owner i)) ^ 3 * jb i * (μ i).expect (fun ω => X i ω ^ 4)) :
    (FiniteLaw.independent μ).expect (fun ω => ∏ i,
      ((∏ k, (scale i k * X i (ω i)) ^ (e i k).val) * likelihood (R i) (T i) (jb i) (η i) (smooth i) (X i (ω i)) +
        ∑ k, normalizedIncrement (e i k) (scale i k) (v i) (R i) (T i) (shift i k) (jb i) (η i) (smooth i) (X i (ω i)) *
          ∏ j ∈ Finset.univ.erase k, (scale i j * X i (ω i)) ^ (e i j).val)) =
    (FiniteLaw.independent μ).expect (fun ω => ∏ i, (∏ k, (scale i k * X i (ω i)) ^ (e i k).val) *
      (likelihood (R i) (T i) (jb i) (η i) (smooth i) (X i (ω i)) +
        realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i))) := by
  let L := fun i (ω : Ξ i) =>
    (∏ k, (scale i k * X i ω) ^ (e i k).val) * likelihood (R i) (T i) (jb i) (η i) (smooth i) (X i ω) +
      ∑ k, normalizedIncrement (e i k) (scale i k) (v i) (R i) (T i) (shift i k) (jb i) (η i) (smooth i) (X i ω) *
        ∏ j ∈ Finset.univ.erase k, (scale i j * X i ω) ^ (e i j).val
  let P := fun i (ω : Ξ i) => (∏ k, (scale i k * X i ω) ^ (e i k).val) *
    (likelihood (R i) (T i) (jb i) (η i) (smooth i) (X i ω) +
      realField (R i) (T i) (smooth i) ((shift i (owner i) * scale i (owner i)) * jb i * v i))
  change (FiniteLaw.independent μ).expect (fun ω => ∏ i, L i (ω i)) =
    (FiniteLaw.independent μ).expect (fun ω => ∏ i, P i (ω i))
  rw [FiniteLaw.expect_independent_prod μ L, FiniteLaw.expect_independent_prod μ P]
  apply Finset.prod_congr rfl
  intro i _
  exact assigned_row_bridge (μ i) (X i) (R i) (T i) (jb i) (η i) (v i) (smooth i)
    (shift i) (scale i) (owner i) (hscale i) (e i) (hmean i) (hvar i) (hthird i) (hcorrection i)

end CausalLowerbound.PartC.RoughOutcome
